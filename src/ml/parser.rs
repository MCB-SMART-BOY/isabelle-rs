use super::lexer::{Token, TokenKind, check_stop, tokenize};
use super::syntax::{Fixity, SourceLocation};
use super::{
    Declaration, Expr, MlError, MlErrorKind, ModuleExpr, Pattern, SignatureExpr, Span,
    Specification, TypeExpr,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::AtomicBool;

const POSITION_CHECKPOINT_BYTES: usize = 256;

#[derive(Clone, Copy)]
struct PositionCheckpoint {
    byte: usize,
    line: i64,
    offset: i64,
}

// Cache symbols at least one checkpoint stride long so position lookups never
// rescan an unbounded symbol; shorter symbols cost at most one bounded scan.
#[derive(Clone, Copy)]
struct LongSymbol {
    start: PositionCheckpoint,
    end: PositionCheckpoint,
}

struct SourcePositions<'a> {
    source: &'a str,
    checkpoints: Vec<PositionCheckpoint>,
    long_symbols: Vec<LongSymbol>,
}

impl<'a> SourcePositions<'a> {
    fn new(source_name: &str, source: &'a str, stop: &AtomicBool) -> Result<Self, MlError> {
        let mut current = PositionCheckpoint { byte: 0, line: 1, offset: 1 };
        let mut checkpoints = vec![current];
        let mut long_symbols = Vec::new();
        while current.byte < source.len() {
            if current.byte - checkpoints.last().map_or(0, |checkpoint| checkpoint.byte)
                >= POSITION_CHECKPOINT_BYTES
            {
                checkpoints.push(current);
                check_stop(stop, source_name, current.byte)?;
            }
            let start = current;
            let (next, is_newline) = next_symbol(source, current.byte, stop, source_name)?;
            current = PositionCheckpoint {
                byte: next,
                line: current.line + i64::from(is_newline),
                offset: current.offset + 1,
            };
            if next - start.byte >= POSITION_CHECKPOINT_BYTES {
                long_symbols.push(LongSymbol { start, end: current });
            }
        }
        check_stop(stop, source_name, current.byte)?;
        Ok(Self { source, checkpoints, long_symbols })
    }

    fn line_position(
        &self,
        byte: usize,
        stop: &AtomicBool,
        source_name: &str,
    ) -> Result<(i64, i64), MlError> {
        let long_index = self.long_symbols.partition_point(|symbol| symbol.start.byte <= byte);
        if let Some(symbol) =
            long_index.checked_sub(1).and_then(|index| self.long_symbols.get(index))
            && byte <= symbol.end.byte
        {
            let position = if byte == symbol.end.byte { symbol.end } else { symbol.start };
            check_stop(stop, source_name, byte)?;
            return Ok((position.line, position.offset));
        }
        let index = self.checkpoints.partition_point(|checkpoint| checkpoint.byte <= byte) - 1;
        let mut current = self.checkpoints[index];
        while current.byte < byte {
            let (next, is_newline) = next_symbol(self.source, current.byte, stop, source_name)?;
            if next > byte {
                break;
            }
            current.byte = next;
            current.line += i64::from(is_newline);
            current.offset += 1;
        }
        Ok((current.line, current.offset))
    }
}

// Match Isabelle Symbol.explode: UTF-8 and \<name> each count as one symbol,
// and CRLF or CR count as one newline. Positions are global 1-based offsets.
fn next_symbol(
    source: &str,
    byte: usize,
    stop: &AtomicBool,
    source_name: &str,
) -> Result<(usize, bool), MlError> {
    let tail = source.get(byte..).filter(|tail| !tail.is_empty()).ok_or_else(|| {
        MlError::new(
            MlErrorKind::HostFailure,
            Span::new(source_name, byte, byte),
            "source position",
            format!("invalid symbol boundary at byte {byte}"),
        )
    })?;
    let bytes = source.as_bytes();
    if bytes[byte] == b'\r' {
        return Ok((byte + if bytes.get(byte + 1) == Some(&b'\n') { 2 } else { 1 }, true));
    }
    if bytes[byte] == b'\\' && bytes.get(byte + 1) == Some(&b'<') {
        let mut next = byte + 2;
        if bytes.get(next) == Some(&b'^') {
            next += 1;
        }
        if bytes.get(next).is_some_and(u8::is_ascii_alphabetic) {
            next += 1;
            while bytes
                .get(next)
                .is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_' || *c == b'\'')
            {
                if (next - byte).is_multiple_of(POSITION_CHECKPOINT_BYTES) {
                    check_stop(stop, source_name, next)?;
                }
                next += 1;
            }
        }
        if bytes.get(next) == Some(&b'>') {
            next += 1;
        }
        return Ok((next, false));
    }
    let character = tail.chars().next().ok_or_else(|| {
        MlError::new(
            MlErrorKind::HostFailure,
            Span::new(source_name, byte, byte),
            "source position",
            format!("missing symbol at byte {byte}"),
        )
    })?;
    Ok((byte + character.len_utf8(), character == '\n'))
}

pub(super) type FixityEnvironment = BTreeMap<String, Fixity>;

pub(super) fn parse(
    source_name: &str,
    source: &str,
    fixities: &FixityEnvironment,
    stop: &AtomicBool,
) -> Result<Vec<Declaration>, MlError> {
    let tokens = tokenize(source_name, source, stop)?;
    let mut parser = Parser {
        tokens,
        positions: SourcePositions::new(source_name, source, stop)?,
        stop,
        offset: 0,
        fixities: fixities.clone(),
        declared_fixities: BTreeSet::new(),
    };
    let mut declarations = Vec::new();
    while !matches!(parser.token().kind, TokenKind::Eof) {
        parser.check_stop()?;
        if parser.eat_symbol(';') {
            continue;
        }
        declarations.push(parser.declaration()?);
        parser.eat_symbol(';');
    }
    parser.check_stop()?;
    parser.require_end()?;
    Ok(declarations)
}

struct Parser<'a> {
    tokens: Vec<Token>,
    offset: usize,
    fixities: FixityEnvironment,
    declared_fixities: BTreeSet<String>,
    positions: SourcePositions<'a>,
    stop: &'a AtomicBool,
}

impl Parser<'_> {
    fn source_location(&self, start: Span, end: usize) -> Result<SourceLocation, MlError> {
        let (start_line, start_position) =
            self.positions.line_position(start.start, self.stop, &start.source_name)?;
        let (end_line, end_position) =
            self.positions.line_position(end, self.stop, &start.source_name)?;
        Ok(SourceLocation {
            span: Span::new(&start.source_name, start.start, end),
            start_line,
            start_position,
            end_line,
            end_position,
        })
    }

    fn check_stop(&self) -> Result<(), MlError> {
        let span = &self.token().span;
        check_stop(self.stop, &span.source_name, span.start)
    }
    fn token(&self) -> &Token {
        &self.tokens[self.offset]
    }
    fn span(&self) -> Span {
        self.token().span.clone()
    }
    fn name(&self) -> Option<&str> {
        if let TokenKind::Name(name) = &self.token().kind { Some(name) } else { None }
    }
    fn at(&self, name: &str) -> bool {
        self.name() == Some(name)
    }
    fn symbol(&self, symbol: char) -> bool {
        self.token().kind == TokenKind::Symbol(symbol)
    }
    fn bump(&mut self) -> Token {
        let token = self.token().clone();
        if !matches!(token.kind, TokenKind::Eof) {
            self.offset += 1;
        }
        token
    }
    fn eat(&mut self, name: &str) -> bool {
        if self.at(name) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn eat_symbol(&mut self, symbol: char) -> bool {
        if self.symbol(symbol) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn error(&self, message: impl Into<String>) -> MlError {
        MlError::syntax(self.span(), message)
    }
    fn expect(&mut self, name: &str) -> Result<(), MlError> {
        if self.eat(name) { Ok(()) } else { Err(self.error(format!("expected {name}"))) }
    }
    fn expect_symbol(&mut self, symbol: char) -> Result<(), MlError> {
        if self.eat_symbol(symbol) { Ok(()) } else { Err(self.error(format!("expected {symbol}"))) }
    }
    fn identifier(&mut self) -> Result<String, MlError> {
        self.check_stop()?;
        let TokenKind::Name(name) = self.bump().kind else {
            return Err(self.error("expected identifier"));
        };
        if KEYWORDS.contains(&name.as_str())
            || name.chars().next().is_some_and(|c| !c.is_alphabetic() && c != '_')
        {
            return Err(self.error(format!("invalid identifier {name}")));
        }
        Ok(name)
    }
    fn value_identifier(&mut self) -> Result<String, MlError> {
        self.read_value_identifier(false)
    }
    fn read_value_identifier(&mut self, allow_infix: bool) -> Result<String, MlError> {
        self.check_stop()?;
        let is_op = self.eat("op");
        let TokenKind::Name(name) = &self.token().kind else {
            return Err(self.error("expected value identifier"));
        };
        if KEYWORDS.contains(&name.as_str())
            || (!allow_infix && !is_op && self.fixities.contains_key(name))
        {
            return Err(self.error(format!("value identifier {name} requires op")));
        }
        let name = name.clone();
        self.bump();
        Ok(name)
    }
    fn fixity_declaration(&mut self, span: Span) -> Result<Declaration, MlError> {
        let fixity = if self.eat("infix") {
            Some(Fixity::Left(self.fixity_precedence()?))
        } else if self.eat("infixr") {
            Some(Fixity::Right(self.fixity_precedence()?))
        } else {
            self.expect("nonfix")?;
            None
        };
        let mut names = Vec::new();
        while let Some(name) = self.name() {
            self.check_stop()?;
            if KEYWORDS.contains(&name) || name == "=" || name == "|" {
                break;
            }
            let name = name.to_owned();
            self.bump();
            match &fixity {
                Some(fixity) => {
                    self.fixities.insert(name.clone(), fixity.clone());
                },
                None => {
                    self.fixities.remove(&name);
                },
            }
            self.declared_fixities.insert(name.clone());
            names.push(name);
        }
        if names.is_empty() {
            return Err(self.error("fixity declaration requires an identifier"));
        }
        Ok(Declaration::Fixity { names, fixity, span })
    }
    fn fixity_precedence(&mut self) -> Result<u8, MlError> {
        if self.at("~")
            && matches!(
                self.tokens.get(self.offset + 1).map(|token| &token.kind),
                Some(TokenKind::Integer { .. })
            )
        {
            return Err(self.error("fixity precedence must be 0..9"));
        }
        let precedence = match &self.token().kind {
            TokenKind::Integer { is_negative: true, .. } => {
                return Err(self.error("fixity precedence must be an unsigned integer 0..9"));
            },
            TokenKind::Integer { value, .. } => *value,
            _ => return Ok(0),
        };
        if !(0..=i64::from(MAX_FIXITY_LEVEL)).contains(&precedence) {
            return Err(self.error(format!("fixity precedence {precedence} must be 0..9")));
        }
        self.bump();
        Ok(precedence as u8)
    }
    fn restore_fixities(&mut self, saved: FixityEnvironment, declared: BTreeSet<String>) {
        self.fixities = saved;
        self.declared_fixities = declared;
    }
    fn function_head(&mut self) -> Result<(String, Vec<Pattern>), MlError> {
        let start = self.offset;
        if self.eat_symbol('(') && self.begins_pattern() {
            let left = self.pattern_atom()?;
            if let Some(name) = self.name().filter(|name| self.fixities.contains_key(*name)) {
                let name = name.to_owned();
                self.bump();
                let right = self.pattern_atom()?;
                self.expect_symbol(')')?;
                return Ok((name, vec![Pattern::Tuple(vec![left, right])]));
            }
        }
        self.offset = start;
        if self.at("op") {
            let name = self.value_identifier()?;
            return Ok((name, Vec::new()));
        }
        if self.begins_pattern() {
            let left = self.pattern_atom()?;
            if let Some(name) = self.name().filter(|name| self.fixities.contains_key(*name)) {
                let name = name.to_owned();
                self.bump();
                let right = self.pattern_atom()?;
                return Ok((name, vec![Pattern::Tuple(vec![left, right])]));
            }
        }
        self.offset = start;
        Ok((self.value_identifier()?, Vec::new()))
    }
    fn function_clause(
        &mut self,
        mut arguments: Vec<Pattern>,
    ) -> Result<(Vec<Pattern>, Expr), MlError> {
        while !self.at("=") && !self.at(":") {
            if !self.begins_pattern() {
                return Err(self.error("expected function argument"));
            }
            arguments.push(self.pattern_atom()?);
        }
        if arguments.is_empty() {
            return Err(self.error("function requires argument"));
        }
        let result_type = if self.eat(":") { Some(self.type_expression()?) } else { None };
        self.expect("=")?;
        let body = self.expression(0)?;
        let body = match result_type {
            Some(typ) => Expr::Typed(Box::new(body), typ),
            None => body,
        };
        Ok((arguments, body))
    }
    fn require_end(&self) -> Result<(), MlError> {
        if matches!(self.token().kind, TokenKind::Eof) {
            Ok(())
        } else {
            Err(self.error("unconsumed input"))
        }
    }
    fn declarations(&mut self, stops: &[&str]) -> Result<Vec<Declaration>, MlError> {
        let mut declarations = Vec::new();
        while !matches!(self.token().kind, TokenKind::Eof)
            && !self.name().is_some_and(|name| stops.contains(&name))
            && !(stops.contains(&")") && self.symbol(')'))
        {
            self.check_stop()?;
            if self.eat_symbol(';') {
                continue;
            }
            let before = self.offset;
            declarations.push(self.declaration()?);
            if self.offset == before {
                return Err(self.error("declaration did not consume input"));
            }
            self.eat_symbol(';');
        }
        Ok(declarations)
    }
    fn declaration(&mut self) -> Result<Declaration, MlError> {
        self.check_stop()?;
        let span = self.span();
        if self.at("infix") || self.at("infixr") || self.at("nonfix") {
            return self.fixity_declaration(span);
        }
        if self.eat("val") {
            let recursive = self.eat("rec");
            let mut bindings = Vec::new();
            loop {
                let pattern = self.pattern()?;
                self.expect("=")?;
                let expression = self.expression(0)?;
                bindings.push((pattern, expression));
                if !self.eat("and") {
                    break;
                }
            }
            return Ok(Declaration::Value { recursive, bindings, span });
        }
        if self.eat("fun") {
            let mut bindings = Vec::new();
            loop {
                let (name, mut first_arguments) = self.function_head()?;
                let head_arity = first_arguments.len();
                let mut clauses = Vec::new();
                loop {
                    clauses.push(self.function_clause(std::mem::take(&mut first_arguments))?);
                    if !self.eat("|") {
                        break;
                    }
                    let (alternate, next_arguments) = self.function_head()?;
                    if next_arguments.len() != head_arity {
                        return Err(self.error("all function clauses must have the same form"));
                    }
                    if alternate != name {
                        return Err(self.error("all function clauses must have the same name"));
                    }
                    first_arguments = next_arguments;
                }
                bindings.push((name, clauses));
                if !self.eat("and") {
                    break;
                }
            }
            return Ok(Declaration::Function { bindings, span });
        }
        if self.eat("exception") {
            let name = self.identifier()?;
            let alias = if self.eat("=") { Some(self.path()?) } else { None };
            let argument = if self.eat("of") { Some(self.type_expression()?) } else { None };
            if alias.is_some() && argument.is_some() {
                return Err(self.error("exception alias cannot have argument"));
            }
            return Ok(Declaration::Exception { name, alias, argument, span });
        }
        if self.eat("datatype") {
            return self.datatype_declaration(span, false);
        }
        if self.eat("abstype") {
            return self.datatype_declaration(span, true);
        }
        if self.eat("type") || self.eat("eqtype") {
            let parameters = self.type_parameters()?;
            let name = self.identifier()?;
            self.expect("=")?;
            return Ok(Declaration::Type {
                name,
                parameters,
                definition: self.type_expression()?,
                span,
            });
        }
        if self.eat("local") {
            let saved = self.fixities.clone();
            let outer = std::mem::take(&mut self.declared_fixities);
            let local = self.declarations(&["in"])?;
            self.expect("in")?;
            self.declared_fixities.clear();
            let body = self.declarations(&["end"])?;
            self.expect("end")?;
            let exported = std::mem::replace(&mut self.declared_fixities, outer);
            let changes = exported
                .iter()
                .map(|name| (name.clone(), self.fixities.get(name).cloned()))
                .collect::<Vec<_>>();
            self.fixities = saved;
            for (name, fixity) in changes {
                match fixity {
                    Some(fixity) => {
                        self.fixities.insert(name, fixity);
                    },
                    None => {
                        self.fixities.remove(&name);
                    },
                }
            }
            self.declared_fixities.extend(exported);
            return Ok(Declaration::Local { local, body, span });
        }
        if self.eat("open") {
            let mut names = vec![self.path()?];
            while self.name().is_some_and(|name| !KEYWORDS.contains(&name)) {
                names.push(self.path()?);
            }
            return Ok(Declaration::Open { names, span });
        }
        if self.eat("structure") {
            let name = self.identifier()?;
            let signature = if self.eat(":") {
                Some((self.signature_expression()?, false))
            } else if self.eat(":>") {
                Some((self.signature_expression()?, true))
            } else {
                None
            };
            self.expect("=")?;
            return Ok(Declaration::Structure {
                name,
                signature,
                body: self.scoped_module_expression()?,
                span,
            });
        }
        if self.eat("signature") {
            let name = self.identifier()?;
            self.expect("=")?;
            let SignatureExpr { base, body } = self.signature_expression()?;
            return Ok(Declaration::Signature { name, base, body, span });
        }
        if self.eat("functor") {
            let name = self.identifier()?;
            self.expect_symbol('(')?;
            let parameter = self.identifier()?;
            self.expect(":")?;
            let signature = self.signature_expression()?;
            self.expect_symbol(')')?;
            let result = if self.eat(":") {
                Some((self.signature_expression()?, false))
            } else if self.eat(":>") {
                Some((self.signature_expression()?, true))
            } else {
                None
            };
            self.expect("=")?;
            let body = self.scoped_module_expression()?;
            let body = match result {
                Some((name, opaque)) => ModuleExpr::Constrained(Box::new(body), name, opaque),
                None => body,
            };
            return Ok(Declaration::Functor { name, parameter, signature, body, span });
        }
        Ok(Declaration::Expression(self.expression(0)?, span))
    }
    fn datatype_declaration(
        &mut self,
        span: Span,
        is_abstract: bool,
    ) -> Result<Declaration, MlError> {
        let type_span = if is_abstract { self.span() } else { span.clone() };
        let parameters = self.type_parameters()?;
        let name = self.identifier()?;
        self.expect("=")?;
        if !is_abstract && self.eat("datatype") {
            if !parameters.is_empty() {
                return Err(self.error("datatype replication cannot declare type parameters"));
            }
            return Ok(Declaration::DatatypeReplication { name, source: self.path()?, span });
        }
        let mut constructors = Vec::new();
        loop {
            let constructor = self.identifier()?;
            let argument = if self.eat("of") { Some(self.type_expression()?) } else { None };
            constructors.push((constructor, argument));
            if !self.eat("|") {
                break;
            }
        }
        let datatype = Declaration::Datatype { name, parameters, constructors, span: type_span };
        if !is_abstract {
            return Ok(datatype);
        }
        self.expect("with")?;
        let body = self.declarations(&["end"])?;
        self.expect("end")?;
        Ok(Declaration::Abstype { datatype: Box::new(datatype), body, span })
    }

    fn signature_expression(&mut self) -> Result<SignatureExpr, MlError> {
        let base = if self.eat("sig") { None } else { Some(self.identifier()?) };
        let mut body = Vec::new();
        if base.is_none() {
            while !self.at("end") {
                self.check_stop()?;
                body.push(self.specification()?);
                self.eat_symbol(';');
            }
            self.expect("end")?;
        }
        while self.eat("where") {
            self.expect("type")?;
            let parameters = self.type_parameters()?;
            let name = self.path()?;
            self.expect("=")?;
            body.push(Specification::WhereType {
                name,
                parameters,
                definition: self.type_expression()?,
            });
        }
        Ok(SignatureExpr { base, body })
    }

    fn specification(&mut self) -> Result<Specification, MlError> {
        self.check_stop()?;
        if self.eat("val") {
            let name = self.read_value_identifier(true)?;
            self.expect(":")?;
            return Ok(Specification::Value(name, self.type_expression()?));
        }
        let equality = self.eat("eqtype");
        if equality || self.eat("type") {
            let parameters = self.type_parameters()?;
            let name = self.identifier()?;
            let definition = if self.eat("=") { Some(self.type_expression()?) } else { None };
            return Ok(Specification::Type { name, parameters, equality, definition });
        }
        if self.eat("datatype") {
            let parameters = self.type_parameters()?;
            let name = self.identifier()?;
            self.expect("=")?;
            if self.eat("datatype") {
                if !parameters.is_empty() {
                    return Err(self.error("datatype replication cannot declare parameters"));
                }
                return Ok(Specification::DatatypeReplication(name, self.path()?));
            }
            let mut constructors = Vec::new();
            loop {
                let constructor = self.identifier()?;
                let argument = if self.eat("of") { Some(self.type_expression()?) } else { None };
                constructors.push((constructor, argument));
                if !self.eat("|") {
                    break;
                }
            }
            return Ok(Specification::Datatype(name, parameters, constructors));
        }
        if self.eat("exception") {
            let name = self.identifier()?;
            let argument = if self.eat("of") { Some(self.type_expression()?) } else { None };
            return Ok(Specification::Exception(name, argument));
        }
        if self.eat("structure") {
            let name = self.identifier()?;
            self.expect(":")?;
            return Ok(Specification::Structure(name, self.signature_expression()?));
        }
        if self.eat("include") {
            return Ok(Specification::Include(self.identifier()?));
        }
        if self.eat("sharing") {
            self.expect("type")?;
            let mut paths = vec![self.path()?];
            while self.eat("=") {
                paths.push(self.path()?);
            }
            if paths.len() < 2 {
                return Err(self.error("sharing needs two paths"));
            }
            return Ok(Specification::Sharing(paths));
        }
        Err(self.error("unsupported signature specification"))
    }
    fn scoped_module_expression(&mut self) -> Result<ModuleExpr, MlError> {
        let saved = self.fixities.clone();
        let declared = std::mem::take(&mut self.declared_fixities);
        let body = self.module_expression()?;
        self.restore_fixities(saved, declared);
        Ok(body)
    }
    fn module_expression(&mut self) -> Result<ModuleExpr, MlError> {
        self.check_stop()?;
        let mut module = if self.eat("struct") {
            let body = self.declarations(&["end"])?;
            self.expect("end")?;
            ModuleExpr::Struct(body)
        } else {
            let name = self.path()?;
            if self.eat_symbol('(') {
                let argument = if self.name().is_some_and(|name| {
                    matches!(
                        name,
                        "type"
                            | "eqtype"
                            | "val"
                            | "fun"
                            | "datatype"
                            | "abstype"
                            | "exception"
                            | "structure"
                            | "open"
                            | "local"
                    )
                }) {
                    ModuleExpr::Struct(self.declarations(&[")"])?)
                } else {
                    self.module_expression()?
                };
                self.expect_symbol(')')?;
                ModuleExpr::Apply(name, Box::new(argument))
            } else {
                ModuleExpr::Name(name)
            }
        };
        if self.eat(":") {
            module = ModuleExpr::Constrained(Box::new(module), self.signature_expression()?, false);
        } else if self.eat(":>") {
            module = ModuleExpr::Constrained(Box::new(module), self.signature_expression()?, true);
        }
        Ok(module)
    }
    fn path(&mut self) -> Result<String, MlError> {
        let mut name = self.identifier()?;
        while self.eat_symbol('.') {
            name.push('.');
            name.push_str(&self.read_value_identifier(true)?);
        }
        Ok(name)
    }
    fn type_parameters(&mut self) -> Result<Vec<String>, MlError> {
        if self.eat_symbol('(') {
            let mut parameters = Vec::new();
            loop {
                parameters.push(self.type_variable()?);
                if !self.eat_symbol(',') {
                    break;
                }
            }
            self.expect_symbol(')')?;
            return Ok(parameters);
        }
        if self.name().is_some_and(|name| name.starts_with('\'')) {
            return Ok(vec![self.type_variable()?]);
        }
        Ok(Vec::new())
    }
    fn type_variable(&mut self) -> Result<String, MlError> {
        self.check_stop()?;
        let Some(name) = self.name().filter(|name| name.starts_with('\'')) else {
            return Err(self.error("expected type variable"));
        };
        let value = name.to_owned();
        self.bump();
        Ok(value)
    }
    fn type_expression(&mut self) -> Result<TypeExpr, MlError> {
        self.check_stop()?;
        let lhs = self.type_product()?;
        if self.eat("->") {
            Ok(TypeExpr::Function(Box::new(lhs), Box::new(self.type_expression()?)))
        } else {
            Ok(lhs)
        }
    }
    fn type_product(&mut self) -> Result<TypeExpr, MlError> {
        let mut types = vec![self.type_atom()?];
        while self.eat("*") {
            types.push(self.type_atom()?);
        }
        if types.len() == 1 { Ok(types.remove(0)) } else { Ok(TypeExpr::Tuple(types)) }
    }
    fn type_atom(&mut self) -> Result<TypeExpr, MlError> {
        let mut typ = if self.eat_symbol('(') {
            let first = self.type_expression()?;
            if self.eat_symbol(',') {
                let mut arguments = vec![first];
                loop {
                    arguments.push(self.type_expression()?);
                    if !self.eat_symbol(',') {
                        break;
                    }
                }
                self.expect_symbol(')')?;
                TypeExpr::Named(self.path()?, arguments)
            } else {
                self.expect_symbol(')')?;
                first
            }
        } else if self.eat_symbol('{') {
            let mut fields = Vec::new();
            if !self.symbol('}') {
                loop {
                    let label = self.label()?;
                    self.expect(":")?;
                    fields.push((label, self.type_expression()?));
                    if !self.eat_symbol(',') {
                        break;
                    }
                }
            }
            self.expect_symbol('}')?;
            TypeExpr::Record(fields)
        } else if self.name().is_some_and(|name| name.starts_with('\'')) {
            TypeExpr::Var(self.type_variable()?)
        } else {
            TypeExpr::Named(self.path()?, Vec::new())
        };
        while self.name().is_some_and(|name| {
            !KEYWORDS.contains(&name)
                && !name.starts_with('\'')
                && name.chars().next().is_some_and(char::is_alphabetic)
        }) {
            typ = TypeExpr::Named(self.path()?, vec![typ]);
        }
        Ok(typ)
    }
    fn label(&mut self) -> Result<String, MlError> {
        match self.bump().kind {
            TokenKind::Name(name) => Ok(name),
            TokenKind::Integer { value, is_negative: false } if value > 0 => Ok(value.to_string()),
            _ => Err(self.error("expected record label")),
        }
    }
    fn begins_pattern(&self) -> bool {
        matches!(
            self.token().kind,
            TokenKind::Integer { .. }
                | TokenKind::Word(_)
                | TokenKind::Text(_)
                | TokenKind::Character(_)
                | TokenKind::Symbol('(' | '[' | '{')
        ) || self.at("op")
            || self.name().is_some_and(|name| {
                !KEYWORDS.contains(&name)
                    && !self.fixities.contains_key(name)
                    && name != "="
                    && name != "|"
                    && name != "=>"
                    && name != ":"
            })
    }
    fn pattern(&mut self) -> Result<Pattern, MlError> {
        self.check_stop()?;
        let mut pattern = self.pattern_atom()?;
        if self.eat("as") {
            let Pattern::Variable(name) = pattern else {
                return Err(self.error("as pattern requires variable"));
            };
            pattern = Pattern::As(name, Box::new(self.pattern()?));
        } else if self.begins_pattern()
            && let Pattern::Variable(name) | Pattern::Constructor(name, None) = pattern
        {
            pattern = Pattern::Constructor(name, Some(Box::new(self.pattern_atom()?)));
        }
        if self.fixities.contains_key("::") && self.eat("::") {
            let tail = self.pattern()?;
            pattern = Pattern::Constructor(
                "::".to_owned(),
                Some(Box::new(Pattern::Tuple(vec![pattern, tail]))),
            );
        }
        if self.eat(":") {
            pattern = Pattern::Typed(Box::new(pattern), self.type_expression()?);
        }
        Ok(pattern)
    }
    fn pattern_atom(&mut self) -> Result<Pattern, MlError> {
        self.check_stop()?;
        if self.at("op") {
            return Ok(Pattern::Variable(self.value_identifier()?));
        }
        if self.eat("_") {
            return Ok(Pattern::Wildcard);
        }
        if self.eat_symbol('(') {
            if self.eat_symbol(')') {
                return Ok(Pattern::Unit);
            }
            let first = self.pattern()?;
            if !self.eat_symbol(',') {
                self.expect_symbol(')')?;
                return Ok(first);
            }
            let mut elements = vec![first];
            loop {
                elements.push(self.pattern()?);
                if !self.eat_symbol(',') {
                    break;
                }
            }
            self.expect_symbol(')')?;
            return Ok(Pattern::Tuple(elements));
        }
        if self.eat_symbol('[') {
            let mut elements = Vec::new();
            if !self.symbol(']') {
                loop {
                    elements.push(self.pattern()?);
                    if !self.eat_symbol(',') {
                        break;
                    }
                }
            }
            self.expect_symbol(']')?;
            return Ok(Pattern::List(elements));
        }
        if self.eat_symbol('{') {
            let mut fields = Vec::new();
            let mut flexible = false;
            while !self.symbol('}') {
                if self.eat("...") {
                    flexible = true;
                    break;
                }
                let label = self.label()?;
                let pattern =
                    if self.eat("=") { self.pattern()? } else { Pattern::Variable(label.clone()) };
                fields.push((label, pattern));
                if !self.eat_symbol(',') {
                    break;
                }
            }
            self.expect_symbol('}')?;
            return Ok(Pattern::Record(fields, flexible));
        }
        let token = self.bump();
        match token.kind {
            TokenKind::Integer { value, .. } => Ok(Pattern::Integer(value)),
            TokenKind::Word(value) => Ok(Pattern::Word { value, span: token.span }),
            TokenKind::Text(text) => Ok(Pattern::Text(text)),
            TokenKind::Character(character) => Ok(Pattern::Character(character)),
            TokenKind::Name(name) if name == "true" || name == "false" || name == "nil" => {
                Ok(Pattern::Constructor(name, None))
            },
            TokenKind::Name(mut name)
                if !KEYWORDS.contains(&name.as_str()) && !self.fixities.contains_key(&name) =>
            {
                while self.eat_symbol('.') {
                    name.push('.');
                    name.push_str(&self.read_value_identifier(true)?);
                }
                Ok(Pattern::Variable(name))
            },
            TokenKind::Name(name) => {
                Err(self.error(format!("pattern identifier {name} requires op")))
            },
            _ => Err(self.error("expected pattern")),
        }
    }
    fn begins_atom(&self) -> bool {
        matches!(
            self.token().kind,
            TokenKind::Integer { .. }
                | TokenKind::Word(_)
                | TokenKind::Real(_)
                | TokenKind::Text(_)
                | TokenKind::Character(_)
                | TokenKind::Symbol('(' | '[' | '{')
        ) || self.at("op")
            || self.at("let")
            || self.name().is_some_and(|name| {
                !KEYWORDS.contains(&name)
                    && !["|", "=>", ":", "->"].contains(&name)
                    && !self.fixities.contains_key(name)
            })
    }
    fn expression(&mut self, minimum: u8) -> Result<Expr, MlError> {
        self.expression_chain(minimum, None)
    }
    fn operator(&self) -> Option<(u8, bool)> {
        match self.name()? {
            "orelse" => Some((ORELSE_PRECEDENCE, true)),
            "andalso" => Some((ANDALSO_PRECEDENCE, true)),
            name => self.fixities.get(name).map(|fixity| match fixity {
                Fixity::Left(level) => (INFIX_PRECEDENCE_BASE + level * 2, false),
                Fixity::Right(level) => (INFIX_PRECEDENCE_BASE + level * 2, true),
            }),
        }
    }
    fn expression_chain(
        &mut self,
        minimum: u8,
        mut previous: Option<(u8, bool)>,
    ) -> Result<Expr, MlError> {
        self.check_stop()?;
        let mut lhs = self.prefix()?;
        loop {
            self.check_stop()?;
            if minimum <= APPLICATION_PRECEDENCE && self.begins_atom() {
                let start = self.span();
                let argument = self.atom()?;
                let end = self.tokens[self.offset - 1].span.end;
                lhs = Expr::Located(
                    Box::new(Expr::Apply(Box::new(lhs), Box::new(argument))),
                    self.source_location(start, end)?,
                );
                continue;
            }
            if self.at(":") && minimum <= 2 {
                self.bump();
                lhs = Expr::Typed(Box::new(lhs), self.type_expression()?);
                continue;
            }
            if self.at("handle") && minimum <= 1 {
                self.bump();
                lhs = Expr::Handle(Box::new(lhs), self.matches()?);
                continue;
            }
            let Some((precedence, is_right_associative)) = self.operator() else { break };
            if precedence < minimum {
                break;
            }
            if let Some((last_precedence, was_right_associative)) = previous
                && precedence == last_precedence
                && is_right_associative != was_right_associative
            {
                return Err(self.error("mixed associativity at the same precedence"));
            }
            let operation = self.bump();
            let rhs = self.expression_chain(
                precedence + u8::from(!is_right_associative),
                is_right_associative.then_some((precedence, is_right_associative)),
            )?;
            lhs = match operation.kind {
                TokenKind::Name(name) if name == "andalso" => {
                    Expr::AndAlso(Box::new(lhs), Box::new(rhs))
                },
                TokenKind::Name(name) if name == "orelse" => {
                    Expr::OrElse(Box::new(lhs), Box::new(rhs))
                },
                TokenKind::Name(name) => Expr::Located(
                    Box::new(Expr::Apply(
                        Box::new(Expr::Name(name)),
                        Box::new(Expr::Tuple(vec![lhs, rhs])),
                    )),
                    self.source_location(
                        operation.span.clone(),
                        self.tokens[self.offset - 1].span.end,
                    )?,
                ),
                _ => return Err(self.error("invalid infix operator")),
            };
            previous = Some((precedence, is_right_associative));
        }
        Ok(lhs)
    }
    fn prefix(&mut self) -> Result<Expr, MlError> {
        if self.eat("fn") {
            let start = self.tokens[self.offset - 1].span.clone();
            let clauses = self.matches()?;
            let end = self.tokens[self.offset - 1].span.end;
            return Ok(Expr::Located(
                Box::new(Expr::Fn(clauses)),
                self.source_location(start, end)?,
            ));
        }
        if self.eat("if") {
            let condition = self.expression(0)?;
            self.expect("then")?;
            let yes = self.expression(0)?;
            self.expect("else")?;
            return Ok(Expr::If(Box::new(condition), Box::new(yes), Box::new(self.expression(0)?)));
        }
        if self.eat("while") {
            let condition = self.expression(0)?;
            self.expect("do")?;
            return Ok(Expr::While(Box::new(condition), Box::new(self.expression(0)?)));
        }
        if self.eat("case") {
            let target = self.expression(0)?;
            self.expect("of")?;
            return Ok(Expr::Case(Box::new(target), self.matches()?));
        }
        if self.at("raise") {
            let start = self.bump().span;
            let body = self.expression(2)?;
            let end = self.tokens[self.offset - 1].span.end;
            return Ok(Expr::Located(
                Box::new(Expr::Raise(Box::new(body))),
                self.source_location(start, end)?,
            ));
        }
        self.atom()
    }
    fn matches(&mut self) -> Result<Vec<(Pattern, Expr)>, MlError> {
        let mut clauses = Vec::new();
        loop {
            let pattern = self.pattern()?;
            self.expect("=>")?;
            clauses.push((pattern, self.expression(0)?));
            if !self.eat("|") {
                break;
            }
        }
        Ok(clauses)
    }
    fn sequence(&mut self, terminator: char) -> Result<Expr, MlError> {
        let mut expressions = vec![self.expression(0)?];
        while self.eat_symbol(';') && !(terminator == 'e' && self.at("end")) && !self.symbol(')') {
            expressions.push(self.expression(0)?);
        }
        if expressions.len() == 1 {
            Ok(expressions.remove(0))
        } else {
            Ok(Expr::Sequence(expressions))
        }
    }
    fn atom(&mut self) -> Result<Expr, MlError> {
        self.check_stop()?;
        if self.eat("let") {
            let saved = self.fixities.clone();
            let declared = std::mem::take(&mut self.declared_fixities);
            let declarations = self.declarations(&["in"])?;
            self.expect("in")?;
            let expression = self.sequence('e')?;
            self.expect("end")?;
            self.restore_fixities(saved, declared);
            return Ok(Expr::Let(declarations, Box::new(expression)));
        }
        if self.eat("op") {
            let mut name = self.read_value_identifier(true)?;
            while self.eat_symbol('.') {
                name.push('.');
                name.push_str(&self.read_value_identifier(true)?);
            }
            return Ok(Expr::Name(name));
        }
        if self.eat_symbol('(') {
            if self.eat_symbol(')') {
                return Ok(Expr::Unit);
            }
            let first = self.expression(0)?;
            if self.eat_symbol(',') {
                let mut elements = vec![first];
                loop {
                    elements.push(self.expression(0)?);
                    if !self.eat_symbol(',') {
                        break;
                    }
                }
                self.expect_symbol(')')?;
                return Ok(Expr::Tuple(elements));
            }
            if self.eat_symbol(';') {
                let mut expressions = vec![first];
                loop {
                    expressions.push(self.expression(0)?);
                    if !self.eat_symbol(';') {
                        break;
                    }
                }
                self.expect_symbol(')')?;
                return Ok(Expr::Sequence(expressions));
            }
            self.expect_symbol(')')?;
            return Ok(first);
        }
        if self.eat_symbol('[') {
            let mut elements = Vec::new();
            if !self.symbol(']') {
                loop {
                    elements.push(self.expression(0)?);
                    if !self.eat_symbol(',') {
                        break;
                    }
                }
            }
            self.expect_symbol(']')?;
            return Ok(Expr::List(elements));
        }
        if self.eat_symbol('{') {
            let mut fields = Vec::new();
            if !self.symbol('}') {
                loop {
                    let label = self.label()?;
                    self.expect("=")?;
                    fields.push((label, self.expression(0)?));
                    if !self.eat_symbol(',') {
                        break;
                    }
                }
            }
            self.expect_symbol('}')?;
            return Ok(Expr::Record(fields));
        }
        if self.eat("#") {
            return Ok(Expr::Select(self.label()?));
        }
        let token = self.bump();
        match token.kind {
            TokenKind::Integer { value, .. } => Ok(Expr::Integer(value)),
            TokenKind::Word(value) => Ok(Expr::Word { value, span: token.span }),
            TokenKind::Real(text) => text
                .parse::<f64>()
                .map(Expr::Real)
                .map_err(|cause| self.error(format!("invalid real literal {text}: {cause}"))),
            TokenKind::Text(text) => Ok(Expr::Text(text)),
            TokenKind::Character(character) => Ok(Expr::Character(character)),
            TokenKind::Name(name)
                if !KEYWORDS.contains(&name.as_str()) && !self.fixities.contains_key(&name) =>
            {
                let mut path = name;
                while self.eat_symbol('.') {
                    path.push('.');
                    path.push_str(&self.read_value_identifier(true)?);
                }
                Ok(Expr::Name(path))
            },
            _ => Err(self.error("expected expression")),
        }
    }
}

const MAX_FIXITY_LEVEL: u8 = 9;
const INFIX_PRECEDENCE_BASE: u8 = 10;
const APPLICATION_PRECEDENCE: u8 = INFIX_PRECEDENCE_BASE + (MAX_FIXITY_LEVEL + 1) * 2;
const ANDALSO_PRECEDENCE: u8 = 5;
const ORELSE_PRECEDENCE: u8 = 4;

const KEYWORDS: &[&str] = &[
    "abstype",
    "and",
    "andalso",
    "as",
    "case",
    "datatype",
    "do",
    "else",
    "end",
    "eqtype",
    "exception",
    "fn",
    "fun",
    "functor",
    "handle",
    "if",
    "in",
    "include",
    "infix",
    "infixr",
    "let",
    "local",
    "nonfix",
    "op",
    "of",
    "open",
    "orelse",
    "raise",
    "rec",
    "sharing",
    "sig",
    "signature",
    "struct",
    "structure",
    "then",
    "type",
    "val",
    "where",
    "while",
    "with",
    "withtype",
];
pub(super) fn basis_fixities() -> FixityEnvironment {
    let mut fixities = FixityEnvironment::new();
    for (precedence, names) in [
        (7, &["*", "/", "div", "mod"][..]),
        (6, &["+", "-", "^"][..]),
        (4, &["=", "<>", "<", ">", "<=", ">="][..]),
    ] {
        for name in names {
            fixities.insert((*name).to_owned(), Fixity::Left(precedence));
        }
    }
    for (precedence, names) in [(5, &["::", "@"][..]), (3, &[":=", "o"][..]), (0, &["before"][..])]
    {
        for name in names {
            fixities.insert((*name).to_owned(), Fixity::Right(precedence));
        }
    }
    fixities
}
