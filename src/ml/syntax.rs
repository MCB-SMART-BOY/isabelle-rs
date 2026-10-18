use super::Span;
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    Variable(String),
    Integer(i64),
    Word { value: u64, span: Span },
    Text(Vec<u8>),
    Character(u8),
    Unit,
    Tuple(Vec<Pattern>),
    List(Vec<Pattern>),
    Record(Vec<(String, Pattern)>, bool),
    Constructor(String, Option<Box<Pattern>>),
    Typed(Box<Pattern>, TypeExpr),
    As(String, Box<Pattern>),
}

/// A source-backed call or raise site retained in executable expressions.
#[derive(Clone, Debug)]
pub struct SourceLocation {
    pub span: Span,
    pub start_line: i64,
    pub start_position: i64,
    pub end_line: i64,
    pub end_position: i64,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Located(Box<Expr>, SourceLocation),
    Name(String),
    Integer(i64),
    Real(f64),
    Word { value: u64, span: Span },
    Text(Vec<u8>),
    Character(u8),
    Unit,
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    Record(Vec<(String, Expr)>),
    Select(String),
    Fn(Vec<(Pattern, Expr)>),
    Apply(Box<Expr>, Box<Expr>),
    Let(Vec<Declaration>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    While(Box<Expr>, Box<Expr>),
    Case(Box<Expr>, Vec<(Pattern, Expr)>),
    Handle(Box<Expr>, Vec<(Pattern, Expr)>),
    Raise(Box<Expr>),
    Sequence(Vec<Expr>),
    Typed(Box<Expr>, TypeExpr),
    AndAlso(Box<Expr>, Box<Expr>),
    OrElse(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    Var(String),
    Named(String, Vec<TypeExpr>),
    Tuple(Vec<TypeExpr>),
    Function(Box<TypeExpr>, Box<TypeExpr>),
    Record(Vec<(String, TypeExpr)>),
}

/// A function name and its curried pattern clauses.
pub type FunctionBinding = (String, Vec<(Vec<Pattern>, Expr)>);

/// A fixity declaration changes parsing, not the dynamic value environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fixity {
    Left(u8),
    Right(u8),
}

#[derive(Clone, Debug)]
pub enum Declaration {
    Fixity {
        names: Vec<String>,
        fixity: Option<Fixity>,
        span: Span,
    },
    Value {
        recursive: bool,
        bindings: Vec<(Pattern, Expr)>,
        span: Span,
    },
    Function {
        bindings: Vec<FunctionBinding>,
        span: Span,
    },
    Datatype {
        name: String,
        parameters: Vec<String>,
        constructors: Vec<(String, Option<TypeExpr>)>,
        span: Span,
    },
    DatatypeReplication {
        name: String,
        source: String,
        span: Span,
    },
    Abstype {
        datatype: Box<Declaration>,
        body: Vec<Declaration>,
        span: Span,
    },
    Exception {
        name: String,
        argument: Option<TypeExpr>,
        alias: Option<String>,
        span: Span,
    },
    Type {
        name: String,
        parameters: Vec<String>,
        definition: TypeExpr,
        span: Span,
    },
    Local {
        local: Vec<Declaration>,
        body: Vec<Declaration>,
        span: Span,
    },
    Open {
        names: Vec<String>,
        span: Span,
    },
    Structure {
        name: String,
        signature: Option<(SignatureExpr, bool)>,
        body: ModuleExpr,
        span: Span,
    },
    Signature {
        name: String,
        base: Option<String>,
        body: Vec<Specification>,
        span: Span,
    },
    Functor {
        name: String,
        parameter: String,
        signature: SignatureExpr,
        body: ModuleExpr,
        span: Span,
    },
    Expression(Expr, Span),
}

impl Declaration {
    pub(super) fn collect_value_names(
        &self,
        names: &mut BTreeSet<String>,
        is_constructor: &impl Fn(&str) -> bool,
    ) {
        match self {
            Self::Value { bindings, .. } => {
                for (pattern, _) in bindings {
                    pattern.collect_bound_names(names, is_constructor);
                }
            },
            Self::Function { bindings, .. } => {
                names.extend(bindings.iter().map(|(name, _)| name.clone()));
            },
            Self::Datatype { constructors, .. } => {
                names.extend(constructors.iter().map(|(name, _)| name.clone()));
            },
            Self::DatatypeReplication { .. } => {},
            Self::Exception { name, .. } => {
                names.insert(name.clone());
            },
            Self::Expression(..) => {
                names.insert("it".to_owned());
            },
            Self::Abstype { body, .. } => {
                for declaration in body {
                    declaration.collect_value_names(names, is_constructor);
                }
            },
            Self::Local { body, .. } => {
                for declaration in body {
                    declaration.collect_value_names(names, is_constructor);
                }
            },
            _ => {},
        }
    }

    pub(super) fn collect_type_names(&self, names: &mut BTreeSet<String>) {
        match self {
            Self::Datatype { name, .. }
            | Self::DatatypeReplication { name, .. }
            | Self::Type { name, .. } => {
                names.insert(name.clone());
            },
            Self::Abstype { datatype, body, .. } => {
                datatype.collect_type_names(names);
                for declaration in body {
                    declaration.collect_type_names(names);
                }
            },
            Self::Local { body, .. } => {
                for declaration in body {
                    declaration.collect_type_names(names);
                }
            },
            _ => {},
        }
    }
}

impl Pattern {
    fn collect_bound_names(
        &self,
        names: &mut BTreeSet<String>,
        is_constructor: &impl Fn(&str) -> bool,
    ) {
        match self {
            Self::Variable(name) if !is_constructor(name) => {
                names.insert(name.clone());
            },
            Self::Tuple(items) | Self::List(items) => {
                for item in items {
                    item.collect_bound_names(names, is_constructor);
                }
            },
            Self::Record(fields, _) => {
                for (_, item) in fields {
                    item.collect_bound_names(names, is_constructor);
                }
            },
            Self::Constructor(_, Some(argument)) | Self::Typed(argument, _) => {
                argument.collect_bound_names(names, is_constructor);
            },
            Self::As(name, pattern) => {
                names.insert(name.clone());
                pattern.collect_bound_names(names, is_constructor);
            },
            _ => {},
        }
    }
}

#[derive(Clone, Debug)]
pub enum ModuleExpr {
    Struct(Vec<Declaration>),
    Name(String),
    Apply(String, Box<ModuleExpr>),
    Constrained(Box<ModuleExpr>, SignatureExpr, bool),
}

/// A named or inline signature, followed by zero or more `where type` refinements.
#[derive(Clone, Debug)]
pub struct SignatureExpr {
    pub base: Option<String>,
    pub body: Vec<Specification>,
}

impl SignatureExpr {
    pub fn is_named(&self, name: &str) -> bool {
        self.base.as_deref() == Some(name) && self.body.is_empty()
    }
}

#[derive(Clone, Debug)]
pub enum Specification {
    Value(String, TypeExpr),
    Type { name: String, parameters: Vec<String>, equality: bool, definition: Option<TypeExpr> },
    Datatype(String, Vec<String>, Vec<(String, Option<TypeExpr>)>),
    DatatypeReplication(String, String),
    Exception(String, Option<TypeExpr>),
    Structure(String, SignatureExpr),
    Include(String),
    Sharing(Vec<String>),
    WhereType { name: String, parameters: Vec<String>, definition: TypeExpr },
}

impl Expr {
    pub(super) fn function_clauses(&self) -> Option<&[(Pattern, Expr)]> {
        match self {
            Self::Located(body, _) => body.function_clauses(),
            Self::Fn(clauses) => Some(clauses),
            _ => None,
        }
    }

    pub(super) fn is_nonexpansive(&self) -> bool {
        match self {
            Self::Located(value, _) => value.is_nonexpansive(),
            Self::Name(_)
            | Self::Integer(_)
            | Self::Real(_)
            | Self::Word { .. }
            | Self::Text(_)
            | Self::Character(_)
            | Self::Unit
            | Self::Fn(_)
            | Self::Select(_) => true,
            Self::Tuple(values) | Self::List(values) => values.iter().all(Self::is_nonexpansive),
            Self::Record(fields) => fields.iter().all(|(_, value)| value.is_nonexpansive()),
            Self::Typed(value, _) => value.is_nonexpansive(),
            _ => false,
        }
    }
}

pub(super) fn curry_clauses(clauses: &[(Vec<Pattern>, Expr)]) -> Option<Vec<(Pattern, Expr)>> {
    let mut result = Vec::with_capacity(clauses.len());
    for (patterns, expression) in clauses {
        let (first, tail) = patterns.split_first()?;
        let body = tail
            .iter()
            .rev()
            .fold(expression.clone(), |body, argument| Expr::Fn(vec![(argument.clone(), body)]));
        result.push((first.clone(), body));
    }
    Some(result)
}
