//! The only native Context cutover: AST-delimited structure replacement, no source edits.
use super::{Declaration, MlError, MlErrorKind, ModuleExpr, Span, Vm, parser};

impl Vm {
    pub fn evaluate_native_context_module(
        &mut self,
        source_name: &str,
        official_source: &str,
        replacement_structure: &str,
    ) -> Result<(), MlError> {
        let result = self.evaluate_native_context_checked(
            source_name,
            official_source,
            replacement_structure,
        );
        if result.is_err() {
            self.request_stop();
        }
        result
    }

    fn evaluate_native_context_checked(
        &mut self,
        source_name: &str,
        official_source: &str,
        replacement_structure: &str,
    ) -> Result<(), MlError> {
        self.check_stop()?;
        let declarations =
            parser::parse(source_name, official_source, &self.fixities, &self.stop.0.requested)?;
        let replacement = parser::parse(
            "native Context implementation",
            replacement_structure,
            &self.fixities,
            &self.stop.0.requested,
        )?;
        let target = find_context_boundary(&declarations, source_name)?;
        if replacement.len() != 1 || !is_structure(&replacement[0], "Context", "PRIVATE_CONTEXT") {
            return Err(context_error(
                source_name,
                "replacement must define exactly one Context: PRIVATE_CONTEXT structure",
            ));
        }
        self.source_name = source_name.to_owned();
        for (index, declaration) in declarations.iter().enumerate() {
            let selected = if index == target { &replacement[0] } else { declaration };
            self.evaluate_declaration(selected)?;
            self.apply_fixity_declaration(selected);
        }
        self.hide_host_structure("Native_Context")?;
        Ok(())
    }
}

fn find_context_boundary(declarations: &[Declaration], source: &str) -> Result<usize, MlError> {
    let targets = declarations
        .iter()
        .enumerate()
        .filter_map(|(index, declaration)| {
            is_structure(declaration, "Context", "PRIVATE_CONTEXT").then_some(index)
        })
        .collect::<Vec<_>>();
    let [target] = targets.as_slice() else {
        return Err(context_error(
            source,
            "expected exactly one original Context: PRIVATE_CONTEXT structure",
        ));
    };
    let Declaration::Structure { body: ModuleExpr::Struct(_), .. } = &declarations[*target] else {
        return Err(context_error(
            source,
            "original Context implementation is not a structure body",
        ));
    };
    for name in ["BASIC_CONTEXT", "CONTEXT", "PRIVATE_CONTEXT"] {
        if !declarations[..*target].iter().any(|declaration| {
            matches!(declaration,
            Declaration::Signature { name: actual, .. } if actual == name)
        }) {
            return Err(context_error(
                source,
                &format!("missing original {name} signature before Context"),
            ));
        }
    }
    let suffix = &declarations[*target + 1..];
    if !suffix.iter().any(|declaration| is_structure(declaration, "Basic_Context", "BASIC_CONTEXT"))
        || !suffix.iter().any(|declaration| is_structure(declaration, "Context", "CONTEXT"))
    {
        return Err(context_error(
            source,
            "missing original public Context and Basic_Context suffix",
        ));
    }
    for name in ["Theory_Data'", "Theory_Data", "Proof_Data", "Generic_Data"] {
        if !suffix.iter().any(|declaration| {
            matches!(declaration,
            Declaration::Functor { name: actual, .. } if actual == name)
        }) {
            return Err(context_error(source, &format!("missing original {name} data functor")));
        }
    }
    Ok(*target)
}

fn is_structure(declaration: &Declaration, expected_name: &str, expected_signature: &str) -> bool {
    matches!(declaration, Declaration::Structure { name, signature: Some((signature, _)), .. }
        if name == expected_name && signature.is_named(expected_signature))
}

fn context_error(source: &str, cause: &str) -> MlError {
    MlError {
        kind: MlErrorKind::Syntax,
        span: Box::new(Span::new(source, 0, 0)),
        operation: "replace native Context".into(),
        cause: cause.to_owned(),
        exception: None,
        trace: Vec::new(),
    }
}
