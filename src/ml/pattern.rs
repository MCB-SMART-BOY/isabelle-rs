use super::environment::ValueEnvironment;
use super::value::ValueData;
use super::{MlError, MlErrorKind, Pattern, Value, Vm};
use std::collections::BTreeMap;
use std::rc::Rc;

impl Vm {
    pub(super) fn match_pattern(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        environment: &ValueEnvironment,
    ) -> Result<Option<BTreeMap<String, Value>>, MlError> {
        let mut bindings = BTreeMap::new();
        if self.match_fields(pattern, value, environment, &mut bindings)? {
            Ok(Some(bindings))
        } else {
            Ok(None)
        }
    }

    fn match_fields(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        environment: &ValueEnvironment,
        bindings: &mut BTreeMap<String, Value>,
    ) -> Result<bool, MlError> {
        match pattern {
            Pattern::Wildcard => Ok(true),
            Pattern::Variable(name) if environment.is_constructor(name) => {
                self.match_constructor(name, None, value, environment, bindings)
            },
            Pattern::Variable(name) => {
                if name.contains('.') {
                    return Err(self.error(
                        MlErrorKind::Type,
                        "match",
                        format!("{name} is not a constructor"),
                    ));
                }
                bindings.insert(name.clone(), value.clone());
                Ok(true)
            },
            Pattern::Integer(number) => Ok(value.as_int() == Some(*number)),
            Pattern::Word { value: number, span } => {
                let key = (span.source_name.clone(), span.start, span.end);
                if self.elaborations.word32_literals.contains(&key) {
                    Ok(value.as_word32() == u32::try_from(*number).ok())
                } else {
                    Ok(value.as_word() == Some(*number))
                }
            },
            Pattern::Text(text) => Ok(value.as_bytes() == Some(text.as_slice())),
            Pattern::Character(character) => {
                Ok(matches!(&*value.0, ValueData::Character(actual) if actual == character))
            },
            Pattern::Unit => Ok(value.is_unit()),
            Pattern::Tuple(patterns) => match &*value.0 {
                ValueData::Tuple(values) => {
                    self.match_sequence(patterns, values, environment, bindings)
                },
                _ => Ok(false),
            },
            Pattern::List(patterns) => match &*value.0 {
                ValueData::List(values) => {
                    self.match_sequence(patterns, values, environment, bindings)
                },
                _ => Ok(false),
            },
            Pattern::Record(patterns, is_open) => {
                self.match_record(patterns, *is_open, value, environment, bindings)
            },
            Pattern::Constructor(name, argument) => {
                self.match_constructor(name, argument.as_deref(), value, environment, bindings)
            },
            Pattern::Typed(pattern, _) => self.match_fields(pattern, value, environment, bindings),
            Pattern::As(name, pattern) => {
                bindings.insert(name.clone(), value.clone());
                self.match_fields(pattern, value, environment, bindings)
            },
        }
    }

    fn match_record(
        &mut self,
        patterns: &[(String, Pattern)],
        is_open: bool,
        value: &Value,
        environment: &ValueEnvironment,
        bindings: &mut BTreeMap<String, Value>,
    ) -> Result<bool, MlError> {
        let Some(length) = value.record_length() else { return Ok(false) };
        if !is_open && patterns.len() != length {
            return Ok(false);
        }
        for (label, pattern) in patterns {
            let Some(field) = value.record_field(label) else { return Ok(false) };
            if !self.match_fields(pattern, field, environment, bindings)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn match_constructor(
        &mut self,
        name: &str,
        argument: Option<&Pattern>,
        value: &Value,
        environment: &ValueEnvironment,
        bindings: &mut BTreeMap<String, Value>,
    ) -> Result<bool, MlError> {
        if !environment.is_constructor(name) {
            return Err(self.error(
                MlErrorKind::Type,
                "match",
                format!("{name} is not a constructor"),
            ));
        }
        let constructor = self.resolve_name(name, environment)?;
        match (&*constructor.0, &*value.0) {
            (
                ValueData::Native(id),
                ValueData::Reference(cell) | ValueData::WeakReference(cell),
            ) if Some(*id) == self.basis_ref_constructor
                && name.rsplit('.').next() == Some("ref") =>
            {
                let current = cell.borrow().clone();
                self.match_argument(argument, Some(&current), environment, bindings)
            },
            (ValueData::Native(_), ValueData::List(values))
                if name.rsplit('.').next() == Some("::") =>
            {
                let Some((first, rest)) = values.split_first() else { return Ok(false) };
                let tail = self.track_value(Value(Rc::new(ValueData::List(rest.to_vec()))));
                let tuple =
                    self.track_value(Value(Rc::new(ValueData::Tuple(vec![first.clone(), tail]))));
                self.match_argument(argument, Some(&tuple), environment, bindings)
            },
            (ValueData::List(expected), ValueData::List(actual)) => {
                Ok(argument.is_none() && expected.is_empty() && actual.is_empty())
            },
            (ValueData::Bool(expected), ValueData::Bool(actual)) => {
                Ok(argument.is_none() && expected == actual)
            },
            (
                ValueData::ConstructorFunction { stamp: expected, .. },
                ValueData::Constructor { stamp, argument: actual, .. },
            )
            | (
                ValueData::Constructor { stamp: expected, .. },
                ValueData::Constructor { stamp, argument: actual, .. },
            ) if expected == stamp => {
                self.match_argument(argument, actual.as_ref(), environment, bindings)
            },
            (
                ValueData::ExceptionFunction { identity: expected, .. },
                ValueData::Exception { identity, argument: actual, .. },
            )
            | (
                ValueData::Exception { identity: expected, .. },
                ValueData::Exception { identity, argument: actual, .. },
            ) if expected == identity => {
                self.match_argument(argument, actual.as_ref(), environment, bindings)
            },
            _ => Ok(false),
        }
    }

    fn match_sequence(
        &mut self,
        patterns: &[Pattern],
        values: &[Value],
        environment: &ValueEnvironment,
        bindings: &mut BTreeMap<String, Value>,
    ) -> Result<bool, MlError> {
        if patterns.len() != values.len() {
            return Ok(false);
        }
        for (pattern, value) in patterns.iter().zip(values) {
            if !self.match_fields(pattern, value, environment, bindings)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn match_argument(
        &mut self,
        pattern: Option<&Pattern>,
        argument: Option<&Value>,
        environment: &ValueEnvironment,
        bindings: &mut BTreeMap<String, Value>,
    ) -> Result<bool, MlError> {
        match (pattern, argument) {
            (None, None) => Ok(true),
            (Some(pattern), Some(argument)) => {
                self.match_fields(pattern, argument, environment, bindings)
            },
            _ => Ok(false),
        }
    }
}
