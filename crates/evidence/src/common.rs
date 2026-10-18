use serde_json::{Map, Value};

use crate::EvidenceError;

pub const COMMIT: &str = "765fb2460a57eb46e8490283241ad46f1fac857f";
pub const ROOTS: [&str; 9] = [
    "HOL.HOL",
    "HOL.Orderings",
    "HOL.Set",
    "HOL.Nat",
    "HOL.List",
    "HOL.Fun",
    "HOL.Product_Type",
    "HOL.Sum_Type",
    "HOL.Option",
];
pub const EXPECTED_THEORY_COUNT: usize = 67;

pub fn require(condition: bool, message: impl Into<String>) -> Result<(), EvidenceError> {
    if condition { Ok(()) } else { Err(EvidenceError::Input(message.into())) }
}

pub fn field<'a>(value: &'a Value, key: &str) -> Result<&'a Value, EvidenceError> {
    value.get(key).ok_or_else(|| EvidenceError::Input(format!("missing field: {key}")))
}

pub fn as_array<'a>(value: &'a Value, context: &str) -> Result<&'a Vec<Value>, EvidenceError> {
    value.as_array().ok_or_else(|| EvidenceError::Input(format!("{context}: expected array")))
}

pub fn as_object<'a>(
    value: &'a Value,
    context: &str,
) -> Result<&'a Map<String, Value>, EvidenceError> {
    value.as_object().ok_or_else(|| EvidenceError::Input(format!("{context}: expected object")))
}

pub fn as_str<'a>(value: &'a Value, context: &str) -> Result<&'a str, EvidenceError> {
    value.as_str().ok_or_else(|| EvidenceError::Input(format!("{context}: expected string")))
}

pub fn require_fields(value: &Value, fields: &[&str], context: &str) -> Result<(), EvidenceError> {
    let object = as_object(value, context)?;
    require(
        object.len() == fields.len() && fields.iter().all(|key| object.contains_key(*key)),
        format!("{context}: expected exactly {}", fields.join(", ")),
    )
}
