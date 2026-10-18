use std::fmt;
use std::io::Read;

use serde::de::{DeserializeSeed, Error, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Number, Value};

const MAX_JSON_DEPTH: usize = 512;

struct StrictValue {
    depth: usize,
    limit: usize,
}

impl<'de> DeserializeSeed<'de> for StrictValue {
    type Value = Value;

    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Value, D::Error> {
        if self.depth > self.limit {
            return Err(D::Error::custom("reference JSON nesting limit exceeded"));
        }
        deserializer.deserialize_any(self)
    }
}

impl<'de> Visitor<'de> for StrictValue {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object fields")
    }

    fn visit_bool<E: Error>(self, value: bool) -> Result<Value, E> {
        Ok(Value::Bool(value))
    }
    fn visit_i64<E: Error>(self, value: i64) -> Result<Value, E> {
        Ok(Value::from(value))
    }
    fn visit_u64<E: Error>(self, value: u64) -> Result<Value, E> {
        Ok(Value::from(value))
    }
    fn visit_f64<E: Error>(self, value: f64) -> Result<Value, E> {
        Number::from_f64(value).map(Value::Number).ok_or_else(|| E::custom("nonfinite JSON number"))
    }
    fn visit_str<E: Error>(self, value: &str) -> Result<Value, E> {
        Ok(Value::from(value))
    }
    fn visit_string<E: Error>(self, value: String) -> Result<Value, E> {
        Ok(Value::String(value))
    }
    fn visit_unit<E: Error>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }
    fn visit_none<E: Error>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Value, A::Error> {
        let mut values = Vec::new();
        while let Some(value) =
            sequence.next_element_seed(StrictValue { depth: self.depth + 1, limit: self.limit })?
        {
            values.push(value);
        }
        Ok(Value::Array(values))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut entries: A) -> Result<Value, A::Error> {
        let mut values = Map::new();
        while let Some(key) = entries.next_key::<String>()? {
            if values.contains_key(&key) {
                return Err(A::Error::custom(format!("JSON: duplicate key {key:?}")));
            }
            let value = entries
                .next_value_seed(StrictValue { depth: self.depth + 1, limit: self.limit })?;
            values.insert(key, value);
        }
        Ok(Value::Object(values))
    }
}

pub(super) fn decode_reader(reader: impl Read) -> Result<Value, serde_json::Error> {
    decode_reader_with_limit(reader, MAX_JSON_DEPTH)
}

pub(super) fn decode_reader_with_limit(
    reader: impl Read,
    max_depth: usize,
) -> Result<Value, serde_json::Error> {
    let mut decoder = serde_json::Deserializer::from_reader(reader);
    decoder.disable_recursion_limit();
    let value =
        StrictValue { depth: 0, limit: max_depth.min(MAX_JSON_DEPTH) }.deserialize(&mut decoder)?;
    decoder.end()?;
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_reader_nested_duplicate_fields_rejects() {
        let error = decode_reader(br#"{"nested":{"result":1,"result":2}}"#.as_slice()).unwrap_err();
        assert!(error.to_string().contains("duplicate key"));
    }

    #[test]
    fn decode_reader_trailing_document_rejects() {
        assert!(decode_reader(b"{} []".as_slice()).is_err());
    }

    #[test]
    fn decode_reader_scalar_types_preserves() {
        let value = decode_reader(br#"[true,null,42,-7,0.5,"name"]"#.as_slice()).unwrap();
        assert_eq!(value, serde_json::json!([true, null, 42, -7, 0.5, "name"]));
    }
}
