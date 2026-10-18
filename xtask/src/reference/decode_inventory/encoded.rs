use super::super::{
    common::require,
    yxml::{self, Node, Part},
};
use crate::runner::StepError;
use serde_json::{Value, json};

fn wrapper(part: &Part) -> Result<&[Part], StepError> {
    let node = match part {
        Part::Element(node) => node,
        _ => return Err(StepError::Input("Expected XML.Encode wrapper".into())),
    };
    Ok(yxml::inspect(node, ":", &[])?.1)
}
fn variant(body: &[Part], arity: u64) -> Result<(u64, Vec<&str>, &[Part]), StepError> {
    require(body.len() == 1, "Expected XML.Encode variant")?;
    let node = yxml::child(body, 0)?;
    let tag = yxml::unsigned(&node.tag)?;
    require(tag < arity, "Invalid XML.Encode variant tag")?;
    require(
        node.attribute_order.iter().enumerate().all(|(index, key)| key == &index.to_string()),
        "Invalid XML.Encode variant attribute vector",
    )?;
    let fields: Vec<&str> =
        node.attribute_order.iter().map(|key| node.attrs[key].as_str()).collect();
    Ok((tag, fields, &node.body))
}
fn index(value: &str) -> Result<i64, StepError> {
    let raw = value.strip_prefix('~').or_else(|| value.strip_prefix('-')).unwrap_or(value);
    require(
        !raw.is_empty() && raw.bytes().all(|byte| byte.is_ascii_digit()),
        format!("Invalid schematic index {value:?}"),
    )?;
    let signed = if raw.len() != value.len() { format!("-{raw}") } else { raw.to_owned() };
    signed.parse().map_err(|_| StepError::Input(format!("Schematic index too large: {value}")))
}
pub fn sort(body: &[Part]) -> Result<Value, StepError> {
    let values: Vec<String> =
        body.iter().map(|part| yxml::text_body(wrapper(part)?)).collect::<Result<_, _>>()?;
    require(values.iter().all(|value| !value.is_empty()), "Empty sort class name")?;
    Ok(json!(values))
}
pub fn typ(body: &[Part]) -> Result<Value, StepError> {
    let (tag, fields, content) = variant(body, 3)?;
    match tag {
        0 => {
            require(
                fields.len() == 1 && !fields[0].is_empty(),
                "Type constructor requires a name",
            )?;
            let args: Vec<Value> =
                content.iter().map(|part| typ(wrapper(part)?)).collect::<Result<_, _>>()?;
            let mut result = json!({"kind":"Type","name":fields[0]});
            result["args"] = Value::Array(args);
            Ok(result)
        },
        1 => {
            require(fields.len() == 1 && !fields[0].is_empty(), "TFree requires a name")?;
            Ok(json!({"kind":"TFree","name":fields[0],"sort":sort(content)?}))
        },
        _ => {
            require(
                (fields.len() == 1 || fields.len() == 2) && !fields[0].is_empty(),
                "TVar requires an index name",
            )?;
            Ok(
                json!({"kind":"TVar","name":fields[0],"index":if fields.len()==2 { index(fields[1])? } else { 0 },"sort":sort(content)?}),
            )
        },
    }
}
fn pair(
    body: &[Part],
    first: fn(&[Part]) -> Result<Value, StepError>,
    second: fn(&[Part]) -> Result<Value, StepError>,
) -> Result<(Value, Value), StepError> {
    require(body.len() == 2, "Expected encoded pair")?;
    Ok((first(wrapper(&body[0])?)?, second(wrapper(&body[1])?)?))
}
pub fn term(body: &[Part]) -> Result<Value, StepError> {
    let (tag, fields, content) = variant(body, 6)?;
    match tag {
        0 | 1 => {
            require(fields.len() == 1 && !fields[0].is_empty(), "Const/Free requires a name")?;
            let mut result = json!({"kind":if tag==0 {"Const"} else {"Free"},"name":fields[0]});
            result["type"] = typ(content)?;
            Ok(result)
        },
        2 => {
            require(
                (fields.len() == 1 || fields.len() == 2) && !fields[0].is_empty(),
                "Var requires an index name",
            )?;
            let mut result = json!({"kind":"Var","name":fields[0],"index":if fields.len()==2 { index(fields[1])? } else { 0 }});
            result["type"] = typ(content)?;
            Ok(result)
        },
        3 => {
            require(fields.is_empty(), "Bound must not have attributes")?;
            Ok(json!({"kind":"Bound","index":yxml::unsigned(&yxml::text_body(content)?)?}))
        },
        4 => {
            require(fields.len() == 1, "Abs requires a binder name")?;
            let (typ, body) = pair(content, typ, term)?;
            let mut result = json!({"kind":"Abs","name":fields[0]});
            result["type"] = typ;
            result["body"] = body;
            Ok(result)
        },
        _ => {
            require(fields.is_empty(), "Application must not have attributes")?;
            let (function, argument) = pair(content, term, term)?;
            let mut result = json!({"kind":"App"});
            result["function"] = function;
            result["argument"] = argument;
            Ok(result)
        },
    }
}
pub fn typed_child(
    node: &Node,
    tag: &str,
    decoder: fn(&[Part]) -> Result<Value, StepError>,
) -> Result<Value, StepError> {
    decoder(yxml::inspect(node, tag, &[])?.1)
}
