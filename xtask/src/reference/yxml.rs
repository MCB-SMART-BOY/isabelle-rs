use std::collections::BTreeMap;

use serde_json::{Value, json};

use super::common::require;
use crate::runner::StepError;

const X: char = '\u{5}';
const Y: char = '\u{6}';

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Part {
    Text(String),
    Element(Node),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub tag: String,
    pub attrs: BTreeMap<String, String>,
    pub attribute_order: Vec<String>,
    pub body: Vec<Part>,
}

pub fn parse(raw: &str) -> Result<Node, StepError> {
    let mut stack = vec![Node {
        tag: "__document__".into(),
        attrs: BTreeMap::new(),
        attribute_order: vec![],
        body: vec![],
    }];
    for token in raw.split(X).filter(|token| !token.is_empty()) {
        if let Some(header) = token.strip_prefix(Y) {
            let parts: Vec<&str> = header.split(Y).collect();
            if parts == [""] {
                require(stack.len() > 1, "Unexpected YXML closing delimiter")?;
                let node =
                    stack.pop().ok_or_else(|| StepError::Input("Missing YXML node".into()))?;
                stack
                    .last_mut()
                    .ok_or_else(|| StepError::Input("Missing YXML parent".into()))?
                    .body
                    .push(Part::Element(node));
                continue;
            }
            require(!parts[0].is_empty(), "Malformed YXML element header")?;
            let mut attrs = BTreeMap::new();
            let mut attribute_order = Vec::with_capacity(parts.len().saturating_sub(1));
            for field in &parts[1..] {
                let (key, value) = field
                    .split_once('=')
                    .ok_or_else(|| StepError::Input("Malformed YXML element header".into()))?;
                require(
                    attrs.insert(key.into(), value.into()).is_none(),
                    "Duplicate YXML attributes",
                )?;
                attribute_order.push(key.into());
            }
            stack.push(Node { tag: parts[0].into(), attrs, attribute_order, body: vec![] });
        } else {
            require(!token.contains(Y), "Malformed YXML text delimiter")?;
            stack
                .last_mut()
                .ok_or_else(|| StepError::Input("Missing YXML parent".into()))?
                .body
                .push(Part::Text(token.into()));
        }
    }
    require(
        stack.len() == 1 && stack[0].body.len() == 1,
        "YXML must contain exactly one closed root element",
    )?;
    let root = stack.pop().ok_or_else(|| StepError::Input("Missing YXML root".into()))?;
    match root.body.into_iter().next() {
        Some(Part::Element(node)) => Ok(node),
        _ => Err(StepError::Input("YXML root is not an element".into())),
    }
}

pub fn inspect<'a>(
    node: &'a Node,
    tag: &str,
    fields: &[&str],
) -> Result<(&'a BTreeMap<String, String>, &'a [Part]), StepError> {
    require(node.tag == tag, format!("Expected {tag} element"))?;
    require(
        node.attrs.len() == fields.len()
            && fields.iter().all(|field| node.attrs.contains_key(*field)),
        format!("Unexpected {tag} attributes: {:?}", node.attrs),
    )?;
    Ok((&node.attrs, &node.body))
}

pub fn elements(body: &[Part]) -> Result<Vec<&Node>, StepError> {
    body.iter()
        .map(|part| match part {
            Part::Element(node) => Ok(node),
            Part::Text(_) => Err(StepError::Input("Expected YXML child element, got text".into())),
        })
        .collect()
}

pub fn group<'a>(node: &'a Node, tag: &str, child: &str) -> Result<Vec<&'a Node>, StepError> {
    let (_, body) = inspect(node, tag, &[])?;
    let children = elements(body)?;
    require(
        children.iter().all(|item| item.tag == child),
        format!("{tag}: expected {child} children"),
    )?;
    Ok(children)
}

pub fn text_body(body: &[Part]) -> Result<String, StepError> {
    body.iter()
        .map(|part| match part {
            Part::Text(text) => Ok(text.as_str()),
            Part::Element(_) => Err(StepError::Input("Expected encoded text atom".into())),
        })
        .collect()
}

pub fn text(node: &Node, tag: &str) -> Result<String, StepError> {
    text_body(inspect(node, tag, &[])?.1)
}

pub fn child(body: &[Part], position: usize) -> Result<&Node, StepError> {
    match body.get(position) {
        Some(Part::Element(node)) => Ok(node),
        _ => Err(StepError::Input(format!("Missing or invalid YXML child {position}"))),
    }
}

pub fn empty_attrs(
    node: &Node,
    tag: &str,
    fields: &[&str],
) -> Result<serde_json::Map<String, Value>, StepError> {
    let (attrs, body) = inspect(node, tag, fields)?;
    require(
        body.is_empty() && attrs.values().all(|value| !value.is_empty()),
        format!("{tag}: invalid attributes or content"),
    )?;
    Ok(attrs.iter().map(|(key, value)| (key.clone(), json!(value))).collect())
}

pub fn read_names(node: &Node, tag: &str, child: &str) -> Result<Vec<Value>, StepError> {
    group(node, tag, child)?
        .into_iter()
        .map(|item| {
            let (attrs, body) = inspect(item, child, &["name"])?;
            require(
                body.is_empty() && !attrs["name"].is_empty(),
                format!("{child}: invalid attributes or content"),
            )?;
            Ok(json!(attrs["name"]))
        })
        .collect()
}

pub fn attr<'a>(node: &'a Node, field: &str) -> Result<&'a str, StepError> {
    node.attrs
        .get(field)
        .map(String::as_str)
        .ok_or_else(|| StepError::Input(format!("{}: missing {field}", node.tag)))
}

pub fn bool_value(value: &str) -> Result<bool, StepError> {
    require(matches!(value, "true" | "false"), format!("Expected boolean, got {value:?}"))?;
    Ok(value == "true")
}

pub fn unsigned(value: &str) -> Result<u64, StepError> {
    require(
        !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()),
        format!("Expected nonnegative integer, got {value:?}"),
    )?;
    value.parse().map_err(|_| StepError::Input(format!("Integer too large: {value}")))
}

pub fn positive(value: &str, identity: &str) -> Result<u64, StepError> {
    let number = unsigned(value)?;
    require(number > 0, format!("{identity}: invalid positive integer"))?;
    Ok(number)
}

pub fn unique(values: impl IntoIterator<Item = String>, identity: &str) -> Result<(), StepError> {
    let mut seen = std::collections::HashSet::new();
    for value in values {
        require(seen.insert(value), format!("Duplicate {identity}"))?;
    }
    Ok(())
}

pub fn array<'a>(value: &'a Value, key: &str) -> Result<&'a [Value], StepError> {
    value
        .get(key)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| StepError::Input(format!("Missing or malformed {key}")))
}

pub fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str, StepError> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| StepError::Input(format!("Missing or malformed {key}")))
}
