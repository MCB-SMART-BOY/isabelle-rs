use super::{
    super::{
        common::require,
        yxml::{self, Node, Part},
    },
    encoded::{sort, term, typ, typed_child},
};
use crate::runner::StepError;
use serde_json::{Value, json};

fn decode_named_term(node: &Node, tag: &str) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, tag, &["name"])?;
    require(!attrs["name"].is_empty() && body.len() == 1, format!("{tag}: missing name or term"))?;
    Ok(json!({"name":attrs["name"],"term":typed_child(yxml::child(body,0)?,"term",term)?}))
}
fn decode_type_declaration(node: &Node) -> Result<Value, StepError> {
    require(node.tag == "type_declaration", "Expected type_declaration")?;
    let name = yxml::attr(node, "name")?;
    let kind = yxml::attr(node, "kind")?;
    require(
        !name.is_empty() && matches!(kind, "logical" | "abbreviation" | "nonterminal"),
        "Invalid type declaration name/kind",
    )?;
    match kind {
        "logical" => {
            yxml::inspect(node, "type_declaration", &["name", "kind", "arity"])?;
            require(node.body.is_empty(), format!("Invalid logical type {name}"))?;
            Ok(
                json!({"name":name,"storage_kind":kind,"arity":yxml::unsigned(yxml::attr(node,"arity")?)?}),
            )
        },
        "abbreviation" => {
            yxml::inspect(node, "type_declaration", &["name", "kind", "syntax"])?;
            require(!node.body.is_empty(), format!("Invalid abbreviation {name}"))?;
            let body = yxml::elements(&node.body)?;
            let parameters: Vec<String> = body[..body.len() - 1]
                .iter()
                .map(|item| yxml::text(item, "parameter"))
                .collect::<Result<_, _>>()?;
            Ok(
                json!({"name":name,"storage_kind":kind,"syntax":yxml::bool_value(yxml::attr(node,"syntax")?)?,"parameters":parameters,"rhs":typed_child(body[body.len()-1],"type",typ)?}),
            )
        },
        _ => {
            yxml::inspect(node, "type_declaration", &["name", "kind"])?;
            require(node.body.is_empty(), format!("Invalid nonterminal {name}"))?;
            Ok(json!({"name":name,"storage_kind":kind}))
        },
    }
}
fn decode_class(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "class", &["name", "info_available"])?;
    require(!attrs["name"].is_empty() && body.len() == 2, "Invalid class detail")?;
    let is_available = yxml::bool_value(&attrs["info_available"])?;
    let params:Vec<Value>=yxml::group(yxml::child(body,0)?,"parameters","parameter")?.into_iter().map(|item|{
        let (fields,contents)=yxml::inspect(item,"parameter",&["name"])?;
        require(!fields["name"].is_empty() && contents.len()==1,"Invalid class parameter")?;
        Ok(json!({"name":fields["name"],"type":typed_child(yxml::child(contents,0)?,"type",typ)?}))
    }).collect::<Result<_,StepError>>()?;
    let axioms: Vec<Value> = yxml::group(yxml::child(body, 1)?, "class_axioms", "term")?
        .into_iter()
        .map(|item| typed_child(item, "term", term))
        .collect::<Result<_, _>>()?;
    require(
        is_available || (params.is_empty() && axioms.is_empty()),
        "Unavailable class info has content",
    )?;
    Ok(
        json!({"name":attrs["name"],"info_available":is_available,"parameters":params,"class_axioms":axioms}),
    )
}
fn decode_entry(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "entry", &["kind", "name"])?;
    require(
        matches!(attrs["kind"].as_str(), "type" | "const") && !attrs["name"].is_empty(),
        "Invalid definition entry",
    )?;
    let types: Vec<Value> = yxml::elements(body)?
        .into_iter()
        .map(|item| typed_child(item, "type", typ))
        .collect::<Result<_, _>>()?;
    Ok(json!({"kind":attrs["kind"],"name":attrs["name"],"types":types}))
}
fn decode_specification(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) =
        yxml::inspect(node, "specification", &["description", "axiom_name", "has_axiom_name"])?;
    require(body.len() == 2, "Specification requires subject and dependencies")?;
    let subject = yxml::group(yxml::child(body, 0)?, "subject", "entry")?;
    require(subject.len() == 1, "Specification must have exactly one subject")?;
    let has_axiom = yxml::bool_value(&attrs["has_axiom_name"])?;
    require(has_axiom || attrs["axiom_name"].is_empty(), "Unmarked axiom relationship")?;
    let deps: Vec<Value> = yxml::group(yxml::child(body, 1)?, "dependencies", "entry")?
        .into_iter()
        .map(decode_entry)
        .collect::<Result<_, _>>()?;
    Ok(
        json!({"description":attrs["description"],"axiom_name":if has_axiom {Some(attrs["axiom_name"].as_str())} else {None},"subject":decode_entry(subject[0])?,"dependencies":deps}),
    )
}
fn decode_reference(node: &Node, tag: &str) -> Result<Value, StepError> {
    let attrs = yxml::empty_attrs(node, tag, &["name", "index", "origin", "serial"])?;
    let name = attrs["name"].as_str().unwrap_or("");
    require(!name.is_empty(), "Invalid theorem name")?;
    Ok(
        json!({"name":name,"index":yxml::unsigned(attrs["index"].as_str().unwrap_or(""))?,"origin":attrs["origin"],"serial":yxml::unsigned(attrs["serial"].as_str().unwrap_or(""))?}),
    )
}
fn decode_oracle(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "oracle", &["name"])?;
    require(!attrs["name"].is_empty() && body.len() <= 1, "Invalid oracle footprint")?;
    Ok(
        json!({"name":attrs["name"],"proposition":if body.is_empty(){None}else{Some(typed_child(yxml::child(body,0)?,"term",term)?)} }),
    )
}
fn decode_theorem(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(
        node,
        "theorem",
        &["name", "index", "owner", "derivation_name", "has_skip_proof"],
    )?;
    require(
        body.len() == 6 && !attrs["owner"].is_empty() && !attrs["name"].is_empty(),
        "Invalid theorem detail",
    )?;
    let proposition = yxml::group(yxml::child(body, 0)?, "proposition", "term")?;
    require(proposition.len() == 1, "Theorem requires exactly one proposition")?;
    let hypotheses =
        map_group(body, 1, "hypotheses", "term", |node| typed_child(node, "term", term))?;
    let shyps = map_group(body, 2, "shyps", "sort", |node| typed_child(node, "sort", sort))?;
    let tpairs = map_group(body, 3, "tpairs", "tpair", |node| {
        let pair = yxml::group(node, "tpair", "term")?;
        require(pair.len() == 2, "Malformed tpair")?;
        Ok(Value::Array(
            pair.iter()
                .map(|term_node| typed_child(term_node, "term", term))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    })?;
    let dependencies = map_group(body, 4, "dependencies", "dependency", |node| {
        decode_reference(node, "dependency")
    })?;
    let oracles = map_group(body, 5, "oracle_footprint", "oracle", decode_oracle)?;
    let mut decoded = json!({"name":attrs["name"],"index":yxml::unsigned(&attrs["index"])?,"owner":attrs["owner"],"derivation_name":attrs["derivation_name"],"has_skip_proof":yxml::bool_value(&attrs["has_skip_proof"])?});
    decoded["proposition"] = typed_child(proposition[0], "term", term)?;
    decoded["hypotheses"] = Value::Array(hypotheses);
    decoded["shyps"] = Value::Array(shyps);
    decoded["tpairs"] = Value::Array(tpairs);
    decoded["dependencies"] = Value::Array(dependencies);
    decoded["oracle_footprint"] = Value::Array(oracles);
    Ok(decoded)
}
fn map_group(
    body: &[Part],
    index: usize,
    tag: &str,
    child: &str,
    decoder: impl Fn(&Node) -> Result<Value, StepError>,
) -> Result<Vec<Value>, StepError> {
    yxml::group(yxml::child(body, index)?, tag, child)?.into_iter().map(decoder).collect()
}
fn decode_fact_group(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "fact_group", &["name"])?;
    require(!attrs["name"].is_empty(), "Empty fact group name")?;
    let theorems: Vec<Value> =
        yxml::elements(body)?.into_iter().map(decode_theorem).collect::<Result<_, _>>()?;
    require(
        theorems.iter().all(|item| item["name"] == attrs["name"]),
        "Fact theorem name differs from group name",
    )?;
    let mut result = json!({"name":attrs["name"]});
    result["theorems"] = Value::Array(theorems);
    Ok(result)
}
fn decode_constant(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "constant", &["name"])?;
    require(
        !attrs["name"].is_empty() && (body.len() == 1 || body.len() == 2),
        "Invalid constant shape",
    )?;
    let mut result =
        json!({"name":attrs["name"],"type":typed_child(yxml::child(body,0)?,"type",typ)?});
    if body.len() == 2 {
        let (abbrev, rhs) = yxml::inspect(yxml::child(body, 1)?, "abbreviation", &["name"])?;
        require(
            abbrev["name"] == attrs["name"] && rhs.len() == 1,
            "Constant abbreviation name or RHS mismatch",
        )?;
        result["abbreviation"] = typed_child(yxml::child(rhs, 0)?, "term", term)?;
    }
    Ok(result)
}
fn decode_fact_index(node: &Node) -> Result<Value, StepError> {
    let attrs = yxml::empty_attrs(node, "fact_index", &["name", "concealed", "dynamic", "origin"])?;
    Ok(
        json!({"name":attrs["name"],"concealed":yxml::bool_value(attrs["concealed"].as_str().unwrap_or(""))?,"dynamic":yxml::bool_value(attrs["dynamic"].as_str().unwrap_or(""))?,"origin":attrs["origin"]}),
    )
}
fn decode_arity(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "arity", &["type", "class"])?;
    require(attrs.values().all(|value| !value.is_empty()), "Invalid type arity")?;
    let sorts: Vec<Value> = yxml::elements(body)?
        .into_iter()
        .map(|item| typed_child(item, "sort", sort))
        .collect::<Result<_, _>>()?;
    Ok(json!({"type":attrs["type"],"class":attrs["class"],"argument_sorts":sorts}))
}
pub fn decode_section(
    body: &[Part],
    index: usize,
    section: &str,
    tag: &str,
) -> Result<Value, StepError> {
    let values: Vec<Value> = yxml::group(yxml::child(body, index)?, section, tag)?
        .into_iter()
        .map(|node| match tag {
            "parent" | "oracle_registration" => {
                Ok(json!(yxml::empty_attrs(node, tag, &["name"])?["name"]))
            },
            "import_specification" => Ok(json!(yxml::text(node, tag)?)),
            "type_declaration" => decode_type_declaration(node),
            "class" => decode_class(node),
            "class_relation" => Ok(Value::Object(yxml::empty_attrs(node, tag, &["sub", "super"])?)),
            "arity" => decode_arity(node),
            "constant" => decode_constant(node),
            "axiom" => decode_named_term(node, tag),
            "specification" => decode_specification(node),
            "constant_definition" => {
                Ok(Value::Object(yxml::empty_attrs(node, tag, &["constant", "axiom"])?))
            },
            "fact_index" => decode_fact_index(node),
            "fact_group" => decode_fact_group(node),
            "named_derivation" => decode_reference(node, tag),
            _ => Err(StepError::Input(format!("Unknown inventory section {section}"))),
        })
        .collect::<Result<_, _>>()?;
    Ok(Value::Array(values))
}
