use super::{
    common::require,
    decode_execution::read_empty_attributes,
    decode_inventory::ROOTS,
    yxml::{self, Node, Part},
};
use crate::runner::StepError;
use serde_json::{Value, json};
use std::collections::{HashMap, HashSet};
const AUTHORIZATION: &str = "none_reference_requirements_only";
const TYPE_TEXT_SEMANTICS: &str = "display_only_not_structural_type_identity";
const NAMESPACE_SEMANTICS: &str = "theory_tables_with_current_global_fallback_when_enabled";
const TYPE_PRINT_DEPTH: u64 = 40;
const SELECTED_STRUCTURES: [&str; 17] = [
    "Thm",
    "Type",
    "Sign",
    "Consts",
    "Defs",
    "Theory",
    "Context",
    "Proofterm",
    "ML_Compiler",
    "ML_Env",
    "ML_Name_Space",
    "ML_Context",
    "Thread",
    "OS",
    "TextIO",
    "BinIO",
    "PolyML",
];
const OBSERVED: [&str; 2] =
    ["theory_scoped_command_keywords_and_kinds", "selected_public_ml_namespace_declarations"];
const UNAVAILABLE: [&str; 3] =
    ["runtime_call_graph", "signature_and_functor_members", "private_bootstrap_runtime_structures"];

fn position(node: &Node) -> Result<Value, StepError> {
    require(node.tag == "declaration_position", "Missing declaration position availability")?;
    let availability = yxml::attr(node, "availability")?;
    if availability == "unavailable" {
        return Ok(Value::Object(read_empty_attributes(
            node,
            "declaration_position",
            &["availability"],
        )?));
    }
    require(availability == "available", "Unknown declaration position availability")?;
    require(
        node.attrs
            .keys()
            .all(|key| matches!(key.as_str(), "availability" | "file" | "line" | "offset")),
        "Unexpected declaration position fields",
    )?;
    let keys = node.attrs.keys().map(String::as_str).collect::<Vec<_>>();
    let mut result = read_empty_attributes(node, "declaration_position", &keys)?;
    for key in ["line", "offset"] {
        if let Some(value) = result.get(key) {
            result.insert(
                key.into(),
                json!(yxml::positive(value.as_str().unwrap_or(""), &format!("declaration {key}"))?),
            );
        }
    }
    Ok(Value::Object(result))
}
fn declaration(node: &Node, tag: &str) -> Result<Value, StepError> {
    let fields = if tag == "value" { &["name", "type_print_depth"][..] } else { &["name"][..] };
    let (attrs, body) = yxml::inspect(node, tag, fields)?;
    require(!attrs["name"].is_empty(), format!("{tag}: empty declaration name"))?;
    let count = if tag == "type_constructor" { 1 } else { 2 };
    require(body.len() == count, format!("{tag}: incomplete declaration"))?;
    let mut result = json!({"name":attrs["name"],"position":position(yxml::child(body,0)?)?});
    if tag == "value" {
        let depth = yxml::positive(&attrs["type_print_depth"], "value type print depth")?;
        require(depth == TYPE_PRINT_DEPTH, "Unsupported type display depth")?;
        let type_text = yxml::text(yxml::child(body, 1)?, "type_text")?;
        require(!type_text.is_empty(), format!("{}: missing type display", attrs["name"]))?;
        result["type_print_depth"] = json!(depth);
        result["type_text"] = json!(type_text);
    } else if matches!(tag, "signature" | "functor") {
        let members =
            read_empty_attributes(yxml::child(body, 1)?, "members", &["availability", "reason"])?;
        require(
            members["availability"] == "unavailable"
                && members["reason"] == format!("no_public_{tag}_contents_api"),
            format!("{tag}: unsupported member availability"),
        )?;
        result["members"] = Value::Object(members);
    }
    Ok(result)
}
fn named_group(node: &Node, group: &str, tag: &str) -> Result<Value, StepError> {
    let entries = yxml::group(node, group, tag)?
        .into_iter()
        .map(|child| declaration(child, tag))
        .collect::<Result<Vec<_>, _>>()?;
    yxml::unique(
        entries.iter().map(|item| item["name"].as_str().unwrap_or("").to_owned()),
        &format!("{group} declaration identities"),
    )?;
    Ok(Value::Array(entries))
}
fn namespace(body: &[Part]) -> Result<Value, StepError> {
    require(body.len() == 4, "Incomplete ML namespace declaration groups")?;
    let mut result = json!({});
    for (index, (group, tag)) in [
        ("values", "value"),
        ("type_constructors", "type_constructor"),
        ("signatures", "signature"),
        ("functors", "functor"),
    ]
    .iter()
    .enumerate()
    {
        result[*group] = named_group(yxml::child(body, index)?, group, tag)?;
    }
    Ok(result)
}
fn structures(
    node: &Node,
    group: &str,
    expected: Option<&[&str]>,
    parent: &str,
) -> Result<Value, StepError> {
    let entries = yxml::group(node, group, "structure")?
        .into_iter()
        .map(|item| structure(item, parent))
        .collect::<Result<Vec<_>, _>>()?;
    let names: Vec<&str> = entries.iter().map(|item| item["name"].as_str().unwrap_or("")).collect();
    yxml::unique(
        names.iter().map(|name| (*name).to_owned()),
        &format!(
            "{} selected structure identities",
            if parent.is_empty() { "top-level" } else { parent }
        ),
    )?;
    let is_ordered = expected
        .map_or_else(|| names.windows(2).all(|pair| pair[0] <= pair[1]), |list| names == list);
    require(
        is_ordered,
        format!(
            "{}: incomplete or unordered public structure inventory",
            if parent.is_empty() { "top-level" } else { parent }
        ),
    )?;
    Ok(Value::Array(entries))
}
fn structure(node: &Node, parent: &str) -> Result<Value, StepError> {
    require(node.tag == "structure", "Expected public structure")?;
    let available = node.attrs.get("availability").is_some_and(|flag| flag == "available");
    let fields = if available {
        &["name", "path", "availability"][..]
    } else {
        &["name", "path", "availability", "reason"][..]
    };
    let (attrs, body) = yxml::inspect(node, "structure", fields)?;
    let name = &attrs["name"];
    require(!name.is_empty() && !name.contains('.'), "Invalid selected structure name")?;
    let expected = if parent.is_empty() { name.clone() } else { format!("{parent}.{name}") };
    require(attrs["path"] == expected, "Inconsistent public structure path")?;
    let mut result = json!(attrs);
    if !available {
        require(
            attrs["availability"] == "unavailable"
                && attrs["reason"] == "not_in_theory_namespace"
                && body.is_empty(),
            "Invalid unavailable public structure",
        )?;
        return Ok(result);
    }
    require(body.len() == 6, format!("{expected}: incomplete public structure"))?;
    result["position"] = position(yxml::child(body, 0)?)?;
    for (index, (group, tag)) in [
        ("values", "value"),
        ("type_constructors", "type_constructor"),
        ("signatures", "signature"),
        ("functors", "functor"),
    ]
    .iter()
    .enumerate()
    {
        result[*group] = named_group(yxml::child(body, index + 1)?, group, tag)?;
    }
    result["structures"] = structures(yxml::child(body, 5)?, "structures", None, &expected)?;
    Ok(result)
}
fn commands(node: &Node, name: &str, executed: &[String]) -> Result<Value, StepError> {
    let entries = yxml::group(node, "commands", "command")?
        .into_iter()
        .map(|item| {
            Ok(Value::Object(read_empty_attributes(
                item,
                "command",
                &["name", "kind", "registration"],
            )?))
        })
        .collect::<Result<Vec<_>, StepError>>()?;
    let names: HashSet<&str> = entries.iter().filter_map(|item| item["name"].as_str()).collect();
    require(names.len() == entries.len(), format!("Duplicate {name} command registry"))?;
    require(
        executed.iter().all(|command| names.contains(command.as_str())),
        format!("{name}: executed commands missing from final registry"),
    )?;
    require(
        entries.iter().all(|entry| entry["registration"] == "at_end_checked"),
        format!("{name}: incorrect parser registration evidence"),
    )?;
    require(!entries.is_empty(), format!("{name}: empty command registry"))?;
    Ok(json!(entries))
}
fn theory(node: &Node, executed: &HashMap<String, Vec<String>>) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "theory", &["name"])?;
    let name = &attrs["name"];
    require(body.len() == 2, format!("{name}: incomplete interface theory"))?;
    let (settings, abi) = yxml::inspect(yxml::child(body, 1)?, "ml_abi", &["read_global"])?;
    require(abi.len() == 5, format!("{name}: incomplete ML interface"))?;
    let mut ml_abi = namespace(&abi[..4])?;
    ml_abi["read_global"] = json!(yxml::bool_value(&settings["read_global"])?);
    ml_abi["selected_structures"] =
        structures(yxml::child(abi, 4)?, "selected_structures", Some(&SELECTED_STRUCTURES), "")?;
    let mut result = json!({"name":name});
    result["commands"] = commands(
        yxml::child(body, 0)?,
        name,
        executed.get(name).map(Vec::as_slice).unwrap_or(&[]),
    )?;
    result["ml_abi"] = ml_abi;
    Ok(result)
}
fn coverage(node: &Node) -> Result<Value, StepError> {
    let (_, body) = yxml::inspect(node, "coverage", &[])?;
    let mut observed = vec![];
    let mut unavailable = vec![];
    for item in yxml::elements(body)? {
        let value = read_empty_attributes(item, &item.tag, &["name"])?["name"].clone();
        match item.tag.as_str() {
            "observed" => observed.push(value),
            "unavailable" => unavailable.push(value),
            _ => return Err(StepError::Input("Unknown interface coverage category".into())),
        }
    }
    require(
        observed == json!(OBSERVED).as_array().cloned().unwrap_or_default()
            && unavailable == json!(UNAVAILABLE).as_array().cloned().unwrap_or_default(),
        "Unsupported interface coverage contract",
    )?;
    Ok(json!({"observed":observed,"unavailable":unavailable}))
}
fn read_executed_commands(execution: &Value) -> Result<HashMap<String, Vec<String>>, StepError> {
    yxml::array(execution, "theories")?
        .iter()
        .map(|item| {
            Ok((
                yxml::string(item, "name")?.into(),
                yxml::array(item, "commands")?
                    .iter()
                    .map(|cmd| Ok(yxml::string(cmd, "name")?.into()))
                    .collect::<Result<_, StepError>>()?,
            ))
        })
        .collect()
}

fn validate_interface_theories(
    theories: &[Value],
    inventory: &Value,
    executed: &HashMap<String, Vec<String>>,
) -> Result<(), StepError> {
    let names: HashSet<&str> = theories.iter().filter_map(|item| item["name"].as_str()).collect();
    yxml::unique(
        theories.iter().map(|item| item["name"].as_str().unwrap_or("").into()),
        "interface theory identities",
    )?;
    let inventory_names: HashSet<&str> = yxml::array(inventory, "theories")?
        .iter()
        .map(|item| yxml::string(item, "name"))
        .collect::<Result<_, _>>()?;
    let mut executed_names: HashSet<&str> = executed.keys().map(String::as_str).collect();
    executed_names.insert("Pure");
    require(
        names == inventory_names && names == executed_names,
        "Missing or foreign interface theory",
    )
}

pub fn decode_interfaces(
    raw: &str,
    inventory: &Value,
    execution: &Value,
) -> Result<Value, StepError> {
    let root = yxml::parse(raw)?;
    let (attrs, body) = yxml::inspect(
        &root,
        "interface_snapshot",
        &["version", "reference", "authorization", "type_text_semantics", "namespace_semantics"],
    )?;
    require(
        attrs["version"] == "1"
            && attrs["reference"] == "Isabelle2025"
            && attrs["authorization"] == AUTHORIZATION
            && attrs["type_text_semantics"] == TYPE_TEXT_SEMANTICS
            && attrs["namespace_semantics"] == NAMESPACE_SEMANTICS,
        "Unsupported reference interface snapshot",
    )?;
    require(body.len() == 4, "Missing interface roots/coverage/theories/bootstrap")?;
    let roots = yxml::read_names(yxml::child(body, 0)?, "roots", "root")?;
    require(
        roots == json!(ROOTS).as_array().cloned().unwrap_or_default()
            && inventory["roots"] == json!(roots)
            && execution["roots"] == json!(roots),
        "Interface root identities differ",
    )?;
    let executed = read_executed_commands(execution)?;
    let theories = yxml::group(yxml::child(body, 2)?, "theories", "theory")?
        .into_iter()
        .map(|item| theory(item, &executed))
        .collect::<Result<Vec<_>, _>>()?;
    validate_interface_theories(&theories, inventory, &executed)?;
    let bootstrap = yxml::group(yxml::child(body, 3)?, "bootstrap_interfaces", "theory")?
        .into_iter()
        .map(|item| theory(item, &HashMap::new()))
        .collect::<Result<Vec<_>, _>>()?;
    require(
        bootstrap.len() == 1
            && bootstrap[0]["name"] == "ML_Bootstrap"
            && bootstrap[0]["ml_abi"]["read_global"] == false,
        "Missing or inconsistent retained bootstrap namespace",
    )?;
    let mut output = json!({"schema":1,"reference":"Isabelle2025","authorization":AUTHORIZATION,"type_text_semantics":TYPE_TEXT_SEMANTICS,"namespace_semantics":NAMESPACE_SEMANTICS,"roots":roots});
    output["coverage"] = coverage(yxml::child(body, 1)?)?;
    output["theories"] = Value::Array(theories);
    output["bootstrap_interfaces"] = Value::Array(bootstrap);
    Ok(output)
}
