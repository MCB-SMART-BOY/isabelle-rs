use crate::common::{EXPECTED_THEORY_COUNT, ROOTS, as_array, as_str, field, require};
use crate::{EvidenceError, EvidenceError as StepError};
use serde_json::Value;
use std::collections::{HashMap, HashSet};

fn array<'a>(value: &'a Value, key: &str) -> Result<&'a Vec<Value>, StepError> {
    as_array(field(value, key)?, key)
}

fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str, StepError> {
    as_str(field(value, key)?, key)
}

fn theory_name(theory: &Value) -> Result<&str, StepError> {
    string(theory, "name")
}
fn parents(theory: &Value) -> Result<Vec<&str>, StepError> {
    array(theory, "parents")?
        .iter()
        .map(|parent| {
            parent.as_str().ok_or_else(|| EvidenceError::Input("Malformed theory parent".into()))
        })
        .collect()
}
fn visit<'a>(
    name: &'a str,
    by_name: &HashMap<&'a str, &'a Value>,
    visited: &mut HashSet<&'a str>,
    visiting: &mut HashSet<&'a str>,
) -> Result<(), StepError> {
    let theory = by_name
        .get(name)
        .ok_or_else(|| EvidenceError::Input(format!("Unknown parent theory {name}")))?;
    require(!visiting.contains(name), format!("Theory import cycle at {name}"))?;
    if visited.contains(name) {
        return Ok(());
    }
    visiting.insert(name);
    let parents = parents(theory)?;
    require(
        parents.iter().collect::<HashSet<_>>().len() == parents.len(),
        format!("duplicate parents of {name}"),
    )?;
    for parent in parents {
        visit(parent, by_name, visited, visiting)?;
    }
    visiting.remove(name);
    visited.insert(name);
    Ok(())
}
pub fn validate_graph(theories: &[Value]) -> Result<(), StepError> {
    require(
        theories.len() == EXPECTED_THEORY_COUNT,
        format!(
            "Expected {EXPECTED_THEORY_COUNT} fixed-closure theory nodes, got {}",
            theories.len()
        ),
    )?;
    let mut by_name = HashMap::new();
    for theory in theories {
        let name = theory_name(theory)?;
        require(by_name.insert(name, theory).is_none(), "Duplicate theory identities")?;
    }
    let mut visited = HashSet::new();
    let mut visiting = HashSet::new();
    for root in ROOTS {
        visit(root, &by_name, &mut visited, &mut visiting)?;
    }
    require(visited.len() == by_name.len(), "Disconnected non-root theories")?;
    require(
        theories.windows(2).all(|pair| pair[0]["name"].as_str() <= pair[1]["name"].as_str()),
        "Theory list is not in deterministic name order",
    )
}
fn ancestry<'a>(
    name: &'a str,
    by_name: &HashMap<&'a str, &'a Value>,
    cache: &mut HashMap<&'a str, HashSet<&'a str>>,
) -> Result<HashSet<&'a str>, StepError> {
    if let Some(found) = cache.get(name) {
        return Ok(found.clone());
    }
    let mut found = HashSet::from([name]);
    let theory =
        by_name.get(name).ok_or_else(|| EvidenceError::Input(format!("Missing theory {name}")))?;
    for parent in parents(theory)? {
        found.extend(ancestry(parent, by_name, cache)?);
    }
    cache.insert(name, found.clone());
    Ok(found)
}
fn unique_section(theory: &Value, name: &str, section: &str) -> Result<(), StepError> {
    let mut seen = HashSet::new();
    for entry in array(theory, section)? {
        let key = if section == "oracle_registrations" {
            entry.to_string()
        } else if section == "named_derivations" {
            format!("{}:{}", string(entry, "name")?, entry["index"])
        } else {
            string(entry, "name")?.to_owned()
        };
        require(seen.insert(key), format!("Duplicate {name} {section}"))?;
    }
    Ok(())
}
fn validate_definitions(theory: &Value, name: &str) -> Result<(), StepError> {
    for section in ["class_relations", "arities", "specifications", "constant_definitions"] {
        let mut seen = HashSet::new();
        for entry in array(theory, section)? {
            require(seen.insert(entry.to_string()), format!("Duplicate {name} {section}"))?;
        }
    }
    let links: HashSet<(&str, &str)> = array(theory, "specifications")?
        .iter()
        .filter_map(|spec| {
            if spec["subject"]["kind"] != "const" {
                return None;
            }
            Some((spec["subject"]["name"].as_str()?, spec["axiom_name"].as_str()?))
        })
        .collect();
    for item in array(theory, "constant_definitions")? {
        require(
            links.contains(&(string(item, "constant")?, string(item, "axiom")?)),
            format!("{name}: constant definition lacks matching dependency specification: {item}"),
        )?;
    }
    Ok(())
}
fn validate_facts(
    theory: &Value,
    name: &str,
    ancestors: &HashSet<&str>,
) -> Result<HashSet<(String, u64)>, StepError> {
    let indexes: HashMap<&str, &Value> = array(theory, "fact_indexes")?
        .iter()
        .map(|item| Ok((string(item, "name")?, item)))
        .collect::<Result<_, StepError>>()?;
    let mut facts = HashSet::new();
    for group in array(theory, "fact_groups")? {
        let group_name = string(group, "name")?;
        require(
            indexes.get(group_name).is_some_and(|index| index["dynamic"] == false),
            format!("{name}: static group absent or marked dynamic: {group_name}"),
        )?;
        let theorems = array(group, "theorems")?;
        for (index, item) in theorems.iter().enumerate() {
            let expected = if theorems.len() == 1 { 0 } else { index + 1 };
            require(
                item["index"].as_u64() == Some(expected as u64),
                format!("{name}.{group_name}: invalid official theorem index sequence"),
            )?;
            require(item["owner"] == name, format!("{name}: theorem transferred context differs"))?;
            facts.insert((string(item, "name")?.to_owned(), expected as u64));
        }
    }
    for index in array(theory, "fact_indexes")? {
        require(
            ancestors.contains(string(index, "origin")?),
            format!("{name}: fact origin outside its ancestry"),
        )?;
    }
    Ok(facts)
}
fn ref_identity(item: &Value) -> Result<(&str, u64), StepError> {
    Ok((
        string(item, "origin")?,
        item["serial"]
            .as_u64()
            .ok_or_else(|| EvidenceError::Input("Invalid derivation serial".into()))?,
    ))
}
fn validate_derivations(
    theories: &[Value],
    facts: &HashMap<&str, HashSet<(String, u64)>>,
    ancestors: &HashMap<&str, HashSet<&str>>,
) -> Result<(), StepError> {
    let mut derivations: HashMap<(&str, u64), (&str, u64)> = HashMap::new();
    for theory in theories {
        let name = theory_name(theory)?;
        for item in array(theory, "named_derivations")? {
            let identity = ref_identity(item)?;
            let target = (
                string(item, "name")?,
                item["index"]
                    .as_u64()
                    .ok_or_else(|| EvidenceError::Input("Invalid named derivation index".into()))?,
            );
            require(identity.0 == name, "Derivation origin differs from table")?;
            require(
                facts[name].contains(&(target.0.to_owned(), target.1)),
                format!("Unresolved named derivation {target:?}"),
            )?;
            require(
                derivations.insert(identity, target).is_none(),
                format!("Duplicate derivation identity {identity:?}"),
            )?;
        }
    }
    for theory in theories {
        let name = theory_name(theory)?;
        for group in array(theory, "fact_groups")? {
            for theorem in array(group, "theorems")? {
                let mut seen = HashSet::new();
                for dep in array(theorem, "dependencies")? {
                    let identity = ref_identity(dep)?;
                    require(seen.insert(identity), "Duplicate theorem dependency identities")?;
                    require(
                        ancestors[name].contains(identity.0),
                        format!("Dependency outside theorem ancestry: {identity:?}"),
                    )?;
                    require(
                        derivations.get(&identity)
                            == Some(&(
                                string(dep, "name")?,
                                dep["index"].as_u64().ok_or_else(|| {
                                    EvidenceError::Input("Invalid dependency index".into())
                                })?,
                            )),
                        format!("Unresolved or inconsistent theorem dependency: {identity:?}"),
                    )?;
                }
            }
        }
    }
    Ok(())
}
pub fn validate_entities(theories: &[Value]) -> Result<(), StepError> {
    let by_name: HashMap<&str, &Value> = theories
        .iter()
        .map(|theory| Ok((theory_name(theory)?, theory)))
        .collect::<Result<_, StepError>>()?;
    let mut ancestors = HashMap::new();
    let mut facts = HashMap::new();
    for theory in theories {
        let name = theory_name(theory)?;
        let inherited = ancestry(name, &by_name, &mut ancestors)?;
        for section in [
            "types",
            "classes",
            "constants",
            "axioms",
            "fact_indexes",
            "fact_groups",
            "named_derivations",
            "oracle_registrations",
        ] {
            unique_section(theory, name, section)?;
        }
        validate_definitions(theory, name)?;
        facts.insert(name, validate_facts(theory, name, &inherited)?);
    }
    require(
        facts.get("HOL.HOL").is_some_and(|items| items.contains(&("HOL.TrueI".into(), 0))),
        "Missing known HOL.TrueI theorem",
    )?;
    validate_derivations(theories, &facts, &ancestors)
}
