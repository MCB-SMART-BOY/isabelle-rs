//! Structural observation requirements. These diagnostics never certify a proof.
use std::collections::BTreeSet;

use serde_json::Value;

use crate::EvidenceError;
use crate::common::{COMMIT, as_array, as_object, as_str, field, require, require_fields};
use crate::compare_syntax::{SyntaxScope, require_index, validate_sort};

const DEPENDENCY_KINDS: [&str; 6] =
    ["Axiom", "Definition", "Typedef", "Class", "Arity", "AcceptedFact"];
const REGISTRATION_KINDS: [&str; 6] =
    ["Command", "Method", "Attribute", "TheoryData", "ProofData", "MLHook"];

fn require_identity<'a>(value: &'a Value, context: &str) -> Result<&'a str, EvidenceError> {
    let identity = as_str(value, context)?;
    require(!identity.is_empty(), format!("{context}: empty identity"))?;
    Ok(identity)
}

fn validate_obligation<'a>(
    value: &'a Value,
    scope: &mut SyntaxScope<'a>,
) -> Result<(), EvidenceError> {
    require_fields(
        value,
        &["type", "required_sort", "source_owner", "occurrence"],
        "sort obligation",
    )?;
    scope.validate_type(field(value, "type")?)?;
    validate_sort(field(value, "required_sort")?)?;
    require_identity(field(value, "source_owner")?, "sort obligation owner")?;
    let occurrence = field(value, "occurrence")?;
    require_fields(occurrence, &["source", "path"], "sort obligation occurrence")?;
    let source = require_identity(field(occurrence, "source")?, "sort obligation source")?;
    require(matches!(source, "P" | "H" | "F" | "C"), "unknown sort obligation source")?;
    for segment in as_array(field(occurrence, "path")?, "sort obligation path")? {
        require_index(segment, "sort obligation path")?;
    }
    Ok(())
}

fn validate_statement(value: &Value, context: &str) -> Result<(), EvidenceError> {
    let mut scope = SyntaxScope::default();
    scope.validate_judgment(value)?;
    for obligation in as_array(field(value, "sort_obligations")?, context)? {
        validate_obligation(obligation, &mut scope)?;
    }
    Ok(())
}

pub(crate) fn validate_dependency(value: &Value) -> Result<(), EvidenceError> {
    require_fields(value, &["kind", "name", "owner", "statement", "certificate"], "dependency")?;
    let kind = require_identity(field(value, "kind")?, "dependency kind")?;
    require(DEPENDENCY_KINDS.contains(&kind), "unknown dependency kind")?;
    let name = require_identity(field(value, "name")?, "dependency name")?;
    require(name.contains('.'), "dependency requires a qualified name")?;
    require_identity(field(value, "owner")?, "dependency owner")?;
    let statement = field(value, "statement")?;
    require_fields(
        statement,
        &["proposition", "hypotheses", "shyps", "tpairs", "sort_obligations"],
        "dependency statement",
    )?;
    validate_statement(statement, "dependency sort obligations")?;
    let certificate = field(value, "certificate")?;
    require_fields(certificate, &["kind", "owner", "goal", "premises"], "dependency certificate")?;
    require(
        as_str(field(certificate, "kind")?, "certificate kind")? == kind
            && field(certificate, "owner")? == field(value, "owner")?
            && field(certificate, "goal")? == field(statement, "proposition")?,
        "dependency certificate does not bind its exact goal and owner",
    )?;
    for premise in as_array(field(certificate, "premises")?, "certificate premises")? {
        SyntaxScope::default().validate_term(premise)?;
    }
    Ok(())
}

pub(super) fn validate_named_payload(field_name: &str, value: &Value) -> Result<(), EvidenceError> {
    match field_name {
        "full_axiom_extension_dependencies" => {
            let mut seen = BTreeSet::new();
            for dependency in as_array(value, field_name)? {
                validate_dependency(dependency)?;
                let key = (
                    dependency["kind"].as_str(),
                    dependency["name"].as_str(),
                    dependency["owner"].as_str(),
                );
                require(seen.insert(key), "duplicate full dependency identity")?;
            }
        },
        "unresolved_sort_obligations" => {
            as_array(value, field_name)?;
        },
        "declaration_origin" => {
            require_fields(
                value,
                &["owner", "source", "command_sequence", "operation", "fact_name", "member_index"],
                "declaration origin",
            )?;
            require_identity(field(value, "owner")?, "declaration owner")?;
            let source = require_identity(field(value, "source")?, "declaration source")?;
            crate::protocol::validate_relative_path(source)?;
            require_index(field(value, "command_sequence")?, "declaration command")?;
            require_identity(field(value, "operation")?, "declaration operation")?;
            require_identity(field(value, "fact_name")?, "declaration fact")?;
            require_index(field(value, "member_index")?, "declaration member index")?;
        },
        _ => return Err(EvidenceError::Input(format!("{field_name}: not a named observation"))),
    }
    Ok(())
}

pub(super) fn validate_sort_obligations(
    value: &Value,
    theorem: &Value,
) -> Result<(), EvidenceError> {
    let mut scope = SyntaxScope::default();
    scope.validate_judgment(theorem)?;
    for obligation in as_array(value, "sort obligations")? {
        validate_obligation(obligation, &mut scope)?;
    }
    Ok(())
}

fn validate_anonymous_fact(value: &Value) -> Result<(), EvidenceError> {
    require_fields(
        value,
        &["owner", "statement", "dependencies", "authorization_kind"],
        "anonymous fact",
    )?;
    require_identity(field(value, "owner")?, "anonymous fact owner")?;
    let statement = field(value, "statement")?;
    require_fields(
        statement,
        &["proposition", "hypotheses", "shyps", "tpairs", "sort_obligations"],
        "anonymous statement",
    )?;
    validate_statement(statement, "anonymous sort obligations")?;
    for dependency in as_array(field(value, "dependencies")?, "anonymous dependencies")? {
        validate_dependency(dependency)?;
    }
    require_identity(field(value, "authorization_kind")?, "anonymous authorization")?;
    Ok(())
}

fn validate_dynamic_evaluation(value: &Value) -> Result<(), EvidenceError> {
    require_fields(value, &["source", "expression", "results"], "dynamic fact evaluation")?;
    crate::protocol::validate_relative_path(require_identity(
        field(value, "source")?,
        "dynamic source",
    )?)?;
    require_identity(field(value, "expression")?, "dynamic expression")?;
    for result in as_array(field(value, "results")?, "dynamic evaluation results")? {
        validate_anonymous_fact(result)?;
    }
    Ok(())
}

fn validate_registration(value: &Value) -> Result<(), EvidenceError> {
    require_fields(
        value,
        &["kind", "name", "owner", "source", "action", "signature"],
        "registration effect",
    )?;
    require(
        REGISTRATION_KINDS.contains(&require_identity(field(value, "kind")?, "registration kind")?),
        "unknown registration kind",
    )?;
    require_identity(field(value, "name")?, "registration name")?;
    require_identity(field(value, "owner")?, "registration owner")?;
    crate::protocol::validate_relative_path(require_identity(
        field(value, "source")?,
        "registration source",
    )?)?;
    require(
        matches!(
            require_identity(field(value, "action")?, "registration action")?,
            "Registered" | "Replaced" | "Removed"
        ),
        "unknown registration action",
    )?;
    let signature = as_object(field(value, "signature")?, "registration signature")?;
    require(
        signature.contains_key("domain") && signature.contains_key("range") && signature.len() == 2,
        "registration signature must specify domain and range",
    )?;
    require_identity(&signature["domain"], "registration domain")?;
    require_identity(&signature["range"], "registration range")?;
    Ok(())
}

pub(super) fn validate_event_payload(field_name: &str, value: &Value) -> Result<(), EvidenceError> {
    match field_name {
        "anonymous_ephemeral_facts" => validate_anonymous_fact(value),
        "dynamic_fact_evaluations" => validate_dynamic_evaluation(value),
        "runtime_registration_effects" => validate_registration(value),
        _ => Err(EvidenceError::Input(format!("{field_name}: not an event observation"))),
    }
}

pub(super) fn validate_statement_signature(
    statement: &Value,
    signature: &crate::signature::Signature<'_>,
) -> Result<(), EvidenceError> {
    signature.validate_judgment(statement)?;
    if let Some(obligations) = statement.get("sort_obligations") {
        for obligation in as_array(obligations, "sort obligations")? {
            signature.validate_type(field(obligation, "type")?)?;
            signature.validate_declared_sort(field(obligation, "required_sort")?)?;
        }
    }
    Ok(())
}

pub(super) fn validate_dependency_signature(
    dependency: &Value,
    signature: &crate::signature::Signature<'_>,
) -> Result<(), EvidenceError> {
    validate_statement_signature(field(dependency, "statement")?, signature)?;
    let certificate = field(dependency, "certificate")?;
    signature.validate_term(field(certificate, "goal")?)?;
    for premise in as_array(field(certificate, "premises")?, "certificate premises")? {
        signature.validate_term(premise)?;
    }
    Ok(())
}

fn collect_inventory_members(
    inventory: &Value,
) -> Result<BTreeSet<(&str, &str, u64)>, EvidenceError> {
    let mut members = BTreeSet::new();
    for theory in as_array(field(inventory, "theories")?, "inventory theories")? {
        let name = require_identity(field(theory, "name")?, "theory")?;
        for group in as_array(field(theory, "fact_groups")?, "fact groups")? {
            let group_name = require_identity(field(group, "name")?, "group")?;
            for member in as_array(field(group, "theorems")?, "group members")? {
                members.insert((
                    name,
                    group_name,
                    require_index(field(member, "index")?, "member")?,
                ));
            }
        }
    }
    Ok(members)
}

fn collect_covered_members(coverage: &Value) -> Result<BTreeSet<(&str, &str, u64)>, EvidenceError> {
    let mut members = BTreeSet::new();
    for item in as_array(field(coverage, "named_members")?, "covered named members")? {
        require_fields(item, &["theory", "fact_group_name", "member_index"], "covered member")?;
        let key = (
            require_identity(field(item, "theory")?, "covered theory")?,
            require_identity(field(item, "fact_group_name")?, "covered group")?,
            require_index(field(item, "member_index")?, "covered index")?,
        );
        require(members.insert(key), "duplicate covered member")?;
    }
    Ok(members)
}

type CommandIdentity<'a> = (&'a str, u64, &'a str);
type CommandIdentities<'a> = BTreeSet<CommandIdentity<'a>>;

fn collect_command_coverage<'a>(
    coverage: &'a Value,
    observed: &'a Value,
) -> Result<(CommandIdentities<'a>, CommandIdentities<'a>), EvidenceError> {
    let mut commands = BTreeSet::new();
    let mut events = BTreeSet::new();
    for item in as_array(field(coverage, "executed_commands")?, "covered commands")? {
        require_fields(
            item,
            &["theory", "sequence", "source", "observed_local_ids"],
            "covered command",
        )?;
        let theory = require_identity(field(item, "theory")?, "command theory")?;
        let sequence = require_index(field(item, "sequence")?, "command sequence")?;
        let source = require_identity(field(item, "source")?, "command source")?;
        require(commands.insert((theory, sequence, source)), "duplicate covered command")?;
        for local in as_array(field(item, "observed_local_ids")?, "observed event IDs")? {
            let local = require_identity(local, "observed local ID")?;
            require(events.insert((theory, sequence, local)), "duplicate observed event identity")?;
        }
    }
    let observed_ids = as_array(observed, "observed events")?
        .iter()
        .map(|entry| {
            Ok((
                require_identity(field(entry, "theory")?, "event theory")?,
                require_index(field(entry, "execution_event")?, "event sequence")?,
                require_identity(field(entry, "local_id")?, "event local ID")?,
            ))
        })
        .collect::<Result<BTreeSet<_>, EvidenceError>>()?;
    require(events == observed_ids, "event coverage does not match observed event identities")?;
    Ok((commands, events))
}

fn collect_executed_commands(
    execution: &Value,
) -> Result<BTreeSet<(&str, u64, &str)>, EvidenceError> {
    let mut commands = BTreeSet::new();
    for theory in as_array(field(execution, "theories")?, "executed theories")? {
        let name = require_identity(field(theory, "name")?, "executed theory")?;
        for item in as_array(field(theory, "commands")?, "executed commands")? {
            let sequence = require_index(field(item, "sequence")?, "executed command sequence")?;
            let source = require_identity(field(item, "source")?, "executed command source")?;
            require(
                commands.insert((name, sequence, source)),
                "duplicate executed command identity",
            )?;
        }
    }
    Ok(commands)
}

pub(super) fn has_complete_coverage(
    artifact: &Value,
    field_name: &str,
    observed: &Value,
    inventory: &Value,
    execution: &Value,
) -> Result<bool, EvidenceError> {
    let Some(coverage_records) = artifact.get("coverage") else {
        return Ok(false);
    };
    require(
        artifact["schema_version"] == 1 && artifact["source_commit"] == COMMIT,
        "observation artifact source/version differs",
    )?;
    let mut seen = BTreeSet::new();
    let mut selected = None;
    for item in as_array(coverage_records, "observation coverage")? {
        require_fields(
            item,
            &["field", "named_members", "executed_commands"],
            "observation coverage",
        )?;
        let name = require_identity(field(item, "field")?, "covered field")?;
        require(
            crate::compare::P0_MISSING.contains(&name),
            format!("unknown coverage field {name}"),
        )?;
        require(seen.insert(name), format!("duplicate observation coverage field {name}"))?;
        if name == field_name {
            selected = Some(item);
        }
    }
    let Some(coverage) = selected else {
        return Ok(false);
    };
    require(
        collect_covered_members(coverage)? == collect_inventory_members(inventory)?,
        format!("{field_name}: named fact observation coverage incomplete"),
    )?;
    let empty = Value::Array(Vec::new());
    let observed_events = if matches!(
        field_name,
        "anonymous_ephemeral_facts" | "dynamic_fact_evaluations" | "runtime_registration_effects"
    ) {
        observed
    } else {
        &empty
    };
    let (commands, _) = collect_command_coverage(coverage, observed_events)?;
    require(
        commands == collect_executed_commands(execution)?,
        format!("{field_name}: executed command observation coverage incomplete"),
    )?;
    Ok(true)
}
