//! Handler for textDocument/completion.

use super::HandlerContext;
use crate::server::lsp_types::*;

/// Isabelle keywords for auto-completion.
const KEYWORDS: &[(&str, &str)] = &[
    ("theory", "Begin a new theory"),
    ("imports", "Import parent theories"),
    ("begin", "Start theory body"),
    ("end", "End theory"),
    ("lemma", "State a lemma"),
    ("theorem", "State a theorem"),
    ("corollary", "State a corollary"),
    ("proof", "Begin proof"),
    ("qed", "End proof"),
    ("done", "Finish proof"),
    ("by", "Terminal proof by method"),
    ("apply", "Apply proof method"),
    ("have", "Intermediate statement"),
    ("show", "Statement matching goal"),
    ("hence", "then have"),
    ("thus", "then show"),
    ("fix", "Fix variables"),
    ("assume", "Assume proposition"),
    ("from", "Use facts"),
    ("with", "Use + chain facts"),
    ("using", "Use facts in method"),
    ("note", "Name a fact"),
    ("let", "Local abbreviation"),
    ("case", "Case analysis"),
    ("next", "Next case"),
    ("also", "Chain equational reasoning"),
    ("finally", "Conclude equational chain"),
    ("moreover", "Collect facts"),
    ("ultimately", "Use collected facts"),
    ("definition", "Define constant"),
    ("fun", "Define recursive function"),
    ("inductive", "Inductive predicate"),
    ("datatype", "Define datatype"),
    ("class", "Define type class"),
    ("instance", "Type class instance"),
    ("locale", "Named local context"),
    ("interpretation", "Interpret locale"),
];

/// Isabelle symbols for auto-completion.
const SYMBOLS: &[(&str, &str)] = &[
    ("-->", "HOL implication"),
    ("==>", "Pure implication"),
    ("&", "HOL conjunction"),
    ("|", "HOL disjunction"),
    ("~", "HOL negation"),
    ("ALL", "Universal quantifier"),
    ("EX", "Existential quantifier"),
    ("!!", "Pure universal"),
    ("==", "Pure equality"),
    ("=>", "Function type arrow"),
    ("True", "Truth constant"),
    ("False", "Falsity constant"),
];

pub fn handle_completion(ctx: &HandlerContext, req: JsonRpcRequest) {
    let _params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    let mut items = Vec::new();

    // Add keywords
    for (kw, desc) in KEYWORDS {
        items.push(CompletionItem {
            label: kw.to_string(),
            kind: Some(CompletionItemKind::Keyword),
            detail: Some(desc.to_string()),
            documentation: None,
            insert_text: Some(format!("{kw} ")),
        });
    }

    // Add symbols
    for (sym, desc) in SYMBOLS {
        items.push(CompletionItem {
            label: sym.to_string(),
            kind: Some(CompletionItemKind::Function),
            detail: Some(desc.to_string()),
            documentation: None,
            insert_text: Some(format!("{sym} ")),
        });
    }

    let result = CompletionList {
        is_incomplete: false,
        items,
    };
    ctx.send_result(
        req.id,
        serde_json::to_value(result).expect("Serialization failed"),
    );
}
