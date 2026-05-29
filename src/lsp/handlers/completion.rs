//! Handler for textDocument/completion.

use super::HandlerContext;
use crate::hol::hol_loader::HolTheoremDb;
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

/// Method names for auto-completion (after "by " or "apply ").
const METHODS: &[(&str, &str)] = &[
    ("auto", "Automatic proof search"),
    ("blast", "Tableau prover"),
    ("fast", "DFS + iterative deepening"),
    ("safe", "Safe rules exhaustively"),
    ("clarify", "Safe rules (alias)"),
    ("step", "Safe rules + one unsafe"),
    ("simp", "Simplification"),
    ("iprover", "Intuitionistic prover"),
    ("rule", "Apply introduction rule"),
    ("erule", "Apply elimination rule"),
    ("drule", "Apply destruction rule"),
    ("frule", "Apply forward rule"),
    ("subst", "Substitution"),
    ("induct", "Induction"),
    ("cases", "Case analysis"),
    ("unfold", "Unfold definitions"),
    ("fold", "Fold definitions"),
    ("insert", "Insert facts"),
    ("arith", "Arithmetic"),
    ("assumption", "Solve by assumption"),
    ("metis", "Metis prover (fallback)"),
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

    // Add method names
    for (method, desc) in METHODS {
        items.push(CompletionItem {
            label: method.to_string(),
            kind: Some(CompletionItemKind::Function),
            detail: Some(desc.to_string()),
            documentation: None,
            insert_text: Some(format!("{method} ")),
        });
    }

    // Add theorem names from the loaded DB (top 200 for performance)
    let db = HolTheoremDb::get();
    let mut count = 0;
    for (name, thm) in &db.by_name {
        if count >= 200 { break; }
        let nprems = thm.nprems();
        let detail = if nprems == 0 {
            "theorem (unconditional)".into()
        } else {
            format!("theorem ({nprems} premises)")
        };
        items.push(CompletionItem {
            label: name.clone(),
            kind: Some(CompletionItemKind::Property),
            detail: Some(detail),
            documentation: None,
            insert_text: Some(name.clone()),
        });
        count += 1;
    }

    let result = CompletionList {
        is_incomplete: count >= 200,
        items,
    };
    ctx.send_result(
        req.id,
        serde_json::to_value(result).expect("Serialization failed"),
    );
}
