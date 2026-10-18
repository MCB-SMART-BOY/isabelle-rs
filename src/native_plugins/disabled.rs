//! Fixed ROOT antiquotations whose original runtime dependency is not yet authorized natively.
//! These are compile-time diagnostics only, never advertised as callable services.
use super::{SessionLink, SessionLinkStatus, SourcePosition};

struct DisabledName {
    name: &'static str,
    single: bool,
    bytes: bool,
    source: &'static str,
    line: u32,
    reason: &'static str,
}

const UNAVAILABLE: &[DisabledName] = &[
    DisabledName {
        name: "scala_toplevel",
        single: true,
        bytes: false,
        source: "isabelle-source/src/Pure/System/scala.scala",
        line: 187,
        reason: "original Scala compiler requires the prohibited JVM runtime",
    },
    DisabledName {
        name: "scala_build",
        single: false,
        bytes: true,
        source: "isabelle-source/src/Pure/Tools/scala_build.scala",
        line: 102,
        reason: "original Scala JAR build requires the prohibited JVM runtime",
    },
    DisabledName {
        name: "jEdit.resource",
        single: false,
        bytes: false,
        source: "isabelle-source/src/Tools/jEdit/src/jedit_jar.scala",
        line: 22,
        reason: "jEdit Java resource loading requires the prohibited JVM runtime",
    },
    DisabledName {
        name: "Prismjs.languages",
        single: false,
        bytes: false,
        source: "isabelle-source/src/Pure/Tools/prismjs.scala",
        line: 125,
        reason: "PrismJS Scala-side service is not linked to a native implementation",
    },
    DisabledName {
        name: "Prismjs.tokenize",
        single: false,
        bytes: false,
        source: "isabelle-source/src/Pure/Tools/prismjs.scala",
        line: 131,
        reason: "PrismJS Scala-side service is not linked to a native implementation",
    },
    DisabledName {
        name: "bibtex_check_database",
        single: true,
        bytes: false,
        source: "isabelle-source/src/Pure/General/bibtex.scala",
        line: 146,
        reason: "original BibTeX validator launches an external executable, not authorized by the plugin host",
    },
    DisabledName {
        name: "bibtex_session_entries",
        single: false,
        bytes: false,
        source: "isabelle-source/src/Pure/General/bibtex.scala",
        line: 206,
        reason: "session command-id and bibliography state have no native provider",
    },
    DisabledName {
        name: "doc_names",
        single: true,
        bytes: false,
        source: "isabelle-source/src/Pure/Tools/doc.scala",
        line: 115,
        reason: "document catalogue requires independently authorized documentation roots and environment",
    },
    DisabledName {
        name: "SystemOnTPTP.list_systems",
        single: true,
        bytes: false,
        source: "isabelle-source/src/HOL/Tools/ATP/system_on_tptp.scala",
        line: 40,
        reason: "remote SystemOnTPTP discovery requires prohibited network access",
    },
    DisabledName {
        name: "SystemOnTPTP.run_system",
        single: false,
        bytes: false,
        source: "isabelle-source/src/HOL/Tools/ATP/system_on_tptp.scala",
        line: 68,
        reason: "remote SystemOnTPTP execution requires prohibited network access",
    },
];

pub(super) fn is_disabled(name: &str) -> Option<&'static str> {
    UNAVAILABLE.iter().find(|entry| entry.name == name).map(|entry| entry.reason)
}

pub(super) fn disabled_links() -> impl Iterator<Item = SessionLink> {
    UNAVAILABLE.iter().map(|entry| SessionLink {
        name: entry.name.to_owned(),
        single: entry.single,
        bytes: entry.bytes,
        position: SourcePosition { file: entry.source.to_owned(), line: entry.line },
        status: SessionLinkStatus::Disabled { reason: entry.reason },
    })
}
