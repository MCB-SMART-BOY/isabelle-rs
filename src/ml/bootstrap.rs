//! Original Pure bootstrap source execution through the same restricted, leased host.
use super::host::context::{ContextHost, replacement_structure};
use super::host::files::{FileHostBridge, HostIoError};
use super::host::lifecycle::{BuildLifecycle, TaskLease};
use super::host::objects::ObjectStore;
use super::value::ValueData;
use super::{MlError, MlErrorKind, Span, Type, TypeScheme, Value, Vm};
use isabelle_kernel::TrustedTheory;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::Path;
use std::rc::Rc;
use std::sync::Arc;
#[path = "bootstrap/text_io.rs"]
mod text_io;

const PURE_SOURCE: &str = "src/Pure/";
const ROOT0: &str = "src/Pure/ROOT0.ML";
const ROOT: &str = "src/Pure/ROOT.ML";
const CONTEXT_SOURCE: &str = "context.ML";
/// Purpose is part of the caller-approved environment capability.
pub const ML_ENVIRONMENT_PURPOSE: &str = "ML bootstrap environment";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedMlSource {
    pub path: String,
    pub sha256: String,
    /// Original source hash remains `sha256`; approved SHA1 native cutover records executed bytes separately.
    pub executable_sha256: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootPrefixProgress {
    /// Successfully evaluated original source files, with the approved SHA1 cutover identified separately.
    pub loaded_files: Vec<LoadedMlSource>,
    /// Source inventory hashes of exactly the ROOT bytes parsed by this runner.
    pub root0_sha256: String,
    pub root_sha256: String,
    pub next_ml_file: String,
    pub remaining_files: Vec<String>,
}
/// Audited original ROOT prefix followed by the approved native Context body.
/// The remaining ROOT files have not been executed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootContextProgress {
    pub prefix: RootPrefixProgress,
    pub context_source_sha256: String,
    pub replacement_structure_sha256: String,
    pub remaining_files: Vec<String>,
}

#[derive(Debug)]
pub struct RootPrefixFailure {
    pub loaded_files: Vec<LoadedMlSource>,
    pub failed_source: String,
    pub remaining_files: Vec<String>,
    pub error: Box<MlError>,
}

/// Per-ROOT directive evidence; CPFileName alone is an untrusted ML label.
pub(super) struct RootLoadEvidence {
    path: String,
    original: Option<(LoadedMlSource, [u8; 32], usize)>,
    compiled: Sha256,
    compiled_len: usize,
}

impl RootLoadEvidence {
    fn new(path: String) -> Self {
        Self { path, original: None, compiled: Sha256::new(), compiled_len: 0 }
    }

    fn verified_source(self) -> Option<LoadedMlSource> {
        let (source, expected, length) = self.original?;
        (self.compiled_len == length && <[u8; 32]>::from(self.compiled.finalize()) == expected)
            .then_some(source)
    }
}

/// Match the fixed ml_compiler0.ML `ml_input` transformation before attesting
/// execution. The compiler's CPFileName is diagnostic metadata, not source proof.
fn expected_ml_input(vm: &Vm, path: &str, bytes: &[u8]) -> Result<([u8; 32], usize), MlError> {
    const HERE: &[u8] = b"\\<^here>";
    const MAKE_STRING: &[u8] = b"@{make_string}";
    let mut digest = Sha256::new();
    let mut length = 0_usize;
    let mut cursor = 0_usize;
    let mut line = 1_usize;
    let mut make_string = None;
    while cursor < bytes.len() {
        let start = cursor;
        while cursor < bytes.len() && !matches!(bytes[cursor], b'\\' | b'@' | b'\n') {
            cursor += 1;
        }
        digest.update(&bytes[start..cursor]);
        length += cursor - start;
        if cursor == bytes.len() {
            break;
        }
        let rest = &bytes[cursor..];
        let (replacement, consumed): (std::borrow::Cow<'_, [u8]>, usize) = if rest.starts_with(HERE)
        {
            (format!("(Position.line_file_only {line} \"{path}\")").into_bytes().into(), HERE.len())
        } else if rest.starts_with(MAKE_STRING) {
            let value = match make_string {
                Some(value) => value,
                None => {
                    let value = vm
                        .lookup_value("ML_Pretty.make_string_fn")?
                        .and_then(Value::as_text)
                        .ok_or_else(|| {
                            vm.error(
                                MlErrorKind::HostFailure,
                                "transform ROOT source",
                                "ML_Pretty.make_string_fn not installed",
                            )
                        })?;
                    make_string = Some(value);
                    value
                },
            };
            (value.as_bytes().into(), MAKE_STRING.len())
        } else if rest.starts_with(b"\\<") {
            (b"\\\\<".as_slice().into(), b"\\<".len())
        } else {
            if rest[0] == b'\n' {
                line += 1;
            }
            (rest[..1].into(), 1)
        };
        length += replacement.len();
        if length > super::host::files::MAX_FILE_BYTES {
            return Err(vm.error(
                MlErrorKind::HostFailure,
                "transform ROOT source",
                format!("{path}: transformed ML source exceeds approved bound"),
            ));
        }
        digest.update(replacement);
        cursor += consumed;
    }
    Ok((digest.finalize().into(), length))
}

#[derive(Clone)]
struct RootDirective {
    source: &'static str,
    line: usize,
    command: String,
    argument: String,
}

impl Vm {
    /// Bind native Basis IO and dynamic compilation to this VM's live Evaluation lease.
    pub fn install_bootstrap_host(&mut self, host: Arc<FileHostBridge>) -> Result<(), MlError> {
        self.check_stop()?;
        if self.bootstrap_host.is_some() {
            return Err(self.error(
                MlErrorKind::Type,
                "install bootstrap",
                "bootstrap host already installed",
            ));
        }
        host.check_vm(self)
            .map_err(|error| self.host_io_failure("install bootstrap", "VM", error))?;
        if self.resolve_host_type("TextIO.instream").is_some() {
            return Err(self.error(
                MlErrorKind::Type,
                "install bootstrap",
                "TextIO.instream already installed",
            ));
        }
        let string = Type::Constructor("string".to_owned(), vec![]);
        let unit = Type::Constructor("unit".to_owned(), vec![]);
        let option = Type::Constructor("option".to_owned(), vec![string.clone()]);
        let loader = TypeScheme::mono(Type::Function(Box::new(string.clone()), Box::new(unit)));
        for name in ["use", "ML_file", "ML_file_debug", "ML_file_no_debug"] {
            self.register_native(name, loader.clone(), use_source)?;
        }
        self.register_native(
            "OS.Process.getEnv",
            TypeScheme::mono(Type::Function(Box::new(string), Box::new(option))),
            get_environment,
        )?;
        text_io::install(self)?;
        self.install_native_sha1()?;
        self.bootstrap_host = Some(host);
        Ok(())
    }

    /// Compile exactly the bytes supplied by the leased restricted host, preserving source attribution.
    pub fn evaluate_source_file(&mut self, path: &str) -> Result<LoadedMlSource, MlError> {
        let bytes = self.read_bootstrap_source(path)?;
        let digest = format!("{:x}", Sha256::digest(&bytes));
        let text = std::str::from_utf8(&bytes).map_err(|error| {
            self.error(MlErrorKind::Syntax, "decode ML source", format!("{path}: {error}"))
        })?;
        let previous_name = std::mem::replace(&mut self.source_name, path.to_owned());
        let previous_span = std::mem::replace(&mut self.declaration_span, Span::new(path, 0, 0));
        let result = if path == super::native_sha1::SHA1_SOURCE {
            self.evaluate_native_sha1_module(path, text)
                .map(|identity| Some(identity.executable_sha256))
        } else {
            self.evaluate(path, text).map(|()| None)
        };
        self.source_name = previous_name;
        self.declaration_span = previous_span;
        let executable_sha256 = result?;
        let source = LoadedMlSource { path: path.to_owned(), sha256: digest, executable_sha256 };
        self.loaded_sources.push(source.clone());
        Ok(source)
    }

    fn record_root_read(&mut self, path: &str, bytes: &[u8]) -> Result<(), MlError> {
        if !self.root_load.as_ref().is_some_and(|load| load.path == path) {
            return Ok(());
        }
        let (expected, length) = expected_ml_input(self, path, bytes).inspect_err(|_| {
            self.request_stop();
        })?;
        let source = LoadedMlSource {
            path: path.to_owned(),
            sha256: format!("{:x}", Sha256::digest(bytes)),
            executable_sha256: None,
        };
        let evidence = (source, expected, length);
        let Some(load) = self.root_load.as_mut() else {
            return Ok(());
        };
        if load.original.as_ref().is_some_and(|prior| prior != &evidence) {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "read ROOT source",
                format!("{path}: source changed during the same load"),
            ));
        }
        load.original = Some(evidence);
        Ok(())
    }

    pub(super) fn record_root_compilation(
        &mut self,
        file: &str,
        bytes: &[u8],
    ) -> Result<(), MlError> {
        let Some(load) = self.root_load.as_mut().filter(|load| load.path == file) else {
            return Ok(());
        };
        let Some(length) = load
            .compiled_len
            .checked_add(bytes.len())
            .filter(|length| *length <= super::host::files::MAX_FILE_BYTES)
        else {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "compile ROOT source",
                format!("{file}: compiled input exceeds approved file bound"),
            ));
        };
        load.compiled.update(bytes);
        load.compiled_len = length;
        Ok(())
    }

    /// Execute ROOT0 and the unchanged ROOT list strictly to (not including) native Context.
    /// Parse/compile failures retain the last completed file and exact unexecuted suffix.
    pub fn evaluate_root_prefix(&mut self) -> Result<RootPrefixProgress, RootPrefixFailure> {
        let mut loaded_files = Vec::new();
        let (root0_sha256, root0) = self.read_root_directives(ROOT0, &loaded_files)?;
        let remaining_root0 = root0
            .iter()
            .filter(|item| is_ml_file(&item.command))
            .map(|item| format!("{PURE_SOURCE}{}", item.argument))
            .collect::<Vec<_>>();
        for (index, directive) in root0.iter().filter(|item| is_ml_file(&item.command)).enumerate()
        {
            self.evaluate_root_directive(directive, &mut loaded_files, &remaining_root0[index..])?;
        }
        let (root_sha256, directives) = self.read_root_directives(ROOT, &loaded_files)?;
        let remaining = directives
            .iter()
            .filter(|item| is_ml_file(&item.command))
            .map(|item| format!("{PURE_SOURCE}{}", item.argument))
            .collect::<Vec<_>>();
        for (index, directive) in
            directives.iter().filter(|item| is_ml_file(&item.command)).enumerate()
        {
            if directive.argument == CONTEXT_SOURCE {
                return Ok(RootPrefixProgress {
                    loaded_files,
                    root0_sha256,
                    root_sha256,
                    next_ml_file: remaining[index].clone(),
                    remaining_files: remaining[index..].to_vec(),
                });
            }
            self.evaluate_root_directive(directive, &mut loaded_files, &remaining[index..])?;
        }
        Err(RootPrefixFailure {
            loaded_files,
            failed_source: ROOT.to_owned(),
            remaining_files: Vec::new(),
            error: Box::new(self.error(
                MlErrorKind::Syntax,
                "read ROOT",
                "native Context boundary absent",
            )),
        })
    }
    /// Execute the actual ROOT prefix and its fixed Context declaration under
    /// the same supervised build. The Context source is read through the host;
    /// only its PRIVATE_CONTEXT body is replaced by the approved native bridge.
    pub fn evaluate_root_with_context(
        &mut self,
        lifecycle: BuildLifecycle,
        lease: Rc<TaskLease>,
        pure: TrustedTheory,
    ) -> Result<RootContextProgress, RootPrefixFailure> {
        let is_same_build =
            self.bootstrap_host.as_ref().is_some_and(|host| host.shares_build(&lifecycle));
        if !is_same_build || !lifecycle.matches_stop_handle(&self.stop_handle()) {
            self.request_stop();
            return Err(RootPrefixFailure {
                loaded_files: Vec::new(),
                failed_source: ROOT0.to_owned(),
                remaining_files: Vec::new(),
                error: Box::new(self.error(
                    MlErrorKind::HostFailure,
                    "install native Context",
                    "bootstrap and Context use different builds",
                )),
            });
        }
        if let Err(cause) = lifecycle.check_task(&lease) {
            let mut failure = RootPrefixFailure {
                loaded_files: Vec::new(),
                failed_source: ROOT0.to_owned(),
                remaining_files: Vec::new(),
                error: Box::new(self.error(
                    MlErrorKind::Stopped,
                    "install native Context",
                    format!("invalid Context task lease: {cause}"),
                )),
            };
            self.revoke_context_build(&lifecycle, &mut failure);
            return Err(failure);
        }
        let mut result = self.evaluate_context_source(lifecycle.clone(), lease, pure);
        if let Err(failure) = &mut result {
            self.revoke_context_build(&lifecycle, failure);
        }
        result
    }

    fn revoke_context_build(
        &mut self,
        lifecycle: &BuildLifecycle,
        failure: &mut RootPrefixFailure,
    ) {
        self.request_stop();
        if let Err(cause) =
            lifecycle.cancel(format!("cannot load {}: {}", failure.failed_source, failure.error))
        {
            failure.error.cause =
                format!("{}; failed to cancel Context build: {cause}", failure.error.cause);
        }
    }

    fn evaluate_context_source(
        &mut self,
        lifecycle: BuildLifecycle,
        lease: Rc<TaskLease>,
        pure: TrustedTheory,
    ) -> Result<RootContextProgress, RootPrefixFailure> {
        let prefix = self.evaluate_root_prefix()?;
        let path = prefix.next_ml_file.clone();
        let fail = |error| RootPrefixFailure {
            loaded_files: prefix.loaded_files.clone(),
            failed_source: path.clone(),
            remaining_files: prefix.remaining_files.clone(),
            error: Box::new(error),
        };
        let bytes = self.read_bootstrap_source(&path).map_err(fail)?;
        let source_sha256 = format!("{:x}", Sha256::digest(&bytes));
        let text = std::str::from_utf8(&bytes).map_err(|cause| {
            fail(self.error(
                MlErrorKind::Syntax,
                "decode Context source",
                format!("{path}: {cause}"),
            ))
        })?;
        let store = ObjectStore::new(self, lifecycle.clone()).map_err(|cause| {
            fail(self.error(
                MlErrorKind::HostFailure,
                "prepare native Context",
                format!("{path}: {cause}"),
            ))
        })?;
        ContextHost::install_official(self, store, lifecycle, lease, pure, &path, text).map_err(
            |cause| {
                fail(self.error(
                    MlErrorKind::HostFailure,
                    "install native Context",
                    format!("{path}: {cause}"),
                ))
            },
        )?;
        Ok(RootContextProgress {
            remaining_files: prefix.remaining_files[1..].to_vec(),
            context_source_sha256: source_sha256,
            replacement_structure_sha256: format!(
                "{:x}",
                Sha256::digest(replacement_structure().as_bytes())
            ),
            prefix,
        })
    }

    fn read_root_directives(
        &mut self,
        path: &'static str,
        loaded_files: &[LoadedMlSource],
    ) -> Result<(String, Vec<RootDirective>), RootPrefixFailure> {
        let bytes = self.read_bootstrap_source(path).map_err(|error| RootPrefixFailure {
            loaded_files: loaded_files.to_vec(),
            failed_source: path.to_owned(),
            remaining_files: Vec::new(),
            error: Box::new(error),
        })?;
        let sha256 = format!("{:x}", Sha256::digest(&bytes));
        let text = std::str::from_utf8(&bytes).map_err(|cause| RootPrefixFailure {
            loaded_files: loaded_files.to_vec(),
            failed_source: path.to_owned(),
            remaining_files: Vec::new(),
            error: Box::new(self.error(
                MlErrorKind::Syntax,
                "decode ROOT",
                format!("{path}: {cause}"),
            )),
        })?;
        parse_root_directives(path, text).map(|directives| (sha256, directives)).map_err(|error| {
            RootPrefixFailure {
                loaded_files: loaded_files.to_vec(),
                failed_source: path.to_owned(),
                remaining_files: Vec::new(),
                error: Box::new(error),
            }
        })
    }

    fn evaluate_root_directive(
        &mut self,
        directive: &RootDirective,
        loaded_files: &mut Vec<LoadedMlSource>,
        remaining: &[String],
    ) -> Result<(), RootPrefixFailure> {
        let path = format!("{PURE_SOURCE}{}", directive.argument);
        self.root_load = Some(RootLoadEvidence::new(path.clone()));
        let previous_loads = self.loaded_sources.len();
        let result = self
            .lookup_value(&directive.command)
            .and_then(|value| {
                value.cloned().ok_or_else(|| {
                    self.error(
                        MlErrorKind::Unbound,
                        "load ROOT source",
                        format!("{}: ML loader {} missing", directive.source, directive.command),
                    )
                })
            })
            .and_then(|loader| self.apply_root_loader(&loader, &path));
        let evidence = self.root_load.take();
        match result {
            Ok(value) if value.is_unit() => {
                let source = self
                    .loaded_sources
                    .get(previous_loads..)
                    .and_then(|loads| loads.last())
                    .filter(|source| source.path == path)
                    .cloned()
                    .or_else(|| {
                        let source = evidence.and_then(RootLoadEvidence::verified_source)?;
                        self.loaded_sources.push(source.clone());
                        Some(source)
                    });
                let Some(source) = source else {
                    self.request_stop();
                    return Err(RootPrefixFailure {
                        loaded_files: loaded_files.clone(),
                        failed_source: path,
                        remaining_files: remaining.to_vec(),
                        error: Box::new(self.error(
                            MlErrorKind::HostFailure,
                            "load ROOT source",
                            "ML_file returned without compiling requested source",
                        )),
                    });
                };
                loaded_files.push(source);
                Ok(())
            },
            Ok(_) => {
                self.request_stop();
                Err(RootPrefixFailure {
                    loaded_files: loaded_files.clone(),
                    failed_source: path,
                    remaining_files: remaining.to_vec(),
                    error: Box::new(self.error(
                        MlErrorKind::HostFailure,
                        "load ROOT source",
                        "ML_file returned without compiling requested source",
                    )),
                })
            },
            Err(mut error) => {
                if error.span.source_name.is_empty() {
                    error.span =
                        Box::new(Span::new(directive.source, directive.line, directive.line));
                }
                Err(RootPrefixFailure {
                    loaded_files: loaded_files.clone(),
                    failed_source: path,
                    remaining_files: remaining.to_vec(),
                    error: Box::new(error),
                })
            },
        }
    }

    fn apply_root_loader(&mut self, loader: &Value, path: &str) -> Result<Value, MlError> {
        if !matches!(
            &*loader.0,
            ValueData::Native(_)
                | ValueData::NativePartial { .. }
                | ValueData::Closure { .. }
                | ValueData::CurriedClosure { .. }
        ) {
            return Err(self.error(
                MlErrorKind::Type,
                "load ROOT source",
                "ML_file is not a compiler-certified function",
            ));
        }
        let argument = Value::text(path);
        self.validate_untyped_closure_argument(loader, &argument)?;
        self.apply_with_type(loader, &argument, Type::Constructor("string".to_owned(), vec![]))
    }

    fn read_bootstrap_source(&mut self, path: &str) -> Result<Vec<u8>, MlError> {
        self.check_stop()?;
        let host = self.bootstrap_host.as_ref().cloned().ok_or_else(|| {
            self.error(
                MlErrorKind::HostPermission,
                "read ML source",
                "no leased bootstrap host installed",
            )
        })?;
        host.read_source_bytes(Path::new(path))
            .map_err(|error| self.host_io_failure("read ML source", path, error))
    }

    fn raise_io_exception(&mut self, operation: &str, path: &str, cause: String) -> MlError {
        let fail = self.raise_named_exception(
            "Fail",
            Some(Value::text(cause.clone())),
            operation,
            cause.clone(),
        );
        let Some(packet) = fail.exception else { return fail };
        let argument = Value(Rc::new(ValueData::Record(BTreeMap::from([
            ("name".to_owned(), Value::text(path)),
            ("function".to_owned(), Value::text(operation)),
            ("cause".to_owned(), packet),
        ]))));
        self.raise_named_exception("IO.Io", Some(argument), operation, cause)
    }

    pub(super) fn host_io_failure(
        &mut self,
        operation: &str,
        path: &str,
        error: HostIoError,
    ) -> MlError {
        let cause = format!("{operation} {path}: {error}");
        if error.is_ordinary_ml_io() {
            return self.raise_io_exception(operation, path, cause);
        }
        self.request_stop();
        let kind = match error {
            HostIoError::Permission { .. }
            | HostIoError::InvalidPath(_)
            | HostIoError::PathLimit { .. } => MlErrorKind::HostPermission,
            HostIoError::Lifecycle { .. } | HostIoError::LeaseCompleted => MlErrorKind::Stopped,
            _ => MlErrorKind::HostFailure,
        };
        self.error(kind, operation, cause)
    }
}

fn is_ml_file(command: &str) -> bool {
    matches!(command, "ML_file" | "ML_file_debug" | "ML_file_no_debug")
}

fn parse_root_directives(path: &'static str, source: &str) -> Result<Vec<RootDirective>, MlError> {
    let uncommented = strip_root_comments(path, source)?;
    let mut directives = Vec::new();
    let mut beginning = 0;
    let mut in_string = false;
    let mut escaped = false;
    for (index, &byte) in uncommented.iter().enumerate() {
        if byte == b'"' && !escaped {
            in_string = !in_string;
        }
        if byte == b';' && !in_string {
            let line = source[..beginning].bytes().filter(|byte| *byte == b'\n').count() + 1;
            let statement = source_from_uncommented(&uncommented[beginning..index]);
            if !statement.trim().is_empty() {
                directives.push(parse_root_directive(path, line, &statement)?);
            }
            beginning = index + 1;
        }
        escaped = in_string && byte == b'\\' && !escaped;
        if byte != b'\\' {
            escaped = false;
        }
    }
    if !source_from_uncommented(&uncommented[beginning..]).trim().is_empty() {
        return Err(root_syntax_error(path, source.len(), "unterminated ROOT directive"));
    }
    Ok(directives)
}

fn strip_root_comments(path: &str, source: &str) -> Result<Vec<u8>, MlError> {
    let bytes = source.as_bytes();
    let mut result = bytes.to_vec();
    let mut depth = 0_usize;
    let mut index = 0;
    let mut in_string = false;
    while index < bytes.len() {
        if depth == 0 && bytes[index] == b'"' && (index == 0 || bytes[index - 1] != b'\\') {
            in_string = !in_string;
        }
        let opens = !in_string && bytes[index..].starts_with(b"(*");
        let closes = !in_string && bytes[index..].starts_with(b"*)");
        if closes && depth == 0 {
            return Err(root_syntax_error(path, index, "unmatched ROOT comment terminator"));
        }
        if opens {
            depth += 1;
        }
        if closes && depth > 0 {
            depth -= 1;
        }
        if depth > 0 || opens || closes {
            let width = if opens || closes { 2 } else { 1 };
            for byte in result.iter_mut().skip(index).take(width) {
                if *byte != b'\n' {
                    *byte = b' ';
                }
            }
            index += width;
        } else {
            index += 1;
        }
    }
    if depth != 0 {
        return Err(root_syntax_error(path, source.len(), "unclosed ROOT comment"));
    }
    Ok(result)
}

fn source_from_uncommented(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn parse_root_directive(
    path: &'static str,
    line: usize,
    statement: &str,
) -> Result<RootDirective, MlError> {
    let statement = statement.trim();
    let (command, argument) = statement
        .split_once(char::is_whitespace)
        .ok_or_else(|| root_syntax_error(path, line, "missing ROOT directive argument"))?;
    let is_presentation = matches!(
        command,
        "chapter" | "section" | "subsection" | "subsubsection" | "paragraph" | "subparagraph"
    );
    if !is_ml_file(command) && !is_presentation {
        return Err(root_syntax_error(path, line, &format!("unknown ROOT directive {command}")));
    }
    let argument = argument.trim();
    let Some(argument) = argument.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
        return Err(root_syntax_error(path, line, "expected quoted ROOT directive argument"));
    };
    if argument.contains('"') || argument.contains('\\') {
        return Err(root_syntax_error(path, line, "unsupported escaped ROOT argument"));
    }
    Ok(RootDirective {
        source: path,
        line,
        command: command.to_owned(),
        argument: argument.to_owned(),
    })
}

fn root_syntax_error(path: &str, position: usize, cause: &str) -> MlError {
    MlError {
        kind: MlErrorKind::Syntax,
        span: Box::new(Span::new(path, position, position)),
        operation: "parse ROOT directive".into(),
        cause: cause.to_owned(),
        exception: None,
        trace: Vec::new(),
    }
}

fn use_source(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(path) = args.first().and_then(Value::as_text) else {
        return Err(vm.error(MlErrorKind::Type, "use", "expected source path string"));
    };
    let path = if path.starts_with(PURE_SOURCE) {
        path.to_owned()
    } else {
        format!("{PURE_SOURCE}{path}")
    };
    vm.evaluate_source_file(&path)?;
    Ok(Value::unit())
}

fn get_environment(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let Some(key) = args.first().and_then(Value::as_text) else {
        return Err(vm.error(
            MlErrorKind::Type,
            "OS.Process.getEnv",
            "expected environment key string",
        ));
    };
    let Some(host) = vm.bootstrap_host.as_ref().cloned() else {
        return Err(vm.error(
            MlErrorKind::HostPermission,
            "OS.Process.getEnv",
            "no leased bootstrap host installed",
        ));
    };
    let value = host
        .read_environment(key, ML_ENVIRONMENT_PURPOSE)
        .map_err(|error| vm.host_io_failure("OS.Process.getEnv", key, error))?;
    vm.make_option(value.map(Value::text))
}
