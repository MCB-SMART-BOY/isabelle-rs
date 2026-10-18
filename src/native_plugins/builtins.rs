//! Explicit first-party functions used by Pure/ROOT.ML and anchored source/resource loading.
//! No unimplemented function is advertised as available.
use std::path::Path;
use std::time::{Duration, UNIX_EPOCH};

use super::{
    HOST_API_VERSION, NativePlugin, NativeService, OperationSpec, PluginEffects, PluginManifest,
    PluginVersion, RegistryError, ResponseSink, ServiceContext, ServiceError, SessionTool,
    SourcePosition, WireType,
};

const MAX_PLUGIN_BYTES: usize = 1024 * 1024;
const YXML_START: &[u8] = b"\x05\x06:\x05";
const YXML_END: &[u8] = b"\x05\x06\x05";
const MAX_SLEEP_SECONDS: f64 = 3600.0;
const BASE64_ALPHABET: &[u8; 64] =
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// First-party ROOT and native-host services; every advertised operation executes real work.
/// A caller must supply sufficiently large independent `RegistryBudget` and host permissions.
pub fn native_core_plugin() -> NativePlugin {
    let names: [(&str, WireType, usize, usize, super::ServiceFn, u32); 11] = [
        ("Base64.encode", WireType::Bytes, 1, 1, encode_base64, line!()),
        ("Base64.decode", WireType::Bytes, 1, 1, decode_base64, line!()),
        ("XZ.compress", WireType::Bytes, 1, 1, super::codecs::compress_xz, line!()),
        ("XZ.uncompress", WireType::Bytes, 1, 1, super::codecs::uncompress_xz, line!()),
        ("Zstd.compress", WireType::Bytes, 1, 1, super::codecs::compress_zstd, line!()),
        ("Zstd.uncompress", WireType::Bytes, 1, 1, super::codecs::uncompress_zstd, line!()),
        ("sleep", WireType::String, 1, 1, sleep, line!()),
        ("Clock.now", WireType::String, 1, 1, clock, line!()),
        ("File.read_source", WireType::Bytes, 1, 1, read_source, line!()),
        ("File.read_resource", WireType::Bytes, 2, 2, read_resource, line!()),
        ("isabelle_tools", WireType::String, 1, 1, list_tools, line!()),
    ];
    let services: Vec<_> = names
        .into_iter()
        .map(|(name, wire, min, max, call, line)| NativeService {
            spec: OperationSpec {
                name: name.to_owned(),
                wire,
                single: max == 1,
                min_arguments: min,
                max_arguments: max,
                max_argument_bytes: MAX_PLUGIN_BYTES,
                max_request_bytes: MAX_PLUGIN_BYTES,
                max_response_items: 1,
                max_response_bytes: MAX_PLUGIN_BYTES,
                position: SourcePosition { file: file!().to_owned(), line },
            },
            call,
        })
        .collect();
    let descriptions = services.iter().map(|service| service.spec.clone()).collect();
    NativePlugin {
        manifest: PluginManifest {
            identity: "isabelle.native.core".into(),
            version: PluginVersion { major: 1, minor: 0, patch: 0 },
            api_version: HOST_API_VERSION,
            dependencies: Vec::new(),
            effects: PluginEffects {
                read_source: true,
                read_resources: ["isabelle".into()].into(),
                read_clock: true,
                sleep: true,
            },
            services: descriptions,
            tools: Vec::new(),
        },
        services,
        tools: Vec::new(),
    }
}

fn list_tools(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    if !args[0].is_empty() {
        return Err(ServiceError::Error("isabelle_tools expects an empty string".into()));
    }
    sink.push(context.tool_catalog_yxml())
}

/// XML.Encode.list(pair(string,properties)), YXML.string_of_body, with no PATH lookup.
pub(super) fn encode_tools_yxml(
    tools: &[SessionTool],
    limit: usize,
) -> Result<Vec<u8>, RegistryError> {
    let mut output = Vec::new();
    for tool in tools {
        append_yxml(&mut output, YXML_START, limit)?;
        append_yxml(&mut output, YXML_START, limit)?;
        append_yxml(&mut output, tool.name.as_bytes(), limit)?;
        append_yxml(&mut output, YXML_END, limit)?;
        append_yxml(&mut output, YXML_START, limit)?;
        append_yxml(&mut output, b"\x05\x06:", limit)?;
        let line = tool.position.line.to_string();
        for property in [
            b"\x06line=".as_slice(),
            line.as_bytes(),
            b"\x06offset=1",
            b"\x06file=",
            tool.position.file.as_bytes(),
            b"\x05",
        ] {
            append_yxml(&mut output, property, limit)?;
        }
        append_yxml(&mut output, YXML_END, limit)?;
        append_yxml(&mut output, YXML_END, limit)?;
        append_yxml(&mut output, YXML_END, limit)?;
    }
    Ok(output)
}

fn append_yxml(output: &mut Vec<u8>, bytes: &[u8], limit: usize) -> Result<(), RegistryError> {
    if bytes.len() > limit.saturating_sub(output.len()) {
        return Err(RegistryError::Invalid(
            "isabelle_tools catalogue exceeds response budget".into(),
        ));
    }
    output.extend_from_slice(bytes);
    Ok(())
}

fn encode_base64(
    _: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let input = args[0];
    let groups = input.len().div_ceil(3);
    let output_len =
        groups.checked_mul(4).ok_or_else(|| ServiceError::Fail("encoded size overflow".into()))?;
    if output_len > sink.remaining {
        return Err(ServiceError::Fail("response byte budget exceeded".into()));
    }
    let mut encoded = Vec::with_capacity(output_len);
    for chunk in input.chunks(3) {
        encoded.push(BASE64_ALPHABET[usize::from(chunk[0] >> 2)]);
        encoded.push(
            BASE64_ALPHABET
                [usize::from(((chunk[0] & 3) << 4) | (chunk.get(1).copied().unwrap_or(0) >> 4))],
        );
        encoded.push(chunk.get(1).map_or(b'=', |second| {
            BASE64_ALPHABET
                [usize::from(((second & 15) << 2) | (chunk.get(2).copied().unwrap_or(0) >> 6))]
        }));
        encoded.push(chunk.get(2).map_or(b'=', |third| BASE64_ALPHABET[usize::from(third & 63)]));
    }
    sink.push_owned(encoded)
}

fn decode_base64(
    _: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let input = args[0];
    let capacity = input.len().div_ceil(4).saturating_mul(3).min(sink.remaining);
    let mut decoded = Vec::with_capacity(capacity);
    for chunk in input.chunks(4) {
        let mut bits = 0u32;
        let mut symbols = 0usize;
        for &byte in chunk {
            if byte == b'=' {
                break;
            }
            let value = base64_digit(byte)
                .ok_or_else(|| ServiceError::Fail("invalid Base64 character".into()))?;
            bits = (bits << 6) | u32::from(value);
            symbols += 1;
        }
        if symbols < 2
            || (symbols < chunk.len() && (chunk.len() != 4 || (symbols == 2 && chunk[3] != b'=')))
        {
            return Err(ServiceError::Fail("invalid Base64 padding".into()));
        }
        let output_len = symbols - 1;
        if output_len > sink.remaining.saturating_sub(decoded.len()) {
            return Err(ServiceError::Fail("response byte budget exceeded".into()));
        }
        let shifted = bits << (6 * (4 - symbols));
        decoded.push((shifted >> 16) as u8);
        if symbols >= 3 {
            decoded.push((shifted >> 8) as u8);
        }
        if symbols == 4 {
            decoded.push(shifted as u8);
        }
        if symbols < chunk.len() {
            break;
        }
    }
    sink.push_owned(decoded)
}

fn base64_digit(byte: u8) -> Option<u8> {
    match byte {
        b'A'..=b'Z' => Some(byte - b'A'),
        b'a'..=b'z' => Some(byte - b'a' + 26),
        b'0'..=b'9' => Some(byte - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

fn sleep(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let text =
        std::str::from_utf8(args[0]).map_err(|error| ServiceError::Fail(error.to_string()))?;
    let seconds: f64 = text
        .parse()
        .map_err(|error: std::num::ParseFloatError| ServiceError::Error(error.to_string()))?;
    if !seconds.is_finite() || !(0.0..=MAX_SLEEP_SECONDS).contains(&seconds) {
        return Err(ServiceError::Error("sleep duration exceeds approved range".into()));
    }
    let before = std::time::Instant::now();
    context.sleep(Duration::from_secs_f64(seconds))?;
    let elapsed = before.elapsed().as_secs_f64().to_string();
    sink.push(elapsed.as_bytes())
}

fn clock(
    context: &ServiceContext<'_>,
    _: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let since_epoch = context
        .read_clock()?
        .duration_since(UNIX_EPOCH)
        .map_err(|error| ServiceError::Fail(format!("read clock before epoch: {error}")))?;
    let millis = since_epoch.as_millis().to_string();
    sink.push(millis.as_bytes())
}

fn read_source(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let path =
        std::str::from_utf8(args[0]).map_err(|error| ServiceError::Fail(error.to_string()))?;
    let bytes = context.read_source(Path::new(path), sink.remaining)?;
    sink.push_owned(bytes)
}

fn read_resource(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let root =
        std::str::from_utf8(args[0]).map_err(|error| ServiceError::Fail(error.to_string()))?;
    let path =
        std::str::from_utf8(args[1]).map_err(|error| ServiceError::Fail(error.to_string()))?;
    let limit = sink.remaining;
    let bytes = context.run_future("read resource", move |child| {
        child.read_resource(root, Path::new(path), limit)
    })?;
    sink.push_owned(bytes)
}
