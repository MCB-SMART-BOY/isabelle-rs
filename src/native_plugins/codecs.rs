//! Bounded XZ and Zstd wire-compatible codecs for Pure/General/{xz,zstd}.ML.
//! The fixed source uses XZ preset 3 and Zstd compression level 3.
use std::io::{self, Read, Write};

use super::{ResponseSink, ServiceContext, ServiceError};

const CODEC_LEVEL: u32 = 3;
const STREAM_CHUNK_BYTES: usize = 8192;
const XZ_DECODER_MEMORY_KIB: u32 = 16 * 1024;
const ZSTD_WINDOW_LOG_MAX: u32 = 24;

struct BoundedOutput {
    bytes: Vec<u8>,
    limit: usize,
}
impl BoundedOutput {
    fn new(limit: usize) -> Self {
        Self { bytes: Vec::new(), limit }
    }
    fn finish(self) -> Vec<u8> {
        self.bytes
    }
}
impl Write for BoundedOutput {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > self.limit.saturating_sub(self.bytes.len()) {
            return Err(io::Error::other("compressed response exceeds approved byte budget"));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn handle_codec_error(
    context: &ServiceContext<'_>,
    operation: &str,
    error: io::Error,
) -> ServiceError {
    match context.check_active() {
        Ok(()) => ServiceError::Fail(format!("{operation}: {error}")),
        Err(stopped) => stopped,
    }
}

fn write_chunks<W: Write>(
    context: &ServiceContext<'_>,
    writer: &mut W,
    input: &[u8],
    operation: &str,
) -> Result<(), ServiceError> {
    for chunk in input.chunks(STREAM_CHUNK_BYTES) {
        context.check_active()?;
        writer.write_all(chunk).map_err(|error| handle_codec_error(context, operation, error))?;
    }
    context.check_active()
}

fn read_bounded<R: Read>(
    context: &ServiceContext<'_>,
    reader: &mut R,
    limit: usize,
    operation: &str,
) -> Result<Vec<u8>, ServiceError> {
    let mut output = Vec::new();
    let mut chunk = [0u8; STREAM_CHUNK_BYTES];
    loop {
        context.check_active()?;
        let count = reader
            .read(&mut chunk)
            .map_err(|error| handle_codec_error(context, operation, error))?;
        if count == 0 {
            break;
        }
        if count > limit.saturating_sub(output.len()) {
            return Err(ServiceError::Fail(format!(
                "{operation}: expanded response exceeds approved byte budget"
            )));
        }
        output.extend_from_slice(&chunk[..count]);
    }
    context.check_active()?;
    Ok(output)
}

pub(super) fn compress_xz(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    context.check_active()?;
    let mut output = BoundedOutput::new(sink.remaining);
    let mut writer =
        lzma_rust2::XzWriter::new(&mut output, lzma_rust2::XzOptions::with_preset(CODEC_LEVEL))
            .map_err(|error| handle_codec_error(context, "initialize XZ encoder", error))?;
    write_chunks(context, &mut writer, args[0], "compress XZ")?;
    writer.finish().map_err(|error| handle_codec_error(context, "finalize XZ stream", error))?;
    context.check_active()?;
    sink.push_owned(output.finish())
}

pub(super) fn uncompress_xz(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    context.check_active()?;
    if !args[0].len().is_multiple_of(4) {
        return Err(ServiceError::Fail("uncompress XZ: incomplete stream padding".into()));
    }
    let mut reader = lzma_rust2::XzReader::new_mem_limit(args[0], true, XZ_DECODER_MEMORY_KIB);
    sink.push_owned(read_bounded(context, &mut reader, sink.remaining, "uncompress XZ")?)
}

pub(super) fn compress_zstd(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    context.check_active()?;
    let mut output = BoundedOutput::new(sink.remaining);
    let mut writer = zstd::stream::write::Encoder::new(&mut output, CODEC_LEVEL as i32)
        .map_err(|error| handle_codec_error(context, "initialize Zstd encoder", error))?;
    write_chunks(context, &mut writer, args[0], "compress Zstd")?;
    writer.finish().map_err(|error| handle_codec_error(context, "finalize Zstd frame", error))?;
    context.check_active()?;
    sink.push_owned(output.finish())
}

pub(super) fn uncompress_zstd(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    context.check_active()?;
    let mut reader = zstd::stream::read::Decoder::with_buffer(args[0])
        .map_err(|error| handle_codec_error(context, "initialize Zstd decoder", error))?;
    reader
        .window_log_max(ZSTD_WINDOW_LOG_MAX)
        .map_err(|error| handle_codec_error(context, "bound Zstd decoder window", error))?;
    sink.push_owned(read_bounded(context, &mut reader, sink.remaining, "uncompress Zstd")?)
}
