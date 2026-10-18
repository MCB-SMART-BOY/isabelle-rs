//! JSON-RPC transport layer over stdio.
//!
//! Implements the LSP wire protocol:
//! - `Content-Length: N\r\n\r\n<json>`
//! - Reads from stdin, writes to stdout
//!
//! Reference: <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#headerPart>

use std::{
    io::{self, BufRead, BufReader, Read, Write},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread::JoinHandle,
    time::Duration,
};

use thiserror::Error;

use super::lsp_types::{JsonRpcNotification, JsonRpcRequest, JsonRpcResponse, Location, RequestId};
use crate::fleche::engine::CheckResult;

/// Maximum number of responses waiting to be written.
pub const OUTGOING_QUEUE_CAPACITY: usize = 16;
/// Maximum number of client or internal messages waiting for dispatch.
pub const INCOMING_QUEUE_CAPACITY: usize = 4;
const MAX_HEADER_BYTES: usize = 8 * 1024;
const MAX_CONTENT_LENGTH: usize = 4 * 1024 * 1024;
const WRITER_EXIT_GRACE: Duration = Duration::from_secs(2);

/// A transport failure visible to the server event loop.
#[derive(Clone, Debug, Error)]
pub enum TransportError {
    /// The bounded outgoing queue has no remaining capacity.
    #[error("outgoing transport queue is full")]
    QueueFull,
    /// The corresponding transport endpoint is no longer connected.
    #[error("transport is disconnected")]
    Disconnected,
    /// Reading or writing the protocol stream failed.
    #[error("transport I/O error: {0}")]
    Io(Arc<io::Error>),
    /// The writer did not finish draining within the bounded shutdown grace period.
    #[error("transport writer shutdown timed out")]
    WriterTimeout,
}

/// A message received from the client or a transport worker.
#[derive(Debug)]
pub enum IncomingMessage {
    Request(JsonRpcRequest),
    Notification(JsonRpcNotification),
    Response(JsonRpcResponse),
    CheckComplete(CheckResult),
    DefinitionComplete {
        id: RequestId,
        cancellation: Arc<AtomicBool>,
        result: Result<Option<Location>, String>,
    },
    WorkerFailed(String),
    TransportError(TransportError),
}

/// A message to send to the client.
#[derive(Debug)]
pub enum OutgoingMessage {
    Response(JsonRpcResponse),
    Notification(JsonRpcNotification),
}

/// The transport layer handles raw stdio communication.
pub struct Transport {
    outgoing_tx: mpsc::SyncSender<OutgoingMessage>,
    incoming_tx: mpsc::SyncSender<IncomingMessage>,
    incoming_rx: mpsc::Receiver<IncomingMessage>,
    running: Arc<AtomicBool>,
    writer: JoinHandle<()>,
    writer_done_rx: mpsc::Receiver<()>,
    writer_exit_grace: Duration,
    writer_error: Arc<Mutex<Option<TransportError>>>,
}

impl Transport {
    /// Create a new transport and spawn the I/O threads.
    pub fn new() -> Self {
        Self::with_io(io::stdin(), io::stdout())
    }

    pub(super) fn with_io<R, W>(reader: R, writer: W) -> Self
    where
        R: Read + Send + 'static,
        W: Write + Send + 'static,
    {
        Self::with_io_and_grace(reader, writer, WRITER_EXIT_GRACE)
    }

    fn with_io_and_grace<R, W>(reader: R, writer: W, writer_exit_grace: Duration) -> Self
    where
        R: Read + Send + 'static,
        W: Write + Send + 'static,
    {
        let (outgoing_tx, outgoing_rx) = mpsc::sync_channel(OUTGOING_QUEUE_CAPACITY);
        let (incoming_tx, incoming_rx) = mpsc::sync_channel(INCOMING_QUEUE_CAPACITY);
        let running = Arc::new(AtomicBool::new(true));
        let writer_error = Arc::new(Mutex::new(None));
        let (writer, writer_done_rx) =
            Self::spawn_writer(writer, outgoing_rx, incoming_tx.clone(), Arc::clone(&writer_error));
        Self::spawn_reader(reader, incoming_tx.clone(), Arc::clone(&running));

        Self {
            outgoing_tx,
            incoming_tx,
            incoming_rx,
            running,
            writer,
            writer_done_rx,
            writer_exit_grace,
            writer_error,
        }
    }

    fn spawn_writer<W>(
        mut writer: W,
        outgoing_rx: mpsc::Receiver<OutgoingMessage>,
        incoming_tx: mpsc::SyncSender<IncomingMessage>,
        writer_error: Arc<Mutex<Option<TransportError>>>,
    ) -> (JoinHandle<()>, mpsc::Receiver<()>)
    where
        W: Write + Send + 'static,
    {
        let (done_tx, done_rx) = mpsc::channel();
        let writer = std::thread::spawn(move || {
            for message in outgoing_rx {
                if let Err(error) = Self::write_message(&mut writer, &message) {
                    let error = TransportError::Io(Arc::new(error));
                    Self::record_writer_error(&writer_error, error.clone());
                    Self::report_transport_error(&incoming_tx, error);
                    break;
                }
            }
            if done_tx.send(()).is_err() {
                tracing::debug!("transport writer completion receiver disconnected");
            }
        });
        (writer, done_rx)
    }

    fn spawn_reader<R>(
        reader: R,
        incoming_tx: mpsc::SyncSender<IncomingMessage>,
        running: Arc<AtomicBool>,
    ) where
        R: Read + Send + 'static,
    {
        std::thread::spawn(move || {
            let mut reader = BufReader::new(reader);
            while running.load(Ordering::Relaxed) {
                match Self::read_message(&mut reader) {
                    Ok(Some(message)) => {
                        if incoming_tx.send(message).is_err() {
                            break;
                        }
                    },
                    Ok(None) => {
                        Self::report_transport_error(&incoming_tx, TransportError::Disconnected);
                        break;
                    },
                    Err(error) => {
                        Self::report_transport_error(
                            &incoming_tx,
                            TransportError::Io(Arc::new(error)),
                        );
                        break;
                    },
                }
            }
            running.store(false, Ordering::Relaxed);
        });
    }

    fn report_transport_error(
        incoming_tx: &mpsc::SyncSender<IncomingMessage>,
        error: TransportError,
    ) {
        if incoming_tx.send(IncomingMessage::TransportError(error)).is_err() {
            tracing::debug!("transport event receiver disconnected");
        }
    }

    fn record_writer_error(writer_error: &Mutex<Option<TransportError>>, error: TransportError) {
        match writer_error.lock() {
            Ok(mut guard) => *guard = Some(error),
            Err(poisoned) => *poisoned.into_inner() = Some(error),
        }
    }

    fn current_writer_error(&self) -> Option<TransportError> {
        match self.writer_error.lock() {
            Ok(guard) => guard.clone(),
            Err(poisoned) => poisoned.into_inner().clone(),
        }
    }

    /// Return a sender that can wake the event loop with internal completions.
    pub fn incoming_sender(&self) -> mpsc::SyncSender<IncomingMessage> {
        self.incoming_tx.clone()
    }

    /// Enqueue an outgoing message without blocking.
    pub fn send(&self, message: OutgoingMessage) -> Result<(), TransportError> {
        if let Some(error) = self.current_writer_error() {
            return Err(error);
        }
        self.outgoing_tx.try_send(message).map_err(|error| match error {
            mpsc::TrySendError::Full(_) => TransportError::QueueFull,
            mpsc::TrySendError::Disconnected(_) => {
                self.current_writer_error().unwrap_or(TransportError::Disconnected)
            },
        })
    }

    /// Receive the next incoming message (blocking).
    pub fn recv(&self) -> Option<IncomingMessage> {
        self.incoming_rx.recv().ok()
    }

    /// Try to receive a message (non-blocking).
    pub fn try_recv(&self) -> Option<IncomingMessage> {
        self.incoming_rx.try_recv().ok()
    }

    /// Stop accepting input. A reader blocked on stdin is intentionally detached.
    pub fn shutdown(&self) {
        self.running.store(false, Ordering::Relaxed);
    }

    /// Drain queued output and wait for the writer, without waiting for stdin.
    pub fn finish(self) -> Result<(), TransportError> {
        self.running.store(false, Ordering::Relaxed);
        let Self {
            outgoing_tx,
            incoming_rx,
            writer,
            writer_done_rx,
            writer_exit_grace,
            writer_error,
            ..
        } = self;
        drop(incoming_rx);
        drop(outgoing_tx);
        match writer_done_rx.recv_timeout(writer_exit_grace) {
            Ok(()) | Err(mpsc::RecvTimeoutError::Disconnected) => {
                Self::join_writer(writer, &writer_error)
            },
            Err(mpsc::RecvTimeoutError::Timeout) => Err(TransportError::WriterTimeout),
        }
    }

    fn join_writer(
        writer: JoinHandle<()>,
        writer_error: &Mutex<Option<TransportError>>,
    ) -> Result<(), TransportError> {
        if writer.join().is_err() {
            return Err(TransportError::Io(Arc::new(io::Error::other(
                "transport writer thread panicked",
            ))));
        }
        match writer_error.lock() {
            Ok(guard) => guard.clone().map_or(Ok(()), Err),
            Err(poisoned) => poisoned.into_inner().clone().map_or(Ok(()), Err),
        }
    }

    fn write_message(writer: &mut impl Write, message: &OutgoingMessage) -> io::Result<()> {
        let body = match message {
            OutgoingMessage::Response(response) => serde_json::to_vec(response),
            OutgoingMessage::Notification(notification) => serde_json::to_vec(notification),
        }
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        write!(writer, "Content-Length: {}\r\n\r\n", body.len())?;
        writer.write_all(&body)?;
        writer.flush()
    }

    fn read_header_line(
        reader: &mut impl BufRead,
        header_bytes: &mut usize,
    ) -> io::Result<Option<Vec<u8>>> {
        let mut line = Vec::new();
        loop {
            let available = reader.fill_buf()?;
            if available.is_empty() {
                return if line.is_empty() { Ok(None) } else { Ok(Some(line)) };
            }
            let take = available
                .iter()
                .position(|byte| *byte == b'\n')
                .map_or(available.len(), |position| position + 1);
            if *header_bytes + take > MAX_HEADER_BYTES {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "LSP header exceeds maximum size",
                ));
            }
            line.extend_from_slice(&available[..take]);
            reader.consume(take);
            *header_bytes += take;
            if line.ends_with(b"\n") {
                return Ok(Some(line));
            }
        }
    }

    fn parse_content_length(line: &[u8]) -> io::Result<Option<usize>> {
        let line = std::str::from_utf8(line)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        let Some((name, value)) = line.split_once(':') else {
            return Ok(None);
        };
        if !name.trim().eq_ignore_ascii_case("Content-Length") {
            return Ok(None);
        }
        let length = value.trim().parse::<usize>().map_err(|error| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("invalid Content-Length header: {error}"),
            )
        })?;
        if length > MAX_CONTENT_LENGTH {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LSP message body exceeds maximum size",
            ));
        }
        Ok(Some(length))
    }

    /// Read a single JSON-RPC message from the reader.
    fn read_message(reader: &mut BufReader<impl Read>) -> io::Result<Option<IncomingMessage>> {
        let mut content_length = None;
        let mut header_bytes = 0;
        loop {
            let Some(mut line) = Self::read_header_line(reader, &mut header_bytes)? else {
                return if header_bytes == 0 {
                    Ok(None)
                } else {
                    Err(io::Error::new(io::ErrorKind::UnexpectedEof, "incomplete LSP header"))
                };
            };
            if line.ends_with(b"\n") {
                line.pop();
            }
            if line.ends_with(b"\r") {
                line.pop();
            }
            if line.is_empty() {
                break;
            }
            if let Some(length) = Self::parse_content_length(&line)?
                && content_length.replace(length).is_some()
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "duplicate Content-Length header",
                ));
            }
        }

        let length = content_length.ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length header")
        })?;
        let mut body = vec![0_u8; length];
        reader.read_exact(&mut body)?;
        Self::parse_message(&body).map(Some)
    }

    fn parse_message(body: &[u8]) -> io::Result<IncomingMessage> {
        if let Ok(request) = serde_json::from_slice::<JsonRpcRequest>(body) {
            return Ok(IncomingMessage::Request(request));
        }
        if let Ok(response) = serde_json::from_slice::<JsonRpcResponse>(body) {
            return Ok(IncomingMessage::Response(response));
        }
        if let Ok(notification) = serde_json::from_slice::<JsonRpcNotification>(body) {
            return Ok(IncomingMessage::Notification(notification));
        }
        Err(io::Error::new(io::ErrorKind::InvalidData, "invalid JSON-RPC message"))
    }
}

impl Default for Transport {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::{
        io::{Cursor, ErrorKind},
        sync::{Arc, Mutex},
    };

    use serde_json::json;

    use super::*;

    #[derive(Clone, Default)]
    struct SharedWriter(Arc<Mutex<Vec<u8>>>);

    impl Write for SharedWriter {
        fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
            self.0
                .lock()
                .map_err(|_| io::Error::other("shared writer lock poisoned"))?
                .extend_from_slice(buffer);
            Ok(buffer.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    struct FailingWriter;

    impl Write for FailingWriter {
        fn write(&mut self, _buffer: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(ErrorKind::BrokenPipe, "test writer failure"))
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    struct BlockingWriter {
        started_tx: mpsc::Sender<()>,
        release_rx: mpsc::Receiver<()>,
        has_blocked: bool,
    }

    impl Write for BlockingWriter {
        fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
            if !self.has_blocked {
                self.has_blocked = true;
                self.started_tx
                    .send(())
                    .map_err(|_| io::Error::other("start receiver disconnected"))?;
                self.release_rx
                    .recv()
                    .map_err(|_| io::Error::other("release sender disconnected"))?;
            }
            Ok(buffer.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn notification() -> JsonRpcNotification {
        JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: "initialized".into(),
            params: json!({}),
        }
    }

    fn framed(body: &[u8]) -> Vec<u8> {
        let mut bytes = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
        bytes.extend_from_slice(body);
        bytes
    }

    fn response() -> JsonRpcResponse {
        JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id: super::super::lsp_types::RequestId::Number(1),
            result: Some(json!(null)),
            error: None,
        }
    }

    #[test]
    fn read_message_malformed_length_returns_invalid_data() {
        let bytes = b"Content-Length: invalid\r\n\r\n";
        let error = Transport::read_message(&mut BufReader::new(Cursor::new(bytes)))
            .expect_err("malformed length must fail");
        assert_eq!(error.kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn read_message_oversize_body_returns_invalid_data_without_reading_body() {
        let bytes = format!("Content-Length: {}\r\n\r\n", MAX_CONTENT_LENGTH + 1);
        let error = Transport::read_message(&mut BufReader::new(Cursor::new(bytes)))
            .expect_err("oversize body must fail");
        assert_eq!(error.kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn read_message_oversize_header_returns_invalid_data() {
        let bytes = vec![b'a'; MAX_HEADER_BYTES + 1];
        let error = Transport::read_message(&mut BufReader::new(Cursor::new(bytes)))
            .expect_err("oversize header must fail");
        assert_eq!(error.kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn read_message_header_at_limit_is_accepted() {
        let body = serde_json::to_vec(&notification()).expect("notification serializes");
        let length_header = format!("Content-Length: {}\r\n", body.len());
        let padding_length = MAX_HEADER_BYTES - length_header.len() - 6;
        let mut bytes =
            format!("X:{}\r\n{length_header}\r\n", "a".repeat(padding_length)).into_bytes();
        assert_eq!(bytes.len(), MAX_HEADER_BYTES);
        bytes.extend_from_slice(&body);

        let message = Transport::read_message(&mut BufReader::new(Cursor::new(bytes)))
            .expect("boundary header is valid")
            .expect("message exists");
        assert!(matches!(message, IncomingMessage::Notification(_)));
    }

    #[test]
    fn finish_drains_all_queued_messages() {
        let writer = SharedWriter::default();
        let output = Arc::clone(&writer.0);
        let transport = Transport::with_io(Cursor::new(Vec::<u8>::new()), writer);
        let message = notification();
        transport
            .send(OutgoingMessage::Notification(message.clone()))
            .expect("first message queues");
        transport
            .send(OutgoingMessage::Notification(message.clone()))
            .expect("second message queues");
        transport.finish().expect("writer drains");

        let body = serde_json::to_vec(&message).expect("notification serializes");
        let expected = [framed(&body), framed(&body)].concat();
        assert_eq!(*output.lock().expect("output lock"), expected);
    }

    #[test]
    fn finish_after_shutdown_drains_final_response() {
        let writer = SharedWriter::default();
        let output = Arc::clone(&writer.0);
        let transport = Transport::with_io(Cursor::new(Vec::<u8>::new()), writer);
        let message = response();
        transport.shutdown();
        transport
            .send(OutgoingMessage::Response(message.clone()))
            .expect("shutdown response queues");
        transport.finish().expect("writer drains shutdown response");

        let body = serde_json::to_vec(&message).expect("response serializes");
        assert_eq!(*output.lock().expect("output lock"), framed(&body));
    }

    #[test]
    fn finish_reports_writer_failure() {
        let transport = Transport::with_io(Cursor::new(Vec::<u8>::new()), FailingWriter);
        transport
            .send(OutgoingMessage::Notification(notification()))
            .expect("message initially queues");
        let error = transport.finish().expect_err("writer error must be reported");
        assert!(matches!(error, TransportError::Io(_)));
    }

    #[test]
    fn finish_blocked_writer_returns_timeout_and_detaches_writer() {
        const TEST_GRACE: Duration = Duration::from_millis(25);
        const WATCHDOG_GRACE: Duration = Duration::from_secs(1);

        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let writer = BlockingWriter { started_tx, release_rx, has_blocked: false };
        let transport =
            Transport::with_io_and_grace(Cursor::new(Vec::<u8>::new()), writer, TEST_GRACE);
        transport
            .send(OutgoingMessage::Notification(notification()))
            .expect("message initially queues");
        started_rx.recv_timeout(WATCHDOG_GRACE).expect("writer reaches blocking write");

        let (finish_returned_tx, finish_returned_rx) = mpsc::channel();
        let watchdog = std::thread::spawn(move || {
            match finish_returned_rx.recv_timeout(WATCHDOG_GRACE) {
                Ok(())
                | Err(mpsc::RecvTimeoutError::Timeout | mpsc::RecvTimeoutError::Disconnected) => {},
            }
            release_tx.send(()).expect("blocked writer still exists");
        });

        let error = transport.finish().expect_err("blocked writer must time out");
        finish_returned_tx.send(()).expect("watchdog remains connected");
        watchdog.join().expect("watchdog exits");
        assert!(matches!(error, TransportError::WriterTimeout));
    }
}
