//! JSON-RPC transport layer over stdio.
//!
//! Implements the LSP wire protocol:
//! - `Content-Length: N\r\n\r\n<json>`
//! - Reads from stdin, writes to stdout
//!
//! Reference: <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#headerPart>

use std::io::{self, BufRead, BufReader, Read, Write};
use std::sync::Arc;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    mpsc,
};

use super::lsp_types::{JsonRpcNotification, JsonRpcRequest, JsonRpcResponse, RequestId};

/// A message received from the client.
#[derive(Debug)]
pub enum IncomingMessage {
    Request(JsonRpcRequest),
    Notification(JsonRpcNotification),
    Response(JsonRpcResponse),
}

/// A message to send to the client.
#[derive(Debug)]
pub enum OutgoingMessage {
    Response(JsonRpcResponse),
    Notification(JsonRpcNotification),
}

/// The transport layer handles raw stdio communication.
///
/// It runs on its own thread, reading from stdin and writing to stdout.
pub struct Transport {
    /// Channel to send outgoing messages.
    outgoing_tx: mpsc::Sender<OutgoingMessage>,
    /// Channel to receive incoming messages.
    incoming_rx: mpsc::Receiver<IncomingMessage>,
    /// Is the transport running?
    running: Arc<AtomicBool>,
}

impl Transport {
    /// Create a new transport and spawn the I/O threads.
    pub fn new() -> Self {
        let (outgoing_tx, outgoing_rx) = mpsc::channel::<OutgoingMessage>();
        let (incoming_tx, incoming_rx) = mpsc::channel::<IncomingMessage>();
        let running = Arc::new(AtomicBool::new(true));

        let running_clone = running.clone();

        // Spawn the writer thread (blocking on outgoing messages → stdout)
        let write_running = running.clone();
        std::thread::spawn(move || {
            let stdout = io::stdout();
            let mut out = stdout.lock();
            while write_running.load(Ordering::Relaxed) {
                match outgoing_rx.recv() {
                    Ok(msg) => {
                        let json = match &msg {
                            OutgoingMessage::Response(r) => serde_json::to_string(r),
                            OutgoingMessage::Notification(n) => serde_json::to_string(n),
                        };
                        match json {
                            Ok(body) => {
                                let header = format!("Content-Length: {}\r\n\r\n", body.len());
                                let _ = out.write_all(header.as_bytes());
                                let _ = out.write_all(body.as_bytes());
                                let _ = out.flush();
                            }
                            Err(e) => {
                                eprintln!("[transport] JSON serialization error: {e}");
                            }
                        }
                    }
                    Err(_) => break,
                }
            }
        });

        // Spawn the reader thread (stdin → incoming messages)
        let read_running = running.clone();
        std::thread::spawn(move || {
            let stdin = io::stdin();
            let mut reader = BufReader::new(stdin.lock());
            while read_running.load(Ordering::Relaxed) {
                match Self::read_message(&mut reader) {
                    Ok(Some(msg)) => {
                        if incoming_tx.send(msg).is_err() {
                            break; // channel closed
                        }
                    }
                    Ok(None) => break, // EOF
                    Err(e) => {
                        eprintln!("[transport] Read error: {e}");
                        break;
                    }
                }
            }
            read_running.store(false, Ordering::Relaxed);
        });

        Transport {
            outgoing_tx,
            incoming_rx,
            running: running_clone,
        }
    }

    /// Send an outgoing message (non-blocking).
    pub fn send(&self, msg: OutgoingMessage) {
        let _ = self.outgoing_tx.send(msg);
    }

    /// Receive the next incoming message (blocking).
    pub fn recv(&self) -> Option<IncomingMessage> {
        self.incoming_rx.recv().ok()
    }

    /// Try to receive a message (non-blocking).
    pub fn try_recv(&self) -> Option<IncomingMessage> {
        self.incoming_rx.try_recv().ok()
    }

    /// Shut down the transport.
    pub fn shutdown(&self) {
        self.running.store(false, Ordering::Relaxed);
    }

    /// Read a single JSON-RPC message from the reader.
    fn read_message(reader: &mut BufReader<impl Read>) -> io::Result<Option<IncomingMessage>> {
        // Read headers: "Content-Length: N\r\n\r\n"
        let mut content_length: Option<usize> = None;
        loop {
            let mut line = String::new();
            let n = reader.read_line(&mut line)?;
            if n == 0 {
                return Ok(None); // EOF
            }
            let line = line.trim();
            if line.is_empty() {
                break; // end of headers
            }
            if let Some(value) = line.strip_prefix("Content-Length:") {
                content_length = value.trim().parse().ok();
            }
            // Ignore other headers (Content-Type, etc.)
        }

        let len = content_length.ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "Missing Content-Length header")
        })?;

        // Read the JSON body
        let mut body = vec![0u8; len];
        reader.read_exact(&mut body)?;

        let body_str = String::from_utf8_lossy(&body);

        // Try to parse as each message type
        let msg = if let Ok(req) = serde_json::from_str::<JsonRpcRequest>(&body_str) {
            if req.id == RequestId::String("".into()) || req.id == RequestId::Number(0) {
                // Actually try notification
                if let Ok(notif) = serde_json::from_str::<JsonRpcNotification>(&body_str) {
                    IncomingMessage::Notification(notif)
                } else {
                    IncomingMessage::Request(req)
                }
            } else {
                IncomingMessage::Request(req)
            }
        } else if let Ok(resp) = serde_json::from_str::<JsonRpcResponse>(&body_str) {
            IncomingMessage::Response(resp)
        } else if let Ok(notif) = serde_json::from_str::<JsonRpcNotification>(&body_str) {
            IncomingMessage::Notification(notif)
        } else {
            eprintln!("[transport] Failed to parse message: {}", body_str);
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Invalid JSON-RPC message: {}", body_str),
            ));
        };

        Ok(Some(msg))
    }
}

impl Default for Transport {
    fn default() -> Self {
        Self::new()
    }
}
