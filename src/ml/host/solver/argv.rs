use std::ffi::OsStr;
use std::path::Path;

use super::{SolverError, SolverErrorKind};

const PROOF: &[&str] = &[
    "--proof-with-sharing",
    "--proof-define-skolems",
    "--proof-prune",
    "--proof-merge",
    "--disable-print-success",
    "--disable-banner",
];
const BEST: &[&str] =
    &["--index-sorts", "--index-fresh-sorts", "--triggers-new", "--triggers-sel-rm-specific"];
const DEL_INSTS: &[&str] = &[
    "--index-sorts",
    "--index-fresh-sorts",
    "--ccfv-breadth",
    "--inst-deletion",
    "--index-SAT-triggers",
    "--inst-deletion-loops",
    "--inst-deletion-track-vars",
    "--inst-deletion",
    "--index-SAT-triggers",
];
const MAX_MILLISECONDS: u64 = 300_000;
const MAX_WORDS: usize = 1 + PROOF.len() + DEL_INSTS.len() + 1;
const MAX_OPTION_BYTES: usize = b"--max-time=300000".len();

fn max_script_bytes(executable: &[u8]) -> Option<usize> {
    let option_bytes = PROOF.iter().chain(DEL_INSTS).map(|word| word.len()).sum::<usize>();
    executable
        .len()
        .checked_mul(7)?
        .checked_add(option_bytes)?
        .checked_add(MAX_OPTION_BYTES + MAX_WORDS - 1)
}

fn invalid(reason: &'static str) -> SolverError {
    SolverError::new(SolverErrorKind::Permission, "decode Bash.strings", reason)
}

// Isabelle's Bash.string translates each byte of an SML string, not Unicode code points.
fn encode_word(word: &[u8], into: &mut Vec<u8>) {
    if word.is_empty() {
        into.extend_from_slice(b"\"\"");
    }
    for &byte in word {
        match byte {
            b'\t' => into.extend_from_slice(b"$'\\t'"),
            b'\n' => into.extend_from_slice(b"$'\\n'"),
            12 => into.extend_from_slice(b"$'\\f'"),
            b'\r' => into.extend_from_slice(b"$'\\r'"),
            b'A'..=b'Z'
            | b'a'..=b'z'
            | b'0'..=b'9'
            | b'+'
            | b','
            | b'-'
            | b'.'
            | b'/'
            | b':'
            | b'_' => into.push(byte),
            0..=15 => into.extend_from_slice(format!("$'\\x0{byte:X}'").as_bytes()),
            16..=31 | 127..=255 => into.extend_from_slice(format!("$'\\x{byte:X}'").as_bytes()),
            _ => {
                into.push(b'\\');
                into.push(byte);
            },
        }
    }
}

fn encode_words(words: &[Vec<u8>]) -> Vec<u8> {
    let mut encoded = Vec::new();
    for (index, word) in words.iter().enumerate() {
        if index != 0 {
            encoded.push(b' ');
        }
        encode_word(word, &mut encoded);
    }
    encoded
}

fn decode_hex(first: u8, second: u8) -> Option<u8> {
    fn digit(value: u8) -> Option<u8> {
        match value {
            b'0'..=b'9' => Some(value - b'0'),
            b'A'..=b'F' => Some(value - b'A' + 10),
            _ => None,
        }
    }
    Some(digit(first)? * 16 + digit(second)?)
}

fn decode_byte(bytes: &[u8]) -> Result<(u8, usize), SolverError> {
    match bytes {
        [b'$', b'\'', b'\\', suffix @ ..] => {
            let (value, consumed) = match suffix {
                [b't', b'\'', ..] => (b'\t', 2),
                [b'n', b'\'', ..] => (b'\n', 2),
                [b'f', b'\'', ..] => (12, 2),
                [b'r', b'\'', ..] => (b'\r', 2),
                [b'x', first, second, b'\'', ..] => {
                    (decode_hex(*first, *second).ok_or_else(|| invalid("invalid hex escape"))?, 4)
                },
                _ => return Err(invalid("invalid ANSI-C escape")),
            };
            Ok((value, 3 + consumed))
        },
        [b'\\', next, ..] => Ok((*next, 2)),
        [b'\\'] => Err(invalid("trailing escape")),
        [
            byte @ (b'A'..=b'Z'
            | b'a'..=b'z'
            | b'0'..=b'9'
            | b'+'
            | b','
            | b'-'
            | b'.'
            | b'/'
            | b':'
            | b'_'),
            ..,
        ] => Ok((*byte, 1)),
        _ => Err(invalid("noncanonical shell metacharacter")),
    }
}

fn decode_words(script: &str, executable: &[u8]) -> Result<Vec<Vec<u8>>, SolverError> {
    let bytes = script.as_bytes();
    if bytes.len()
        > max_script_bytes(executable).ok_or_else(|| invalid("solver executable path too long"))?
    {
        return Err(invalid("encoded Bash.strings script exceeds fixed argv bound"));
    }
    let max_word_bytes = executable
        .len()
        .max(MAX_OPTION_BYTES)
        .max(PROOF.iter().chain(BEST).chain(DEL_INSTS).map(|word| word.len()).max().unwrap_or(0));
    let mut words = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        if words.len() == MAX_WORDS {
            return Err(invalid("solver argv contains too many words"));
        }
        let mut word = Vec::new();
        if bytes[position..].starts_with(b"\"\"") {
            position += 2;
        } else {
            while position < bytes.len() && bytes[position] != b' ' {
                if word.len() == max_word_bytes {
                    return Err(invalid("solver argv word exceeds fixed argument bound"));
                }
                let (byte, consumed) = decode_byte(&bytes[position..])?;
                word.push(byte);
                position += consumed;
            }
        }
        words.push(word);
        if position == bytes.len() {
            break;
        }
        position += 1;
        if position == bytes.len() || bytes[position] == b' ' {
            return Err(invalid("noncanonical whitespace"));
        }
    }
    if encode_words(&words) != bytes {
        return Err(invalid("Bash.strings re-encoding differs"));
    }
    Ok(words)
}

#[cfg(unix)]
fn executable_bytes(executable: &Path) -> Result<&[u8], SolverError> {
    use std::os::unix::ffi::OsStrExt;
    Ok(executable.as_os_str().as_bytes())
}

#[cfg(not(unix))]
fn executable_bytes(executable: &Path) -> Result<&[u8], SolverError> {
    executable.to_str().map(str::as_bytes).ok_or_else(|| invalid("non-UTF-8 solver executable"))
}

pub(super) fn parse_script(script: &str, executable: &Path) -> Result<Vec<String>, SolverError> {
    let executable_bytes = executable_bytes(executable)?;
    let words = decode_words(script, executable_bytes)?;
    if words.first().map(Vec::as_slice) != Some(executable_bytes) {
        return Err(invalid("executable identity request does not match configured veriT"));
    }
    let args: Vec<String> = words[1..]
        .iter()
        .map(|word| {
            std::str::from_utf8(word)
                .map(str::to_owned)
                .map_err(|_| invalid("non-UTF-8 solver argument"))
        })
        .collect::<Result<_, _>>()?;
    validate_arguments(&args)?;
    Ok(args)
}

fn argument<T: AsRef<OsStr>>(value: &T) -> Result<&str, SolverError> {
    value.as_ref().to_str().ok_or_else(|| invalid("non-UTF-8 solver argument"))
}

pub(super) fn validate_arguments<T: AsRef<OsStr>>(args: &[T]) -> Result<(), SolverError> {
    if !args
        .iter()
        .take(PROOF.len())
        .zip(PROOF)
        .all(|(arg, expected)| argument(arg).is_ok_and(|value| value == *expected))
        || args.len() < PROOF.len()
    {
        return Err(invalid("fixed proof flags differ"));
    }
    let rest = &args[PROOF.len()..];
    let (strategy, time) = match rest.last().map(argument).transpose()? {
        Some(option) if option.starts_with("--max-time=") => {
            (&rest[..rest.len() - 1], Some(option))
        },
        _ => (rest, None),
    };
    if ![&[][..], BEST, DEL_INSTS].iter().any(|allowed| {
        strategy.len() == allowed.len()
            && strategy
                .iter()
                .zip(*allowed)
                .all(|(arg, expected)| argument(arg).is_ok_and(|value| value == *expected))
    }) {
        return Err(invalid("strategy sequence differs or extra options supplied"));
    }
    if let Some(option) = time {
        let digits =
            option.strip_prefix("--max-time=").ok_or_else(|| invalid("invalid max-time"))?;
        if digits.is_empty()
            || digits.starts_with('0')
            || !digits.bytes().all(|byte| byte.is_ascii_digit())
            || !matches!(digits.parse::<u64>(), Ok(1..=MAX_MILLISECONDS))
        {
            return Err(invalid("max-time must be positive milliseconds at most 300000"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn encoder_roundtrips_all_nonzero_bytes() {
        for byte in 1..=255 {
            let words = vec![vec![byte]];
            let script = String::from_utf8(encode_words(&words)).unwrap();
            assert_eq!(decode_words(&script, b"test").unwrap(), words);
        }
    }
}
