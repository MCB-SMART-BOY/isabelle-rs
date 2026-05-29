# Scripts

Quick installation scripts for Isabelle-rs.

## Linux / macOS

```bash
# One-line install (from GitHub)
curl -fsSL https://raw.githubusercontent.com/mcbgaruda/isabelle-rs/main/scripts/install.sh | bash

# Or run locally
./scripts/install.sh

# Options
./scripts/install.sh --release          # Build in release mode
./scripts/install.sh --check            # Only check compilation
./scripts/install.sh --dir /opt/isabelle-rs  # Custom directory
```

## Windows (PowerShell)

```powershell
# One-line install (from GitHub)
powershell -c "iwr https://raw.githubusercontent.com/mcbgaruda/isabelle-rs/main/scripts/install.ps1 | iex"

# Or run locally
.\scripts\install.ps1

# Options
.\scripts\install.ps1 -Release          # Build in release mode
.\scripts\install.ps1 -Check            # Only check compilation
.\scripts\install.ps1 -Dir C:\Tools\isabelle-rs  # Custom directory
```

## What the scripts do

1. **Check/install Rust** (1.80+) via rustup
2. **Clone** the repository (or pull latest if already cloned)
3. **Build** the project (`cargo build`)
4. **Display** next steps (run tests, start LSP, etc.)

## After installation

```bash
# Run all tests (250+)
cargo test

# Run core verification benchmark (~4.1s, 125/125 theorems)
cargo test test_verify_all_core_files -- --nocapture

# Run beyond-core verification (128/128 theorems, 9 files)
RUST_MIN_STACK=134217728 cargo test test_verify_beyond_core -- --nocapture

# Start LSP server
cargo run -- --lsp

# Load full HOL library (1,000 files, ~2.7s)
RUST_MIN_STACK=33554432 cargo test test_load_1000_from_full_hol -- --nocapture
```
