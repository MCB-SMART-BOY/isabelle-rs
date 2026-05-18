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
# Run tests
cargo test

# Start LSP server
cargo run -- --lsp

# Run verification benchmark
cargo test test_verify_all_core_files -- --nocapture
```
