# Scripts

Quick installation scripts for Isabelle-rs.

These scripts build the repository; they do not turn Isabelle-rs into a full
Isabelle replacement. The current project is a Rust research prototype of an
Isabelle/Pure-inspired LCF kernel. See
[../docs/PROJECT_STATUS.md](../docs/PROJECT_STATUS.md).

## Linux / macOS

```bash
# One-line install from GitHub
curl -fsSL https://raw.githubusercontent.com/mcbgaruda/isabelle-rs/main/scripts/install.sh | bash

# Or run locally
./scripts/install.sh

# Options
./scripts/install.sh --release
./scripts/install.sh --check
./scripts/install.sh --dir /opt/isabelle-rs
```

## Windows PowerShell

```powershell
# One-line install from GitHub
powershell -c "iwr https://raw.githubusercontent.com/mcbgaruda/isabelle-rs/main/scripts/install.ps1 | iex"

# Or run locally
.\scripts\install.ps1

# Options
.\scripts\install.ps1 -Release
.\scripts\install.ps1 -Check
.\scripts\install.ps1 -Dir C:\Tools\isabelle-rs
```

## After Installation

Fast checks:

```bash
cargo fmt --check
cargo check
```

Kernel/proof replay gate:

```bash
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
```

Stack-sensitive theory runs:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Do not claim broad `cargo test --lib` success unless the known theory-loader
stack-sensitive test has been verified fixed in the current checkout.
