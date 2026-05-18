#!/usr/bin/env bash
# =============================================================================
# Isabelle-rs — Quick Install Script (Linux / macOS)
# =============================================================================
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/.../scripts/install.sh | bash
#   or
#   ./scripts/install.sh [--release] [--check] [--dir PATH]
#
# Options:
#   --release    Build in release mode (faster, no debug symbols)
#   --check      Only check if the build compiles (cargo check)
#   --dir PATH   Install to a specific directory (default: ./isabelle-rs)
# =============================================================================

set -euo pipefail

# --- Colors ----------------------------------------------------------------
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m' # No Color

# --- Defaults --------------------------------------------------------------
BUILD_MODE="debug"
CHECK_ONLY=false
INSTALL_DIR=""
RUSTUP_URL="https://sh.rustup.rs"

# --- Parse arguments -------------------------------------------------------
while [[ $# -gt 0 ]]; do
    case "$1" in
        --release)   BUILD_MODE="release" ;;
        --check)     CHECK_ONLY=true ;;
        --dir)       INSTALL_DIR="$2"; shift ;;
        --help|-h)   sed -n '2,13p' "$0"; exit 0 ;;
        *)           echo -e "${RED}Unknown option: $1${NC}"; exit 1 ;;
    esac
    shift
done

# --- Banner ----------------------------------------------------------------
echo ""
echo -e "${BOLD}${CYAN}╔══════════════════════════════════════════╗${NC}"
echo -e "${BOLD}${CYAN}║   Isabelle-rs — Quick Installer          ║${NC}"
echo -e "${BOLD}${CYAN}║   Isabelle Proof Assistant in Rust       ║${NC}"
echo -e "${BOLD}${CYAN}╚══════════════════════════════════════════╝${NC}"
echo ""

# --- Detect platform -------------------------------------------------------
OS="$(uname -s)"
ARCH="$(uname -m)"
echo -e "${YELLOW}→ Detected:${NC} $OS / $ARCH"

case "$OS" in
    Linux)   PLATFORM="linux" ;;
    Darwin)  PLATFORM="macos" ;;
    *)       echo -e "${RED}✗ Unsupported OS: $OS${NC}"; exit 1 ;;
esac

# --- Check / install Rust --------------------------------------------------
echo ""
echo -e "${YELLOW}→ Checking Rust toolchain...${NC}"

if command -v rustc &>/dev/null; then
    RUST_VERSION=$(rustc --version)
    echo -e "${GREEN}  ✓ Found:${NC} $RUST_VERSION"

    # Check minimum version (1.80+)
    VER=$(rustc --version | grep -oP '\d+\.\d+' | head -1)
    MAJOR=$(echo "$VER" | cut -d. -f1)
    MINOR=$(echo "$VER" | cut -d. -f2)
    if [ "$MAJOR" -lt 1 ] || ([ "$MAJOR" -eq 1 ] && [ "$MINOR" -lt 80 ]); then
        echo -e "${YELLOW}  ⚠ Rust $VER is too old (need 1.80+). Updating...${NC}"
        rustup update stable
    fi
else
    echo -e "${YELLOW}  Rust not found. Installing via rustup...${NC}"
    curl --proto '=https' --tlsv1.2 -sSf "$RUSTUP_URL" | sh -s -- -y --default-toolchain stable
    # shellcheck disable=SC1091
    source "$HOME/.cargo/env"
    echo -e "${GREEN}  ✓ Rust installed${NC}"
fi

# --- Determine install directory -------------------------------------------
if [ -z "$INSTALL_DIR" ]; then
    INSTALL_DIR="$PWD/isabelle-rs"
fi

echo ""
echo -e "${YELLOW}→ Install directory:${NC} $INSTALL_DIR"

# --- Clone or update -------------------------------------------------------
if [ -d "$INSTALL_DIR/.git" ]; then
    echo -e "${YELLOW}→ Repository exists. Pulling latest changes...${NC}"
    cd "$INSTALL_DIR"
    git pull --ff-only origin main 2>/dev/null || {
        echo -e "${YELLOW}  ⚠ Could not pull (local changes?). Continuing with current code.${NC}"
    }
else
    if [ -d "$INSTALL_DIR" ]; then
        echo -e "${RED}✗ Directory exists but is not a git repository: $INSTALL_DIR${NC}"
        exit 1
    fi
    echo -e "${YELLOW}→ Cloning repository...${NC}"
    git clone https://github.com/mcbgaruda/isabelle-rs.git "$INSTALL_DIR" 2>/dev/null || {
        # Fallback: if the script is run from within the repo, copy the current directory
        SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
        REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
        if [ -f "$REPO_DIR/Cargo.toml" ]; then
            echo -e "${YELLOW}  Using local repository at $REPO_DIR${NC}"
            INSTALL_DIR="$REPO_DIR"
        else
            echo -e "${RED}✗ Could not clone and no local repo found.${NC}"
            exit 1
        fi
    }
    cd "$INSTALL_DIR"
fi

# --- Build -----------------------------------------------------------------
echo ""
if [ "$CHECK_ONLY" = true ]; then
    echo -e "${YELLOW}→ Checking compilation (cargo check)...${NC}"
    cargo check
    echo ""
    echo -e "${GREEN}╔══════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║  ✓ Compilation check passed!             ║${NC}"
    echo -e "${GREEN}╚══════════════════════════════════════════╝${NC}"
else
    if [ "$BUILD_MODE" = "release" ]; then
        echo -e "${YELLOW}→ Building in release mode...${NC}"
        cargo build --release
        BINARY_PATH="$INSTALL_DIR/target/release/isabelle-rs"
    else
        echo -e "${YELLOW}→ Building in debug mode...${NC}"
        cargo build
        BINARY_PATH="$INSTALL_DIR/target/debug/isabelle-rs"
    fi

    echo ""
    if [ -f "$BINARY_PATH" ]; then
        echo -e "${GREEN}╔══════════════════════════════════════════╗${NC}"
        echo -e "${GREEN}║  ✓ Build successful!                     ║${NC}"
        echo -e "${GREEN}║                                          ║${NC}"
        echo -e "${GREEN}║  Binary: $BINARY_PATH                    ║${NC}"
        echo -e "${GREEN}║                                          ║${NC}"
        echo -e "${GREEN}║  Run tests:    cargo test                ║${NC}"
        echo -e "${GREEN}║  Run LSP:      cargo run -- --lsp        ║${NC}"
        echo -e "${GREEN}║  Verification: cargo test -- benchmark   ║${NC}"
        echo -e "${GREEN}╚══════════════════════════════════════════╝${NC}"
        echo ""
        echo -e "  Add to PATH:  ${CYAN}export PATH=\"\$PATH:$INSTALL_DIR/target/$BUILD_MODE\"${NC}"
    else
        echo -e "${RED}✗ Build failed. Check the output above for errors.${NC}"
        exit 1
    fi
fi
