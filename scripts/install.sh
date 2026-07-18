#!/usr/bin/env bash
# =============================================================================
# Isabelle-rs — Quick Install Script (Linux / macOS)
# =============================================================================
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/MCB-SMART-BOY/isabelle-rs/main/scripts/install.sh | bash
#   or
#   ./scripts/install.sh [--release] [--check] [--dir PATH]
#
# Options:
#   --release    Build in release mode (faster, no debug symbols)
#   --check      Only check if the build compiles (cargo check --locked)
#   --dir PATH   Install to a specific directory (default: current checkout or ./isabelle-rs)
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

LOCAL_REPO_DIR=""
if [ -n "${BASH_SOURCE[0]:-}" ] && [ -f "${BASH_SOURCE[0]}" ]; then
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    CANDIDATE_REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
    if [ -f "$CANDIDATE_REPO_DIR/Cargo.toml" ] &&
        [ "$(git -C "$CANDIDATE_REPO_DIR" rev-parse --is-inside-work-tree 2>/dev/null)" = "true" ]; then
        LOCAL_REPO_DIR="$CANDIDATE_REPO_DIR"
    fi
fi

# --- Parse arguments -------------------------------------------------------
while [[ $# -gt 0 ]]; do
    case "$1" in
        --release)   BUILD_MODE="release" ;;
        --check)     CHECK_ONLY=true ;;
        --dir)
            if [ "$#" -lt 2 ]; then
                echo -e "${RED}Missing value for --dir${NC}"
                exit 2
            fi
            INSTALL_DIR="$2"
            shift
            ;;
        --help|-h)   sed -n '2,13p' "$0"; exit 0 ;;
        *)           echo -e "${RED}Unknown option: $1${NC}"; exit 1 ;;
    esac
    shift
done

# --- Banner ----------------------------------------------------------------
echo ""
echo -e "${BOLD}${CYAN}╔══════════════════════════════════════════╗${NC}"
echo -e "${BOLD}${CYAN}║   Isabelle-rs — Quick Installer          ║${NC}"
echo -e "${BOLD}${CYAN}║   Isabelle/Pure kernel prototype         ║${NC}"
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

    # Keep this in sync with `package.rust-version` in Cargo.toml.
    RUST_SEMVER="${RUST_VERSION#rustc }"
    RUST_SEMVER="${RUST_SEMVER%% *}"
    IFS='.' read -r MAJOR MINOR _PATCH <<<"$RUST_SEMVER"
    if [ "$MAJOR" -lt 1 ] || { [ "$MAJOR" -eq 1 ] && [ "$MINOR" -lt 96 ]; }; then
        if ! command -v rustup >/dev/null 2>&1; then
            echo -e "${RED}  Rust $RUST_SEMVER is too old; Rust 1.96+ and rustup are required.${NC}"
            exit 1
        fi
        echo -e "${YELLOW}  Rust $RUST_SEMVER is too old (need 1.96+). Updating stable...${NC}"
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
    if [ -n "$LOCAL_REPO_DIR" ]; then
        INSTALL_DIR="$LOCAL_REPO_DIR"
    else
        INSTALL_DIR="$PWD/isabelle-rs"
    fi
fi

echo ""
echo -e "${YELLOW}→ Install directory:${NC} $INSTALL_DIR"

# --- Clone or update -------------------------------------------------------
if [ "$(git -C "$INSTALL_DIR" rev-parse --is-inside-work-tree 2>/dev/null)" = "true" ]; then
    cd "$INSTALL_DIR"
    if [ -n "$LOCAL_REPO_DIR" ] && [ "$(pwd)" = "$LOCAL_REPO_DIR" ]; then
        echo -e "${YELLOW}→ Using current checkout without pulling another branch.${NC}"
    else
        echo -e "${YELLOW}→ Repository exists. Pulling latest main...${NC}"
        git pull --ff-only origin main 2>/dev/null || {
            echo -e "${YELLOW}  ⚠ Could not pull (local changes?). Continuing with current code.${NC}"
        }
    fi
else
    if [ -d "$INSTALL_DIR" ]; then
        echo -e "${RED}✗ Directory exists but is not a git repository: $INSTALL_DIR${NC}"
        exit 1
    fi
    echo -e "${YELLOW}→ Cloning repository...${NC}"
    git clone https://github.com/MCB-SMART-BOY/isabelle-rs.git "$INSTALL_DIR" 2>/dev/null || {
        # Fallback: when executed from a checkout, use that checkout directly.
        REPO_DIR="$LOCAL_REPO_DIR"
        if [ -n "$REPO_DIR" ] && [ -f "$REPO_DIR/Cargo.toml" ]; then
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
    echo -e "${YELLOW}→ Checking compilation (cargo check --locked)...${NC}"
    cargo check --locked
    echo ""
    echo -e "${GREEN}╔══════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║  ✓ Compilation check passed!             ║${NC}"
    echo -e "${GREEN}╚══════════════════════════════════════════╝${NC}"
else
    if [ "$BUILD_MODE" = "release" ]; then
        echo -e "${YELLOW}→ Building in release mode...${NC}"
        cargo build --locked --release
        BINARY_PATH="$INSTALL_DIR/target/release/isabelle-rs"
    else
        echo -e "${YELLOW}→ Building in debug mode...${NC}"
        cargo build --locked
        BINARY_PATH="$INSTALL_DIR/target/debug/isabelle-rs"
    fi

    echo ""
    if [ -f "$BINARY_PATH" ]; then
        echo -e "${GREEN}╔══════════════════════════════════════════╗${NC}"
        echo -e "${GREEN}║  ✓ Build successful!                     ║${NC}"
        echo -e "${GREEN}║                                          ║${NC}"
        echo -e "${GREEN}║  Binary: $BINARY_PATH                    ║${NC}"
        echo -e "${GREEN}║                                          ║${NC}"
        echo -e "${GREEN}║  Workflows: scripts/README.md             ║${NC}"
        echo -e "${GREEN}╚══════════════════════════════════════════╝${NC}"
        echo ""
        echo -e "  Add to PATH:  ${CYAN}export PATH=\"\$PATH:$INSTALL_DIR/target/$BUILD_MODE\"${NC}"
    else
        echo -e "${RED}✗ Build failed. Check the output above for errors.${NC}"
        exit 1
    fi
fi
