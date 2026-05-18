# =============================================================================
# Isabelle-rs — Quick Install Script (Windows / PowerShell)
# =============================================================================
# Usage:
#   powershell -c "irm https://raw.githubusercontent.com/.../scripts/install.ps1 | iex"
#   or
#   .\scripts\install.ps1 [-Release] [-Check] [-Dir PATH]
#
# Options:
#   -Release    Build in release mode
#   -Check      Only check if the build compiles (cargo check)
#   -Dir PATH   Install to a specific directory (default: .\isabelle-rs)
# =============================================================================

param(
    [switch]$Release,
    [switch]$Check,
    [string]$Dir = ""
)

$ErrorActionPreference = "Stop"

# --- Banner ----------------------------------------------------------------
Write-Host ""
Write-Host "╔══════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   Isabelle-rs — Quick Installer          ║" -ForegroundColor Cyan
Write-Host "║   Isabelle Proof Assistant in Rust       ║" -ForegroundColor Cyan
Write-Host "╚══════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# --- Detect platform -------------------------------------------------------
$OS = if ($IsWindows) { "windows" } elseif ($IsLinux) { "linux" } elseif ($IsMacOS) { "macos" } else { "unknown" }
$ARCH = if ([Environment]::Is64BitOperatingSystem) { "x86_64" } else { "x86" }
Write-Host "→ Detected: $OS / $ARCH" -ForegroundColor Yellow

# --- Check / install Rust --------------------------------------------------
Write-Host ""
Write-Host "→ Checking Rust toolchain..." -ForegroundColor Yellow

$rustc = Get-Command rustc -ErrorAction SilentlyContinue
if ($rustc) {
    $rustVer = & rustc --version
    Write-Host "  ✓ Found: $rustVer" -ForegroundColor Green
} else {
    Write-Host "  Rust not found. Installing via rustup..." -ForegroundColor Yellow
    Write-Host "  Downloading from https://win.rustup.rs ..." -ForegroundColor Yellow

    $rustupInit = "$env:TEMP\rustup-init.exe"
    Invoke-WebRequest -Uri "https://win.rustup.rs" -OutFile $rustupInit
    & $rustupInit -y --default-toolchain stable
    Remove-Item $rustupInit

    # Refresh PATH
    $env:PATH = "$env:USERPROFILE\.cargo\bin;$env:PATH"
    Write-Host "  ✓ Rust installed" -ForegroundColor Green
}

# --- Determine install directory -------------------------------------------
if (-not $Dir) {
    $Dir = Join-Path (Get-Location) "isabelle-rs"
}
Write-Host "→ Install directory: $Dir" -ForegroundColor Yellow

# --- Clone or update -------------------------------------------------------
if (Test-Path "$Dir\.git") {
    Write-Host "→ Repository exists. Pulling latest changes..." -ForegroundColor Yellow
    Push-Location $Dir
    try {
        git pull --ff-only origin main 2>$null
    } catch {
        Write-Host "  ⚠ Could not pull. Continuing with current code." -ForegroundColor Yellow
    }
    Pop-Location
} else {
    if (Test-Path $Dir) {
        Write-Host "✗ Directory exists but is not a git repository: $Dir" -ForegroundColor Red
        exit 1
    }

    Write-Host "→ Cloning repository..." -ForegroundColor Yellow
    git clone https://github.com/mcbgaruda/isabelle-rs.git $Dir 2>$null

    if (-not $?) {
        # Fallback: use local repo
        $scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
        $repoDir = Split-Path -Parent $scriptDir
        if (Test-Path "$repoDir\Cargo.toml") {
            Write-Host "  Using local repository at $repoDir" -ForegroundColor Yellow
            $Dir = $repoDir
        } else {
            Write-Host "✗ Could not clone and no local repo found." -ForegroundColor Red
            exit 1
        }
    }
}

Push-Location $Dir

# --- Build -----------------------------------------------------------------
Write-Host ""
if ($Check) {
    Write-Host "→ Checking compilation (cargo check)..." -ForegroundColor Yellow
    cargo check
    if ($LASTEXITCODE -eq 0) {
        Write-Host ""
        Write-Host "╔══════════════════════════════════════════╗" -ForegroundColor Green
        Write-Host "║  ✓ Compilation check passed!             ║" -ForegroundColor Green
        Write-Host "╚══════════════════════════════════════════╝" -ForegroundColor Green
    }
} else {
    $buildMode = if ($Release) { "release" } else { "debug" }
    $targetDir = if ($Release) { "release" } else { "debug" }

    Write-Host "→ Building in $buildMode mode..." -ForegroundColor Yellow
    if ($Release) {
        cargo build --release
    } else {
        cargo build
    }

    $binary = Join-Path $Dir "target" $targetDir "isabelle-rs"
    if ($IsWindows) { $binary += ".exe" }

    Write-Host ""
    if (Test-Path $binary) {
        Write-Host "╔══════════════════════════════════════════╗" -ForegroundColor Green
        Write-Host "║  ✓ Build successful!                     ║" -ForegroundColor Green
        Write-Host "║                                          ║" -ForegroundColor Green
        Write-Host "║  Binary: $binary                         ║" -ForegroundColor Green
        Write-Host "║                                          ║" -ForegroundColor Green
        Write-Host "║  Run tests:    cargo test                ║" -ForegroundColor Green
        Write-Host "║  Run LSP:      cargo run -- --lsp        ║" -ForegroundColor Green
        Write-Host "║  Verification: cargo test -- benchmark   ║" -ForegroundColor Green
        Write-Host "╚══════════════════════════════════════════╝" -ForegroundColor Green
        Write-Host ""
        Write-Host "  Add to PATH:  `$env:PATH += `";$($Dir)\target\$targetDir`"" -ForegroundColor Cyan
    } else {
        Write-Host "✗ Build failed. Check the output above for errors." -ForegroundColor Red
        Pop-Location
        exit 1
    }
}

Pop-Location
