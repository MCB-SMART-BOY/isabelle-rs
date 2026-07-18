# =============================================================================
# Isabelle-rs — Quick Install Script (Windows / PowerShell)
# =============================================================================
# Usage:
#   powershell -c "irm https://raw.githubusercontent.com/MCB-SMART-BOY/isabelle-rs/main/scripts/install.ps1 | iex"
#   or
#   .\scripts\install.ps1 [-Release] [-Check] [-Dir PATH]
#
# Options:
#   -Release    Build in release mode
#   -Check      Only check if the build compiles (cargo check --locked)
#   -Dir PATH   Install to a specific directory (default: current checkout or .\isabelle-rs)
# =============================================================================

param(
    [switch]$Release,
    [switch]$Check,
    [string]$Dir = ""
)

$ErrorActionPreference = "Stop"

function Test-GitWorkTree {
    param([string]$Path)

    if (-not (Test-Path -LiteralPath $Path -PathType Container) -or
        -not (Get-Command git -ErrorAction SilentlyContinue)) {
        return $false
    }

    $isInsideWorkTree = & git -C $Path rev-parse --is-inside-work-tree 2>$null
    return ($LASTEXITCODE -eq 0) -and ($isInsideWorkTree -eq "true")
}

$localRepoDir = $null
$scriptPath = $MyInvocation.MyCommand.Path
if ($scriptPath) {
    $scriptDir = Split-Path -Parent $scriptPath
    $candidateRepoDir = Split-Path -Parent $scriptDir
    if ((Test-Path "$candidateRepoDir\Cargo.toml") -and
        (Test-GitWorkTree $candidateRepoDir)) {
        $localRepoDir = $candidateRepoDir
    }
}

# --- Banner ----------------------------------------------------------------
Write-Host ""
Write-Host "╔══════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   Isabelle-rs — Quick Installer          ║" -ForegroundColor Cyan
Write-Host "║   Isabelle/Pure kernel prototype         ║" -ForegroundColor Cyan
Write-Host "╚══════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# --- Detect platform -------------------------------------------------------
$isWindowsHost = $env:OS -eq "Windows_NT"
$OS = if ($isWindowsHost) { "windows" } elseif ($IsLinux) { "linux" } elseif ($IsMacOS) { "macos" } else { "unknown" }
$ARCH = if ([Environment]::Is64BitOperatingSystem) { "x86_64" } else { "x86" }
Write-Host "→ Detected: $OS / $ARCH" -ForegroundColor Yellow

# --- Check / install Rust --------------------------------------------------
Write-Host ""
Write-Host "→ Checking Rust toolchain..." -ForegroundColor Yellow

$minimumRust = [Version]"1.96.0"
$rustc = Get-Command rustc -ErrorAction SilentlyContinue
if ($rustc) {
    $rustVer = & rustc --version
    Write-Host "  ✓ Found: $rustVer" -ForegroundColor Green
    $installedRust = [Version](((($rustVer -split '\s+')[1]) -replace '-.*$', ''))
    if ($installedRust -lt $minimumRust) {
        if (-not (Get-Command rustup -ErrorAction SilentlyContinue)) {
            throw "Rust $installedRust is too old; Rust 1.96+ and rustup are required."
        }
        Write-Host "  Rust $installedRust is too old. Updating stable..." -ForegroundColor Yellow
        & rustup update stable
        if ($LASTEXITCODE -ne 0) { throw "rustup update stable failed." }
    }
} else {
    Write-Host "  Rust not found. Installing via rustup..." -ForegroundColor Yellow
    Write-Host "  Downloading from https://win.rustup.rs ..." -ForegroundColor Yellow

    $rustupInit = "$env:TEMP\rustup-init.exe"
    Invoke-WebRequest -Uri "https://win.rustup.rs" -OutFile $rustupInit
    & $rustupInit -y --default-toolchain stable
    if ($LASTEXITCODE -ne 0) { throw "rustup installation failed." }
    Remove-Item $rustupInit

    # Refresh PATH
    $env:PATH = "$env:USERPROFILE\.cargo\bin;$env:PATH"
    Write-Host "  ✓ Rust installed" -ForegroundColor Green
}

# --- Determine install directory -------------------------------------------
if (-not $Dir) {
    if ($localRepoDir) {
        $Dir = $localRepoDir
    } else {
        $Dir = Join-Path (Get-Location) "isabelle-rs"
    }
}
Write-Host "→ Install directory: $Dir" -ForegroundColor Yellow

# --- Clone or update -------------------------------------------------------
if (Test-GitWorkTree $Dir) {
    $usingLocalCheckout = $localRepoDir -and ((Resolve-Path $Dir).Path -eq (Resolve-Path $localRepoDir).Path)
    if ($usingLocalCheckout) {
        Write-Host "→ Using current checkout without pulling another branch." -ForegroundColor Yellow
    } else {
        Write-Host "→ Repository exists. Pulling latest main..." -ForegroundColor Yellow
        Push-Location $Dir
        try {
            git pull --ff-only origin main 2>$null
            if ($LASTEXITCODE -ne 0) { throw "git pull failed" }
        } catch {
            Write-Host "  ⚠ Could not pull. Continuing with current code." -ForegroundColor Yellow
        }
        Pop-Location
    }
} else {
    if (Test-Path $Dir) {
        Write-Host "✗ Directory exists but is not a git repository: $Dir" -ForegroundColor Red
        exit 1
    }

    Write-Host "→ Cloning repository..." -ForegroundColor Yellow
    git clone https://github.com/MCB-SMART-BOY/isabelle-rs.git $Dir 2>$null

    if (-not $?) {
        # Fallback: when executed from a checkout, use that checkout directly.
        if ($localRepoDir) {
            Write-Host "  Using local repository at $localRepoDir" -ForegroundColor Yellow
            $Dir = $localRepoDir
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
    Write-Host "→ Checking compilation (cargo check --locked)..." -ForegroundColor Yellow
    cargo check --locked
    if ($LASTEXITCODE -ne 0) { throw "cargo check --locked failed." }
    Write-Host ""
    Write-Host "╔══════════════════════════════════════════╗" -ForegroundColor Green
    Write-Host "║  ✓ Compilation check passed!             ║" -ForegroundColor Green
    Write-Host "╚══════════════════════════════════════════╝" -ForegroundColor Green
} else {
    $buildMode = if ($Release) { "release" } else { "debug" }
    $targetDir = if ($Release) { "release" } else { "debug" }

    Write-Host "→ Building in $buildMode mode..." -ForegroundColor Yellow
    if ($Release) {
        cargo build --locked --release
    } else {
        cargo build --locked
    }
    if ($LASTEXITCODE -ne 0) { throw "cargo build --locked failed." }

    $binary = Join-Path $Dir "target" $targetDir "isabelle-rs"
    if ($isWindowsHost) { $binary += ".exe" }

    Write-Host ""
    if (Test-Path $binary) {
        Write-Host "╔══════════════════════════════════════════╗" -ForegroundColor Green
        Write-Host "║  ✓ Build successful!                     ║" -ForegroundColor Green
        Write-Host "║                                          ║" -ForegroundColor Green
        Write-Host "║  Binary: $binary                         ║" -ForegroundColor Green
        Write-Host "║                                          ║" -ForegroundColor Green
        Write-Host "║  Workflows: scripts/README.md             ║" -ForegroundColor Green
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
