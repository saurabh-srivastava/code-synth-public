#!/usr/bin/env bash
# lean/setup.sh — one-command setup for the Lean proof backend.
#
# Idempotent: safe to re-run.  Installs `elan` (the Lean toolchain
# manager) if missing, then triggers installation of the Lean
# version pinned in `lean-toolchain` and runs a sanity build.
#
# Run from the lean/ directory:
#
#     ./setup.sh
#
# Or from the repo root:
#
#     ./lean/setup.sh
#
# Exits non-zero on any failure.

set -euo pipefail

# Resolve to the directory this script lives in, so the working
# directory of the caller doesn't matter.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Sanity: lean-toolchain is what pins the Lean version.  If it's
# missing, the project is in a weird state.
if [ ! -f lean-toolchain ]; then
    echo "ERROR: $SCRIPT_DIR/lean-toolchain missing — bailing." >&2
    echo "The Lean project should always pin a toolchain." >&2
    exit 1
fi

echo "==> Lean backend setup"
echo "    pinned toolchain: $(cat lean-toolchain)"

# Step 1: ensure elan is installed.
ELAN_BIN="$HOME/.elan/bin"
if ! command -v elan >/dev/null 2>&1; then
    if [ -x "$ELAN_BIN/elan" ]; then
        # Installed but not on PATH for this shell.
        export PATH="$ELAN_BIN:$PATH"
        echo "==> elan present at $ELAN_BIN (added to PATH for this run)"
    else
        echo "==> elan not found — installing"
        # `--default-toolchain none` keeps the install minimal; the
        # `lean-toolchain` file below drives which version actually
        # gets installed.
        curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            -sSf | sh -s -- -y --default-toolchain none
        # Pick up the freshly-installed elan without requiring a new shell.
        export PATH="$ELAN_BIN:$PATH"
    fi
else
    echo "==> elan present: $(elan --version)"
fi

# Step 2: trigger toolchain install + sanity build.  `lake build`
# in a directory with a `lean-toolchain` file causes elan to
# auto-fetch the pinned version on first invocation.
echo "==> lake build (installs pinned toolchain on first run)"
lake build

# Step 3: warm OS page cache for mathlib oleans.
#
# Each `lake env lean <tmpfile>` invocation that the
# synthesizer's verify path spawns has to read mathlib
# .olean files from disk and load them into a fresh lean
# process.  On a cold cache this is 10-15s per dispatch,
# which blows the per-class 15s timeout in solver.py
# (community-validation finding F1, 2026-06-08).
#
# Running a one-time `lake env lean` here populates the
# OS page cache so subsequent invocations read mathlib
# oleans from RAM, not disk — typically 2-3s faster per
# dispatch.  Not a complete fix (Lean's process model
# doesn't share elaboration state), but reduces the
# probability of first-dispatch timeouts on fresh
# machines.  See problem.skill "Lean dispatch — cold-cache
# trap" for the failure mode this avoids.
echo "==> warm mathlib olean cache (~5-10s first run)"
echo 'import SynthLean.Basic' > /tmp/synth_setup_warmup.lean
lake env lean /tmp/synth_setup_warmup.lean >/dev/null 2>&1 || true
rm -f /tmp/synth_setup_warmup.lean

echo
echo "==> Setup complete."
echo
echo "If elan is fresh, add it to your shell profile so future"
echo "sessions pick it up automatically.  For zsh:"
echo
echo "    echo '. \"\$HOME/.elan/env\"' >> ~/.zshrc"
echo
echo "For bash:"
echo
echo "    echo '. \"\$HOME/.elan/env\"' >> ~/.bashrc"
