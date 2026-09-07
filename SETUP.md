# Setup

Step-by-step instructions for getting the synthesizer running
from scratch.  Tested on macOS (Apple Silicon, Sonoma 14.x) and
Ubuntu 22.04+.  Other Linux distros should be similar.

## TL;DR — happy path

```bash
git clone https://github.com/saurabh-srivastava/code-synth.git
cd code-synth

# 1. Python venv + synth package.
python3.12 -m venv .venv
source .venv/bin/activate      # or `. .venv/bin/activate`
pip install --upgrade pip
pip install -e .

# 2. Lean toolchain + mathlib (one-time, takes a few minutes).
./lean/setup.sh

# 3. Sanity-check: run the quick regression.
python tests/regression.py
```

If that all succeeds, you're done.  Each piece is broken down
below if any step needs more detail.

---

## What you need

| Tool | Version | Why |
| --- | --- | --- |
| **Python** | 3.10 or newer (3.12 used in CI) | Synth package + Z3 bindings + emitter tests. |
| **Z3** | latest `z3-solver` pip | SMT verifier.  Installed via `pip install -e .`. |
| **Lean 4** | `v4.30.0-rc2` (pinned in `lean/lean-toolchain`) | Proof backend.  `elan` (the Lean toolchain manager) installs this automatically; you do not run `elan default stable`. |
| **lake + elan** | auto-installed by `lean/setup.sh` | Lean's build tool + version manager. |
| **mathlib** | `master` (auto-pulled) | Lean's standard library; cost-composition lemmas + tactics depend on it. |
| **clang** | any modern (Apple clang 15+ or GCC 11+) | Compiling C emitter outputs in `tests/test_emit_c.py`. |
| **rustc** | 2021 edition (any recent stable) | Compiling Rust emitter outputs in `tests/test_emit_rust.py`. |
| **git** | any | Cloning + LFS skip flag. |

If you only want to *read* the framework and case studies
(`CASE_STUDY.md`, `CASE_STUDY.OPEN.md`, `BENCHMARKS.STATUS.md`,
`RESEARCH.md`), none of the toolchain is required.

---

## 1. Python + synth package

The framework is a regular Python package installed in editable
mode into a project-local virtualenv.  All Python tools should
go in this venv — not in your system Python or Homebrew Python.

### macOS

```bash
# Ensure Python 3.12 is on PATH.  Homebrew is the easy route:
brew install python@3.12

# Project venv.
python3.12 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install -e .
```

If you have multiple Python versions, double-check the venv
points at 3.12: `.venv/bin/python --version` should print
`Python 3.12.x`.

### Linux

```bash
# Debian / Ubuntu 22.04+:
sudo apt update
sudo apt install python3.12 python3.12-venv

# Project venv.
python3.12 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install -e .
```

### What `pip install -e .` does

Reads `pyproject.toml` and installs the `synth` package in
editable mode (so changes in `synth/*.py` are picked up without
re-installing).  Pulls one dependency: `z3-solver`.

Verify:

```bash
.venv/bin/python -c "import synth; print(synth.__file__)"
.venv/bin/python -c "import z3; print(z3.get_version())"
```

The first should print the path to `synth/__init__.py` in your
clone; the second should print `(4, ..., ..., ...)`.

---

## 2. Lean 4 + mathlib

The Lean backend uses Lean 4 (current version pinned to
`v4.30.0-rc2` in `lean/lean-toolchain`) and depends on mathlib.
A helper script `lean/setup.sh` installs `elan` (Lean's
toolchain manager) if missing, then pulls the pinned Lean + a
pre-built mathlib cache.

```bash
./lean/setup.sh
```

What it does:

1.  Installs `elan` via the official one-line installer if not
    found on PATH.  This installs to `~/.elan/`.
2.  Reads `lean/lean-toolchain` and triggers download of the
    pinned Lean version.
3.  Runs `lake update` to fetch mathlib at the version recorded
    in `lake-manifest.json`.
4.  Runs `lake exe cache get` to download pre-built mathlib
    olean files (skipping the ~30-minute mathlib compile).
5.  Runs a sanity `lake build` on the project's smoke modules.

Expected timing: first run is **5-15 minutes** depending on
network speed (downloading mathlib oleans is the slow part).
Subsequent runs are near-instant.

### Manual verification

```bash
cd lean
lake env lean --version
lake build SynthLean.Basic
```

`SynthLean.Basic` is a tiny smoke module; should build in
1-3 seconds.  If this fails:

  - Check `~/.elan/` exists and contains the pinned Lean
    version: `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/`.
  - Try `elan toolchain install $(cat lean-toolchain)`
    manually.
  - On Apple Silicon: make sure you're using a native ARM
    Lean (the elan installer picks this automatically).

### Common gotchas

  - **`error: no default toolchain configured`** when running
    `lake` outside the `lean/` directory.  This is normal —
    Lean's toolchain is pinned in `lean/lean-toolchain`; you
    must run `lake env lean` *from inside the lean/ directory*
    (or with `cd lean && ...`).  Outside that directory there's
    no toolchain pin and elan refuses to pick a default.
  - **Stale mathlib oleans after a `lake update`**.  Run
    `lake exe cache get` again to fetch the matching oleans.

---

## 3. clang (for the C emitter tests)

The C emitter tests synthesize a benchmark, emit C source,
compile with `clang -Wall -Werror`, run the binary, and assert
stdout.  Any modern clang or gcc works.

### macOS

```bash
# Apple ships clang with Xcode Command Line Tools.
xcode-select --install
clang --version
```

### Linux

```bash
sudo apt install clang
# or use gcc; the emitter tests run `clang` by name, so install
# clang specifically:
clang --version
```

Verify:

```bash
.venv/bin/python tests/test_emit_c.py
```

This runs ~12 benchmarks (synth + emit + compile + run); takes
2-5 minutes.

---

## 4. rustc (for the Rust emitter tests)

The Rust emitter tests do the same as C but with `rustc -O`.

### macOS / Linux

```bash
# rustup is the standard installer.
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
# or via Homebrew on macOS:  brew install rustup-init && rustup-init
source $HOME/.cargo/env
rustc --version
```

The emitter tests use the 2021 edition; any recent stable
toolchain (1.70+) works.

Verify:

```bash
.venv/bin/python tests/test_emit_rust.py
```

---

## 5. Running the test suite

The three test surfaces, in increasing depth:

```bash
# Quick regression — all synth benchmarks except the slow
# axiom-heavy ones (~3-5 min total).
.venv/bin/python tests/regression.py

# Plus the slow ones (~10-15 min).
.venv/bin/python tests/regression.py --slow

# Emitter round-trips: Python, C, Rust (each ~2-5 min).
.venv/bin/python tests/test_emit_py.py
.venv/bin/python tests/test_emit_c.py
.venv/bin/python tests/test_emit_rust.py

# Lean backend tests (~5-10 min on cold mathlib cache).
.venv/bin/python tests/test_lean_backend.py

# Y2 corpus mechanical-check (compiles every committed
# .solved.lean and .invalid.lean; ~3-5 min).
.venv/bin/python tests/test_y2corpus.py
```

All of these run in CI on every push to `main`; see
`.github/workflows/ci.yml`.

---

## 6. Running a single benchmark

Each benchmark is a self-executable Python script:

```bash
.venv/bin/python benchmarks/intsqrt.py
.venv/bin/python benchmarks/open_prbs/l16_bipartite_matching/bench_greedy_match_general.py
```

The script prints the synthesized solution(s) + verdict +
helpful hints (helper coverage, Lean fallthrough stats, etc.).
Timing varies from milliseconds (intsqrt) to several minutes
(stretch benchmarks with axiom-heavy posts).

For the cleanest "first run on a new machine" demo, try:

```bash
# Simplest — single loop, single τ atom, ~2s.
.venv/bin/python benchmarks/intsqrt.py

# Then a fully-concrete graph algorithm:
.venv/bin/python benchmarks/open_prbs/l16_bipartite_matching/bench_greedy_match_general.py
```

The first is from POPL'10 Example 1.  The second is the
greedy maximal bipartite matching that
`CASE_STUDY.md` walks through end-to-end.

> **CWD matters for `dump_lean_failures_dir`** (F19,
> community-validation 2026-06-08).  When a benchmark sets
> `dump_lean_failures_dir` to a *relative* path (the
> convention is `"lean/SynthLean/Y2Corpus/<bench>"`), the
> dump dir is resolved against the **current working
> directory** at solve time.  Run benchmarks from the
> repo root (or worktree root) — running from a subdir
> will silently dump `.failed.lean` / `.solved.lean`
> companions to the wrong place, and cache lookups
> won't find your hand-authored proofs.  The
> `Problem.__post_init__` now normalizes to absolute
> path and logs the resolved location.

---

## 7. Optional: nightly CI knob

`.github/workflows/nightly.yml` runs the slow regression once a
day.  If you fork the repo and want this enabled, push to
GitHub and the Actions tab will offer manual `workflow_dispatch`
triggers in addition to the schedule.

---

## 8. Troubleshooting

  - **Python 3.10 / 3.11 also works** but CI uses 3.12.  If
    you see warnings about `match` statements, you may be on
    3.9 or older — upgrade.
  - **`pip install -e .` fails on `z3-solver` build**: usually
    a wheel-availability mismatch.  Try `pip install --upgrade
    pip wheel setuptools` first.
  - **Z3 results differ between machines**.  Z3 is
    deterministic *given the same input* but the order of
    evaluation can shift slightly when other processes contend
    for CPU.  This rarely affects sound benchmarks.  If
    a regression flake appears reproducibly, the most likely
    cause is Z3 state leakage (see CLAUDE.md lesson #40 —
    `tests/regression.py` uses subprocess isolation
    specifically for this).
  - **`lake env lean` is slow** (~5-15s per call).  This is
    expected — lake loads mathlib oleans each invocation.  The
    framework's Lean backend amortizes by batching dispatches
    within a single benchmark run; per-call cost dominates only
    for one-off scripts.
  - **macOS GateKeeper** may quarantine the elan installer.
    `xattr -d com.apple.quarantine ~/.elan/bin/elan` fixes
    this.
  - **Working from a git worktree** (`git worktree add
    /tmp/my-branch <branch>`): the canonical `.venv/` has
    `synth` editable-installed pointing at the canonical
    repo path, so `synth.lean_backend.verify._LEAN_DIR`
    resolves to the canonical `lean/` directory — *not*
    the worktree's `lean/`.  This means a `Helpers.lean`
    you've built in the worktree's `lean/` won't be visible
    to dispatch.  Two fixes:
      - **Worktree-local venv** (cleanest): from the
        worktree root, run `python3.12 -m venv .venv-local
        && .venv-local/bin/pip install -e . --no-deps` and
        copy / re-install `z3-solver` into it.
      - **Modify the canonical install** (only if you're
        sure you want to): re-run `.venv/bin/pip install
        -e <worktree-path>` to point editable-install at
        the worktree.  This affects every shell using that
        venv; use with care.
    The non-Lean parts of the pipeline (Z3, emitters,
    tests) all work fine from a worktree using the shared
    venv — only the Lean-dispatch path-resolution needs
    attention.
  - **Skipping mathlib rebuild in a fresh worktree** (the
    `.lake/build/` rsync trap).  A fresh worktree has no
    `lean/.lake/` directory, so the first `lake build`
    re-fetches mathlib oleans — ~5-10 min on a warm cache,
    up to 30+ min on a cold one.  The tempting shortcut
    is `rsync -a /canonical/lean/.lake/ /worktree/lean/.lake/`
    to copy the canonical's already-built oleans.  **DO
    NOT do a wholesale rsync of `.lake/build/`** — its
    `.trace` files carry canonical *absolute* paths, and
    lake's incremental build will then dispatch
    `lake env lean` against canonical-path oleans that
    don't exist in the worktree, surfacing as
    `object file '/Users/.../canonical/lean/.lake/...' does
    not exist` errors during synth (community-validation
    finding F10, 2026-06-08 — v3 Q3 stall).

    Two safe alternatives:
      - **Skip mathlib rebuild entirely; let dispatch run
        in canonical's lake env** (cleanest — the v5
        agents discovered this).  `synth.lean_backend.
        verify._LEAN_DIR` resolves to the **canonical**
        `lean/` directory (via the editable-installed
        synth package).  Lean dispatches run with
        `cwd=_LEAN_DIR=/path/to/canonical/lean`, so the
        worktree never needs `lake build` for the
        framework's existing helpers.  Authored
        `.solved.lean` companions still land in the
        worktree (under `dump_lean_failures_dir`,
        CWD-relative) and are read by absolute path —
        the typecheck inherits canonical's mathlib +
        SynthLean oleans without contamination.  Only
        author a **new** `Helpers.lean` in the worktree
        if you intend the synth to import it, in which
        case follow one of the rsync alternatives below.
        See "Worktree↔canonical lean/ dataflow"
        callout further down for the full picture.
        (F13, community-validation 2026-06-08.)
      - **Rsync mathlib's oleans only** (skips the slow
        part, leaves project oleans to rebuild from
        worktree paths):
        ```bash
        mkdir -p /worktree/lean/.lake
        rsync -a /canonical/lean/.lake/packages/ \
                 /worktree/lean/.lake/packages/
        rsync -a /canonical/lean/.lake/build/lib/Mathlib* \
                 /worktree/lean/.lake/build/lib/ 2>/dev/null || true
        cd /worktree/lean && lake build SynthLean
        ```
      - **Full rsync + force-rebuild** (uglier but
        bulletproof, only needed when adding a NEW
        `Helpers.lean` module the synth must import):
        ```bash
        rsync -a /canonical/lean/.lake/ /worktree/lean/.lake/
        cd /worktree/lean
        rm -rf .lake/build/lib/SynthLean* .lake/build/ir/SynthLean*
        lake build SynthLean
        ```
        This wipes the project's stale-trace oleans while
        keeping mathlib's intact (mathlib oleans don't
        reference project paths).

### Worktree↔canonical `lean/` dataflow (F13)

For the **common** case (working in a worktree but using
only existing helpers + curating `.solved.lean`
companions), here's exactly where files live and which
process touches them:

```
                                Worktree                    Canonical
                                /tmp/agent-vX-qN/           /Users/saurabh/code/synthesizer/
benchmark Python source         benchmarks/<bench>.py       (unmodified)
benchmark imports synth         (via canonical venv)        .venv/bin/python ← edits resolve here
synth.lean_backend._LEAN_DIR    —                           lean/ ← used as cwd for `lake env lean`
dispatch tempfile               (synth writes to $TMPDIR)   typechecks against canonical's mathlib
dump_lean_failures_dir          lean/SynthLean/Y2Corpus/    (CWD-relative, lands in worktree)
                                  <bench>/sc*.failed.lean
hand-authored companions        lean/SynthLean/Y2Corpus/    (you commit these to worktree branch)
                                  <bench>/sc*.solved.lean
cache lookup at dispatch        reads from worktree path    (absolute path; canonical mathlib still works)
```

The key invariant: `_LEAN_DIR` is canonical, so the lake
toolchain (mathlib, SynthLean core/basic) comes from
canonical's `.lake/`.  But `dump_lean_failures_dir` is
CWD-relative, so dump files (and the curated companions
that pair with them) live in the **worktree**.  The
`_consult_companions` lookup uses absolute paths to read
them, so cache hits work end-to-end without any worktree
`lake build`.

The only time you need a worktree-side `lake build` is
when you're authoring a **new** `Helpers.lean` module
that synth's `HelperRegistry` path must import — that
module needs an olean visible to canonical's lake env,
which requires either committing it and re-building in
canonical, or one of the rsync alternatives above.

---

## What you DO NOT need

  - **No GPU.**  Pure CPU work.
  - **No Docker.**  Native install.
  - **No conda / pyenv** required (a venv with `python3.12 -m
    venv` is enough).
  - **No homebrew lean** — `elan` is the supported install path.
    `brew install lean` will install a different toolchain
    version and conflict with the project's pinned one.
  - **No `cargo`-managed crates** beyond `rustc` standalone —
    the Rust emitter tests compile single-file programs with
    `rustc -O`, no Cargo project.

---

## Where to read next

  - `CASE_STUDY.md` — end-to-end walkthrough of one benchmark
    (greedy maximal matching).  Best first read after setup.
  - `README.md` — project overview + Status paragraph.
  - `BENCHMARKS.STATUS.md` — per-benchmark inventory + caveats.
  - `DESIGN.md` — long-form design and phase log.
  - `RESEARCH.md` — forward-looking research threads.
  - `CLAUDE.md` — implementation history + encoding lessons
    (currently #1-#63).
