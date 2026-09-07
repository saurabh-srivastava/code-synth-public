# lean — Lean 4 proof backend

Lean 4 + mathlib as the verifier for axiom-heavy soundness-
critical obligations.  `synth/lean_backend/` (Python)
translates `SafetyConstraint` objects into Lean theorems; the
verifier runs `lake env lean <tempfile>` to dispatch each
class.  Curated `.solved.lean` / `.invalid.lean` companions
in `SynthLean/Y2Corpus/<bench>/` act as a content-addressable
proof cache (signature-hash filenames).

See [`../RESEARCH.LEAN.md`](../RESEARCH.LEAN.md) for the
architectural pitch and [`../SOUNDNESS.md`](../SOUNDNESS.md)
for the verifier-pipeline policy.

## Prerequisites

- `git`, `curl`, `sh` (standard on macOS / Linux).
- ~5 GB free disk space (mathlib is large).
- First-time build: ~10-15 minutes (downloads mathlib +
  compiles oleans).  Subsequent builds: ~3-7 seconds.

## Setup

One command from a clean checkout (from the **repo root**):

```bash
./lean/setup.sh
```

The script is idempotent and does three things:

1. Installs **elan** (the Lean toolchain manager) under
   `~/.elan/` if it isn't already on `PATH`.
2. Triggers installation of the Lean version pinned in
   `lean-toolchain` — `lake build` picks this up on first
   run.
3. Runs `lake build` to verify the smoke test compiles.

If `elan` was freshly installed, the script reminds you to
add `. "$HOME/.elan/env"` to your shell profile so future
sessions pick it up automatically.

### Manual setup (alternative)

```bash
# 1. elan (skip if already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -sSf | sh -s -- -y --default-toolchain none
. "$HOME/.elan/env"        # or open a new shell

# 2. Toolchain auto-installs on first lake invocation
cd lean
lake build                 # ~10-15 min on first run
```

### Verifying the setup worked

After `lake build` finishes cleanly:

```bash
cd lean
lake env lean --version    # should print "Lean (version ...)"
lake build SynthLean.Basic # ~3s; rebuilds the core module
```

If both succeed, the toolchain is ready.  The synthesizer
will invoke `lake env lean <tempfile>` per per-class Lean
dispatch — verify this works:

```bash
cd ..  # back to repo root
.venv/bin/python -c "from synth.lean_backend.verify import lean_available; print(lean_available())"
# expected: True
```

## Building

From the **`lean/` directory**:

```bash
lake build                       # build everything
lake build SynthLean.Basic       # build just the core module
lake build SynthLean.Y2Corpus.gale_shapley.Helpers   # build a per-benchmark Helpers
```

Build artifacts land in `.lake/` (gitignored).

## Running the Y2 corpus test

```bash
.venv/bin/python tests/test_y2corpus.py
```

This invokes `lake env lean` on every committed `.solved.lean`
/ `.invalid.lean` companion to make sure they still type-check
against the current Helpers.

## Troubleshooting

| Symptom | Likely cause / fix |
| --- | --- |
| `lake: command not found` | `elan` not on PATH.  `. "$HOME/.elan/env"` or restart shell. |
| `error: failed to fetch ... mathlib` | Network issue.  Retry `lake build`.  Mathlib is fetched once on first build. |
| `error: object file ... .olean does not exist` | Stale build.  `cd lean && lake build SynthLean.Y2Corpus.<bench>.Helpers` to rebuild that helper. |
| First `lake build` looks frozen | Normal.  Mathlib download + compile is 10-15 min one-time cost.  Subsequent builds are seconds. |
| `lake env lean` slow (>10s for a small file) | mathlib oleans being recompiled.  Wait it out; subsequent calls cache. |

## Layout

```
lean/
├── lakefile.lean             — lake project + mathlib dep
├── lean-toolchain            — pinned lean4 version
├── setup.sh                  — idempotent toolchain installer
└── SynthLean/
    ├── Basic.lean            — store / store2d defs (array
    │                            primitives shared by all
    │                            translated theorems)
    ├── GridPaths.lean        — hand-written proof of grid_paths
    │                            inductive (Ring 1 Day 5).
    └── Y2Corpus/
        ├── README.md         — corpus protocol
        └── <bench>/
            ├── Helpers.lean         (Tier-3 helpers + axioms)
            ├── <stem>.failed.lean   (auto-dumped; debug artifact)
            ├── <stem>.solved.lean   (hand-curated proof)
            └── <stem>.invalid.lean  (hand-curated counterexample)
```

## Status

- **Ring 1 (DONE)**: toolchain scaffold + smoke test +
  `theorem_for_safety_inductive` + `theorem_for_ranking_lb`
  + `theorem_for_ranking_decrease`.  End-of-MVP review in
  [`../RESEARCH.LEAN.md`](../RESEARCH.LEAN.md) §"Ring 1 —
  end-of-MVP review".
- **Ring 2 (DONE)**: Lean integrated as the UNKNOWN-
  fallthrough verifier (`synth/lean_backend/verify.py`);
  sound-by-default policy in `synth/solver.py`.
- **Phase Y.1.5 (DONE, 2026-05-17)**: chain-bundle
  translators + per-branch dispatch for SB(n>1) loop
  bodies.  All axiom-heavy benchmarks now sound by default.
- **Phase H.2.CODEGEN + #167 + H.4 (2026-05-19)**: Tier-3
  helper-citation codegen + chain-aware translators +
  cardinality-ordered enum + cache-only Lean for
  ranking-*.  Stretch corpus 11/11 verified E2E.
- **Tier-1 push (2026-05-19+)**: ongoing axiom-to-theorem
  promotion; see [`../BENCHMARKS.STATUS.md`](../BENCHMARKS.STATUS.md)
  (Stretch tier + ceilings) and [`../PRINCIPLES.md`](../PRINCIPLES.md)
  P-2 (axiom-free preferred).
