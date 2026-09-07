"""Y2 corpus mechanical-check test.

Every `.invalid.lean` and `.solved.lean` under
`lean/SynthLean/Y2Corpus/` is a curated training-pair companion to
an auto-dumped `.failed.lean`.  The companions are claims:

  - `.invalid.lean`: "this obligation is genuinely unprovable —
                     here's a Lean-checked existential counterexample"
  - `.solved.lean`:  "this obligation IS provable — here's the proof"

Both claims are mechanically verifiable by running
`lake env lean <file>`.  This test enforces that every committed
companion type-checks under the project's Lean toolchain.

A companion that drifts out of sync with its `.failed.lean` (e.g.,
the obligation's hypotheses change because the translator's encoding
shifted) fails this test, surfacing the drift immediately.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


_REPO = Path(__file__).resolve().parent.parent
_LEAN_DIR = _REPO / "lean"
_CORPUS = _LEAN_DIR / "SynthLean" / "Y2Corpus"
_LAKE = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
# CI runners may not have lake at the elan path; allow the test to
# skip gracefully if the toolchain isn't reachable.
_LAKE_OK = os.path.exists(_LAKE) and os.access(_LAKE, os.X_OK)

# Per-file timeout — companion proofs should be small/local.  If one
# takes longer than this, it's either pathological or the test
# infrastructure is wedged.
_TIMEOUT_S = 120.0


def _check_one(path: Path) -> tuple[bool, str]:
    """Run `lake env lean <file>` on a companion file.

    `path` may be relative to _LEAN_DIR (canonical corpus) or an
    absolute path (e.g. a proof relocated under a per-task VERINA
    dir).  Either way it type-checks against canonical's built
    SynthLean.Core via `cwd=_LEAN_DIR`.

    Returns (ok, detail).  `ok` is True iff lean returns exit 0.
    """
    try:
        proc = subprocess.run(
            [_LAKE, "env", "lean", str(path)],
            cwd=_LEAN_DIR,
            capture_output=True,
            text=True,
            timeout=_TIMEOUT_S,
        )
    except subprocess.TimeoutExpired:
        return False, f"timed out after {_TIMEOUT_S}s"
    if proc.returncode == 0:
        return True, ""
    tail = (proc.stdout + proc.stderr).strip()[-800:]
    return False, f"exit {proc.returncode}\n{tail}"


def main() -> int:
    if not _LAKE_OK:
        print(f"SKIP — lake not available at {_LAKE}")
        return 0

    # Collect companions from BOTH the canonical corpus AND the
    # per-task VERINA dirs (benchmarks/verina/<vid>/lean/...), where
    # the search-based-verina-proving campaign relocated its proofs.
    _VERINA = _REPO / "benchmarks" / "verina"
    companions: list[Path] = []
    if _CORPUS.exists():
        companions += sorted(_CORPUS.rglob("*.invalid.lean"))
        companions += sorted(_CORPUS.rglob("*.solved.lean"))
    if _VERINA.exists():
        companions += sorted(_VERINA.rglob("*.invalid.lean"))
        companions += sorted(_VERINA.rglob("*.solved.lean"))

    if not companions:
        print("SKIP — no companion files yet")
        return 0

    # Run lake env lean on each.  Stop reporting at first failure within
    # a file but continue the suite so the user sees all failures.
    ok_count = 0
    failures: list[tuple[str, str]] = []
    for path in companions:
        # Canonical-corpus files run by their path relative to
        # _LEAN_DIR; relocated per-task files run by absolute path.
        try:
            arg = path.relative_to(_LEAN_DIR)
        except ValueError:
            arg = path.resolve()
        disp = path.relative_to(_REPO) if path.is_absolute() \
            or _REPO in path.resolve().parents else path
        ok, detail = _check_one(arg)
        if ok:
            print(f"PASS  {disp}")
            ok_count += 1
        else:
            print(f"FAIL  {disp}\n      {detail}")
            failures.append((str(disp), detail))

    print()
    print(f"{ok_count} passed, {len(failures)} failed "
          f"({len(companions)} total)")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
