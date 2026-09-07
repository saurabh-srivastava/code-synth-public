"""Cheap output-shape drift triage over ported VERINA benchmarks.

Before the (expensive) per-task SpecGen fidelity fan-out, catch the
GROSS mis-ports for free: cases where a ported Problem's output does
not even have the same SHAPE as VERINA's declared return type.

The motivating case: verina_basic_60 (findEvenNumbers) returns
`Array Int` in VERINA, but its ported Problem outputs a single `int`
count — the agent silently solved "count the evens" instead of
"return the evens".  A scalar-vs-array mismatch is a certain
mis-port; no need to run the full concrete-test check to know.

This does NOT confirm faithfulness (a same-shape port can still be
semantically wrong — that is what specgen_check.py is for).  It only
flags the certain drifts cheaply.

Verdicts per task:
  DRIFT  — output shape (scalar / 1d-array / 2d-array) disagrees with
           VERINA's return type.  Near-certain mis-port.
  OK     — shapes agree (still needs specgen_check for semantics).
  REVIEW — could not classify (unusual output arity / type).

Usage:
  python verina/drift_triage.py            # all ported benchmarks
"""
from __future__ import annotations
import importlib.util
import json
import re
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent
_PORTED = _REPO / "benchmarks" / "verina"
_VERINA = Path("/private/tmp/verina-data/datasets/verina")


def _verina_shape(ret: str) -> str:
    r = ret.strip()
    if "Array (Array" in r or "Array Array" in r:
        return "2d-array"
    if r.startswith("Array"):
        return "1d-array"
    # tuple/product return -> multi; treat as its own bucket
    if "×" in r or "Prod" in r:
        return "tuple"
    return "scalar"   # Int / Nat / Bool


def _our_shape(problem) -> str:
    # Our output(s): the Var(s) in problem.outputs.  If any output is
    # an array type, the result is array-shaped; else scalar.
    outs = list(problem.outputs)
    if not outs:
        return "none"
    types = [v.type for v in outs]
    if any("[][]" in t for t in types):
        return "2d-array"
    if any(t.endswith("[]") for t in types):
        return "1d-array"
    if len(outs) > 1:
        return "tuple"
    return "scalar"


def _load(vid: str):
    path = _PORTED / vid / "problem.py"
    if not path.is_file():
        flat = sorted(_PORTED.glob(f"{vid}_*.py"))
        path = flat[0] if flat else path
    spec = importlib.util.spec_from_file_location(f"{vid}_p", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _vid(stem: str) -> str:
    m = re.match(r"(verina_basic_\d+)", stem)
    return m.group(1) if m else stem


def main() -> int:
    # Per-task dir layout (<vid>/problem.py) + legacy flat.
    stems = sorted({d.name for d in _PORTED.glob("verina_basic_*")
                    if (d / "problem.py").is_file()}
                   | {_vid(p.stem) for p in _PORTED.glob("verina_basic_*.py")},
                   key=lambda s: int(s.rsplit("_", 1)[1]))
    drifts, oks, reviews = [], [], []
    for stem in stems:
        vid = _vid(stem)
        try:
            problem = _load(stem)
            tj = json.loads((_VERINA / vid / "task.json").read_text())
            vret = tj["signature"].get("return_type", "")
            vshape = _verina_shape(vret)
            oshape = _our_shape(problem)
            row = (stem, vshape, oshape, vret)
            if oshape == "none" or vshape == "tuple" or oshape == "tuple":
                reviews.append(row)
            elif vshape != oshape:
                drifts.append(row)
            else:
                oks.append(row)
        except Exception as e:  # noqa: BLE001
            reviews.append((stem, "?", f"ERR:{type(e).__name__}", str(e)[:60]))

    print(f"Output-shape drift triage — {len(stems)} ported benchmarks\n")
    print(f"OK (shape matches): {len(oks)}")
    print(f"DRIFT (shape mismatch — near-certain mis-port): {len(drifts)}")
    print(f"REVIEW (tuple / unusual): {len(reviews)}\n")
    if drifts:
        print("=== DRIFTS ===")
        for stem, vs, os_, vret in drifts:
            print(f"  {stem:44s} VERINA={vs:9s} ({vret})  ours={os_}")
    if reviews:
        print("\n=== REVIEW ===")
        for stem, vs, os_, vret in reviews:
            print(f"  {stem:44s} VERINA={vs:9s}  ours={os_}  ({vret})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
