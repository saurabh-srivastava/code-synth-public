"""VERINA-basic portability triage — search-based-verina-proving campaign.

Reads the 108 VERINA-basic tasks from a local clone of
`sunblaze-ucb/verina` and classifies each by whether this
repo's synthesizer IR can EXPRESS it at all — independent of
whether synthesis then succeeds.  This produces the honest
denominator for the campaign: "of 108 VERINA-basic tasks, N
are expressible in our IR; the rest are out of reach because
of <reason>."

Our IR reach (as of this campaign):
  - Scalar types: Int (`int`), Nat (approximated as int with
    a `>= 0` precond), Bool (int 0/1).
  - Arrays: 1D `Array Int` (`int[]`), 2D `Array (Array Int)`
    (`int[][]`).
  - Control flow: straight-line SB, single/nested Loop, Recur.
  - Specs: pre/post as quantifier-bounded predicates over the
    above; uninterpreted functions + recurrence axioms for
    fold-style accumulations.

Two kinds of "not expressible today":

  - **encodable-not-yet** (engineering gap, NOT a fundamental
    limit): String and Char are integer / codepoint sequences;
    List is our Array; tuples / `×` are multiple outputs (which
    the IR already supports — one output per component); Option
    is a tag+value or sentinel encoding; Map is UF- or
    array-backed; a higher-order `Int → Bool` parameter is
    UF-encodable with axioms.  All of these are expressible in
    the integer-array + multi-output + UF substrate; we just
    haven't written the encodings yet.

  - **fundamental** (plausibly a real limit): Float / Real /
    Rat — non-integer numerics.  Z3 and Lean both have real
    arithmetic, so even this may be "not yet" rather than
    "never", but it is the one class that is not obviously an
    afternoon of encoding.  Flagged separately, not lumped in
    with the engineering gaps.

Usage:
  python verina/triage.py [--verina-root /path/to/verina/clone]

Default root: /private/tmp/verina-data (the campaign clone).

Output: a per-task table + summary counts to stdout, and a
machine-readable `verina/triage.json` for downstream porting.
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path


# Types our IR can model directly (after Nat->int lowering).
_IR_SCALAR = {"Int", "Nat", "Bool"}
_IR_ARRAY = {"Array Int", "Array Nat", "Array Bool"}
_IR_ARRAY2D = {"Array (Array Int)", "Array (Array Nat)"}
_IR_OK = _IR_SCALAR | _IR_ARRAY | _IR_ARRAY2D

# Non-integer numerics: the one class that is plausibly a
# fundamental limit rather than an unwritten encoding.
_FUNDAMENTAL_MARKERS = ["Float", "Real", "Rat"]

# Encodable in the integer-array + multi-output + UF substrate;
# we simply haven't written the encoding yet.  NOT fundamental
# limits.  (String/Char = int/codepoint sequences; List = Array;
# Prod/× = multiple outputs, already supported; Option = tag+value;
# Map = UF/array-backed; `→` param = UF with axioms.)
_NOT_YET_ENCODED_MARKERS = [
    "String", "Char",
    "List",
    "Option", "Except", "Prod", "×",
    "Map",
    "→", "->",          # higher-order param (UF-encodable with axioms)
    "UInt", "BitVec",   # fixed-width / bitvector — Z3 BV theory, not-yet
    "Structure", "structure",
]


def _extract_marker(text: str, name: str) -> str | None:
    """Pull the body between `-- !benchmark @start <name>` and
    `-- !benchmark @end <name>`.  Returns stripped body or None."""
    pat = (rf"--\s*!benchmark\s*@start\s+{re.escape(name)}\b(.*?)"
           rf"--\s*!benchmark\s*@end\s+{re.escape(name)}\b")
    m = re.search(pat, text, flags=re.DOTALL)
    if not m:
        return None
    return m.group(1).strip()


def _classify_type(t: str) -> str:
    """Return 'ok' | 'fundamental:<m>' | 'notyet:<m>' | 'unknown:<t>'
    for a single Lean type string."""
    t = t.strip()
    for marker in _FUNDAMENTAL_MARKERS:
        if marker in t:
            return f"fundamental:{marker}"
    for marker in _NOT_YET_ENCODED_MARKERS:
        if marker in t:
            return f"notyet:{marker}"
    if t in _IR_OK:
        return "ok"
    # Unknown type we haven't seen — flag for manual review
    # rather than silently counting it in or out.
    return f"unknown:{t}"


def triage_task(task_dir: Path) -> dict:
    tj = json.loads((task_dir / "task.json").read_text())
    sig = tj["signature"]
    lean = (task_dir / "task.lean").read_text()

    param_types = [p["param_type"] for p in sig.get("parameters", [])]
    ret_type = sig.get("return_type", "")
    all_types = param_types + [ret_type]

    # Type-reachability verdict.
    type_verdicts = {t: _classify_type(t) for t in set(all_types)}
    fundamental_reasons = sorted({v.split(":", 1)[1]
                                  for v in type_verdicts.values()
                                  if v.startswith("fundamental:")})
    notyet_reasons = sorted({v.split(":", 1)[1]
                             for v in type_verdicts.values()
                             if v.startswith("notyet:")})
    unknown_types = sorted({v.split(":", 1)[1]
                            for v in type_verdicts.values()
                            if v.startswith("unknown:")})

    precond = _extract_marker(lean, "precond") or ""
    postcond = _extract_marker(lean, "postcond") or ""
    code = _extract_marker(lean, "code") or ""

    # Structural signals of the postcondition.
    post_has_forall = ("∀" in postcond)
    post_has_exists = ("∃" in postcond)
    post_array_index = bool(re.search(r"\[\s*\w+\s*\]!?", postcond))
    precond_trivial = (precond.strip() in ("True", ""))

    # Coarse reach verdict.  Fundamental (Float/Real) only counts
    # if there is NO accompanying not-yet-encoded blocker — we
    # attribute a task to the harder of its blockers, but keep
    # "fundamental" reserved for tasks whose ONLY obstacle is
    # non-integer numerics.
    if unknown_types:
        reach = "review"
    elif fundamental_reasons and not notyet_reasons:
        reach = "fundamental"
    elif notyet_reasons or fundamental_reasons:
        reach = "encodable-not-yet"
    else:
        reach = "expressible"

    # Coarse shape guess (for later template selection).
    has_array_param = any(t in _IR_ARRAY or t in _IR_ARRAY2D
                          for t in param_types)
    array_out = ret_type in _IR_ARRAY or ret_type in _IR_ARRAY2D
    if not has_array_param and not array_out:
        shape = "scalar"
    elif array_out and has_array_param:
        shape = "array->array"
    elif has_array_param and not array_out:
        shape = "array->scalar"
    else:
        shape = "scalar->array"

    return {
        "id": tj["id"],
        "name": sig.get("name", ""),
        "param_types": param_types,
        "return_type": ret_type,
        "reach": reach,
        "fundamental_reasons": fundamental_reasons,
        "notyet_reasons": notyet_reasons,
        "unknown_types": unknown_types,
        "shape": shape,
        "precond_trivial": precond_trivial,
        "post_has_forall": post_has_forall,
        "post_has_exists": post_has_exists,
        "post_array_index": post_array_index,
        "code_len": len(code),
        "postcond": postcond,
        "precond": precond,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--verina-root", default="/private/tmp/verina-data")
    ap.add_argument("--out", default="verina/triage.json")
    args = ap.parse_args()

    root = Path(args.verina_root) / "datasets" / "verina"
    if not root.is_dir():
        print(f"ERROR: {root} not found.  Clone sunblaze-ucb/verina "
              f"first (see verina/README.md).", file=sys.stderr)
        return 1

    task_dirs = sorted(
        (d for d in root.glob("verina_basic_*") if d.is_dir()),
        key=lambda p: int(p.name.rsplit("_", 1)[1]),
    )
    rows = [triage_task(d) for d in task_dirs]

    # Summary counts.
    n = len(rows)
    by_reach: dict[str, int] = {}
    by_shape: dict[str, int] = {}
    notyet_counts: dict[str, int] = {}
    fundamental_counts: dict[str, int] = {}
    for r in rows:
        by_reach[r["reach"]] = by_reach.get(r["reach"], 0) + 1
        by_shape[r["shape"]] = by_shape.get(r["shape"], 0) + 1
        for reason in r["notyet_reasons"]:
            notyet_counts[reason] = notyet_counts.get(reason, 0) + 1
        for reason in r["fundamental_reasons"]:
            fundamental_counts[reason] = fundamental_counts.get(reason, 0) + 1

    print(f"VERINA-basic triage — {n} tasks\n")
    print("Reach:")
    for k in sorted(by_reach):
        print(f"  {k:18s} {by_reach[k]:3d}")
    print("\nShape (all tasks):")
    for k in sorted(by_shape):
        print(f"  {k:18s} {by_shape[k]:3d}")
    print("\nNot-yet-encoded type markers (engineering gaps, encodable):")
    for k in sorted(notyet_counts, key=lambda x: -notyet_counts[x]):
        print(f"  {k:18s} {notyet_counts[k]:3d}")
    print("\nFundamental-limit type markers (non-integer numerics):")
    for k in sorted(fundamental_counts, key=lambda x: -fundamental_counts[x]):
        print(f"  {k:18s} {fundamental_counts[k]:3d}")

    expressible = [r for r in rows if r["reach"] == "expressible"]
    print(f"\nExpressible-in-IR shape breakdown ({len(expressible)}):")
    esh: dict[str, int] = {}
    for r in expressible:
        esh[r["shape"]] = esh.get(r["shape"], 0) + 1
    for k in sorted(esh):
        print(f"  {k:16s} {esh[k]:3d}")

    Path(args.out).write_text(json.dumps(rows, indent=2))
    print(f"\nWrote {args.out} ({len(rows)} rows).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
