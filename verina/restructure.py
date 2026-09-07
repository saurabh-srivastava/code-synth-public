"""Restructure ported VERINA benchmarks into self-contained per-task dirs.

Converts the flat fan-out layout
  benchmarks/verina/<vid>_<name>.py
  lean/SynthLean/Y2Corpus/<vid>_<name>/*.solved.lean
into one directory per task
  benchmarks/verina/<vid>/...

FAITHFUL tasks (verified + post faithfully captures VERINA) get the
full self-contained bundle:
  README.md, nl.txt, verina-spec.md, problem.py, synthesized.py,
  invariants.md, fidelity-verdict.md,
  lean/SynthLean/Y2Corpus/<vid>/*.solved.lean

NON-FAITHFUL tasks (partial-fidelity / synth-wedge / mis-port /
not-expressible) get ONLY a single `<category>.md` holding the
serialized data (a JSON block) + a detailed prose note on the
outcome — not the full contingent.

Run once after the fan-out + fidelity pass:
  python verina/restructure.py
Then re-verify the UF tasks, extend the CI scanner, and commit.
"""
from __future__ import annotations
import importlib.util
import json
import re
import shutil
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent
_PORTED = _REPO / "benchmarks" / "verina"
_CORPUS = _REPO / "lean" / "SynthLean" / "Y2Corpus"
_VERINA = Path("/private/tmp/verina-data/datasets/verina")

sys.path.insert(0, str(_REPO / "verina"))
import materialize_e2e as M   # noqa: E402
import specgen_check as S     # noqa: E402

# ── Classification (from the fidelity + wedge analysis) ─────────
PARTIAL = {
    "verina_basic_52": "sortedness asserted WITHOUT the permutation clause "
                       "VERINA requires (`List.isPerm result a`).  Our post "
                       "is `∀p≤q. A[p]≤A[q]` only, so e.g. an all-zeros "
                       "output would satisfy it.  Verified, but against a "
                       "spec strictly weaker than VERINA's.",
    "verina_basic_87": "same as BubbleSort: our post asserts sortedness only, "
                       "not that the result is a permutation of the input.",
}
WEDGE = {
    "verina_basic_22": "synth wedged — no solution within 120s wall (25s "
                       "per-query Z3 budget).  The port's post (sorted + "
                       "nodup + set-symmetric-difference membership) is "
                       "faithful, but the set-difference + nodup reasoning "
                       "over two arrays exceeded the search budget.",
    "verina_basic_35": "synth reached Lean dispatch and wedged on the first "
                       "safety obligation (sc2, L0 branch 0).  The stable-"
                       "partition (move-zeroes) invariant needs the `nz` "
                       "compaction-index UF preserved across a quantified "
                       "Store — the multiset/permutation E-matching cliff.",
}
MISPORT = {
    "verina_basic_60": "MIS-PORT.  VERINA's findEvenNumbers RETURNS the array "
                       "of even elements (order + multiplicity).  The fan-out "
                       "agent, unable to express the data-dependent-length "
                       "filter, silently reformulated it as COUNTING the "
                       "evens — output `c : int`, post `c == count_even(A,n)`. "
                       "That verifies, but solves a different problem.  Caught "
                       "by drift_triage.py (output shape scalar != VERINA's "
                       "Array Int).  A verifying benchmark that answers the "
                       "wrong question is worse than a failure; excluded from "
                       "the faithful set.",
}
NOTEXPR = {
    "verina_basic_34": "NOT-EXPRESSIBLE (rigorous).  Filter with data-"
                       "dependent output length + multiplicity + order.  A "
                       "faithful index-encoded probe wedged 0/63 valid Lean "
                       "dispatches (52 elaboration errors).  Full analysis in "
                       "verina/reach-limits/verina_basic_34_findEvenNumbers.md.",
}


def _vid(stem: str) -> str:
    return re.match(r"(verina_basic_\d+)", stem).group(1)


def _category(vid: str) -> str:
    if vid in PARTIAL:
        return "partial-fidelity"
    if vid in WEDGE:
        return "synth-wedge"
    if vid in MISPORT:
        return "mis-port"
    if vid in NOTEXPR:
        return "not-expressible"
    return "faithful"


def _verina_spec(vid: str) -> dict:
    tj = json.loads((_VERINA / vid / "task.json").read_text())
    nl = (_VERINA / vid / "description.txt").read_text().strip() \
        if (_VERINA / vid / "description.txt").is_file() else ""
    lean = (_VERINA / vid / "task.lean").read_text() \
        if (_VERINA / vid / "task.lean").is_file() else ""
    return {
        "signature": tj.get("signature", {}),
        "nl": nl,
        "precond": M._marker(lean, "precond"),
        "code": M._marker(lean, "code"),
        "postcond": M._marker(lean, "postcond"),
    }


def _load_problem(stem: str):
    p = _PORTED / f"{stem}.py"
    spec = importlib.util.spec_from_file_location(stem, p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _fidelity_verdict(stem: str) -> str:
    try:
        return S._fmt(S.check_task(stem))
    except Exception as e:  # noqa: BLE001
        return f"(specgen_check unavailable: {type(e).__name__}: {e})"


def _write_faithful(stem: str, vid: str, dest: Path):
    problem = _load_problem(stem)
    v = _verina_spec(vid)
    py, rust, inv = M._synth_output(problem)
    dest.mkdir(parents=True, exist_ok=True)

    (dest / "nl.txt").write_text(v["nl"] + "\n")

    (dest / "verina-spec.md").write_text(
        f"# VERINA spec — {vid}\n\n"
        f"```json\n{json.dumps(v['signature'], indent=2)}\n```\n\n"
        f"```lean\n-- precondition\n{v['precond']}\n\n"
        f"-- reference code\n{v['code']}\n\n"
        f"-- postcondition\n{v['postcond']}\n```\n")

    (dest / "invariants.md").write_text(
        f"# Discovered invariant + ranking — {vid}\n\n```\n{inv}\n```\n")

    if py:
        (dest / "synthesized.py").write_text(py.rstrip() + "\n")

    (dest / "fidelity-verdict.md").write_text(
        f"# SpecGen fidelity — {vid}\n\n"
        f"VERINA's own test-based spec soundness/completeness check "
        f"(specgen_check.py) on the ported spec vs VERINA's concrete "
        f"tests:\n\n```\n{_fidelity_verdict(stem)}\n```\n")

    # problem.py with dump path repointed into this dir.
    src = (_PORTED / f"{stem}.py").read_text()
    new_dump = f"benchmarks/verina/{vid}/lean/SynthLean/Y2Corpus/{vid}"
    src = re.sub(r'dump_lean_failures_dir\s*=\s*"[^"]*"',
                 f'dump_lean_failures_dir = "{new_dump}"', src)
    (dest / "problem.py").write_text(src)

    # move .solved.lean companions (if any) into the task dir.
    old_lean = _CORPUS / stem
    n_solved = 0
    if old_lean.is_dir():
        newdir = dest / "lean" / "SynthLean" / "Y2Corpus" / vid
        newdir.mkdir(parents=True, exist_ok=True)
        for f in old_lean.glob("*.solved.lean"):
            shutil.copy(f, newdir / f.name)
            n_solved += 1
        shutil.rmtree(old_lean)

    verifier = "Z3 + Lean" if n_solved else "Z3 only"
    (dest / "README.md").write_text(
        f"# {vid} — {v['signature'].get('name','')}\n\n"
        f"VERINA-basic task ported to this repo's proof-theoretic "
        f"synthesizer and **faithfully verified** ({verifier}, "
        f"{n_solved} `.solved.lean` proof(s)).\n\n"
        f"| File | What |\n| --- | --- |\n"
        f"| `nl.txt` | VERINA natural-language statement |\n"
        f"| `verina-spec.md` | VERINA signature + precond / code / postcond |\n"
        f"| `problem.py` | our Problem spec (runnable) |\n"
        f"| `synthesized.py` | the synthesized program |\n"
        f"| `invariants.md` | discovered inductive invariant + ranking |\n"
        f"| `fidelity-verdict.md` | spec soundness/completeness vs VERINA's tests |\n"
        + ("| `lean/…/*.solved.lean` | the machine-checked Lean proofs |\n"
           if n_solved else "")
        + f"\nReproduce: `python benchmarks/verina/{vid}/problem.py`\n")
    return n_solved


def _write_nonfaithful(vid: str, cat: str, note: str, dest: Path):
    dest.mkdir(parents=True, exist_ok=True)
    v = _verina_spec(vid)
    data = {"id": vid, "name": v["signature"].get("name", ""),
            "category": cat, "verina_signature": v["signature"],
            "verina_precond": v["precond"], "verina_code": v["code"],
            "verina_postcond": v["postcond"]}

    # If a Problem was authored, serialize its spec too.
    stem = next((p.stem for p in _PORTED.glob(f"{vid}_*.py")), None)
    if stem:
        try:
            pr = _load_problem(stem)
            data["our_pre"] = pr.pre
            data["our_post"] = pr.post
            data["our_axioms"] = list(getattr(pr, "axioms", []))
            data["our_outputs"] = [(x.name, x.type) for x in pr.outputs]
        except Exception:  # noqa: BLE001
            pass

    (dest / f"{cat}.md").write_text(
        f"# {vid} — {cat.upper().replace('-', ' ')}\n\n"
        f"**{v['signature'].get('name','')}** — {v['nl'].splitlines()[1].strip() if len(v['nl'].splitlines())>1 else v['nl'][:120]}\n\n"
        f"## Outcome\n\n{note}\n\n"
        f"## Serialized data\n\n```json\n{json.dumps(data, indent=2)}\n```\n")


def main() -> int:
    stems = sorted(p.stem for p in _PORTED.glob("verina_basic_*.py"))
    counts = {"faithful": 0, "partial-fidelity": 0, "synth-wedge": 0,
              "mis-port": 0, "not-expressible": 0}
    total_solved = 0

    handled_vids = set()
    for stem in stems:
        vid = _vid(stem)
        cat = _category(vid)
        dest = _PORTED / vid
        handled_vids.add(vid)
        if cat == "faithful":
            total_solved += _write_faithful(stem, vid, dest)
        else:
            note = (PARTIAL | WEDGE | MISPORT | NOTEXPR)[vid]
            _write_nonfaithful(vid, cat, note, dest)
        counts[cat] += 1
        # remove the flat .py now that the dir is built.
        (_PORTED / f"{stem}.py").unlink()

    # not-expressible task 34 has no ported .py — build its dir directly.
    for vid, note in NOTEXPR.items():
        if vid not in handled_vids:
            _write_nonfaithful(vid, "not-expressible", note, _PORTED / vid)
            counts["not-expressible"] += 1

    print("Restructure complete:")
    for k, n in counts.items():
        print(f"  {k:16s} {n:3d}")
    print(f"  total .solved.lean moved: {total_solved}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
