"""SpecGen fidelity check — search-based-verina-proving campaign.

Adopts VERINA's test-based specification soundness/completeness
check (arXiv:2505.23135 §4.2) and applies it to the specs WE
consume when porting a VERINA task.  It answers the trust-surface
question raised in `../related-work/verina.md` §6:

  "Our pipeline proves the code correct w.r.t. OUR spec.  But
   does our spec actually mean what VERINA's spec means?"

Method (VERINA's, adapted to our eDSL):
  Instead of proving the universally-quantified soundness /
  completeness implications, evaluate our `pre`/`post` predicate
  strings on VERINA's concrete test cases:

    - pre soundness   : our pre accepts every valid test input.
    - pre completeness: our pre rejects every reject_inputs input.
    - post soundness  : our post accepts every (input, expected).
    - post completeness: our post rejects every (input, u) for u
      in the test's `unexpected` list.

Our `post` typically reads `result == UF(A, n)` where UF is
uninterpreted in the synthesizer (its meaning comes from the
Problem's axioms).  To evaluate concretely we supply an explicit
Python interpretation of each UF in `_UF_INTERP` below.  THAT
DICT IS THE FIDELITY CLAIM: "we assert VERINA's `sumTo` is
Python `sum`", checked against VERINA's own expected outputs.  If
the check passes, our UF re-axiomatization reproduces VERINA's
ground truth on every test — closing the spec-fidelity half of
the trust surface.  (The other half — that our axioms actually
*define* that function — is what the Lean proof establishes.)

Out-of-range array reads return 0, matching Lean's `getElem!`
default and making guarded quantifiers (`Implies(0<=k<n, ...)`)
safe to evaluate eagerly.

Usage:
  python verina/specgen_check.py --task verina_basic_47_array_sum
  python verina/specgen_check.py --all      # every ported task

Task name = the benchmark module stem under benchmarks/verina/,
which must also embed the VERINA id (verina_basic_<n>_...).
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent
_VERINA_ROOT = Path("/private/tmp/verina-data/datasets/verina")
_PORTED_DIR = _REPO / "benchmarks" / "verina"

_QUANT_BOUND = 64  # concrete range for ForAll/Exists over test arrays


# ── Explicit UF interpretations = the fidelity claim ────────────
# For each ported task, the concrete meaning we ASSERT for each
# uninterpreted function in the Problem's spec.  Verified against
# VERINA's expected outputs by this checker.  Keep the interp
# minimal and obviously-correct; the whole point is that a
# reviewer can eyeball "yes, sum means sum".
_UF_INTERP: dict[str, dict] = {
    "verina_basic_47_array_sum": {
        # VERINA: sumTo a a.size = sum of all elements.
        "sum": lambda A, n: sum(A[i] for i in range(n)),
    },
    "verina_basic_57_count_less_than": {
        # VERINA: foldl count of elements strictly < threshold.
        "count_less": lambda A, t, n: sum(1 for i in range(n) if A[i] < t),
    },
    # sign / swap tasks have no UFs — empty interp.
    "verina_basic_1_has_opposite_sign": {},
    "verina_basic_32_swap_first_last": {},
    # fan-out UF ports (fidelity claims for the auto-checked set).
    "verina_basic_18": {
        # VERINA: sum of decimal digits of n.
        "digitSum": lambda n: sum(int(d) for d in str(abs(int(n)))),
    },
    "verina_basic_23": {
        "arrmin": lambda A, n: min(A[i] for i in range(n)),
        "arrmax": lambda A, n: max(A[i] for i in range(n)),
    },
    "verina_basic_80": {
        "count_occ": lambda A, key, n: sum(1 for i in range(n) if A[i] == key),
    },
    "verina_basic_47": {"sum": lambda A, n: sum(A[i] for i in range(n))},
    "verina_basic_57": {
        "count_less": lambda A, t, n: sum(1 for i in range(n) if A[i] < t)},
}


# ── VERINA-var -> our-Problem-var mapping = part of the fidelity claim ──
# Ports use heterogeneous conventions (renamed params, a ghost copy
# of the input to name the pre-state, in-place array output, a
# differently-named output var).  This map states, per task, how
# VERINA's concrete test variables bind onto our Problem's
# variables — a reviewable declaration, not silent auto-magic.
#   vin       : VERINA test-input key -> our input var name.
#   result_var: our output var name to bind VERINA's `expected` to.
#   ghost     : our input var -> VERINA input key it copies (the
#               pre-state ghost convention, e.g. B == original A).
_PORT_MAP: dict[str, dict] = {
    "verina_basic_1": {
        "vin": {"a": "a", "b": "b"}, "result_var": "result", "ghost": {}},
    "verina_basic_32": {
        "vin": {"a": "A"}, "result_var": "A", "ghost": {"B": "a"}},
    "verina_basic_47": {
        "vin": {"a": "A"}, "result_var": "result", "ghost": {}},
    "verina_basic_57": {
        "vin": {"numbers": "A", "threshold": "threshold"},
        "result_var": "c", "ghost": {}},
}


class _SafeList(list):
    """List whose out-of-range read returns 0 (Lean getElem! default)."""
    def __getitem__(self, i):
        if isinstance(i, int) and (i < 0 or i >= len(self)):
            return 0
        return super().__getitem__(i)


def _parse_array_literal(s: str):
    """Parse a (possibly nested) Lean array literal `#[...]` into a
    _SafeList, honoring nested `#[...]` for 2D inputs."""
    s = s.strip()
    assert s.startswith("#[") and s.endswith("]"), s
    inner = s[2:-1].strip()
    if not inner:
        return _SafeList([])
    # Split top-level commas only (respect nested #[...] brackets).
    parts, depth, cur = [], 0, ""
    for ch in inner:
        if ch == "[":
            depth += 1
            cur += ch
        elif ch == "]":
            depth -= 1
            cur += ch
        elif ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    out = []
    for p in parts:
        p = p.strip()
        if p.startswith("#["):
            out.append(_parse_array_literal(p))
        else:
            out.append(int(p))
    return _SafeList(out)


def _parse_value(v):
    """Parse a VERINA test value ('#[1,2,3]', nested, ints, bools)."""
    if isinstance(v, bool):
        return 1 if v else 0
    if isinstance(v, (int, float)):
        return v
    if isinstance(v, str):
        s = v.strip()
        if s.startswith("#["):
            return _parse_array_literal(s)
        if s in ("true", "True"):
            return 1
        if s in ("false", "False"):
            return 0
        return int(s)
    if isinstance(v, list):
        return _SafeList(_parse_value(x) for x in v)
    return v


def _eval_env(uf_interp: dict) -> dict:
    """Namespace for evaluating our eDSL pre/post strings concretely."""
    def ForAll(f):
        return all(bool(f(k)) for k in range(0, _QUANT_BOUND))

    def Exists(f):
        return any(bool(f(k)) for k in range(0, _QUANT_BOUND))

    def Implies(p, q):
        return (not bool(p)) or bool(q)

    env = {
        "ForAll": ForAll, "Exists": Exists, "Implies": Implies,
        "And": lambda *a: all(bool(x) for x in a),
        "Or": lambda *a: any(bool(x) for x in a),
        "Not": lambda x: not bool(x),
        "abs": abs, "min": min, "max": max, "len": len,
        # eDSL boolean literals (Problem.pre defaults to "true").
        "true": True, "false": False, "True": True, "False": False,
    }
    env.update(uf_interp)
    return env


def _eval_pred(expr: str, inputs: dict, result, uf_interp: dict,
               result_var: str = "result") -> bool:
    """Evaluate a pre/post predicate string on concrete values.

    The namespace is passed as eval GLOBALS (not locals) so that
    lambdas defined inside the expression — e.g.
    `ForAll(lambda k: Implies(...))` — resolve helper names like
    `Implies` at call time (Python closures capture globals).

    When `result` is given, it is bound under the Problem's actual
    output variable name (`result_var` — may be `c`, `A`, ...) as
    well as the generic `result`."""
    g = _eval_env(uf_interp)
    g["__builtins__"] = {}
    g.update(inputs)
    if result is not None:
        g[result_var] = result
        g.setdefault("result", result)
    return bool(eval(expr, g))  # noqa: S307


def _load_problem(vid: str):
    """Load the Problem for a task by its VERINA id.  Supports both
    the per-task dir layout (benchmarks/verina/<vid>/problem.py) and
    the legacy flat layout (benchmarks/verina/<vid>_<name>.py)."""
    path = _PORTED_DIR / vid / "problem.py"
    if not path.is_file():
        flat = sorted(_PORTED_DIR.glob(f"{vid}_*.py"))
        if not flat:
            raise FileNotFoundError(f"no ported Problem for {vid}")
        path = flat[0]
    spec = importlib.util.spec_from_file_location(f"{vid}_problem", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _verina_id(name: str) -> str:
    m = re.match(r"(verina_basic_\d+)", name)
    if not m:
        raise ValueError(f"cannot extract VERINA id from {name}")
    return m.group(1)


def _auto_port_map(problem, vid: str) -> dict:
    """Best-effort VERINA-var -> our-var mapping when no manual
    _PORT_MAP entry exists.  Handles the common port conventions:
    renamed params (a->A, numbers->A, arr->A), a synthetic length
    input `n`, a pre-state ghost array (B pinned == A), and a
    possibly-renamed output var.  Falls back to positional matching.
    Not a fidelity guarantee — just enough to evaluate the spec on
    concrete tests; genuine drifts still surface as GAPs/errors."""
    tj = json.loads((_VERINA_ROOT / vid / "task.json").read_text())
    vparams = tj["signature"].get("parameters", [])
    vnames = {p["param_name"] for p in vparams}
    our_types = {v.name: v.type for v in problem.inputs}
    our_names = [v.name for v in problem.inputs]

    # `n` is synthetic iff we declare it but VERINA has no such param.
    primary = [nm for nm in our_names
               if not (nm == "n" and "n" not in vnames)]

    vin: dict[str, str] = {}
    remaining = list(primary)
    for p in vparams:
        pn = p["param_name"]
        cand = next((nm for nm in remaining if nm == pn), None) \
            or next((nm for nm in remaining if nm.lower() == pn.lower()), None) \
            or (remaining[0] if remaining else None)
        if cand:
            vin[pn] = cand
            remaining.remove(cand)

    # Leftover primary array inputs are pre-state ghosts of the first
    # VERINA array param (the B==A convention).
    v_arr = [p["param_name"] for p in vparams
             if p["param_type"].strip().startswith("Array")]
    ghost = {nm: v_arr[0] for nm in remaining
             if our_types.get(nm, "").endswith("[]") and v_arr}

    result_var = problem.outputs[0].name if problem.outputs else "result"
    return {"vin": vin, "result_var": result_var, "ghost": ghost,
            "_auto": True}


def _bind_inputs(problem, port: dict, raw_input: dict) -> dict:
    """Map a VERINA test's raw input dict onto our Problem's input
    variables, using the task's explicit _PORT_MAP entry.  Fills the
    implicit array-length `n` and any pre-state ghost copies."""
    vin = port["vin"]
    parsed = {k: _parse_value(v) for k, v in raw_input.items()}
    env: dict = {}
    # VERINA key -> our input var.
    for vkey, our in vin.items():
        if vkey in parsed:
            env[our] = parsed[vkey]
    # Ghost copies (pre-state): our_var := VERINA input it copies.
    for our, vkey in port.get("ghost", {}).items():
        if vkey in parsed:
            env[our] = parsed[vkey]
    # Implicit length inputs: any int input we declare that VERINA
    # does not pass is a synthetic array length.  `n` -> first array;
    # `n<x>` (na, nb, ...) -> length of the array bound from VERINA
    # param <x>; else positional over the bound arrays in order.
    arrays_in_order = [env[our] for p in port["vin"]
                       for our in [port["vin"][p]]
                       if isinstance(env.get(our), list)]
    fallback_arr = arrays_in_order[0] if arrays_in_order else \
        next((x for x in env.values() if isinstance(x, list)), None)
    for v in problem.inputs:
        if v.name in env or v.type != "int":
            continue
        nm = v.name
        if nm == "n":
            if fallback_arr is not None:
                env["n"] = len(fallback_arr)
        elif re.fullmatch(r"n[a-zA-Z]\w*", nm) or nm.startswith("len"):
            suffix = nm[1:] if nm.startswith("n") else nm[3:]
            our = port["vin"].get(suffix) or port["vin"].get(suffix.lower())
            arr = env.get(our) if our else None
            if not isinstance(arr, list):
                arr = fallback_arr
            if isinstance(arr, list):
                env[nm] = len(arr)
    return env


def check_task(task: str) -> dict:
    """`task` is a VERINA id (verina_basic_<n>) or a legacy flat stem."""
    vid = _verina_id(task)
    problem = _load_problem(vid)
    uf_interp = _UF_INTERP.get(vid, {})

    tdir = _VERINA_ROOT / vid
    tests = json.loads((tdir / "test.json").read_text())
    rejects = json.loads((tdir / "reject_inputs.json").read_text())

    pre, post = problem.pre, problem.post
    port = _PORT_MAP.get(vid) or _auto_port_map(problem, vid)
    rvar = port["result_var"]

    res = {"task": vid, "id": vid,
           "pre_sound": [0, 0], "pre_complete": [0, 0],
           "post_sound": [0, 0], "post_complete": [0, 0],
           "errors": []}

    def _inp(raw):
        return _bind_inputs(problem, port, raw["input"])

    # Precondition soundness: pre accepts every valid test input.
    for t in tests:
        inp = _inp(t)
        res["pre_sound"][1] += 1
        try:
            if _eval_pred(pre, inp, None, uf_interp, rvar):
                res["pre_sound"][0] += 1
        except Exception as e:  # noqa: BLE001
            res["errors"].append(f"pre_sound {inp}: {type(e).__name__}: {e}")

    # Precondition completeness: pre rejects every reject input.
    for r in rejects:
        inp = _inp(r)
        res["pre_complete"][1] += 1
        try:
            if not _eval_pred(pre, inp, None, uf_interp, rvar):
                res["pre_complete"][0] += 1
        except Exception as e:  # noqa: BLE001
            res["errors"].append(f"pre_complete {inp}: {type(e).__name__}: {e}")

    # Postcondition soundness: post accepts (input, expected).
    for t in tests:
        inp = _inp(t)
        exp = _parse_value(t["expected"])
        res["post_sound"][1] += 1
        try:
            if _eval_pred(post, inp, exp, uf_interp, rvar):
                res["post_sound"][0] += 1
        except Exception as e:  # noqa: BLE001
            res["errors"].append(f"post_sound {inp}: {type(e).__name__}: {e}")

    # Postcondition completeness: post rejects (input, unexpected).
    for t in tests:
        inp = _inp(t)
        for u in t.get("unexpected", []):
            uv = _parse_value(u)
            res["post_complete"][1] += 1
            try:
                if not _eval_pred(post, inp, uv, uf_interp, rvar):
                    res["post_complete"][0] += 1
            except Exception as e:  # noqa: BLE001
                res["errors"].append(
                    f"post_complete {inp} u={uv}: {type(e).__name__}: {e}")
    return res


def _fmt(res: dict) -> str:
    def rate(pair):
        got, tot = pair
        mark = "OK " if got == tot else "XX "
        return f"{mark}{got}/{tot}"
    lines = [f"  pre  soundness    {rate(res['pre_sound'])}",
             f"  pre  completeness {rate(res['pre_complete'])}",
             f"  post soundness    {rate(res['post_sound'])}",
             f"  post completeness {rate(res['post_complete'])}"]
    if res["errors"]:
        lines.append(f"  errors: {len(res['errors'])} (first: "
                     f"{res['errors'][0]})")
    passed = all(res[k][0] == res[k][1] for k in
                 ("pre_sound", "pre_complete", "post_sound", "post_complete"))
    header = f"[{'FIDELITY OK' if passed and not res['errors'] else 'GAP'}] {res['task']}"
    return header + "\n" + "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", help="ported module stem under benchmarks/verina/")
    ap.add_argument("--all", action="store_true")
    args = ap.parse_args()

    if args.all:
        # Per-task dir layout (<vid>/problem.py) + legacy flat.
        stems = sorted({d.name for d in _PORTED_DIR.glob("verina_basic_*")
                        if (d / "problem.py").is_file()}
                       | {_verina_id(p.stem)
                          for p in _PORTED_DIR.glob("verina_basic_*.py")},
                       key=lambda s: int(s.rsplit("_", 1)[1]))
        if not stems:
            print("no ported tasks under benchmarks/verina/", file=sys.stderr)
            return 1
    elif args.task:
        stems = [args.task]
    else:
        ap.error("pass --task <stem> or --all")

    ok = True
    for stem in stems:
        try:
            res = check_task(stem)
            print(_fmt(res))
        except Exception as e:  # noqa: BLE001
            print(f"[ERROR] {stem}: {type(e).__name__}: {e}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
