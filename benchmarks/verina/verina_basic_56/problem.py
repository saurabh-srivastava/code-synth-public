"""verina_basic_56 (copy) — VERINA-basic port.

Segment copy: overwrite the length-`len` window of `dest` starting at
`dStart` with the length-`len` window of `src` starting at `sStart`,
leaving every other element of `dest` unchanged.  This is a pointwise
array-write with offsets (no accumulation), so it is PURE Z3 with a
quantified prefix invariant — no UF, no axioms.  Shape mirrors
`array_shift_right` / `array_rotate_left`: the output array is `dest`
written in place, and a ghost input array `D0` holds dest's ORIGINAL
values so the postcondition can refer to them.

VERINA source (source of truth):
  signature : copy (src : Array Int) (sStart : Nat) (dest : Array Int)
                   (dStart : Nat) (len : Nat) -> Array Int
  precond   : src.size  >= sStart + len  ∧  dest.size >= dStart + len
  code      : if len = 0 then dest
              else updateSegment dest src sStart dStart len
              (updateSegment recursively sets dest[dStart+n] := src[sStart+n]
               for n = len-1 .. 0)
  postcond  : result.size = dest.size
              ∧ (∀ i, i < dStart            → result[i]! = dest[i]!)
              ∧ (∀ i, dStart+len <= i, i < result.size
                                           → result[i]! = dest[i]!)
              ∧ (∀ i, i < len              → result[dStart+i]! = src[sStart+i]!)

Fidelity mapping:
  - VERINA `src : Array Int`         -> our read-only input array `src`.
  - VERINA `dest : Array Int`        -> our in-place output array `dest`;
                                        its ORIGINAL values are captured by
                                        the ghost input `D0` (pre pins
                                        ForAll k. D0[k] == dest[k]).  So
                                        `dest[i]!` in VERINA's postcond
                                        (the original dest) maps to `D0[i]`.
  - VERINA `sStart, dStart, len` (Nat)
                                     -> int inputs sStart, dStart, len, each
                                        with an implied `>= 0` (Nat).
                                        Renamed nothing; `len` is used as an
                                        expression variable only.
  - `result.size = dest.size`        -> dropped: our arrays are unbounded Z3
                                        maps (no explicit size), and the
                                        SB()>>Loop>>SB() shape only writes
                                        `dest` in place, so length is
                                        preserved by construction.
  - `∀ i < dStart. result[i]! = dest[i]!`
                                     -> ForAll k. k < dStart => dest[k]==D0[k].
  - `∀ dStart+len<=i<size. result[i]!=dest[i]!`
                                     -> ForAll k. dStart+len<=k => dest[k]==D0[k]
                                        (the `i < size` guard is a bounds
                                        guard, vacuous in the unbounded model).
  - `∀ i < len. result[dStart+i]! = src[sStart+i]!`
                                     -> ForAll k. 0<=k<len =>
                                        dest[dStart+k] == src[sStart+k].
  - VERINA precond `src.size >= sStart+len ∧ dest.size >= dStart+len`
                                     -> has no counterpart in the unbounded
                                        model (no out-of-bounds is possible);
                                        we keep only the Nat non-negativity
                                        `sStart>=0 ∧ dStart>=0 ∧ len>=0`.

  The `len = 0` branch of VERINA's code is subsumed: with len==0 the loop
  runs zero iterations and the two "unchanged" conjuncts (plus the vacuous
  segment conjunct) hold immediately, matching `if len = 0 then dest`.

No auxiliary fold/sum/count/product function is referenced by the
postcondition, so no UF is introduced — pure Z3.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a source array src, a destination array dest, start "
        "indices sStart and dStart (both >= 0), and a length len (>= 0), "
        "overwrite dest[dStart .. dStart+len) with src[sStart .. sStart+len) "
        "and leave every other element of dest unchanged.  D0 is a ghost "
        "copy pinning dest's original values."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("src", "int[]", "input"),
                Var("dest", "int[]", "input"),
                Var("D0", "int[]", "input"),        # ghost: original dest
                Var("sStart", "int", "input"),
                Var("dStart", "int", "input"),
                Var("len", "int", "input")],
    outputs  = [Var("dest", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = (
        "(sStart >= 0) and (dStart >= 0) and (len >= 0) and "
        "ForAll(lambda k: D0[k] == dest[k])"
    ),
    post     = (
        # prefix (i < dStart) unchanged
        "ForAll(lambda k: Implies(k < dStart, dest[k] == D0[k])) and "
        # suffix (dStart+len <= i) unchanged
        "ForAll(lambda k: Implies(dStart + len <= k, dest[k] == D0[k])) and "
        # copied segment
        "ForAll(lambda k: Implies(0 <= k and k < len, "
        "dest[dStart + k] == src[sStart + k]))"
    ),

    atoms = {
        # Init: start the segment cursor at 0.
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= len",
            # Copied-so-far: first i segment slots already carry src.
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "dest[dStart + k] == src[sStart + k]))"),
            # Prefix (left of the window) never touched -> equals original.
            "ForAll(lambda k: Implies(k < dStart, dest[k] == D0[k]))",
            # Suffix (right of the window) never touched -> equals original.
            "ForAll(lambda k: Implies(dStart + len <= k, dest[k] == D0[k]))",
        ],
        "g@L0":   ["i < len"],
        "phi@L0": ["len - i"],

        # Body: dest[dStart + i] := src[sStart + i]; i := i + 1.
        "s@B1": [{"dest": "Update(dest, dStart + i, src[sStart + i])",
                  "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_56/lean/SynthLean/Y2Corpus/verina_basic_56",
    wedge_threshold = 200,
    solver_timeout_ms = 120_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
