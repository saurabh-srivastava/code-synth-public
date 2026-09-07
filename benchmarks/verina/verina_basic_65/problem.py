"""verina_basic_65 — SquareRoot (integer square root), scalar shape.

Ported from VERINA task `verina_basic_65` (upstream: Clover
`Clover_integer_square_root`).  Source of truth:
`/private/tmp/verina-data/datasets/verina/verina_basic_65/{task.json,task.lean}`.

VERINA spec (verbatim from the @start/@end markers):
  * signature : SquareRoot (N : Nat) -> Nat
  * precond   : True
  * code      : boundedLoop that starts r := 0 and increments r while
                (r + 1) * (r + 1) <= N, returning r otherwise.
  * postcond  : result * result <= N  ∧  N < (result + 1) * (result + 1)

Fidelity mapping (Nat -> int with implied >= 0):
  * N : Nat            ->  Var("N", "int")   with  pre = "N >= 0".
  * result r : Nat     ->  Var("r", "int")   (the output; r >= 0 is a
                           loop invariant atom, so the returned r is
                           non-negative, matching the Nat return type).
  * post (verbatim)    ->  "r*r <= N and N < (r + 1)*(r + 1)".

The postcondition is transcribed one-for-one; no auxiliary
fold/sum/count function is involved, so there is NO uninterpreted
function and NO axiom — the fidelity claim is exact.

Algorithm / proof witness (matches VERINA's boundedLoop reference):
    r := 0
    while (r + 1)*(r + 1) <= N:
        r := r + 1
    // post: r*r <= N  and  N < (r + 1)*(r + 1)

    τ : r*r <= N  ∧  r >= 0
    g : (r + 1)*(r + 1) <= N
    ϕ : N - r          (linear; strictly decreases, bounded below by 0
                        because r*r <= N ∧ r >= 0 ⟹ r <= N)

The loop guard `(r + 1)*(r + 1) <= N` is *exactly* the inductive
conclusion `r'*r' <= N` after the update `r := r + 1`, and its
negation at loop exit is *exactly* the second post conjunct
`N < (r + 1)*(r + 1)`.  So Z3's NIA closes every obligation without
a running-square local (contrast `intsqrt.py`, which keeps `v == i*i`
under a different `(i-1)² <= x < i²` parametrization).  Pure Z3;
expected_lean_hits = 0.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1)),
    inputs   = [Var("N", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "N >= 0",
    post     = "r*r <= N and N < (r + 1)*(r + 1)",

    atoms = {
        # SB B0 — entry: r := 0.
        "s@B0": [
            {"r": "0"},                 # published
            {"r": "1"},                 # wrong start (misses r == 0 case)
            {"r": "N"},                 # far too big
        ],
        # Loop L0 invariant.
        "tau@L0": [
            "r*r <= N",                 # published #1 — r is a valid lower bound
            "r >= 0",                   # published #2 — non-negativity (Nat)
            "r <= N",                   # weaker distractor
            "r*r < N",                  # too strict (fails at perfect squares)
        ],
        "g@L0": [
            "(r + 1)*(r + 1) <= N",     # published — matches inductive conclusion
            "(r + 1)*(r + 1) < N",      # off-by-one
            "r*r <= N",                 # too weak — never terminates correctly
        ],
        "phi@L0": [
            "N - r",                    # published — linear, decreases by 1
            "N - r*r",                  # also valid — decreases faster
            "r",                        # wrong direction (increases)
        ],
        # Loop body B1 — r := r + 1.
        "s@B1": [
            {"r": "r + 1"},             # published
            {"r": "r + 2"},             # skips candidates
            {"r": "r"},                 # no progress (non-terminating)
        ],
    },
    max_solutions = 1,          # cap at the single best-scored verified
                                # solution -> "Found 1 solution(s)".
    expected_solutions = 1,
    expected_lean_hits = 0,     # pure Z3 NIA; no Lean dispatch expected.
    wedge_threshold = 200,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_65/lean/SynthLean/Y2Corpus/verina_basic_65",
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
        print("  choices:")
        for hid, k in sorted(sol.choices.items()):
            print(f"    {hid:10s}  →  [#{k}]  {sol.atoms[hid]!r}")
