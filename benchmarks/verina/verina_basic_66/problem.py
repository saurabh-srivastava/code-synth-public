"""verina_basic_66 — ComputeIsEven (VERINA-basic port).

Determine whether an integer x is even.  Returns a boolean, which we
encode as an int r ∈ {0, 1} (1 = true = even, 0 = false = odd).

Template: `SB(n=2)` — one acyclic block, two guarded branches
(even / odd), exactly the shape of `abs.py`.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_66):
    precond  : True
    code     : if x % 2 = 0 then true else false
    postcond : result = true ↔ ∃ k : Int, x = 2 * k

Port mapping
------------
    * VERINA `x : Int`      → our `Var("x", "int", "input")`.
    * VERINA `result : Bool`→ our `Var("r", "int", "output")`, with the
      Bool→int convention true=1 / false=0.
    * VERINA precond `True` → our `pre = "true"`.
    * VERINA postcond `result = true ↔ ∃ k, x = 2*k` → our
      `post = "(r == 1) == Exists(lambda k: x == 2 * k)"`.
      The biconditional `↔` is Z3 boolean-equality (`Bool == Bool`),
      and the existential is ported LITERALLY via `Exists(lambda k: ...)`
      — no reinterpretation of the spec into a mod predicate.  The
      branch guards use `x % 2 == 0` / `x % 2 != 0`; Z3's Euclidean mod
      lets it discharge both directions of the ↔ against the raw
      existential (even branch: instantiate k = x div 2; odd branch:
      skolemize k, `2*k % 2 = 0` contradicts `x % 2 != 0`).

Fidelity: the postcondition is the VERINA existential verbatim, so the
port is exact (no equivalence lemma interposed on the spec side).

Pure Z3 — no UF, no axioms, no Lean dispatch (expected_lean_hits = 0).

Spec:
    Pre  : true
    Post : (r == 1) ↔ (∃ k. x == 2*k)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return 1 if x is even (there exists an "
        "integer k with x = 2*k) and 0 otherwise."
    ),

    template = SB(n=2),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "true",
    post     = "(r == 1) == Exists(lambda k: x == 2 * k)",

    atoms = {
        # Branch 0 — x is even: return 1.
        "g@B0.0": ["x % 2 == 0"],
        "s@B0.0": [{"r": "1"}],
        # Branch 1 — x is odd (the "else"): return 0.  Coverage
        # `g@B0.0 ∨ g@B0.1 ≡ true` holds since (x%2==0) ∨ (x%2!=0).
        "g@B0.1": ["x % 2 != 0"],
        "s@B0.1": [{"r": "0"}],
    },

    max_solutions      = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_66/lean/SynthLean/Y2Corpus/verina_basic_66",
    wedge_threshold    = 200,
    solver_timeout_ms  = 60_000,
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
