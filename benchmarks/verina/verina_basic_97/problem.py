"""verina_basic_97 — TestArrayElements (VERINA-basic port).

Set the element at a given valid index j to the constant 60;
leave every other element unchanged.  Pure acyclic single write —
one `Update`, constant value.  Same shape as `swap_first_last` /
`array_swap`, but simpler (a single Update, no exchange).

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_97):

    signature : TestArrayElements (a : Array Int) (j : Nat) : Array Int
    code      : a.set! j 60
    precond   : j < a.size
    postcond  : result.size = a.size ∧
                result[j]! = 60 ∧
                (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)

Fidelity mapping to our IR:
  - `a : Array Int`  -> input array `A` (abstract function; the
    output var `A` is the result).
  - `j : Nat`        -> input `j : int` with implied `j >= 0`
    (Nat lower bound folded into Pre).
  - `a.size`         -> input `n : int` (the array length; our
    arrays are unbounded abstract functions, so we carry the
    length as an explicit parameter as the corpus does elsewhere).
  - old array `a`    -> ghost copy `B` (caller passes A twice);
    Pre pins `B == A` over 0..n-1 so Post can reference the
    original values, since SMT has no `old`.
  - `result.size = a.size` : our `Update` preserves the array's
    domain by construction (it rewrites one point of the abstract
    function), so size-preservation holds definitionally and is
    not a separately-modelled conjunct.
  - `result[j]! = 60`                 -> `A[j] == 60`.
  - `∀ k, k < a.size → k ≠ j → result[k]! = a[k]!`
                                       -> ForAll k. (0<=k<n ∧ k!=j)
                                          ⇒ A[k] == B[k].

This is a faithful capture: the only VERINA conjunct not
represented as an explicit clause is `result.size = a.size`,
which is definitionally true for a point-Update on an abstract
array.  Pure Z3, no UF, no axioms.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n and a valid index j "
        "(0 <= j < n), set A[j] := 60; every other element is "
        "unchanged."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),   # ghost copy of original A
                Var("j", "int", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(0 <= j) and (j < n) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = ("(A[j] == 60) and "
                "ForAll(lambda k: Implies("
                "0 <= k and k < n and k != j, A[k] == B[k]))"),
    atoms = {
        # Single point-write: A[j] := 60.
        "s@B0": [
            {"A": "Update(A, j, 60)"},
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/verina_basic_97_TestArrayElements"
    ),
    wedge_threshold = 200,
    solver_timeout_ms = 60_000,
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
