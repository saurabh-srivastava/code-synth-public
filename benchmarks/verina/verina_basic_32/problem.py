"""verina_basic_32 — swapFirstAndLast (ported from VERINA).

Source: /private/tmp/verina-data/datasets/verina/verina_basic_32/
Upstream: dafny-synthesis task_id_625.

VERINA signature:
    swapFirstAndLast(a: Array Int) -> Array Int

VERINA precondition:
    a.size > 0

VERINA reference code:
    let first := a[0]!
    let last  := a[a.size - 1]!
    a.set! 0 last |>.set! (a.size - 1) first

VERINA postcondition (4 conjuncts):
    result.size = a.size ∧
    result[0]! = a[a.size - 1]! ∧
    result[result.size - 1]! = a[0]! ∧
    (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)

Mapping to this framework
-------------------------
The synthesizer models arrays as unbounded Z3 maps with a separate
length variable `n`; there is no reified `.size`, so `result.size =
a.size` (conjunct 1) is preserved automatically by in-place Update
and needs no explicit atom.  The remaining three conjuncts map
directly.  Because the output overwrites A, we thread a ghost copy
`B` of the original array (caller passes A twice; Pre pins B == A on
[0, n)) so the post can refer to the *original* values — the standard
"old_A" trick (see benchmarks/array_swap.py, benchmarks/swap_first_last.py).

VERINA's middle-unchanged quantifier
`(List.range (result.size - 2)).all (fun i => result[i+1]! = a[i+1]!)`
ranges i over [0, n-2), so the touched index j = i+1 ranges over
[1, n-1).  Our quantifier `ForAll k. 1 <= k < n-1 => A[k] == B[k]`
(written `0 < k and k < n - 1`) matches these bounds EXACTLY:
  - VERINA i ∈ {0, .., n-3}  ⇒  j = i+1 ∈ {1, .., n-2}
  - ours   k ∈ {1, .., n-2}  (integers with 1 <= k < n-1)
Both are vacuous for n <= 2 (n-1 <= 1 ⇒ empty range; Lean's
List.range(n-2) truncates to [] under Nat subtraction).

Spec:
    Pre  : n >= 1 ∧ (∀k. 0 <= k < n ⇒ B[k] == A[k])
    Post : A[0] == B[n-1] ∧ A[n-1] == B[0] ∧
           (∀k. 0 < k < n-1 ⇒ A[k] == B[k])

Straight-line SB, one nested Update, pure Z3 (no UF, no Lean).
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-empty integer array A of length n (n >= 1), "
        "swap the first and last elements: A[0] receives the old "
        "A[n-1] and A[n-1] receives the old A[0]; every other "
        "element is unchanged."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),   # ghost copy of the original A
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(n >= 1) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    # conjunct 2: result[0]      == a[n-1]
    # conjunct 3: result[n-1]    == a[0]
    # conjunct 4: middle [1, n-1) unchanged
    post     = ("(A[0] == B[n - 1]) and (A[n - 1] == B[0]) and "
                "ForAll(lambda k: Implies("
                "0 < k and k < n - 1, A[k] == B[k]))"),
    atoms = {
        # Nested Update: swap A[0] and A[n-1].  Outer Update reads the
        # ORIGINAL A[0] (before the inner store), so no temp is needed.
        "s@B0": [
            {"A": "Update(Update(A, 0, A[n - 1]), n - 1, A[0])"},
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
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
