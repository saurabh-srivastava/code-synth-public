"""verina_basic_103 (UpdateElements) — VERINA-basic port.

Update two fixed positions of an array: index 4 gets `+3`, index 7
is set to the constant 516; every other position is left unchanged.
Pure acyclic — two array writes, no loop.  Same shape as
`array_swap` / `swap_first_last` (a nested `Update`), just with
constant indices and a `+3` / `:= 516` payload instead of a swap.

VERINA source (source of truth):
  signature : UpdateElements (a : Array Int) -> Array Int
  precond   : a.size ≥ 8
  code      : let a1 := a.set! 4 ((a[4]!) + 3)
              let a2 := a1.set! 7 516
              a2
  postcond  : result.size = a.size ∧
              result[4]! = (a[4]!) + 3 ∧
              result[7]! = 516 ∧
              (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)

Fidelity mapping:
  - VERINA `a : Array Int` (size ≥ 8) -> our input array A + length
    n, plus a ghost copy B that equals the *original* A pointwise
    (Pre pins `B[k] == A[k]`).  A is also the output var — the
    single transition rewrites A in place, and the post references
    B for the original values (the standard `old_A` ghost trick, cf.
    `array_swap`).  This is needed because `result[4]! = a[4]! + 3`
    relates the post-state result to the *original* a[4].
  - VERINA precond `a.size ≥ 8`      -> our `n >= 8`.
  - `result.size = a.size`           -> Update is a functional store
    that preserves the array's domain; length `n` is a separate,
    unmodified parameter.  Size preservation is therefore implicit
    (not a separate atom), exactly as in `array_swap` / cubeElements.
  - `result[4]! = a[4]! + 3`         -> A[4] == B[4] + 3.
  - `result[7]! = 516`               -> A[7] == 516.
  - `∀ i<size, i≠4, i≠7 => result[i]!=a[i]!`
                                     -> ForAll k. 0<=k<n ∧ k≠4 ∧ k≠7
                                        => A[k] == B[k].  (VERINA's i
                                        is a Nat, so 0<=k is implicit
                                        and faithful.)

No auxiliary fold/sum/count function is referenced by the postcond,
so this is PURE Z3 (no UF, no axioms).  The transition is the
constant-index nested store
  A := Update(Update(A, 4, A[4] + 3), 7, 516)
whose RHS reads the pre-state (original) A[4]; since Pre gives
A[4] == B[4], the post's `A[4] == B[4] + 3` closes congruently.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (with n >= 8), update "
        "index 4 to its original value plus 3 and index 7 to the "
        "constant 516, leaving every other position unchanged."
    ),

    template = SB(n=1),
    # B is the ghost copy of the original A (caller passes A twice).
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(n >= 8) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = ("(A[4] == B[4] + 3) and (A[7] == 516) and "
                "ForAll(lambda k: Implies("
                "0 <= k and k < n and k != 4 and k != 7, A[k] == B[k]))"),

    atoms = {
        # Single transition: the two constant-index writes as a
        # nested store (index-7 store is outermost, index-4 innermost).
        "s@B0": [
            {"A": "Update(Update(A, 4, A[4] + 3), 7, 516)"},
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_103/lean/SynthLean/Y2Corpus/verina_basic_103",
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
