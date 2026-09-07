"""array_rotate_left — Phase X corpus benchmark.

Cyclic shift of the first n elements of A left by 1:
A[0..n-1) become A[1..n), and A[n-1] takes the old A[0].
A two-step program: save A[0], shift, place saved at A[n-1].

Spec:
    Pre  : n >= 1 ∧ B is a ghost copy of A
    Post : ForAll k. 0 ≤ k < n - 1 ⇒ A[k] == B[k + 1]
         ∧ A[n - 1] == B[0]
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


_MODULE = "SynthLean.Y2Corpus.ArrayRotateLeft"


def _cite_arl_post(chosen, hyp_for):
    # FLAT chain-bundle-post: helper signature matches the translator's
    # emitted theorem with the new `<var>_post` binder for A (since the
    # post-loop skip SB rewrites loop-modified A).  See #242.
    return (
        f"exact {_MODULE}.arl_post "
        "n saved i A B i' A' A_post "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_not_g h_skip_A h_init_saved"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.array_rotate_left.Helpers",
    entries=[
        HelperEntry("arl_post",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L0",
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_arl_post),
    ],
)


PROBLEM = Problem(
    description = (
        "Given an integer array A of length at least n (with n ≥ 1), "
        "rotate the first n elements one position to the left.  After "
        "the operation, A[0] takes the old value of A[1], A[1] takes "
        "the old A[2], ..., A[n-2] takes the old A[n-1], and A[n-1] "
        "wraps around to take the old A[0]."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),  # ghost copy
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("saved", "int", "local"),
                Var("i", "int", "local")],

    pre      = ("(n >= 1) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n - 1, A[k] == B[k + 1])) and "
        "(A[n - 1] == B[0])"
    ),

    atoms = {
        # Init: save A[0] and start i := 0.
        "s@B0": [{"saved": "A[0]", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n - 1",
            "n >= 1",
            "saved == B[0]",
            # Rotated prefix matches.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] == B[k + 1]))"),
            # Unrotated tail still matches B at the SHIFTED-BY-i
            # positions:  for j in [i, n-1], A[j] == B[j] (we
            # haven't touched these yet).
            ("ForAll(lambda k: Implies("
             "i <= k and k < n, A[k] == B[k]))"),
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - 1 - i"],

        # Body: A[i] := A[i + 1], i := i + 1.
        "s@B1": [{"A": "Update(A, i, A[i + 1])", "i": "i + 1"}],

        # Final: A[n - 1] := saved.
        "s@B2": [{"A": "Update(A, n - 1, saved)"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
    helper_registry = _HELPER_REGISTRY,
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
