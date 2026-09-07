"""insertion_sort — Phase 3.R: classical insertion sort with sortedness post.

Companion to `bubble_sort` and `selection_sort`.  The inner loop
walks the inserting element leftward by swapping with the "wall"
(`A[j-1]`), stopping when either we've reached the start (`j = 0`)
or the wall is already ≤ the inserting element.

    i := 0
    while (i < n):
        j := i
        while (j > 0 and A[j-1] > A[j]):
            A := swap(A, j, j-1)
            j := j - 1
        i := i + 1
    // post: ∀p, q. 0 ≤ p ≤ q < n  ⇒  A[p] ≤ A[q]

Invariants
----------
`τ_outer`: after `i` outer iterations, the prefix `A[0..i)` is
sorted.  Standard sortedness invariant.

`τ_inner`: three quantified atoms that together carry the
"partially sorted" state during the leftward walk:
  - **Left portion sorted**: A[0..j) is sorted (unchanged from
    the outer prefix).
  - **Right portion sorted**: A[j..i] is sorted (the inserting
    element at j plus the shifted-right slice of the original
    sorted prefix).
  - **Wall lower-bound** (when j > 0): A[j-1] ≤ A[k] for k in
    (j, i].  This is what makes the inductive step go through
    across the swap: the shifted slice's lower bound is A[j-1]
    (preserved unchanged in [0, j)).

At inner exit (¬(j > 0 ∧ A[j-1] > A[j]) = j = 0 ∨ A[j-1] ≤ A[j]):
either j = 0 and the right portion IS the full prefix, or the
boundary A[j-1] ≤ A[j] chains the left and right portions into
one fully-sorted A[0..i].

Spec:
    Pre  : n ≥ 0
    Post : ForAll(p, q: 0 ≤ p ≤ q < n  ⇒  A[p] ≤ A[q])
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


def _cite_insertion_sort_l1_body_inductive_chain(chosen, hyp_for):
    """sc5 — L1's body around the inner L1 loop (outer L0 inductive).

    Chain: SB(B1) j:=i, Loop(L1) abstract, SB(B3) i:=i+1.  4 states.
    Goal: τ@L0 at s3.
    """
    return (
        "exact insertion_sort_l1_body_inductive_chain "
        "n_s0 i_s0 j_s0 A_s0 "
        "n_s1 i_s1 j_s1 A_s1 "
        "n_s2 i_s2 j_s2 A_s2 "
        "n_s3 i_s3 j_s3 A_s3 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_g "
        "h_i0_trans_j h_i0_frame_n h_i0_frame_i h_i0_frame_A "
        "h_i1_L1_tau_0 h_i1_L1_tau_1 h_i1_L1_tau_2 h_i1_L1_tau_3 "
        "h_i1_L1_tau_4 h_i1_L1_tau_5 h_i1_L1_tau_6 "
        "h_i1_L1_not_g "
        "h_i1_L1_frame_n h_i1_L1_frame_i "
        "h_i2_trans_i h_i2_frame_n h_i2_frame_j h_i2_frame_A"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.insertion_sort.Helpers",
    entries=[
        # sc5 — L1 body inductive (nested in L0).
        HelperEntry(
            helper_name="insertion_sort_l1_body_inductive_chain",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post" and loop_id == "L1"),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3}),
                "tau@L1": frozenset({0, 1, 2, 3, 4, 5, 6}),
            },
            cite=_cite_insertion_sort_l1_body_inductive_chain,
        ),
    ],
)


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=1)) >> SB(n=1)),
    inputs   = [Var("n", "int", "input"), Var("A", "int[]", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local"), Var("j", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda p, q: Implies(0 <= p and p <= q and q < n, "
                "A[p] <= A[q]))"),

    atoms = {
        # SB0: i := 0.
        "s@B0": [{"i": "0"}],

        # Outer τ.
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p <= q and q < i, "
             "A[p] <= A[q]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # SB1: j := i.
        "s@B1": [{"j": "i"}],

        # Inner τ.  Three quantified atoms: left sorted, right sorted,
        # wall lower-bound.
        "tau@L1": [
            "0 <= j",
            "j <= i",
            "i < n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p <= q and q < j, "
             "A[p] <= A[q]))"),
            ("ForAll(lambda p, q: Implies("
             "j <= p and p <= q and q <= i, "
             "A[p] <= A[q]))"),
            ("ForAll(lambda k: Implies("
             "j > 0 and j < k and k <= i, "
             "A[j-1] <= A[k]))"),
        ],
        "g@L1":   ["j > 0 and A[j-1] > A[j]"],
        "phi@L1": ["j"],

        # Inner body: swap A[j-1] and A[j], then j := j - 1.
        "s@B2": [{
            "A": "Update(Update(A, j, A[j-1]), j-1, A[j])",
            "j": "j - 1",
        }],

        # SB3: i := i + 1.
        "s@B3": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 1_800_000,   # 30 min
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
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
