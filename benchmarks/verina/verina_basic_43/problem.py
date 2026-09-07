"""verina_basic_43 — sumOfFourthPowerOfOddNumbers (VERINA-basic port).

Compute the sum of the fourth powers of the first n odd natural numbers,
i.e. 1^4 + 3^4 + 5^4 + ... + (2n-1)^4, by an accumulator loop.  Scalar,
PURE Z3 — the VERINA postcondition is a *closed-form polynomial* in n
(no auxiliary fold/sum function), so no uninterpreted function is
required; Z3's nonlinear arithmetic discharges the (degree-5) inductive
polynomial identity directly.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_43/):
    signature : sumOfFourthPowerOfOddNumbers (n : Nat) : Nat
    precond   : True
    code      : match n with
                | 0     => 0
                | n + 1 => let prev := sumOfFourthPowerOfOddNumbers n
                           let nextOdd := 2 * n + 1
                           prev + nextOdd^4
    postcond  : 15 * result = n * (2*n + 1) * (7 + 24*n^3 - 12*n^2 - 14*n)

Fidelity mapping:
    n      : Nat  -> our "int" input with the implied `n >= 0`
                    (Nat's nonnegativity carried as the precondition).
    result : Nat  -> our output var `s`.
    precond True  -> pre = "n >= 0".

    VERINA's postcond is the *exact algebraic identity* that the closed
    form of the sum satisfies:
        15 * result == n * (2*n + 1) * (7 + 24*n^3 - 12*n^2 - 14*n)
    We reproduce it verbatim over our output `s`, expanding VERINA's
    `n^3` -> `n*n*n` and `n^2` -> `n*n` (our expression surface uses
    explicit `*`, no `^` operator).  This is a WORD-FOR-WORD transcription
    of VERINA's postcond — the fidelity is total: any `s` accepted by our
    post is accepted by VERINA's post and vice versa (they are the same
    polynomial equation).  Spot-checked: n=1 -> s=1 (=1^4); n=2 -> s=82
    (=1+81); n=3 -> s=707 (=1+81+625).

Algorithm synthesized (an iterative form of the VERINA recursion):
    s := 0; i := 0;
    while i < n:
        s := s + (2*i + 1)^4;     // add the i-th (0-indexed) odd number^4
        i := i + 1;
    // post: 15*s == n*(2n+1)*(7 + 24n^3 - 12n^2 - 14n)

Proof witness (all obligations close in pure Z3 NIA):
    tau : 15*s == i*(2*i+1)*(7 + 24*i^3 - 12*i^2 - 14*i)  ∧  i <= n
    phi : n - i                                (decreases; > 0 under guard)
    g   : i < n
  Loop-inductive: the closed form at i and at i+1 differ by exactly
    15*(2*i+1)^4 (a degree-5 polynomial identity in i), which Z3
    normalizes to true; the invariant `i <= n` is preserved from i<n.
  Exit: ¬(i < n) ∧ i <= n ⇒ i = n, so tau collapses to the post at n.
  Entry: i=0, s=0 give 15*0 == 0*... (trivially true) and 0 <= n
    (uses Fpre's `n >= 0`, propagated post Phase Fpre-Sym).

Spec:
    Pre  : n >= 0
    Post : 15*s == n*(2*n+1)*(7 + 24*n*n*n - 12*n*n - 14*n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, return the sum of the fourth "
        "powers of the first n odd natural numbers (1^4 + 3^4 + ... + "
        "(2n-1)^4)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre  = "n >= 0",
    post = "15*s == n*(2*n + 1)*(7 + 24*n*n*n - 12*n*n - 14*n)",

    atoms = {
        # Init: s := 0, i := 0.
        "s@B0": [
            {"s": "0", "i": "0"},                          # published
            {"s": "0", "i": "1"},                          # wrong: skips first odd
            {"s": "1", "i": "0"},                          # wrong: pre-seeds s
        ],

        "tau@L0": [
            # published main closed-form invariant (mirrors the post at i)
            "15*s == i*(2*i + 1)*(7 + 24*i*i*i - 12*i*i - 14*i)",
            "i <= n",                                      # published — needed for exit
        ],
        "g@L0": [
            "i < n",                                       # published
            "i <= n",                                      # off-by-one (over-runs)
            "i > 0",                                       # wrong
        ],
        "phi@L0": [
            "n - i",                                       # published — decreases by 1
            "i",                                           # wrong direction
            "n",                                           # constant, not decreasing
        ],

        # Body: s := s + (2*i+1)^4; i := i + 1.
        "s@B1": [
            {"s": "s + (2*i + 1)*(2*i + 1)*(2*i + 1)*(2*i + 1)",
             "i": "i + 1"},                                # published
            {"s": "s + (2*i + 1)*(2*i + 1)", "i": "i + 1"},  # wrong: square not 4th power
            {"s": "s + (2*i + 1)*(2*i + 1)*(2*i + 1)*(2*i + 1)",
             "i": "i"},                                    # wrong: forgets i increment
        ],

        # Final SB: no-op (result already accumulated in s).
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_43/lean/SynthLean/Y2Corpus/verina_basic_43",
    wedge_threshold = 200,
    solver_timeout_ms = 300_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    print(f"wall: {time.monotonic() - t:.1f}s")
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for k, sol in enumerate(result.solutions):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
