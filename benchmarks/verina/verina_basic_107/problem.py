"""verina_basic_107 — ComputeAvg (VERINA-basic port).

Compute the integer average of two integers via integer division:
`avg := (a + b) / 2`.  Straight-line single-branch block `SB(n=1)` —
the scalar analogue of `benchmarks/verina/verina_basic_11_lastDigit.py`
(and the entry block of `benchmarks/intdiv.py`), which likewise reason
about integer `/` and `%` over Z3's integer theory.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_107/task.lean):
    signature : ComputeAvg (a : Int) (b : Int) : Int
    precond   : True
    code      : (a + b) / 2
    postcond  : 2 * result = a + b - ((a + b) % 2)

(The task.json summary lists the weaker bracketing form
`a+b-1 ≤ 2*avg ≤ a+b+1`; the task.lean postcond — our source of truth —
is the exact equality above, which implies that bracketing.)

Fidelity mapping (VERINA -> ours)
---------------------------------
    * `a : Int`, `b : Int`  -> Var("a"/"b", "int", "input").  Both are
      already Int in VERINA, so no Nat->int nonnegativity is implied.
    * `result : Int`        -> our output Var("avg", "int", "output").
    * precond `True`        -> pre = "true".
    * postcond
          2 * result = a + b - ((a + b) % 2)
      is ported VERBATIM as
          post = "2 * avg == a + b - ((a + b) % 2)".
      No reinterpretation, no auxiliary fold/sum/count/product function
      (there is none in the spec), so no uninterpreted function and no
      axiom are needed — this closes in pure Z3.

Why the port is faithful AND provable.  Both Z3 and Lean tie their `/`
and `%` on Int into the *same* division-algorithm identity for a
matching (div, mod) pair:  a+b = 2*((a+b)/2) + ((a+b) % 2).  Rearranged,
that is exactly `2*((a+b)/2) = (a+b) - ((a+b) % 2)`, i.e. the reference
code `(a+b)/2` satisfies the postcond as an *identity*, independent of
the rounding convention (T- vs. Euclidean), because `/` and `%` are the
matching pair on both sides.  Z3's `%` here is Euclidean (remainder in
[0, 2)); Lean's default Int `/`/`%` are likewise a matched pair, so the
equality holds identically in both.  TRUST SURFACE: pure Z3 — no UF, no
axioms, no Lean dispatch (expected_lean_hits = 0).

Template `SB(n=1)` recovers the reference body `avg := (a + b) / 2`.
The transition candidate list carries distractors that each violate the
postcond for some parity of `a + b`, so the postcond genuinely
discriminates the reference assignment.

Spec:
    Pre  : true
    Post : 2 * avg == a + b - ((a + b) % 2)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integers a and b, return their integer average "
        "(a + b) / 2 (VERINA verina_basic_107 / Clover_avg)."
    ),

    template = SB(n=1),
    inputs   = [Var("a", "int", "input"), Var("b", "int", "input")],
    outputs  = [Var("avg", "int", "output")],
    pre      = "true",
    # Verbatim transcription of VERINA's postcond over our output var.
    post     = "2 * avg == a + b - ((a + b) % 2)",

    atoms = {
        # Single unguarded branch: avg := (a + b) / 2.
        "s@B0": [
            {"avg": "(a + b) / 2"},         # published — the reference code
            {"avg": "(a + b + 1) / 2"},     # distractor — rounds up; fails
                                            #   post when a+b is odd
            {"avg": "a / 2 + b / 2"},       # distractor — loses the shared
                                            #   low bit; fails when a,b both odd
        ],
    },
    max_solutions          = 1,
    expected_solutions     = 1,
    expected_lean_hits     = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_107/lean/SynthLean/Y2Corpus/verina_basic_107",
    wedge_threshold        = 200,
    solver_timeout_ms      = 60_000,
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
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
