"""verina_basic_53 (CalSum) — sum of the first N natural numbers.

Ported from VERINA-basic task `verina_basic_53`
(/private/tmp/verina-data/datasets/verina/verina_basic_53).

VERINA source of truth (between the @start/@end markers):
    precond  : True                       (no precondition)
    code     : let rec loop (n) := if n = 0 then 0 else n + loop (n-1); loop N
    postcond : 2 * result = N * (N + 1)

Fidelity mapping (VERINA -> this synthesizer):
    * N : Nat  ->  int input with an implied `N >= 0`  (pre = "N >= 0").
    * return Nat `result`  ->  int output `s`.
    * VERINA's postcond is the CLOSED FORM `2 * result = N * (N + 1)`,
      NOT a reference to the recursive `loop`.  So we carry it over
      VERBATIM as `2*s == N*(N+1)` — a purely arithmetic obligation.
      No auxiliary fold/sum uninterpreted function is needed, and no
      Lean dispatch: Z3's nonlinear arithmetic (NIA) discharges the
      `i*(i+1)` / `N*(N+1)` products directly (same as intsqrt's `i*i`).

Synthesized shape (iterative accumulator, closed under NIA):

    s, i := 0, 0;
    while (i < N)
        s, i := s + i + 1, i + 1;      // s gains (i+1) each step

    τ  : 2*s == i*(i+1)  ∧  i <= N
    g  : i < N
    ϕ  : N - i
    post at exit: ¬(i<N) ∧ i<=N ⇒ i == N ⇒ 2*s == N*(N+1)

This is the same straight-line-SB + single-loop scalar family as
`mul.py` / `intsqrt.py`: PURE Z3, no UF, no axioms, no Lean.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("N", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "N >= 0",                       # Nat N -> int with implied >= 0
    post     = "2*s == N*(N + 1)",             # VERINA postcond, verbatim

    atoms = {
        # Loop invariant — conjunctive dispatch picks the valid subset.
        # Published τ is the conjunction of atoms 0, 1.
        "tau@L0": [
            "2*s == i*(i + 1)",                # published #1 — closed-form partial sum
            "i <= N",                          # published #2 — needed to pin i==N at exit
            "s == 0",                          # distractor — only true at entry
            "i == 0",                          # distractor — only true at entry
            "2*s == i*i",                      # distractor — wrong closed form
        ],
        "g@L0": [
            "i < N",                           # published
            "i <= N",                          # off-by-one — would run one step too far
            "i > 0",                           # wrong direction
        ],
        "phi@L0": [
            "N - i",                           # published — decreases each iter
            "i",                               # wrong direction — increases
            "N",                               # constant — does not decrease
        ],

        # Entry SB B0 — {output_var: rhs}; vars not listed are preserved.
        "s@B0": [
            {"s": "0", "i": "0"},              # published
            {"s": "0", "i": "1"},              # off-by-one start
            {"s": "N", "i": "0"},              # wrong
        ],

        # Loop body B1 — s gains (i+1); i increments.
        "s@B1": [
            {"s": "s + i + 1", "i": "i + 1"},  # published
            {"s": "s + i",     "i": "i + 1"},  # off-by-one accumulation
            {"s": "s + 1",     "i": "i + 1"},  # wrong — counts iterations, not sum
        ],

        # Exit SB B2 — identity.
        "s@B2": [ {} ],
    },

    max_solutions          = 5,
    expected_solutions     = 1,
    expected_lean_hits     = 0,                # pure Z3, no Lean dispatch expected
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_53/lean/SynthLean/Y2Corpus/verina_basic_53",
    wedge_threshold        = 200,
    solver_timeout_ms      = 60_000,
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
