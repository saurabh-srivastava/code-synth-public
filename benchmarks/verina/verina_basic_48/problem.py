"""verina_basic_48 — isPerfectSquare (VERINA basic corpus port).

VERINA task `verina_basic_48` (upstream dafny-synthesis task_id_803).
Signature: `isPerfectSquare (n : Nat) : Bool`.

  precond  : True  (works for any Nat)
  code     : bounded search — `check 1 n` scans i = 1,2,… while i*i ≤ n,
             returns true iff some i*i == n.
  postcond : `result ↔ ∃ i : Nat, i * i = n`

── Port mapping (fidelity claim) ───────────────────────────────────────
VERINA's `n : Nat` → our `n : int` with the implied precondition
`n >= 0`.  VERINA's `Bool` result → our `result : int` in {0, 1}
(1 ≡ true, 0 ≡ false).  VERINA's postcondition
`result ↔ ∃ i : Nat, i * i = n` is captured EXACTLY as the two-way
implication

    (result == 1)  ↔  ∃ i. (i >= 0 ∧ i*i == n)

where the `i >= 0` guard on the existential witness is the faithful
translation of VERINA's `i : Nat` (naturals are non-negative).  Over
n >= 0 this is equivalent to the unrestricted `∃ i:int` (squares are
sign-symmetric), but we keep the `i >= 0` guard to mirror `Nat`
literally.

── Synthesized algorithm ───────────────────────────────────────────────
Rather than VERINA's fuel-bounded linear scan, the synthesizer picks
the equivalent monotone integer-floor-sqrt shape:

    r := 0                                  # B0
    while ((r+1)*(r+1) <= n)  r := r + 1     # L0 body B1
    result := (r*r == n) ? 1 : 0            # B2

Loop invariant  τ  :  r*r <= n  ∧  r >= 0
Guard           g  :  (r+1)*(r+1) <= n
Ranking         ϕ  :  n - r*r          (strictly decreases; ≥ 0 under τ)

At loop exit ¬g gives  r*r <= n < (r+1)*(r+1)  with r >= 0, i.e. r is
floor(sqrt n).  Then n is a perfect square iff r*r == n, which is what
B2 stores into `result`.

── Verifier split ──────────────────────────────────────────────────────
Entry / inductive-preservation / ranking obligations are concrete
integer arithmetic and close in Z3 directly.  The post obligation
(`safety-bundle-post`) needs monotonicity of squaring on the
non-negative integers to discharge the existential's backward
direction

    (∃ i>=0. i*i == n)  ∧  r*r <= n < (r+1)*(r+1)  ∧  r >= 0
        ⟹  r*r == n

which Z3 cannot instantiate (the required lemma `a*a <= b*b → a <= b`
has no valid e-matching trigger — `*` is interpreted).  Z3 returns
UNKNOWN and the obligation falls through to the Lean backend, where the
monotonicity is proved from first principles.  There are NO uninterpreted
functions and NO trusted axioms — the Lean companion proves the
biconditional outright (`trust_axioms = []`).
"""
from synth import Problem, SB, Loop, Var, solve


# The existential witness, reused verbatim in both directions of the
# postcondition biconditional so the emitted Lean goal is syntactically
# identical on both sides.
_EXISTS = "Exists(lambda i: i >= 0 and i*i == n)"

PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, return 1 if n is a perfect "
        "square (there exists i >= 0 with i*i == n) and 0 otherwise."
    ),

    template = SB(n=1) >> Loop(SB(n=1)) >> SB(n=1),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("r", "int", "local")],

    pre  = "n >= 0",
    post = (
        f"Implies(result == 1, {_EXISTS}) and "
        f"Implies({_EXISTS}, result == 1)"
    ),

    atoms = {
        # B0 entry: r := 0.
        "s@B0": [
            {"r": "0"},                         # published
            {"r": "1"},
            {"r": "n"},
        ],
        # L0 invariant τ (conjunctive): both atoms load-bearing.  Kept
        # minimal — the post obligation dispatches to Lean per τ-subset,
        # so every extra τ atom doubles the (expensive) Lean-dispatch
        # count without buying coverage (REC 1 / F17: shrink τ).
        "tau@L0": [
            "r*r <= n",                         # published #1 — floor-sqrt lower bound
            "r >= 0",                           # published #2 — non-negativity
        ],
        # L0 guard: keep iterating while (r+1)^2 still fits under n.
        "g@L0": [
            "(r+1)*(r+1) <= n",                 # published
            "r*r <= n",                         # off-by-one (never exits early enough)
            "(r+1)*(r+1) < n",
        ],
        # Ranking function.
        "phi@L0": [
            "n - r*r",                          # published — decreases, ≥0 under τ
            "n - r",
            "r",
        ],
        # L0 body B1: r := r + 1.
        "s@B1": [
            {"r": "r + 1"},                     # published
            {"r": "r + 2"},
            {"r": "r"},                         # no progress
        ],
        # B2 exit: result := (r*r == n) ? 1 : 0.
        "s@B2": [
            {"result": "1 if r*r == n else 0"},  # published
            {"result": "0 if r*r == n else 1"},  # inverted
            {"result": "1"},
        ],
    },

    max_solutions      = 1,      # the executable code is unique; the
                                 # phi distractors admit two valid ranking
                                 # proofs (n-r, n-r*r) for the SAME program,
                                 # so cap at the best-scoring one.
    expected_solutions = 1,
    expected_lean_hits = 1,      # the sc4 safety-bundle-post obligation
                                 # (full τ) is the lone Lean-verified class
                                 # (via the .solved.lean companion);
                                 # informative only.
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_48/lean/SynthLean/Y2Corpus/verina_basic_48",
    wedge_threshold    = 200,
    solver_timeout_ms  = 120_000,
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
