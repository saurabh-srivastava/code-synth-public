"""verina_basic_18 — sumOfDigits (VERINA-basic port).

Compute the sum of the decimal digits of a non-negative integer by
repeatedly peeling the last digit (`n % 10`) and dividing by ten
(`n / 10`) until the running value reaches zero.  Scalar accumulator
loop, axiom-heavy: the postcondition references the digit-sum of `n`,
which we model as an uninterpreted function `digitSum` with a base
axiom + a decimal recurrence.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_18/):
    signature : sumOfDigits (n : Nat) : Nat
    precond   : True
    code      : let rec loop (n) (acc) :=
                    if n = 0 then acc
                    else loop (n / 10) (acc + n % 10)
                loop n 0
    postcond  : result - S = 0  ∧  S - result = 0
                where S = List.sum (List.map
                    (fun c => Char.toNat c - Char.toNat '0')
                    (String.toList (Nat.repr n)))
                i.e. `result = S`, the sum of `n`'s decimal digits.

Fidelity mapping:
    n      : Nat  -> our "int" input with the implied `n >= 0`
                    (Nat's nonnegativity carried as the precondition).
    result : Nat  -> our output var `s`.
    precond True  -> pre = "n >= 0".

    VERINA's postcond `result - S = 0 ∧ S - result = 0` is the Nat
    (truncated-subtraction) idiom for the equality `result = S`, where
    `S` is the sum of the decimal digits of `n` (obtained by mapping
    each character of `Nat.repr n` — the base-10 string of `n` — to
    its digit value and summing).  We model that digit-sum as the UF
    `digitSum : Int -> Int`, characterised by:
        digitSum(0) == 0                                  (empty repr)
        digitSum(10*q + r) == digitSum(q) + r   for q >= 0, 0 <= r <= 9
                                              (append last digit r)
    This is exactly the mathematical definition of the base-10 digit
    sum: any k > 0 is `10*q + r` with `q = k/10` (k with its last digit
    dropped) and `r = k%10` (the last digit, 0..9), so digitSum(k) =
    digitSum(k/10) + k%10; and `digitSum(0) = 0` terminates the peel.
    So `digitSum(n)` equals VERINA's `S`, and our post `s ==
    digitSum(n)` faithfully captures VERINA's `result = S`.  (VERINA's
    informal "sum is non-negative" clause is not in the formal postcond
    markers, so we omit it — the equality is the whole spec.)

    (The multiplicative direction is a Z3 E-matching hygiene choice, not
    a fidelity change — see the `axioms` block below.)

Algorithm synthesized (mirrors the VERINA reference, iteratively):
    s := 0; m := n;
    while m != 0:
        s := s + m % 10;
        m := m / 10;
    // post: s == digitSum(n)

Proof witness:
    tau : s + digitSum(m) == digitSum(n)  ∧  m >= 0
    phi : m                                  (m / 10 < m for m > 0)
    g   : m != 0
  Loop-inductive: body applies the recurrence axiom at k = m (fires
    because guard m!=0 + tau's m>=0 give m > 0), turning
    s + digitSum(m) into (s + m%10) + digitSum(m/10).
  Exit: ¬(m != 0) ⇒ m = 0 ⇒ digitSum(m) = digitSum(0) = 0, so the
    invariant collapses to s = digitSum(n).

Spec:
    Pre  : n >= 0
    Post : s == digitSum(n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, return the sum of its "
        "decimal digits."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("m", "int", "local")],

    uninterpreted = [("digitSum", ["int"], "int")],
    axioms = [
        "digitSum(0) == 0",
        # Decimal peel written in the MULTIPLICATIVE (successor)
        # direction — digitSum(10q + r) = digitSum(q) + r for a last
        # digit 0 <= r <= 9 — rather than the predecessor form
        # `digitSum(k) = digitSum(k/10) + k%10`.  The predecessor form's
        # auto-inferred Z3 trigger `digitSum(k)` E-matches infinitely
        # (digitSum(m) -> digitSum(m/10) -> digitSum(m/100) -> ...),
        # which makes Z3 *time out* (not refute) the ranking obligation
        # on the invalid τ-subsets that omit `m >= 0` (there `m > m/10`
        # is genuinely false for negative m).  The multiplicative form's
        # sole trigger `digitSum(10*q + r)` never matches the loop's
        # `digitSum(m)` / `digitSum(m/10)` terms, so the axiom stays
        # inert in Z3 (ranking / entry / post close directly) and the
        # inductive obligation dispatches to Lean, where the peel is
        # applied explicitly (see the .solved.lean companion).
        ("ForAll(lambda q, r: Implies("
         "(q >= 0) and (0 <= r) and (r <= 9), "
         "digitSum(10 * q + r) == digitSum(q) + r))"),
    ],

    pre  = "n >= 0",
    post = "s == digitSum(n)",

    atoms = {
        # Init: s := 0, m := n.
        "s@B0": [{"s": "0", "m": "n"}],

        "tau@L0": [
            "s + digitSum(m) == digitSum(n)",   # main invariant
            "m >= 0",                            # needed: m>0 fires recurrence
        ],
        "g@L0":   ["m != 0"],
        "phi@L0": ["m"],

        # Body: s := s + m % 10; m := m / 10.
        "s@B1": [{"s": "s + m % 10", "m": "m / 10"}],

        # Final SB: no-op (output already accumulated in s).
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_18/lean/SynthLean/Y2Corpus/verina_basic_18",
    wedge_threshold = 200,
    solver_timeout_ms = 1_800_000,   # 30 min budget for axiom-heavy
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
