"""verina_basic_28 (isPrime) — VERINA-basic port.

Determine whether a natural number n (>= 2) is prime, i.e. whether it
has no divisor k with 2 <= k < n.  Returns 1 (true) if n is prime,
0 (false) otherwise.

VERINA spec (from datasets/verina/verina_basic_28/task.lean, between the
@start/@end markers; source of truth):
    signature : isPrime (n : Nat) -> Bool
    precond   : n >= 2
    code      : let bound := n
                let rec check (i : Nat) (fuel : Nat) : Bool :=
                  if fuel = 0 then true
                  else if i * i > n then true
                  else if n % i = 0 then false
                  else check (i + 1) (fuel - 1)
                check 2 bound
    postcond  : (result -> (List.range' 2 (n - 2)).all (fun k => n % k != 0)) and
                (not result -> (List.range' 2 (n - 2)).any (fun k => n % k = 0))

Port / fidelity mapping
-----------------------
    Pre  : n >= 2                        (VERINA's precond, verbatim)
    Post : Implies(result == 1, NODIV(n)) and
           Implies(result == 0, HASDIV(n))
      where NODIV(ub) = ForAll k. 2 <= k < ub -> n % k != 0
            HASDIV(ub) = Exists k. 2 <= k < ub and n % k == 0

    VERINA output var `result : Bool` -> our output var `result : int`
    with the Bool->{0,1} convention (1 = true / prime, 0 = false).

SPEC-FIDELITY NOTE
------------------
`List.range' 2 (n - 2)` is the list [2, 3, ..., n-1] (start 2, length
n-2, so values 2 .. 2+(n-2)-1 = n-1).  Hence VERINA's
`(List.range' 2 (n-2)).all (fun k => n % k != 0)` is exactly our
NODIV(n) = `forall k in [2, n), n % k != 0`, and its `.any (fun k =>
n % k = 0)` is exactly our HASDIV(n) = `exists k in [2, n), n % k = 0`.
Our post is the LITERAL transcription of VERINA's two implications
under the Bool->{0,1} coding: `result -> NODIV` becomes
`Implies(result == 1, NODIV(n))` and `not result -> HASDIV` becomes
`Implies(result == 0, HASDIV(n))`.  Because the synthesized code only
ever assigns 0 or 1 to `result` (via `flag`), `result in {0,1}` is
total, so the two forward implications together are equivalent to the
biconditional `PRIME(n) <-> (result == 1)`, a faithful rendering of
VERINA's postcond.  VERINA's `n % k` is our `n % k` verbatim: Z3's
integer `%` uses the same Euclidean convention as Lean's `Nat.mod`
(non-negative result in [0, k) for k > 0, and here k >= 2 > 0), so
`n % k == 0 <-> k divides n` holds identically in Z3 and Lean.

NOTE on the sqrt optimization: VERINA's reference `check` stops at
`i * i > n` (only trial-divides up to sqrt n).  We synthesize the
simpler, spec-structural algorithm that trial-divides the WHOLE range
[2, n) with no early sqrt cutoff.  This is a different algorithm with
the SAME postcondition — the postcond quantifies over all of
[2, n) either way, so our synthesized program satisfies VERINA's spec
without importing the (nontrivial) "a composite has a factor <= sqrt n"
number-theory lemma the reference implicitly relies on.

Same shape as corpus `verina_basic_19_isSorted` (the forall-primary
flag-fold) and `verina_basic_9_hasCommonElement` (quantifier-in-post
single-pass flag-fold).  PURE Z3: no uninterpreted function, no
axioms, no Lean dispatch — the invariant `flag == 1 <-> prefix [2, i)
has no divisor` is expressible with quantified tau atoms, and the
divisor test `n % i` in the body uses the concrete loop variable i
(not a quantified variable), so Z3 discharges the whole obligation.

Algorithm (single upward pass over trial divisors, monotone flag):

    flag := 1; i := 2;
    while (i < n):
        if (n % i == 0):  flag := 0; i := i + 1;   // divisor at i -> not prime
        else:             i := i + 1;              // no divisor at i
    result := flag;

Loop invariant tau@L0 (flag mirrors "no divisor in scanned prefix
[2, i)"):
    2 <= i <= n, n >= 2, and
    (flag == 1 and forall k in [2, i). n % k != 0) or
    (flag == 0 and exists k in [2, i). n % k == 0)
At loop exit i == n, so tau collapses to exactly the postcondition.

TRUST SURFACE: none beyond Z3 (no uninterpreted functions, no axioms).
The result rests only on the SMT solver's discharge of the loop
invariant / coverage / termination obligations.
"""
from synth import Problem, SB, Loop, Var, solve


# "no divisor of n in [2, ub)" — the primality prefix predicate.
def _NODIV(ub: str) -> str:
    return f"ForAll(lambda k: Implies(2 <= k and k < {ub}, n % k != 0))"


# "some divisor of n in [2, ub)".
def _HASDIV(ub: str) -> str:
    return f"Exists(lambda k: 2 <= k and k < {ub} and n % k == 0)"


PROBLEM = Problem(
    description = (
        "Given a natural number n (n >= 2), return 1 if n is prime "
        "(no integer k with 2 <= k < n divides n), otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre  = "n >= 2",
    # Literal port of VERINA's two-implication postcondition, with the
    # Bool result modeled as int 0/1 and divisibility encoded as `%`.
    post = (
        f"Implies(result == 1, {_NODIV('n')}) and "
        f"Implies(result == 0, {_HASDIV('n')})"
    ),

    atoms = {
        # Init: flag := 1 (prime so far), i := 2.
        "s@B0": [{"flag": "1", "i": "2"}],

        "tau@L0": [
            "2 <= i",
            "i <= n",
            "n >= 2",
            # flag is 1 iff the scanned prefix [2, i) has no divisor.
            (f"((flag == 1) and {_NODIV('i')}) or "
             f"((flag == 0) and {_HASDIV('i')})"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: i divides n -> flag := 0; advance.
        "g@B1.0": ["n % i == 0"],
        "s@B1.0": [{"flag": "0", "i": "i + 1"}],
        # Branch 1: i does not divide n -> advance (flag unchanged).
        "g@B1.1": ["n % i != 0"],
        "s@B1.1": [{"i": "i + 1"}],

        # Final: result := flag.
        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_28/lean/SynthLean/Y2Corpus/verina_basic_28",
    wedge_threshold = 200,
    solver_timeout_ms = 600_000,
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
