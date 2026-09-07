"""verina_basic_9 — hasCommonElement (ported from VERINA-basic).

Upstream: VERINA `verina_basic_9` (dafny-synthesis task_id_431).

    signature : hasCommonElement(a : Array Int, b : Array Int) -> Bool
    precond   : a.size > 0 ∧ b.size > 0
    reference : a.any fun x => b.any fun y => x = y
    postcond  : (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result

i.e. `result` is true iff `a` and `b` share at least one element.

Framework encoding
------------------
    inputs : a : int[], b : int[], na = a.size, nb = b.size
    Pre    : na > 0 and nb > 0            (VERINA a.size > 0 ∧ b.size > 0)
    Post   : ((result == 1) and  ∃p<na. ∃j<nb. a[p] == b[j]) or
             ((result == 0) and  ∀p<na. ∀j<nb. a[p] != b[j])

Bool→int modeling.  Our IR is integer-valued, so the Bool `result`
is modeled as an int with the convention `result == 1` ⇔ true,
`result == 0` ⇔ false.  VERINA's `↔` is rendered as the standard
all_positive-style disjunction over the two result values (the two
branches only ever assign 0 or 1, so `result ∈ {0,1}` holds in
every satisfying solution).

AXIOM-FREE (P-2).  The double existential is kept *verbatim* in the
post and in the loop invariant — it is NOT abstracted into an
uninterpreted fold.  The inner array membership (`a[i] appears in b`)
is expressed as a quantified *guard* `∃j<nb. a[i] == b[j]`, so the
algorithm stays a single outer pass over `a` (no nested Loop, no UF).
This is pure Z3: the discharge rests only on Z3's quantifier
instantiation, so the trust surface is exactly VERINA's own spec.

Algorithm (single outer pass over a, with a monotone `found` flag):

    found := 0; i := 0;
    while (i < na):
        if (∃j<nb. a[i] == b[j]):  found := 1; i := i + 1;   // match at i
        else:                       i := i + 1;               // no match at i
    result := found;

Loop invariant τ@L0 (the flag mirrors "a match exists in prefix a[0..i)"):
    0 <= i <= na, na >= 0, nb >= 0, and
    (found == 1 ∧ ∃p<i. ∃j<nb. a[p] == b[j]) ∨
    (found == 0 ∧ ∀p<i. ∀j<nb. a[p] != b[j])

At loop exit i == na, so τ collapses to exactly the postcondition.

SPEC-FIDELITY NOTE
------------------
Our post is a faithful, structure-preserving rendering of VERINA's
`(∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result`:
  * `na`/`nb` stand for `a.size`/`b.size` (Nat sizes, so `≥ 0`; pre
    keeps VERINA's strict `> 0`).
  * VERINA's panic-get `a[i]!` / `b[j]!` under the in-range guards
    `i < a.size` / `j < b.size` equals the safe read `a[i]` / `b[j]`,
    which is what our `a[p]` / `b[j]` denote.
  * the `↔` is the two-way disjunction: `result == 1` on the ∃∃
    side, `result == 0` on the ∀∀ (= negated ∃∃) side.
No fold/count UF is introduced, so there is NO extra fidelity gap to
argue and NO trust axiom: the existential in our post IS VERINA's.

TRUST SURFACE: none beyond Z3 (no uninterpreted functions, no axioms).
"""
from synth import Problem, SB, Loop, Var, solve


# "some element of b[0..nb) equals x" — the inner membership test.
def _MEMB(x: str) -> str:
    return f"Exists(lambda j: 0 <= j and j < nb and {x} == b[j])"


def _NO_MEMB(x: str) -> str:
    return f"ForAll(lambda j: Implies(0 <= j and j < nb, {x} != b[j]))"


# "a[p] shares an element with b, for some p in [0, UB)".
def _ANY_COMMON(ub: str) -> str:
    return (f"Exists(lambda p: 0 <= p and p < {ub} and "
            f"Exists(lambda j: 0 <= j and j < nb and a[p] == b[j]))")


def _NO_COMMON(ub: str) -> str:
    return (f"ForAll(lambda p: Implies(0 <= p and p < {ub}, "
            f"ForAll(lambda j: Implies(0 <= j and j < nb, a[p] != b[j]))))")


PROBLEM = Problem(
    description = (
        "Given two integer arrays a and b (both non-empty), return 1 "
        "if they share at least one common element, otherwise 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("a", "int[]", "input"),
                Var("b", "int[]", "input"),
                Var("na", "int", "input"),
                Var("nb", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("found", "int", "local"),
                Var("i", "int", "local")],

    pre  = "na > 0 and nb > 0",
    post = (
        f"((result == 1) and {_ANY_COMMON('na')}) or "
        f"((result == 0) and {_NO_COMMON('na')})"
    ),

    atoms = {
        # Init: found := 0, i := 0.
        "s@B0": [{"found": "0", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= na",
            "na >= 0",
            "nb >= 0",
            # found is 1 iff a match exists in the scanned prefix a[0..i).
            (f"((found == 1) and {_ANY_COMMON('i')}) or "
             f"((found == 0) and {_NO_COMMON('i')})"),
        ],
        "g@L0":   ["i < na"],
        "phi@L0": ["na - i"],

        # Branch 0: a[i] occurs somewhere in b → found := 1, advance i.
        "g@B1.0": [_MEMB("a[i]")],
        "s@B1.0": [{"found": "1", "i": "i + 1"}],
        # Branch 1: a[i] occurs nowhere in b → advance i (found unchanged).
        "g@B1.1": [_NO_MEMB("a[i]")],
        "s@B1.1": [{"i": "i + 1"}],

        # Final: result := found.
        "s@B2": [{"result": "found"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_9/lean/SynthLean/Y2Corpus/verina_basic_9",
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
