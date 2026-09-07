"""modular_exponentiation — Phase X.S stretch corpus
(edge of open).

Compute b^e mod m in O(log e) time via repeated squaring.

Spec:
    Pre  : e >= 0  ∧  m >= 1
    Post : result == pow(b, e) % m

Where `pow` is a UF axiomatized as
    pow(_, 0)     == 1
    pow(b, e + 1) == b * pow(b, e)

Why this is a stretch benchmark
-------------------------------
1. **Log-time ranking.**  The classical algorithm halves `e`
   each iteration (`e := e / 2`), so the natural ranking
   function ϕ = e *strictly decreases* on each step.  This is
   exactly what POPL'10's framework supports, but every prior
   benchmark in our corpus uses unit-decrement (`i := i + 1`,
   `n := n - 1`).  This benchmark verifies the ranking-decrease
   constraint generalizes to `e' < e` without unit step — a
   load-bearing capability for any divide-and-conquer
   algorithm (mergesort, FFT, binary search by halving).

2. **Bit-decomposition invariant.**  The classical proof works
   from the invariant
        result * pow(base, e) == pow(b, e_original)  (mod m)
   tracked alongside the doubling base.  When the loop exits
   (e == 0), pow(base, 0) == 1, so result == pow(b, e_orig).

3. **Modular arithmetic.**  We need `pow` axioms plus the fact
   that `(x * y) % m == ((x % m) * (y % m)) % m` — composing
   well with Lean's `Nat.pow` lemmas or Z3's modular reasoning.

Expected outcome
----------------
- Z3 may struggle with the combined `pow` + `%` quantified
  axiom instantiation.  Lean fallthrough is the backup; we
  may need a curated `.solved.lean` for the inductive class.

Likely failure modes
--------------------
- Integer division `/2` vs. bit-shift: the standard semantics
  for nonnegative `e` is `e / 2 = floor(e/2)`, which Z3 handles
  but combined with the `pow` recurrence may need lemmas like
  `pow(b, 2*k) == pow(b*b, k)`.  We expose this as an axiom.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


# === Helper registry (§H.2 codegen) ===============================
# `lean/SynthLean/Y2Corpus/modular_exponentiation/Helpers.lean`
# ships `post_from_inv` — derives `result = pow(b, e) % m` from
# the 5-atom invariant via omega + user_axiom_0 + Int.emod_eq_of_lt.
# Atom-index conventions for tau@L0:
#   0: "exp >= 0"               2: pow_inv
#   1: "m >= 1"                 3: "result >= 0"
#   4: "result < m"
# Required: {0, 1, 2, 3, 4} — all 5 τ atoms.  Loop-modified vars
# {result, base, exp} primed at exit; m, b, e are inputs (unprimed).


def _cite_modexp_post_from_inv(chosen, hyp_for):
    h_exp_nn = hyp_for("tau@L0", 0)
    h_m = hyp_for("tau@L0", 1)
    h_pow_inv = hyp_for("tau@L0", 2)
    h_res_nn = hyp_for("tau@L0", 3)
    h_res_lt_m = hyp_for("tau@L0", 4)
    return (
        "exact SynthLean.ModExpHelpers.post_from_inv "
        f"b e m result' base' exp' "
        f"{h_exp_nn} {h_m} {h_pow_inv} {h_res_nn} {h_res_lt_m} h_not_g"
    )


def _cite_modexp_safety_branch(branch_idx: int):
    axiom_name = (
        "modexp_branch0_preserves_inv" if branch_idx == 0
        else "modexp_branch1_preserves_inv"
    )

    def cite(chosen, hyp_for):
        h_t0 = hyp_for("tau@L0", 0)
        h_t1 = hyp_for("tau@L0", 1)
        h_t2 = hyp_for("tau@L0", 2)
        h_t3 = hyp_for("tau@L0", 3)
        h_t4 = hyp_for("tau@L0", 4)
        if branch_idx == 0:
            # Branch 0 (odd) modifies {result, base, exp}.
            return (
                f"exact {axiom_name} b e m result base exp "
                f"result' base' exp' h_pre "
                f"{h_t0} {h_t1} {h_t2} {h_t3} {h_t4} h_guard "
                f"h_trans_result h_trans_base h_trans_exp"
            )
        else:
            # Branch 1 (even) modifies {base, exp}; result stays.
            # Translator emits only `base' exp'` as primed binders.
            return (
                f"exact {axiom_name} b e m result base exp "
                f"base' exp' h_pre "
                f"{h_t0} {h_t1} {h_t2} {h_t3} {h_t4} h_guard "
                f"h_trans_base h_trans_exp"
            )
    return cite


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.modular_exponentiation.Helpers",
    entries=[
        HelperEntry(
            helper_name="post_from_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post" and loop_id == "L0"),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4})},
            cite=_cite_modexp_post_from_inv,
        ),
        HelperEntry(
            helper_name="modexp_branch0_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 0),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4})},
            cite=_cite_modexp_safety_branch(0),
        ),
        HelperEntry(
            helper_name="modexp_branch1_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 1),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4})},
            cite=_cite_modexp_safety_branch(1),
        ),
    ],
)


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-19 via H.2.CODEGEN.
# History: Run 1 (1506s, 4 atoms, UNSAT — missing result<m), Run 2
# (1800s timeout, 5 atoms — added result<m, hit enumeration wall).
# Now ~70s via H.2.CODEGEN helper-citation path: bundle-post +
# 2 safety branch helpers (modexp_branchN_preserves_inv).
# Demonstrates: the τ-size-vs-enumeration tradeoff dissolves when
# the codegen short-circuits enumeration via helper match.


PROBLEM = Problem(
    description = (
        "Given a base b, a non-negative exponent e, and a positive "
        "modulus m, compute b^e mod m using O(log e) modular "
        "multiplications via repeated squaring."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("b", "int", "input"),
                Var("e", "int", "input"),
                Var("m", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("base", "int", "local"),
                Var("exp",  "int", "local")],
    pre  = "e >= 0 and m >= 1",
    post = "result == pow(b, e) % m",

    uninterpreted = [
        ("pow", ["int", "int"], "int"),
    ],
    axioms = [
        # Base case.
        "ForAll(lambda x: pow(x, 0) == 1)",
        # Successor recurrence.
        ("ForAll(lambda x, k: Implies(k >= 0, "
         " pow(x, k + 1) == x * pow(x, k)))"),
        # Square-shift identity: pow(b, 2k) == pow(b*b, k).
        ("ForAll(lambda x, k: Implies(k >= 0, "
         " pow(x, 2 * k) == pow(x * x, k)))"),
        # Modular factorization: useful for connecting result % m.
        # (Not strictly necessary if Z3 handles modular UF; included
        # to give the prover a fighting chance.)
        ("ForAll(lambda x, y, mm: Implies(mm >= 1, "
         " (x * y) % mm == ((x % mm) * (y % mm)) % mm))"),
    ],

    atoms = {
        # Initial: result := 1 % m (handles m = 1 degenerate cleanly),
        # base := b, exp := e.
        "s@B0": [{"result": "1 % m", "base": "b", "exp": "e"}],

        # Loop invariant — Z3 picks the working subset.
        "tau@L0": [
            "exp >= 0",
            "m >= 1",
            # The classical invariant: result tracks b^(e - exp) mod m,
            # base tracks b^(2^iter) mod m.  We express the conjunction
            # as a single combined atom (avoids needing iter counter).
            "result * pow(base, exp) % m == pow(b, e) % m",
            "result >= 0",
            # The crucial atom (added 2026-05-18 after debugging the
            # spec gap): result is in canonical mod-m form.  Needed
            # for the bundle-post to derive result' = pow(b, e) % m
            # (not just result' % m = pow(b, e) % m).
            "result < m",
        ],
        "g@L0":   ["exp > 0"],
        "phi@L0": ["exp"],

        # Branch 0: exp odd — fold base into result, then halve.
        "g@B1.0": ["exp % 2 == 1"],
        "s@B1.0": [{"result": "(result * base) % m",
                    "base":   "(base * base) % m",
                    "exp":    "exp // 2"}],

        # Branch 1: exp even — just halve.
        "g@B1.1": ["exp % 2 == 0"],
        "s@B1.1": [{"base": "(base * base) % m",
                    "exp":  "exp // 2"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    solver_timeout_ms = 1_800_000,  # 30 min
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/modular_exponentiation"
    ),
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    print(f"modular_exponentiation — XFAIL_REASON: {XFAIL_REASON!r}")
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1 if XFAIL_REASON is None else 0)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
