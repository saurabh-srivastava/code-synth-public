"""speculate.py — L1.6 template-class speculation framework.

For each candidate (template, cost-target) pair, query Lean
whether the cost axiom for that template closes the obligation
`cost ≤ target`.  Same L1.2-pattern shape but at the cost-bound
level rather than the bilinear-rank level.

Templates considered (per COST_INVS.md §3):
  T1  Glover                — sorted sweep        O(N log N + E)
  T2  Bucketed              — bucket-fill scan    O(N + E)
  T3  Greedy                — adjacency walk      O(E)        [incorrect on general]
  T4  Hopcroft-Karp         — BFS-layered         O(E·√V)
  T5  Radix-Sweep           — radix sort + sweep  O(N + E)

Cost targets tried:
  TGT_LOOSE = N·log₂N + E + 100   (Glover-level)
  TGT_LINEAR = N + E + 100        (Bucketed-level — known best)
  TGT_TIGHT  = N + E              (sub-(N+E) — the L1.6 OPEN target)

Each (template, target) pair generates a Lean theorem of the form:

  ∀ G N W endpoints,
    IntervalGraphWith G N endpoints →
    BoundedEndpoints G N W endpoints →
    Bipartite G N →
    ∃ M cost, IsMaxMatching G N M ∧ cost ≤ <target>

The proof body cites the template's cost axiom (HopcroftKarpCost,
GloverIntervalCost, or BucketedIntervalCost) and we check whether
Lean can discharge `<axiom_bound> ≤ <target>` via omega.

SAT (Lean closes proof) → template achieves target.
UNSAT (Lean can't close + we can produce counterexample) →
template definitely fails target.
"unknown" / "error" → indeterminate.

This is the L1.2-pattern Lean-axiomatized speculation, applied
to L1.6's template space.
"""
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


REPO = Path("/Users/saurabh/code/synthesizer").resolve()
LEAN_DIR = REPO / "lean"


@dataclass
class TemplateClass:
    name: str
    description: str
    cost_axiom: str     # e.g., "HopcroftKarpCost"
    cost_bound: str     # Lean expression, e.g., "EdgeCount G N * IntSqrt N + 100"
    preconditions: list[str]   # e.g., ["Bipartite G N"]


@dataclass
class CostTarget:
    name: str
    expr: str           # Lean expression


TEMPLATES = [
    TemplateClass(
        name="T1_Glover",
        description="Sort endpoints O(N log N), then linear sweep O(N + E)",
        cost_axiom="GloverIntervalCost",
        cost_bound="N * IntLog2 N + EdgeCount G N + 100",
        preconditions=["IntervalGraph G N", "Bipartite G N"],
    ),
    TemplateClass(
        name="T2_Bucketed",
        description="Bucket-fill on bounded endpoints, then linear scan",
        cost_axiom="BucketedIntervalCost",
        cost_bound="N + EdgeCount G N + 100",
        preconditions=[
            "IntervalGraphWith G N endpoints",
            "BoundedEndpoints G N W endpoints",
            "Bipartite G N",
        ],
    ),
    TemplateClass(
        name="T4_HopcroftKarp",
        description="BFS-layered augmenting paths",
        cost_axiom="HopcroftKarpCost",
        cost_bound="EdgeCount G N * IntSqrt N + 100",
        preconditions=["Bipartite G N"],
    ),
]


TARGETS = [
    CostTarget(name="TGT_LOOSE_NlogN",
               expr="N * IntLog2 N + EdgeCount G N + 200"),
    CostTarget(name="TGT_LINEAR_N_PLUS_E",
               expr="N + EdgeCount G N + 200"),
    CostTarget(name="TGT_TIGHT_OPEN",
               expr="N + EdgeCount G N - 1"),
]


def lean_theorem_for(tc: TemplateClass, ct: CostTarget) -> str:
    """Emit a Lean theorem asking 'does template TC's cost axiom
    imply cost ≤ target CT's expression'?"""
    # Build the hypotheses list.
    if tc.name == "T2_Bucketed":
        # T2 has the endpoints + bounded-endpoints arguments.
        params = "(G : Adj) (N W : Int) (endpoints : Int → Int × Int)"
        hyps = [
            "(h_iwith : IntervalGraphWith G N endpoints)",
            "(h_bnd : BoundedEndpoints G N W endpoints)",
            "(h_bip : Bipartite G N)",
        ]
        axiom_call = f"{tc.cost_axiom} G N W endpoints h_iwith h_bnd h_bip"
    elif tc.name == "T1_Glover":
        params = "(G : Adj) (N : Int)"
        hyps = [
            "(h_int : IntervalGraph G N)",
            "(h_bip : Bipartite G N)",
        ]
        axiom_call = f"{tc.cost_axiom} G N h_int h_bip"
    else:  # T4_HopcroftKarp
        params = "(G : Adj) (N : Int)"
        hyps = ["(h_bip : Bipartite G N)"]
        axiom_call = f"{tc.cost_axiom} G N h_bip"

    target_expr = ct.expr

    # Conclusion: ∃ M cost, IsMaxMatching G N M ∧ cost ≤ target.
    conclusion = (
        "∃ (M : Int → Int) (cost : Int), "
        "IsMaxMatching G N M ∧ cost ≤ "
        f"({target_expr})"
    )

    # Proof: obtain (M, cost, hM, hcost) from the cost axiom, then
    # chain `cost ≤ <bound>` to `cost ≤ <target>` via the target
    # being structurally ≥ the bound.  linarith handles trivial
    # additive slack; nlinarith handles multiplicative shape diffs.
    hyps_block = "\n    ".join(hyps)
    name = f"speculate_{tc.name}_vs_{ct.name}"
    return f"""set_option linter.unusedVariables false in
open SynthLean.Graph SynthLean.Matching in
theorem {name}
    {params}
    {hyps_block} :
    {conclusion} := by
  obtain ⟨M, cost, hM, hcost⟩ := {axiom_call}
  refine ⟨M, cost, hM, ?_⟩
  have h_sqrt := IntSqrt_nonneg N
  have h_log2 := IntLog2_nonneg N
  have h_ec := EdgeCount_nonneg G N
  first
    | linarith
    | nlinarith [hcost, h_sqrt, h_log2, h_ec]
    | nlinarith [hcost, h_sqrt, h_log2, h_ec,
                 mul_nonneg h_ec h_sqrt]
"""


def run_lean(theorem_text: str, timeout_s: int = 60) -> tuple[str, float]:
    """Write theorem to a temp file and try to compile via lake.
    Returns (status, elapsed) where status ∈ {valid, invalid, error, timeout}."""
    src = (
        "import Mathlib.Tactic\n"
        "import SynthLean.Graph\n"
        "import SynthLean.Matching\n"
        "\n"
        + theorem_text
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=str(LEAN_DIR / "SynthLean"),
        delete=False,
    ) as f:
        f.write(src)
        tmp_path = Path(f.name)
    try:
        t0 = time.monotonic()
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(tmp_path)],
                capture_output=True, text=True,
                cwd=str(LEAN_DIR), timeout=timeout_s,
            )
            elapsed = time.monotonic() - t0
            if result.returncode == 0:
                return "valid", elapsed
            # "Failed to prove" patterns Lean emits when a tactic
            # leaves goals open (= invalid for our purpose).  Match
            # specific failure markers, not just tactic names.
            err_text = (result.stdout + result.stderr).lower()
            failure_markers = (
                "linarith failed", "nlinarith failed",
                "tactic 'linarith' failed", "tactic 'nlinarith' failed",
                "unsolved goals", "no progress",
            )
            if any(m in err_text for m in failure_markers):
                return "invalid", elapsed
            return "error", elapsed
        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - t0
            return "timeout", elapsed
    finally:
        try:
            tmp_path.unlink()
        except FileNotFoundError:
            pass


def lean_lower_bound_check(ct: CostTarget) -> str:
    """Emit a Lean theorem asking 'does any of the trivial lower
    bounds CONTRADICT target CT?'.

    If the cost lower bound (max(N, EdgeCount)) exceeds the target,
    the target is INFEASIBLE under any algorithm — closes that
    target in the negative.

    For our trivial bounds, max(N, E) > N + E - 1 only when N + E
    is < max(N, E) + 1, which is never (N + E ≥ max(N, E) always).
    So the trivial bounds CAN'T close TGT_TIGHT (= N + E - 1).
    The framework reports this honestly.
    """
    return f"""set_option linter.unusedVariables false in
open SynthLean.Graph SynthLean.Matching in
theorem lower_bound_vs_{ct.name}
    (G : Adj) (N : Int) (endpoints : Int → Int × Int)
    (h_iwith : IntervalGraphWith G N endpoints)
    (cost : Int)
    (h_alg : cost ≤ ({ct.expr})) :
    False := by
  have h_E := LowerBound_InputRead_EdgeList G N cost
  have h_N := LowerBound_InputRead_Endpoints G N endpoints cost h_iwith
  have h_ec := EdgeCount_nonneg G N
  -- If the lower bound contradicts the target, this closes.
  -- Trivial bounds give cost ≥ max(N, E); target gives cost ≤ <target>.
  -- Contradiction requires max(N, E) > <target>.
  first
    | linarith
    | nlinarith [h_E, h_N, h_ec]
"""


def main():
    print("L1.6 template-class speculation framework")
    print("=" * 70)
    print(f"{'Template':<20} {'Target':<28} {'Verdict':<10} {'Time':>8}")
    print("-" * 70)
    results: list[tuple[TemplateClass, CostTarget, str, float]] = []
    for tc in TEMPLATES:
        for ct in TARGETS:
            theorem = lean_theorem_for(tc, ct)
            verdict, elapsed = run_lean(theorem, timeout_s=60)
            print(f"{tc.name:<20} {ct.name:<28} {verdict:<10} {elapsed:>7.2f}s")
            sys.stdout.flush()
            results.append((tc, ct, verdict, elapsed))

    print()
    print("Lower-bound CONTRADICTION check (against trivial Ω(max(N,E)) bounds):")
    print(f"{'Target':<28} {'Lower-bd kills?':<18} {'Time':>8}")
    print("-" * 70)
    lb_results: list[tuple[CostTarget, str, float]] = []
    for ct in TARGETS:
        theorem = lean_lower_bound_check(ct)
        verdict, elapsed = run_lean(theorem, timeout_s=60)
        kill_flag = (verdict == "valid")
        kill_str = "YES (target infeasible)" if kill_flag else "no  (target survives)"
        print(f"{ct.name:<28} {kill_str:<18} {elapsed:>7.2f}s")
        sys.stdout.flush()
        lb_results.append((ct, verdict, elapsed))

    print()
    print("Summary:")
    print("-" * 70)
    valid_pairs = [(tc, ct) for tc, ct, v, _ in results if v == "valid"]
    invalid_pairs = [(tc, ct) for tc, ct, v, _ in results if v == "invalid"]
    print(f"  Valid:   {len(valid_pairs)}  "
          f"(template ⊕ target where cost axiom dominates)")
    print(f"  Invalid: {len(invalid_pairs)}  "
          f"(template cost axiom does NOT dominate target)")
    print()
    killed = [ct for ct, v, _ in lb_results if v == "valid"]
    survive = [ct for ct, v, _ in lb_results if v != "valid"]
    print(f"  Targets killed by lower bound: {len(killed)}")
    print(f"  Targets surviving (gap remains): {len(survive)}")
    print()
    print("Valid (T, target) pairs:")
    for tc, ct in valid_pairs:
        print(f"  ✓ {tc.name}  ⇒  {ct.name}")
    if killed:
        print()
        print("Targets the trivial lower bounds CLOSE:")
        for ct in killed:
            print(f"  ⊥ {ct.name}  (no algorithm can achieve)")
    if survive:
        print()
        print("Targets surviving trivial lower bounds (gap to upper bound):")
        for ct in survive:
            ub_valid_for_ct = [tc for tc, ct2 in valid_pairs if ct2.name == ct.name]
            if ub_valid_for_ct:
                ub_str = f"upper achieved by {ub_valid_for_ct[0].name}"
            else:
                ub_str = "*** OPEN — no known upper, no closing lower bound ***"
            print(f"  ◯ {ct.name}: {ub_str}")


if __name__ == "__main__":
    main()
