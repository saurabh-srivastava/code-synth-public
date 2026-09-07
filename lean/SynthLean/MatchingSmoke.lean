/-
SynthLean.MatchingSmoke — composition smoke for §3.

Demonstrates that the axiomatized graph + matching library
composes cleanly.  Each theorem here cites one or more axioms
from Graph.lean / Matching.lean and would be the kind of
"L1.6 composition theorem" the synth framework cites during
template-class speculation.

These proofs are intentionally trivial — the framework's job is
to find synthesized algorithms whose proof obligations match
these shapes; here we just confirm the citations type-check.
-/
import Mathlib.Tactic
import SynthLean.Graph
import SynthLean.Matching

namespace SynthLean.MatchingSmoke

open SynthLean.Graph SynthLean.Matching

/-! ### Composition: existence of a max matching at a cost bound -/

/-- For any bipartite graph, Hopcroft-Karp delivers a maximum
    matching at cost ≤ E·√V + C.  Trivial citation. -/
theorem hopcroft_karp_existence
    (G : Adj) (N : Int) (h_bip : Bipartite G N) :
    ∃ (M : Int → Int) (cost : Int),
      IsMaxMatching G N M ∧
      cost ≤ EdgeCount G N * IntSqrt N + 100 :=
  HopcroftKarpCost G N h_bip

/-- For interval bipartite graphs, Glover delivers a max matching
    at cost ≤ N·log₂N + E + C — strictly better than Hopcroft-Karp
    when the input is interval-structured. -/
theorem glover_beats_hopcroft_karp_on_intervals
    (G : Adj) (N : Int)
    (h_int : IntervalGraph G N) (h_bip : Bipartite G N) :
    ∃ (M : Int → Int) (cost : Int),
      IsMaxMatching G N M ∧
      cost ≤ N * IntLog2 N + EdgeCount G N + 100 :=
  GloverIntervalCost G N h_int h_bip

/-- For interval bipartite graphs with bounded endpoints, the
    bucketed algorithm beats even Glover — cost ≤ N + E + C.
    This is the L1.6 open question's known upper bound. -/
theorem bucketed_beats_glover
    (G : Adj) (N W : Int) (endpoints : Int → Int × Int)
    (h_iwith : IntervalGraphWith G N endpoints)
    (h_bnd   : BoundedEndpoints G N W endpoints)
    (h_bip   : Bipartite G N) :
    ∃ (M : Int → Int) (cost : Int),
      IsMaxMatching G N M ∧
      cost ≤ N + EdgeCount G N + 100 :=
  BucketedIntervalCost G N W endpoints h_iwith h_bnd h_bip


/-! ### A speculation-style claim

The L1.6 search target: is there an algorithm beating O(N + E)
on interval bipartite graphs?  Equivalently: ∃ algorithm with
cost < N + E + C (subset relation on growth rates).

This is currently OPEN; we cannot discharge it without either:
  (a) A concrete algorithm with proven sub-linear bound (would
      yield a new theorem in this module), OR
  (b) A lower-bound proof showing N + E is tight.

We state the claim shape here as a `target` predicate — the
synth framework would search for templates that satisfy it. -/

/-- L1.6 target: ∃ algorithm achieving sub-(N + E) cost on
    interval bipartite graphs.  Open. -/
def L16Target (G : Adj) (N W : Int)
    (endpoints : Int → Int × Int) (k : Int) : Prop :=
  IntervalGraphWith G N endpoints →
  BoundedEndpoints G N W endpoints →
  Bipartite G N →
  ∃ (M : Int → Int) (cost : Int),
    IsMaxMatching G N M ∧
    cost ≤ N + EdgeCount G N + k - 1   -- k = 0 ⇒ strict improvement


end SynthLean.MatchingSmoke
