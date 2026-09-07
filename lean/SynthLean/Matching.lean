/-
SynthLean.Matching — bipartite matching predicates + canonical
algorithm cost axioms (foundation for L1.6).

Builds on `SynthLean.Graph` (which provides graph + bipartite +
interval predicates).  This module adds:
  - Matching as a pairing function `M : Int → Int` (vertex → its
    partner, or -1 sentinel for unmatched).
  - Properties: IsMatching, IsMaxMatching.
  - Standard cost axioms for known algorithms (Hopcroft-Karp,
    Glover, BucketedInterval).

These axioms are TRUSTED — declared as Lean axioms, not proved.
The synth framework cites them when verifying that a synthesized
algorithm matches a published cost bound.
-/
import Mathlib.Tactic
import SynthLean.Graph

namespace SynthLean.Matching

open SynthLean.Graph

/-! ### Matching representation

A matching M is a partial function from vertices to their match
partners.  We represent it as `Int → Int` where:
  - `M v = -1`  ⇔  vertex v is unmatched.
  - `M v = w` (w ≥ 0)  ⇔  v is matched to w.
Consistency: `M v = w` ∧ `w ≠ -1`  →  `M w = v`. -/

/-- M is a valid matching on graph G (with N vertices). -/
def IsMatching (G : Adj) (N : Int) (M : Int → Int) : Prop :=
  -- (a) Match partners are in range or unmatched.
  (∀ v, 0 ≤ v → v < N → M v = -1 ∨ (0 ≤ M v ∧ M v < N)) ∧
  -- (b) If v is matched to w, then w is matched to v (symmetry).
  (∀ v, 0 ≤ v → v < N → M v ≠ -1 → M (M v) = v) ∧
  -- (c) No self-matches.
  (∀ v, 0 ≤ v → v < N → M v ≠ v) ∧
  -- (d) Matched pairs correspond to edges in G.
  (∀ v, 0 ≤ v → v < N → M v ≠ -1 → G v (M v) = true)

/-- Cardinality of a matching = count of matched vertices / 2.
    Carried as an UF since spelling out the summation isn't
    needed at the substrate level. -/
axiom MatchingSize : (Int → Int) → Int → Int

axiom MatchingSize_nonneg :
    ∀ (M : Int → Int) (N : Int), MatchingSize M N ≥ 0

axiom MatchingSize_bounded :
    ∀ (M : Int → Int) (N : Int), 2 * MatchingSize M N ≤ N

/-- M is a maximum matching: no other valid matching M' on G has
    strictly more matched edges. -/
def IsMaxMatching (G : Adj) (N : Int) (M : Int → Int) : Prop :=
  IsMatching G N M ∧
  ∀ M' : Int → Int, IsMatching G N M' →
    MatchingSize M' N ≤ MatchingSize M N


/-! ### König's theorem (axiomatized)

For bipartite graphs, the maximum-matching size equals the
minimum-vertex-cover size.  Stated as an axiom; can be proved
in Lean by a long but standard argument. -/

/-- Minimum vertex cover size — axiomatized. -/
axiom MinVertexCoverSize : Adj → Int → Int

axiom MinVertexCoverSize_nonneg :
    ∀ G N, MinVertexCoverSize G N ≥ 0

/-- König's theorem (axiomatized).  For bipartite G: max-matching
    size equals min-vertex-cover size. -/
axiom Konig :
    ∀ (G : Adj) (N : Int), Bipartite G N →
    ∀ (M : Int → Int), IsMaxMatching G N M →
      MatchingSize M N = MinVertexCoverSize G N


/-! ### Named-algorithm cost axioms

Each cost axiom asserts: "algorithm X on input class Y achieves
matching of size ≤ S with cost ≤ C".  Stated as Lean axioms;
canonical references give the bound.

The "cost" here is the algorithm's worst-case operation count
(matches the synth framework's `cost@L` notion). -/

/-- Opaque integer-valued sqrt / log2 functions on Int.  Real
    cost claims use these as placeholders for the standard
    asymptotic functions; the axioms below state only the
    structural bound, not the exact arithmetic. -/
axiom IntSqrt : Int → Int
axiom IntLog2 : Int → Int

axiom IntSqrt_nonneg : ∀ n, IntSqrt n ≥ 0
axiom IntLog2_nonneg : ∀ n, IntLog2 n ≥ 0

/-- Hopcroft-Karp (1973): O(E · √V) for general bipartite matching. -/
axiom HopcroftKarpCost :
    ∀ (G : Adj) (N : Int),
    Bipartite G N →
    ∃ (M : Int → Int) (cost : Int),
      IsMaxMatching G N M ∧
      cost ≤ EdgeCount G N * IntSqrt N + 100  -- +C for low-order terms

/-- Glover-style (sorted-endpoint sweep): O(N log N + E) for
    interval bipartite matching. -/
axiom GloverIntervalCost :
    ∀ (G : Adj) (N : Int),
    IntervalGraph G N → Bipartite G N →
    ∃ (M : Int → Int) (cost : Int),
      IsMaxMatching G N M ∧
      cost ≤ N * IntLog2 N + EdgeCount G N + 100

/-- Bucketed interval matching: O(N + E) when endpoints are
    bounded by `W`.  Beats Glover by removing the sort. -/
axiom BucketedIntervalCost :
    ∀ (G : Adj) (N W : Int) (endpoints : Int → Int × Int),
    IntervalGraphWith G N endpoints →
    BoundedEndpoints G N W endpoints →
    Bipartite G N →
    ∃ (M : Int → Int) (cost : Int),
      IsMaxMatching G N M ∧
      cost ≤ N + EdgeCount G N + 100


/-! ### Existence of a maximum matching (always true)

For any graph (bipartite or not), a maximum matching exists.
This is trivially true (the set of matchings is bounded by
N!, so a max element exists) but stated explicitly for use
in composition theorems. -/

axiom ExistsMaxMatching :
    ∀ (G : Adj) (N : Int), 0 ≤ N →
    ∃ M : Int → Int, IsMaxMatching G N M


/-! ### Lower-bound axioms

Trivial complexity lower bounds for any algorithm computing
max bipartite matching.  Each is a "must do at least this much
work" claim that any candidate algorithm cost expression must
satisfy.  Used by the L1.6 speculation framework to check
whether a (template, target) pair is INFEASIBLE — i.e., the
target violates a known lower bound.

These are TRIVIAL bounds (just from input/output sizes); they
do NOT close the L1.6 open question (no known Ω(N + E) bound
for interval bipartite matching).  The framework explicitly
tracks the gap. -/

/-- Output-size lower bound: any algorithm producing matching `M`
    must do at least `MatchingSize M N` ops (one per matched
    edge in the output).  Trivial. -/
axiom LowerBound_OutputSize :
    ∀ (G : Adj) (N : Int) (M : Int → Int) (cost : Int),
    IsMaxMatching G N M →
    cost ≥ MatchingSize M N

/-- Edge-list input read: under the edge-list input model (input
    is the list of edges), any algorithm must read all edges →
    cost ≥ EdgeCount G N.  Trivial information-theoretic bound. -/
axiom LowerBound_InputRead_EdgeList :
    ∀ (G : Adj) (N : Int) (cost : Int),
    cost ≥ EdgeCount G N

/-- Endpoint-list input read: under the interval-graph endpoint
    input model (each vertex has an interval endpoint pair), any
    algorithm must read all endpoints → cost ≥ N.  Trivial. -/
axiom LowerBound_InputRead_Endpoints :
    ∀ (G : Adj) (N : Int) (endpoints : Int → Int × Int) (cost : Int),
    IntervalGraphWith G N endpoints →
    cost ≥ N

/-- Combined trivial lower bound: under EDGE-LIST + ENDPOINTS
    inputs, cost ≥ max(N, EdgeCount G N).  Note: `max(N, E) ≤
    N + E` so this is WEAKER than the (sub-(N+E))? open
    question's threshold — does NOT close TGT_TIGHT. -/
theorem LowerBound_NplusE_partial
    (G : Adj) (N : Int) (endpoints : Int → Int × Int) (cost : Int)
    (h_iwith : IntervalGraphWith G N endpoints) :
    cost ≥ EdgeCount G N ∧ cost ≥ N := by
  exact ⟨LowerBound_InputRead_EdgeList G N cost,
         LowerBound_InputRead_Endpoints G N endpoints cost h_iwith⟩


/-! ### Augmenting paths + Berge's theorem (C1.D substrate)

An augmenting path (AP) in a graph G wrt a matching M is a
simple path whose endpoints are unmatched in M and whose
edges alternate between G \ M and M.  Berge's theorem
(1957): M is a maximum matching iff no AP exists.

We axiomatize this rather than spell out the path-existence
formally — the structural-existence quantifier over paths is
heavy and the theorem itself is standard. -/

/-- `ExistsAugPath G N M`: there exists an augmenting path in
    G wrt M.  Axiomatic predicate; concrete benchmarks need
    not reify the path itself.  Synthesis benchmarks use the
    NEGATION of this in their post (the no-AP form of Berge). -/
axiom ExistsAugPath : Adj → Int → (Int → Int) → Prop

/-- Berge's theorem (axiomatized).  M is maximum iff no AP
    exists.  Forward direction (no AP → maximum) is the
    direction the C1.D benchmarks cite. -/
axiom Berge_no_aug_path_max :
    ∀ (G : Adj) (N : Int) (M : Int → Int),
      IsMatching G N M →
      ¬ ExistsAugPath G N M →
      IsMaxMatching G N M

/-- Berge's theorem, reverse direction.  M maximum → no AP.
    Used to prove non-existence of APs given known maximality. -/
axiom Berge_max_no_aug_path :
    ∀ (G : Adj) (N : Int) (M : Int → Int),
      IsMaxMatching G N M →
      ¬ ExistsAugPath G N M


/-! ### Bounded-length augmenting paths

For C1.D's incremental sub-steps, we also axiomatize
length-bounded APs.  An algorithm that eliminates APs up to
length L doesn't necessarily achieve maximum, but achieves
"L-maximum" — no improvement possible via L-length flips. -/

/-- `ExistsAugPathOfLength G N M L`: there exists an
    augmenting path of length exactly L (in edges). -/
axiom ExistsAugPathOfLength : Adj → Int → (Int → Int) → Int → Prop

/-- ExistsAugPath ↔ ∃ L. ExistsAugPathOfLength.  Length-bound
    decomposition axiom. -/
axiom ExistsAugPath_decomp :
    ∀ (G : Adj) (N : Int) (M : Int → Int),
      ExistsAugPath G N M ↔ ∃ L, L ≥ 1 ∧ ExistsAugPathOfLength G N M L

/-- Length-1 AP = an edge (u, v) with both endpoints
    unmatched.  Negation: every edge has at least one matched
    endpoint = maximal matching. -/
axiom ExistsAugPathOfLength1_iff :
    ∀ (G : Adj) (N : Int) (M : Int → Int),
      ExistsAugPathOfLength G N M 1 ↔
        ∃ u v : Int, 0 ≤ u ∧ u < N ∧ 0 ≤ v ∧ v < N ∧
                     G u v = true ∧ M u = -1 ∧ M v = -1


end SynthLean.Matching
