/-
SynthLean.Graph — axiomatized graph predicates for L1.6 (bipartite
matching) and related catalog targets.

Design: the synth framework's pattern from L1.2 / L1.5 is to
declare verified sub-algorithms / structural facts as Lean axioms
(or theorems where short proofs are available) and let Z3 thread
the parametric search on top.  This module follows that pattern
for graph predicates.

The graph is represented abstractly: a graph G on N vertices is
an adjacency function `adj : Int → Int → Bool` where
`adj u v = true` iff edge (u, v) exists.  We use `Int` (not `Nat`)
for parity with the rest of the framework's Int-indexed arrays.

Vertices are integers in [0, N).  Out-of-range indices are
allowed by `adj` but expected to be False.

This module is a SUBSTRATE — concrete graph theorems and cost
lemmas live in `Matching.lean` and `IntervalMatching.lean`.
-/
import Mathlib.Tactic

namespace SynthLean.Graph

/-! ### Graph representation -/

/-- A graph on N vertices, given by its adjacency function.
    `Adj u v = true` ↔ edge (u, v) exists.  Undirected unless
    constrained otherwise (see `Undirected`).

    The cardinality `N : Int` is carried separately rather than
    encoded into a sigma type — matches how our existing
    benchmarks pass an `n : Int` input alongside an `A : Int → Int`
    array. -/
abbrev Adj := Int → Int → Bool

/-- The graph is undirected: edges are symmetric. -/
def Undirected (G : Adj) : Prop :=
  ∀ u v : Int, G u v = G v u

/-- An edge connects two vertices in range [0, N). -/
def InRangeEdge (N : Int) (u v : Int) : Prop :=
  0 ≤ u ∧ u < N ∧ 0 ≤ v ∧ v < N

/-- The graph is loop-free: no self-edges. -/
def Simple (G : Adj) : Prop :=
  ∀ u : Int, G u u = false


/-! ### Bipartite graphs

A graph is bipartite iff its vertex set partitions into two parts
such that every edge has endpoints in different parts.

We express bipartiteness via an explicit 2-coloring witness:
`color : Int → Bool` (true / false picks part).  An edge (u, v)
is valid iff `color u ≠ color v`. -/

/-- `G` is bipartite on `N` vertices with the given 2-coloring. -/
def BipartiteWithColor (G : Adj) (N : Int) (color : Int → Bool) : Prop :=
  ∀ u v : Int, 0 ≤ u → u < N → 0 ≤ v → v < N →
    G u v = true → color u ≠ color v

/-- `G` is bipartite (some 2-coloring exists). -/
def Bipartite (G : Adj) (N : Int) : Prop :=
  ∃ color : Int → Bool, BipartiteWithColor G N color


/-! ### Interval graphs

An interval graph is one whose vertices correspond to intervals on
the real line, with edges between overlapping intervals.  For
bipartite interval graphs (the L1.6 setting), intervals are split
into two classes (one per bipartition side) and edges connect
overlapping intervals from different classes.

We axiomatize the interval-graph property as a predicate without
spelling out the full geometric definition; concrete benchmarks
can refine. -/

/-- `G` is an interval graph on `N` vertices.  Carries a witness:
    `endpoints : Int → Int × Int` mapping each vertex to (left, right)
    such that edges correspond to interval overlaps. -/
def IntervalGraphWith (G : Adj) (N : Int)
    (endpoints : Int → Int × Int) : Prop :=
  ∀ u v : Int, 0 ≤ u → u < N → 0 ≤ v → v < N → u ≠ v →
    G u v = true ↔ (
      let (lu, ru) := endpoints u
      let (lv, rv) := endpoints v
      lu ≤ rv ∧ lv ≤ ru)

/-- `G` is an interval graph (some endpoint assignment exists). -/
def IntervalGraph (G : Adj) (N : Int) : Prop :=
  ∃ endpoints : Int → Int × Int, IntervalGraphWith G N endpoints

/-- Bounded-endpoint interval graph: all endpoints in `[0, W)`.
    Enables radix-sort-style linear-time algorithms. -/
def BoundedEndpoints (G : Adj) (N W : Int)
    (endpoints : Int → Int × Int) : Prop :=
  IntervalGraphWith G N endpoints ∧
  ∀ u : Int, 0 ≤ u → u < N →
    0 ≤ (endpoints u).1 ∧ (endpoints u).1 < W ∧
    0 ≤ (endpoints u).2 ∧ (endpoints u).2 < W


/-! ### Vertex degree and edge count

These functions are conceptually summations — encoded as opaque
UFs for now since closed-form summation lemmas aren't needed at
this stage.  When concrete benchmarks need them, we'll either
spell them out (`Finset.card`-based) or axiomatize specific
identities. -/

/-- Total edge count (over directed pairs / 2 for undirected). -/
axiom EdgeCount : Adj → Int → Int

/-- Degree of vertex v in G. -/
axiom Degree : Adj → Int → Int → Int

axiom EdgeCount_nonneg : ∀ G N, EdgeCount G N ≥ 0
axiom Degree_nonneg    : ∀ G N v, Degree G N v ≥ 0


end SynthLean.Graph
