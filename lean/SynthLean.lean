-- This module serves as the root of the `SynthLean` library.
-- Import modules here that should be built as part of the library.
import SynthLean.Core
import SynthLean.Basic
import SynthLean.GridPaths
-- COST_INVS §2 — resource-bound invariant Lean library.
-- Authored polynomial identities + cost-composition lemmas;
-- cited from synth dispatch for quadratic+ cost-bound proofs
-- that wedge Z3-NIA.  See COST_INVS.md and CLAUDE.md lesson #56.
import SynthLean.CostLemmas
-- COST_INVS §3 — graph + matching axiomatized library for L1.6.
-- Bipartite / IntervalGraph predicates plus named-algorithm
-- cost axioms (Hopcroft-Karp, Glover, BucketedInterval).
import SynthLean.Graph
import SynthLean.Matching
-- Y2 corpus Tier-3 helpers (RESEARCH.md §H.1).  Each benchmark
-- with curated bundle-post or shared inductive proofs declares
-- its helpers here so they get built into .olean cache and are
-- importable from per-subset shim .solved.lean files.
import SynthLean.Y2Corpus.modular_exponentiation.Helpers
import SynthLean.Y2Corpus.majority_element.Helpers
import SynthLean.Y2Corpus.kadane_max_subarray.Helpers
import SynthLean.Y2Corpus.floyd_warshall.Helpers
import SynthLean.Y2Corpus.merge_two_sorted.Helpers
import SynthLean.Y2Corpus.insertion_sort.Helpers
import SynthLean.Y2Corpus.edit_distance.Helpers
import SynthLean.Y2Corpus.l16_aug3_two_loops.Helpers
import SynthLean.Y2Corpus.l16_aug3_three_loops.Helpers
import SynthLean.Y2Corpus.l16_aug3_three_loops_flip.Helpers
import SynthLean.Y2Corpus.l16_max_matching_recur.Helpers
import SynthLean.Y2Corpus.l16_max_matching_concrete.Helpers
import SynthLean.Y2Corpus.array_rotate_left.Helpers
import SynthLean.Y2Corpus.interval_greedy.Helpers
import SynthLean.Y2Corpus.gale_shapley.Helpers
