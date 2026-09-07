/-
================================================================================
verina_basic_47 (arraySum) — END-TO-END GLUE
================================================================================
The three sibling `.solved.lean` files each discharge ONE verification
condition, but none of them states the thing we actually care about:

    "from the precondition, the SYNTHESIZED PROGRAM halts and returns the
     specified value."

That composition normally lives (untyped, unchecked) in the Python
VC-generator + SAT layer.  This file lifts it into Lean.  See
`benchmarks/README.E2E-GLUE.md` for the full write-up.

WHAT THIS FILE PROVES
  `arraySum_total` : n ≥ 1 → ∃ s', Exec (gg n) (bb A) {0,0} s' ∧ s'.result = sum A n
  i.e. an explicit total-correctness Hoare triple {Pre} program {Post}.

HOW IT REUSES THE VCs (same τ = {0 ≤ i, i ≤ n, result = sum(A,i)})
  sc0_fallthrough (entry)          ↦ `h_entry` inside `arraySum_total`
  sc1_fallthrough (loop-inductive) ↦ `pres_lemma`  (fed to `while_rule`)
  sc4_fallthrough (post/exit)      ↦ exit reasoning inside `arraySum_total`
  ranking φ = n − i (Z3-side)      ↦ `terminates` (now IN Lean, not just Z3)

TRUST SURFACE (unchanged from the .solved.lean files)
  The three `sum` axioms below re-axiomatize VERINA's `sumTo` (base + step).
  See problem.py's docstring for the fidelity argument, and note that the
  final link `sumTo a a.size = a.toList.sum` (the "intent" tie) remains prose.

MOVED (not removed) SEAM
  `Exec`/`gg`/`bb`/`II` is a hand-written Lean model of the loop.  This file
  does NOT prove that model = synthesized.py's IR; it only shrinks the trusted
  step from "the VC-generator is sound" to "this model transliterates the IR"
  (a syntactic, mechanizable check).  See README.E2E-GLUE.md §"What's still trusted".

CHECK:  cd lean && lake env lean \
        ../benchmarks/verina/verina_basic_47/lean/SynthLean/Y2Corpus/verina_basic_47/arraySum.glue.lean
        (self-contained; no imports; core Lean only)
================================================================================
-/

namespace Glue
variable {S : Type}

/-- Big-step semantics of `while g do body`. A derivation of
    `Exec g body s s'` witnesses that the loop, started in state `s`,
    HALTS in state `s'`. (Existence of a derivation = termination.) -/
inductive Exec (g : S → Prop) (body : S → S) : S → S → Prop
  | stop (s : S) (h : ¬ g s) : Exec g body s s
  | step (s s' : S) (h : g s) (rest : Exec g body (body s) s') : Exec g body s s'

/-- REUSABLE generic while-rule (partial correctness), proven ONCE and shared
    by every single-loop benchmark. This is the composition metatheorem the
    Python VC-generator currently only asserts. -/
theorem while_rule {g : S → Prop} {body : S → S} {I : S → Prop}
    (pres : ∀ s, I s → g s → I (body s)) :
    ∀ {s s'}, Exec g body s s' → I s → I s' ∧ ¬ g s' := by
  intro s s' e
  induction e with
  | stop s h             => exact fun hi => ⟨hi, h⟩
  | step s s' hg rest ih => exact fun hi => ih (pres s hi hg)

end Glue

/- ===================== per-benchmark: arraySum ===================== -/
-- Same two recurrences the sibling .solved.lean files declare (VERINA `sumTo`):
axiom sum  : (Int → Int) → Int → Int
axiom sum0 : ∀ (A : Int → Int), sum A 0 = 0
axiom sumS : ∀ (A : Int → Int) (k : Int), k ≥ 0 → sum A (k + 1) = sum A k + A k

/-- Program state: the two live variables of `synthesized.py`. -/
structure St where
  result : Int
  i      : Int

section
variable (A : Int → Int) (n : Int)

-- The three atoms of the synthesized loop, as Lean objects:
def gg : St → Prop := fun s => s.i < n                                  -- guard  (g@L0)
def bb : St → St   := fun s => { result := s.result + A s.i, i := s.i + 1 } -- body (s@B1)
def II : St → Prop := fun s => 0 ≤ s.i ∧ s.i ≤ n ∧ s.result = sum A s.i  -- invariant (τ@L0)

/-- Content of `sc1_fallthrough` (consecution): τ is preserved by the body. -/
theorem pres_lemma : ∀ s, II A n s → gg n s → II A n (bb A s) := by
  intro s hI hg
  have h0 : 0 ≤ s.i := hI.1
  have h2 : s.result = sum A s.i := hI.2.2
  refine ⟨?_, ?_, ?_⟩
  · show 0 ≤ s.i + 1; omega
  · show s.i + 1 ≤ n; have : s.i < n := hg; omega
  · show s.result + A s.i = sum A (s.i + 1)
    rw [sumS A s.i h0, h2]

/-- Termination via the ranking function φ = n − i (ported from the Z3-side
    ranking obligation into a genuine well-founded Lean proof). -/
theorem terminates (s : St) : ∃ s', Glue.Exec (gg n) (bb A) s s' := by
  by_cases hg : gg n s
  · have hlt : s.i < n := hg
    have h := terminates (bb A s)
    exact ⟨h.choose, Glue.Exec.step s h.choose hg h.choose_spec⟩
  · exact ⟨s, Glue.Exec.stop s hg⟩
termination_by (n - s.i).toNat
decreasing_by simp only [bb]; omega

/-- CAPSTONE — the explicit total-correctness Hoare triple {Pre} program {Post}:
    from Pre (n ≥ 1) the program HALTS in some s' with s'.result = sum A n. -/
theorem arraySum_total (h_pre : n ≥ 1) :
    ∃ s', Glue.Exec (gg n) (bb A) { result := 0, i := 0 } s'
        ∧ s'.result = sum A n := by
  have hrun := terminates A n { result := 0, i := 0 }
  refine ⟨hrun.choose, hrun.choose_spec, ?_⟩
  -- entry (sc0): τ holds at the initial state
  have h_entry : II A n { result := 0, i := 0 } := by
    refine ⟨?_, ?_, ?_⟩
    · show (0:Int) ≤ 0; omega
    · show (0:Int) ≤ n; omega
    · show (0:Int) = sum A 0; exact (sum0 A).symm
  -- compose consecution across the whole run
  have hfin := Glue.while_rule (pres_lemma A n) hrun.choose_spec h_entry
  -- exit (sc4): τ ∧ ¬guard ⇒ i = n ⇒ result = sum A n
  have h1 : hrun.choose.i ≤ n := hfin.1.2.1
  have h2 : hrun.choose.result = sum A hrun.choose.i := hfin.1.2.2
  have hi_eq : hrun.choose.i = n := by
    have hng : ¬ (hrun.choose.i < n) := hfin.2
    omega
  rw [h2, hi_eq]

end

-- No `sorry`; only domain axioms are the three `sum` recurrences above.
#print axioms arraySum_total
