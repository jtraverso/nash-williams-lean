/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveBlockTailsStage199

/-! # Query tails refer to the actual triangle-union reserve

No independent physical-edge trials are introduced. The independent
coordinates are packing triangles, and success implies both real legs.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReservePhysicalQueryStage200

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks ReserveBlockTailsStage199

variable {V : Type} [DecidableEq V] {t : ℕ}

def selected (D : Finset (Finset V)) (ω : Finset V → Bool) : Finset (Finset V) :=
  D.filter fun s => ω s = true

def reserve (D : Finset (Finset V)) (ω : Finset V → Bool) : Finset (Sym2 V) :=
  (selected D ω).biUnion triEdges

def queryBlocks (D : Finset (Finset V)) (u v w : V) : Finset (Finset V) :=
  D.filter fun s => s(u, w) ∈ triEdges s ∨ s(v, w) ∈ triEdges s

noncomputable def neighbours (D : Finset (Finset V)) (u v : V) (C : Finset V)
    (ω : Finset V → Bool) : Finset V :=
  C.filter fun w => s(u, w) ∈ reserve D ω ∧ s(v, w) ∈ reserve D ω

theorem sampled_edge_iff (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (e : Sym2 V) (he : e ∈ Q) (ω : Finset V → Bool) :
    e ∈ reserve D ω ↔ ∀ s ∈ D, e ∈ triEdges s → ω s = true := by
  classical
  constructor
  · intro h s hs hes
    obtain ⟨a, ha, hea⟩ := mem_biUnion.mp h
    obtain ⟨haD, hamark⟩ := mem_filter.mp ha
    have heq : a = s := by
      by_contra hne
      exact disjoint_left.mp (hD.2.1 haD hs hne) hea hes
    exact heq ▸ hamark
  · intro h
    rw [← hD.2.2] at he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨s, mem_filter.mpr ⟨hs, h s hs hes⟩, hes⟩

theorem query_event_iff (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (u v w : V) (huw : s(u, w) ∈ Q) (hvw : s(v, w) ∈ Q) (ω : Finset V → Bool) :
    ω ∈ blockEvent (fun s => {ω : Finset V → Bool | ω s = true}) (queryBlocks D u v w) ↔
      s(u, w) ∈ reserve D ω ∧ s(v, w) ∈ reserve D ω := by
  rw [sampled_edge_iff p F Q D hD _ huw, sampled_edge_iff p F Q D hD _ hvw]
  simp only [blockEvent, Set.mem_iInter, Set.mem_setOf_eq, queryBlocks, mem_filter]
  constructor
  · intro h
    exact ⟨fun s hs he => h s ⟨hs, Or.inl he⟩, fun s hs he => h s ⟨hs, Or.inr he⟩⟩
  · rintro ⟨h₁, h₂⟩ s ⟨hs, he⟩
    rcases he with he | he
    · exact h₁ s hs he
    · exact h₂ s hs he

theorem physical_query_lower_tail (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (u v : V) (huv : u ≠ v) (C : Finset V) (hC : 2 ≤ C.card)
    (hlegs : ∀ w ∈ C, s(u, w) ∈ Q ∧ s(v, w) ∈ Q)
    (hroot : ∀ w ∈ C, w ≠ u ∧ w ≠ v)
    (μ : Measure (Finset V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun s => {ω | ω s = true}) μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmarg : ∀ s, μ {ω | ω s = true} = ENNReal.ofReal ρ) :
    μ.real {ω | ((neighbours D u v C ω).card : ℝ) ≤ ρ ^ 2 * (C.card - 1 : ℝ) / 6} ≤
      Real.exp (-ρ ^ 4 * (C.card - 1 : ℝ) / 6) := by
  classical
  obtain ⟨I, hIC, hcount, hcard, hdis⟩ :=
    ReserveTwoBlockTrialsStage198.extract_two_block_trials p F Q D hD u v huv C hlegs hroot
  have hI : I.Nonempty := by
    apply card_pos.mp
    omega
  have hc : (C.card : ℝ) - 1 ≤ 3 * (I.card : ℝ) := by
    have hh : (C.card : ℝ) ≤ 1 + 3 * (I.card : ℝ) := by exact_mod_cast hcount
    linarith
  have hb := two_block_lower_tail μ hind ρ hρ hmarg I hI (queryBlocks D u v)
    hcard hdis
  have hsub : {ω | ((neighbours D u v C ω).card : ℝ) ≤ ρ ^ 2 * (C.card - 1 : ℝ) / 6} ⊆
      {ω | ((successes I (queryBlocks D u v) ω).card : ℝ) ≤ ρ ^ 2 * I.card / 2} := by
    intro ω hω
    have hs : successes I (queryBlocks D u v) ω ⊆ neighbours D u v C ω := by
      intro w hw
      obtain ⟨hwI, hm⟩ := mem_filter.mp hw
      have hl := hlegs w (hIC hwI)
      refine mem_filter.mpr ⟨hIC hwI, ?_⟩
      apply (query_event_iff p F Q D hD u v w hl.1 hl.2 ω).mp
      simpa only [blockEvent, Set.mem_iInter, Set.mem_setOf_eq] using hm
    have hdeg : ((successes I (queryBlocks D u v) ω).card : ℝ) ≤ (neighbours D u v C ω).card :=
      Nat.cast_le.mpr (card_le_card hs)
    change ((neighbours D u v C ω).card : ℝ) ≤ _ at hω
    change ((successes I (queryBlocks D u v) ω).card : ℝ) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg ρ)]
  apply (measureReal_mono hsub).trans (hb.trans (Real.exp_le_exp.mpr ?_))
  nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg hρ 4)]


end PartitionedTriangleAbsorption.ReservePhysicalQueryStage200
