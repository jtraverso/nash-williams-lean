/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.FiniteTemplates
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalParity
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TorsionRefiner

/-! # Concrete charge and torsion tokens in a guarded host

The templates and their charges are fixed finite objects. Their entire physical
family is supplied by `guarded_template_family_scaled`, before any leftover is
chosen. The theorems give the exact token interfaces consumed by both layers.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open GuardedTemplates

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem F1Good_image {W : Type*} [DecidableEq W]
    (f : W → V) (hf : Function.Injective f) (p : V → Fin 4) (label : W → Fin 4)
    (hlabel : ∀ w, p (f w) = label w) (E : Finset (Sym2 W)) (hE : F1Good label E) :
    F1Good p (E.image (Sym2.map f)) := by
  exact ⟨loopless_image f hf E hE.1, active_image F1 f p label hlabel E hE.2.1,
    even_image f hf E hE.2.2.1, (f1FreeCharge_image f hf p label hlabel E).trans hE.2.2.2⟩

omit [Fintype V] in
theorem F2Good_image {W : Type*} [DecidableEq W]
    (f : W → V) (hf : Function.Injective f) (p : V → Fin 4) (label : W → Fin 4)
    (hlabel : ∀ w, p (f w) = label w) (E : Finset (Sym2 W)) (hE : F2Good label E) :
    F2Good p (E.image (Sym2.map f)) := by
  exact ⟨loopless_image f hf E hE.1, active_image F2 f p label hlabel E hE.2.1,
    even_image f hf E hE.2.2.1, (f2FreeCharge_image f hf p label hlabel E).trans hE.2.2.2⟩

omit [Fintype V] in
theorem torsion_F1_image (f : Fin 6 → V) (hf : Function.Injective f)
    (p : V → Fin 4) (hlabel : ∀ w, p (f w) = torsionF1Label w) :
    F1Good p (mapped cycleSlots f) ∧ (f1Parity p).value (mapped cycleSlots f) = 1 := by
  refine ⟨F1Good_image f hf p torsionF1Label hlabel cycleSlots
    ⟨cycleSlots_loopless, torsion_active_F1, cycleSlots_even, torsion_freeCharge_F1⟩, ?_⟩
  change intParity (unorderedCount p (cycleSlots.image (Sym2.map f)) 0 2) = 1
  rw [unorderedCount_image f hf p torsionF1Label hlabel, torsion_count_F1]
  decide

set_option maxHeartbeats 600000 in
theorem torsion_F2_image (f : Fin 6 → V) (hf : Function.Injective f)
    (p : V → Fin 4) (hlabel : ∀ w, p (f w) = torsionF2Label w) :
    F2Good p (mapped cycleSlots f) ∧ (f2Parity p).value (mapped cycleSlots f) = 1 := by
  refine ⟨F2Good_image f hf p torsionF2Label hlabel cycleSlots
    ⟨cycleSlots_loopless, torsion_active_F2, cycleSlots_even, torsion_freeCharge_F2⟩, ?_⟩
  change f2Bit p (mapped cycleSlots f) = 1
  unfold f2Bit mapped
  rw [f2Numerator_image f hf p torsionF2Label hlabel, torsion_numerator_F2]
  decide

/-- The common concrete signed-charge supply; F1/F2 supply its four finite data
lemmas from `FiniteTemplates`. -/
theorem host_charge_tokens {κ : Type*}
    (F : Finset (Multiset (Fin 4))) (χ : Fin 4 → Fin 4 → ℤ)
    (hplus : ActiveEdges F plusLabel triangleSlots) (hminus : ActiveEdges F minusLabel cycleSlots)
    (hplusCharge : charge χ plusLabel triangleSlots = 12)
    (hminusCharge : charge χ minusLabel cycleSlots = -12)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Tok κ)) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : Tok κ → Finset (Sym2 V), TokReal χ (fun _ _ => 0) p 12 6 B S tok ∧
      (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V := by
  classical
  let E : Tok κ → Finset (Sym2 (Fin 6)) := fun τ => if τ.sign then triangleSlots else cycleSlots
  let label : Tok κ → Fin 6 → Fin 4 := fun τ => if τ.sign then plusLabel else minusLabel
  have hdata (τ : Tok κ) : (∀ e ∈ E τ, ¬ e.IsDiag) ∧ ActiveEdges F (label τ) (E τ) ∧
      (∀ w, Even (incidentLoad (E τ) w)) ∧ (E τ).card ≤ 6 ∧
      charge χ (label τ) (E τ) = if τ.sign then 12 else -12 := by
    by_cases hτ : τ.sign = true
    · simp only [E, label, ite_eq_left hτ]
      exact ⟨triangleSlots_loopless, hplus, triangleSlots_even,
        by rw [triangleSlots_card]; norm_num, hplusCharge⟩
    · simp only [E, label, ite_eq_right hτ]
      exact ⟨cycleSlots_loopless, hminus, cycleSlots_even,
        cycleSlots_card.le, hminusCharge⟩
  obtain ⟨f, hf, hload⟩ := guarded_template_family_scaled p G (fun i j => ∃ k, Link F i j k)
    S E label (fun τ _ => (hdata τ).1) (fun τ _ => (hdata τ).2.1)
    (fun τ _ => (hdata τ).2.2.2.1) ω lam rho hs B hB hω hlam hlamω hrho hscale hn1 hcount
  let tok := fun τ => mapped (E τ) (f τ)
  refine ⟨tok, ⟨hf.disjoint, hf.avoid, ?_, ?_, ?_, ?_, ?_⟩, hf.subgraph, hload⟩
  · intro τ hτ
    exact loopless_image (f τ) (hf.injective τ hτ) (E τ) (hdata τ).1
  · intro τ hτ
    exact even_image (f τ) (hf.injective τ hτ) (E τ) (hdata τ).2.2.1
  · intro τ hτ
    change charge χ p ((E τ).image (Sym2.map (f τ))) = _
    rw [charge_image (f τ) (hf.injective τ hτ) p (label τ) (hf.labels τ hτ)]
    exact (hdata τ).2.2.2.2
  · intro τ _
    simp [charge, pair]
  · intro τ _
    exact card_image_le.trans (hdata τ).2.2.2.1

theorem host_parity_template
    (F : Finset (Multiset (Fin 4))) (p : V → Fin 4)
    (Good : Finset (Sym2 V) → Prop) (q : ParityEvaluation Good)
    (label : Fin 6 → Fin 4)
    (hactive : ActiveEdges F label cycleSlots)
    (hsource : ∀ f : Fin 6 → V, Function.Injective f →
      (∀ w, p (f w) = label w) → Good (mapped cycleSlots f) ∧ q.value (mapped cycleSlots f) = 1)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset TorsionChain.Atom) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : TorsionChain.Atom → Finset (Sym2 V), ParityTokenReal q B S tok ∧
      (∀ τ ∈ S, (tok τ).card ≤ 6) ∧ (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V := by
  obtain ⟨f, hf, hload⟩ := guarded_template_family_scaled p G (fun i j => ∃ k, Link F i j k)
    S (fun _ => cycleSlots) (fun _ => label) (fun _ _ => cycleSlots_loopless)
    (fun _ _ => hactive) (fun _ _ => cycleSlots_card.le)
    ω lam rho hs B hB hω hlam hlamω hrho hscale hn1 hcount
  refine ⟨fun τ => mapped cycleSlots (f τ), ⟨hf.disjoint, hf.avoid, ?_, ?_⟩,
    fun _ _ => card_image_le.trans cycleSlots_card.le, hf.subgraph, hload⟩
  · intro τ hτ
    exact (hsource (f τ) (hf.injective τ hτ) (hf.labels τ hτ)).1
  · intro τ hτ
    exact (hsource (f τ) (hf.injective τ hτ) (hf.labels τ hτ)).2

theorem host_torsion_tokens_F1
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset TorsionChain.Atom) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F1 i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : TorsionChain.Atom → Finset (Sym2 V), ParityTokenReal (f1Parity p) B S tok ∧
      (∀ τ ∈ S, (tok τ).card ≤ 6) ∧ (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V :=
  host_parity_template F1 p (F1Good p) (f1Parity p) torsionF1Label torsion_active_F1
    (fun f hf hp => torsion_F1_image f hf p hp) G S B ω lam rho hs hB
    hω hlam hlamω hrho hscale hn1 hcount

theorem host_torsion_tokens_F2
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset TorsionChain.Atom) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F2 i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : TorsionChain.Atom → Finset (Sym2 V), ParityTokenReal (f2Parity p) B S tok ∧
      (∀ τ ∈ S, (tok τ).card ≤ 6) ∧ (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V :=
  host_parity_template F2 p (F2Good p) (f2Parity p) torsionF2Label torsion_active_F2
    (fun f hf hp => torsion_F2_image f hf p hp) G S B ω lam rho hs hB
    hω hlam hlamω hrho hscale hn1 hcount

#print axioms torsion_F1_image
#print axioms torsion_F2_image
#print axioms host_charge_tokens
#print axioms host_torsion_tokens_F1
#print axioms host_torsion_tokens_F2

end PaddedF12
