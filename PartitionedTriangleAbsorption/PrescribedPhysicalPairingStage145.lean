/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairingRepairStage145
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Sum

/-! # Perfect physical pairings with an exact prescribed class profile

The constructor permits zero and small pair demands. Its only geometric
requirements are bounded cross-class non-neighbours and at most one small class.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrescribedPhysicalPairingStage145

open Finset PairingRepairStage145

abbrev Slots {K : Type*} (t : K → K → ℕ) := Σ j, Σ k, Fin (t j k)

def slotSwap {K : Type*} (t : K → K → ℕ) (hsym : ∀ j k, t j k = t k j) :
    Slots t ≃ Slots t where
  toFun u := ⟨u.2.1, u.1, Fin.cast (hsym u.1 u.2.1) u.2.2⟩
  invFun u := ⟨u.2.1, u.1, Fin.cast (hsym u.1 u.2.1) u.2.2⟩
  left_inv := by rintro ⟨j, k, x⟩; rfl
  right_inv := by rintro ⟨j, k, x⟩; rfl

theorem slotSwap_involutive {K : Type*} (t : K → K → ℕ)
    (hsym : ∀ j k, t j k = t k j) : Function.Involutive (slotSwap t hsym) := by
  rintro ⟨j, k, x⟩
  rfl

/-- The profile row identities construct a complete abstract pairing. -/
theorem exists_template {V K : Type*} [Fintype V] [Fintype K] [DecidableEq K]
    (p : V → K) (t : K → K → ℕ)
    (hsym : ∀ j k, t j k = t k j) (hdiag : ∀ j, t j j = 0)
    (hrow : ∀ j, ∑ k, t j k = (univ.filter fun v => p v = j).card) :
    ∃ f : V ≃ V, Function.Involutive f ∧ (∀ v, p (f v) ≠ p v) ∧
      ∀ j k, (univ.filter fun v => p v = j ∧ p (f v) = k).card = t j k := by
  classical
  have hc (j : K) : Fintype.card (Σ k, Fin (t j k)) = Fintype.card {v // p v = j} := by
    simpa only [Fintype.card_sigma, Fintype.card_fin, Fintype.card_subtype] using hrow j
  let b (j : K) : (Σ k, Fin (t j k)) ≃ {v // p v = j} := Fintype.equivOfCardEq (hc j)
  let e : Slots t ≃ V := (Equiv.sigmaCongrRight b).trans (Equiv.sigmaFiberEquiv p)
  have hp (u : Slots t) : p (e u) = u.1 := (b u.1 u.2).property
  let f : V ≃ V := (e.symm.trans (slotSwap t hsym)).trans e
  have hfe (u : Slots t) : f (e u) = e (slotSwap t hsym u) := by simp [f]
  have hfp (u : Slots t) : p (f (e u)) = u.2.1 := by rw [hfe, hp]; rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [hfe, hfe, slotSwap_involutive t hsym u]
  · intro v h
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [hfp, hp] at h
    have hz : t u.1 u.2.1 = 0 := by rw [h, hdiag]
    have hl := u.2.2.isLt
    omega
  · intro j k
    have heq : (univ.filter fun v => p v = j ∧ p (f v) = k) =
        univ.image (fun x : Fin (t j k) => e ⟨j, k, x⟩) := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hv
        obtain ⟨⟨j', k', x⟩, rfl⟩ := e.surjective v
        rw [hp, hfp] at hv
        obtain ⟨rfl, rfl⟩ := hv
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨hp _, hfp _⟩
    rw [heq, card_image_of_injective]
    · simp
    · intro x y h
      have he := e.injective h
      exact Fin.ext (congrArg (fun u : Slots t => u.2.2.val) he)

/-- An exact physical matching, constructed rather than assumed as input. -/
theorem exists_prescribed_physical_pairing {V K : Type*}
    [Fintype V] [Fintype K] [DecidableEq K]
    (R : V → V → Prop) [DecidableRel R] (hsymR : ∀ u v, R u v → R v u)
    (p : V → K) (t : K → K → ℕ)
    (hsym : ∀ j k, t j k = t k j) (hdiag : ∀ j, t j j = 0)
    (hrow : ∀ j, ∑ k, t j k = (univ.filter fun v => p v = j).card)
    (D : ℕ)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D)
    (hlarge : ∀ j k, j ≠ k →
      2 * D + 1 < (univ.filter fun w => p w = j).card ∨
      2 * D + 1 < (univ.filter fun w => p w = k).card) :
    ∃ f : V ≃ V, Function.Involutive f ∧ (∀ v, p (f v) ≠ p v) ∧
      (∀ v, R v (f v)) ∧
      ∀ j k, (univ.filter fun v => p v = j ∧ p (f v) = k).card = t j k := by
  classical
  obtain ⟨f, hf, hcross, hcount⟩ := exists_template p t hsym hdiag hrow
  obtain ⟨e, he, hphysical⟩ := exists_physical_conjugate R hsymR p f hf hcross D hmiss hlarge
  refine ⟨conjugate f e, conjugate_involutive f e hf,
    conjugate_cross p f e hcross he, hphysical, ?_⟩
  intro j k
  rw [conjugate_count p f e he, hcount]

/-- Cross-class missing edges and forbidden edges share an additive budget. -/
theorem cross_missing_avoiding {V K : Type*} [Fintype V] [DecidableEq K]
    (p : V → K) (R B : V → V → Prop) [DecidableRel R] [DecidableRel B]
    (D U : ℕ)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D)
    (hused : ∀ v, (univ.filter fun w => B v w).card ≤ U) (v : V) :
    (univ.filter fun w => p w ≠ p v ∧ ¬ (R v w ∧ ¬ B v w)).card ≤ D + U := by
  classical
  have hs : (univ.filter fun w => p w ≠ p v ∧ ¬ (R v w ∧ ¬ B v w)) ⊆
      (univ.filter fun w => p w ≠ p v ∧ ¬ R v w) ∪ (univ.filter fun w => B v w) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
    tauto
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add (hmiss v) (hused v)))

/-- The prescribed physical pairing avoids all edges of a sparse prior packing. -/
theorem exists_prescribed_avoiding_pairing {V K : Type*}
    [Fintype V] [Fintype K] [DecidableEq K]
    (R B : V → V → Prop) [DecidableRel R] [DecidableRel B]
    (hsymR : ∀ u v, R u v → R v u) (hsymB : ∀ u v, B u v → B v u)
    (p : V → K) (t : K → K → ℕ)
    (hsym : ∀ j k, t j k = t k j) (hdiag : ∀ j, t j j = 0)
    (hrow : ∀ j, ∑ k, t j k = (univ.filter fun v => p v = j).card)
    (D U : ℕ)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D)
    (hused : ∀ v, (univ.filter fun w => B v w).card ≤ U)
    (hlarge : ∀ j k, j ≠ k →
      2 * (D + U) + 1 < (univ.filter fun w => p w = j).card ∨
      2 * (D + U) + 1 < (univ.filter fun w => p w = k).card) :
    ∃ f : V ≃ V, Function.Involutive f ∧ (∀ v, p (f v) ≠ p v) ∧
      (∀ v, R v (f v) ∧ ¬ B v (f v)) ∧
      ∀ j k, (univ.filter fun v => p v = j ∧ p (f v) = k).card = t j k := by
  apply exists_prescribed_physical_pairing (fun u v => R u v ∧ ¬ B u v)
    (fun u v h => ⟨hsymR _ _ h.1, fun hB => h.2 (hsymB _ _ hB)⟩)
    p t hsym hdiag hrow (D + U)
    (cross_missing_avoiding p R B D U hmiss hused) hlarge

end PartitionedTriangleAbsorption.PrescribedPhysicalPairingStage145
