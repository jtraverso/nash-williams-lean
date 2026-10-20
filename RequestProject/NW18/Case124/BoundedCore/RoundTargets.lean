/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Transport the sampled-reserve budgets to the targets after nibble and apex coverage.
These finite-set statements do not assert that the graph supplies the hypotheses. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset

variable {V X : Type*} [DecidableEq V] [DecidableEq X]

/-- New targets were not reserved and were left by the preliminary packing. -/
theorem target_new_subset (available reserve packing apex : Finset V) :
    (available \ (packing ∪ apex)) \ reserve ⊆ available \ (reserve ∪ packing) := by
  intro v hv
  simp only [mem_sdiff, mem_union] at hv ⊢
  exact ⟨hv.1.1, fun h => h.elim hv.2 (fun h' => hv.1.2 (Or.inl h'))⟩

/-- A reserved target can only disappear through the apex cover, not the protected packing. -/
theorem reserve_removed_subset (available reserve packing apex : Finset V)
    (hsub : reserve ⊆ available) (hdisj : Disjoint reserve packing) :
    reserve \ (available \ (packing ∪ apex)) ⊆ reserve ∩ apex := by
  intro v hv
  obtain ⟨hvR, hvT⟩ := mem_sdiff.mp hv
  refine mem_inter.mpr ⟨hvR, ?_⟩
  by_contra hvA
  apply hvT
  exact mem_sdiff.mpr ⟨hsub hvR, fun h => (mem_union.mp h).elim
    (fun hvP => disjoint_left.mp hdisj hvR hvP) hvA⟩

/-- Both target budgets follow from actual leftover and apex incidences. -/
theorem target_difference_budgets (available reserve packing apex : Finset V) (D : ℕ)
    (hsub : reserve ⊆ available) (hdisj : Disjoint reserve packing)
    (hleft : (available \ (reserve ∪ packing)).card ≤ D)
    (hapex : (reserve ∩ apex).card ≤ D) :
    ((available \ (packing ∪ apex)) \ reserve).card ≤ D ∧
      (reserve \ (available \ (packing ∪ apex))).card ≤ D := by
  exact ⟨(card_le_card (target_new_subset _ _ _ _)).trans hleft,
    (card_le_card (reserve_removed_subset _ _ _ _ hsub hdisj)).trans hapex⟩

theorem card_target_le (T R : Finset V) (D : ℕ) (h : (T \ R).card ≤ D) :
    T.card ≤ R.card + D := by
  have := card_le_card_sdiff_add_card (s := T) (t := R)
  omega

theorem card_reserve_le (T R : Finset V) (D : ℕ) (h : (R \ T).card ≤ D) :
    R.card ≤ T.card + D := by
  exact card_target_le R T D h

/-- A pointwise defect predicate loses at most the number of newly introduced targets. -/
theorem target_filter_le (T R : Finset V) (D : ℕ) (p : V → Prop) [DecidablePred p]
    (h : (T \ R).card ≤ D) :
    (T.filter p).card ≤ (R.filter p).card + D := by
  have hsub : T.filter p ⊆ R.filter p ∪ (T \ R) := by
    intro v hv
    obtain ⟨hvT, hvp⟩ := mem_filter.mp hv
    by_cases hvR : v ∈ R
    · exact mem_union_left _ (mem_filter.mpr ⟨hvR, hvp⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hvT, hvR⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left h _))

/-- Two changed targets cost at most one new-target budget each. -/
theorem target_overlap_le (T₁ T₂ R₁ R₂ : Finset V) (D : ℕ)
    (h₁ : (T₁ \ R₁).card ≤ D) (h₂ : (T₂ \ R₂).card ≤ D) :
    (T₁ ∩ T₂).card ≤ (R₁ ∩ R₂).card + 2 * D := by
  have hsub : T₁ ∩ T₂ ⊆ (R₁ ∩ R₂) ∪ ((T₁ \ R₁) ∪ (T₂ \ R₂)) := by
    intro v hv
    obtain ⟨hvt₁, hvt₂⟩ := mem_inter.mp hv
    by_cases hvr₁ : v ∈ R₁
    · by_cases hvr₂ : v ∈ R₂
      · exact mem_union_left _ (mem_inter.mpr ⟨hvr₁, hvr₂⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨hvt₂, hvr₂⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨hvt₁, hvr₁⟩))
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hnew := card_union_le (T₁ \ R₁) (T₂ \ R₂)
  omega

/-- Inverse load needs a per-vertex error bound, not the per-root bounds above. -/
theorem target_load_le (roots : Finset X) (T R : X → Finset V) (v : V) (D : ℕ)
    (h : (roots.filter (fun x => v ∈ T x \ R x)).card ≤ D) :
    (roots.filter (fun x => v ∈ T x)).card ≤
      (roots.filter (fun x => v ∈ R x)).card + D := by
  have hsub : roots.filter (fun x => v ∈ T x) ⊆
      roots.filter (fun x => v ∈ R x) ∪ roots.filter (fun x => v ∈ T x \ R x) := by
    intro x hx
    obtain ⟨hxroots, hxT⟩ := mem_filter.mp hx
    by_cases hxR : v ∈ R x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxroots, hxR⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hxroots, mem_sdiff.mpr ⟨hxT, hxR⟩⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left h _))

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.card_target_le
#print axioms NashWilliams18.Case124.BoundedCore.target_new_subset
#print axioms NashWilliams18.Case124.BoundedCore.reserve_removed_subset
#print axioms NashWilliams18.Case124.BoundedCore.target_difference_budgets
#print axioms NashWilliams18.Case124.BoundedCore.card_reserve_le
#print axioms NashWilliams18.Case124.BoundedCore.target_filter_le
#print axioms NashWilliams18.Case124.BoundedCore.target_overlap_le
#print axioms NashWilliams18.Case124.BoundedCore.target_load_le
