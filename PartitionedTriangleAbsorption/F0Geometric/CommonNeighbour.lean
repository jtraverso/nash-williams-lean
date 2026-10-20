/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0RigidBoost

/-! # The common-neighbour hypothesis `CN6` (NEW candidate geometric hypothesis)

`CommonNbrRich r p J β`: for every root set `R` with `|R| ≤ r` and each colour
`i`, at least `β n` vertices `w` of colour `i` are adjacent in `J` to every
member of `R` (the empty `R` included). `CN6 = CommonNbrRich 6`.

This hypothesis is **not** claimed to follow from Theorem 13.16, from the
application, or from Stage36; it is an explicitly labelled new assumption.

Here we prove the deletion robustness (`commonNbrRich_of_delete`) and that it
implies `AntiEdgeful` (`antiEdgeful_of_commonNbrRich`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0Geometric

open Finset TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Common-neighbour richness** with up to `r` roots. -/
def CommonNbrRich (r : ℕ) (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (β : ℝ) : Prop :=
  ∀ R : Finset V, R.card ≤ r → ∀ i : Fin 2,
    β * Fintype.card V ≤ ((univ.filter (fun w => p w = i ∧ ∀ u ∈ R, J.Adj u w)).card : ℝ)

/-- The six-root hypothesis `CN6(p, J, β)`. -/
abbrev CN6 (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] (β : ℝ) : Prop :=
  CommonNbrRich 6 p J β

/-- **Deletion robustness, query form.** If at every vertex at most `d` incident
edges of `J` are missing from `J'`, every common-neighbour query with root set `R`
loses at most `|R| d` vertices. (The intended use is `J' ≤ J`, i.e. edge deletion,
but the inequality does not need it.) -/
theorem card_common_delete (p : V → Fin 2) (J J' : SimpleGraph V) [DecidableRel J.Adj]
    [DecidableRel J'.Adj] (d : ℝ)
    (hdel : ∀ v, ((univ.filter (fun w => J.Adj v w ∧ ¬ J'.Adj v w)).card : ℝ) ≤ d)
    (R : Finset V) (i : Fin 2) :
    ((univ.filter (fun w => p w = i ∧ ∀ u ∈ R, J.Adj u w)).card : ℝ) - R.card * d ≤
      ((univ.filter (fun w => p w = i ∧ ∀ u ∈ R, J'.Adj u w)).card : ℝ) := by
  set A := univ.filter (fun w => p w = i ∧ ∀ u ∈ R, J.Adj u w)
  set A' := univ.filter (fun w => p w = i ∧ ∀ u ∈ R, J'.Adj u w)
  set B := fun v => univ.filter (fun w => J.Adj v w ∧ ¬ J'.Adj v w)
  have hsubset : A ⊆ A' ∪ R.biUnion B := by
    intro w hw
    simp only [A, mem_filter, mem_univ, true_and] at hw
    by_cases h : ∀ u ∈ R, J'.Adj u w
    · exact mem_union_left _ (by simpa [A', hw.1] using h)
    · push Not at h
      obtain ⟨u, hu, hnu⟩ := h
      exact mem_union_right _ (mem_biUnion.mpr ⟨u, hu, by simp [B, hw.2 u hu, hnu]⟩)
  have h1 : (A.card : ℝ) ≤ A'.card + ∑ u ∈ R, ((B u).card : ℝ) := by
    have := (card_le_card hsubset).trans (card_union_le _ _)
    have h2 := card_biUnion_le (s := R) (t := B)
    have : (A.card : ℝ) ≤ A'.card + ((R.biUnion B).card : ℝ) := by exact_mod_cast this
    have h3 : (((R.biUnion B).card : ℕ) : ℝ) ≤ ∑ u ∈ R, ((B u).card : ℝ) := by
      exact_mod_cast h2
    linarith
  have h2 : ∑ u ∈ R, ((B u).card : ℝ) ≤ R.card * d := by
    have := Finset.sum_le_sum (fun u (_ : u ∈ R) => hdel u)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  linarith

/-- **Deletion robustness.** `CommonNbrRich r β` passes to `CommonNbrRich r (β/2)`
after deleting at most `d` incident edges at each vertex, when `r d ≤ β n / 2`.
For `r = 6` this is the condition `d ≤ β n / 12`. -/
theorem commonNbrRich_of_delete {r : ℕ} (p : V → Fin 2) (J J' : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel J'.Adj] {β d : ℝ} (hd : 0 ≤ d)
    (hdel : ∀ v, ((univ.filter (fun w => J.Adj v w ∧ ¬ J'.Adj v w)).card : ℝ) ≤ d)
    (hrd : r * d ≤ β * Fintype.card V / 2) (hJ : CommonNbrRich r p J β) :
    CommonNbrRich r p J' (β / 2) := by
  intro R hR i
  have h1 := card_common_delete p J J' d hdel R i
  have h2 := hJ R hR i
  have h3 : (R.card : ℝ) * d ≤ r * d :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hR) hd
  linarith

/-- The six-root case of deletion robustness: `d ≤ β n / 12`. -/
theorem cn6_of_delete (p : V → Fin 2) (J J' : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel J'.Adj] {β d : ℝ} (hd : 0 ≤ d)
    (hdel : ∀ v, ((univ.filter (fun w => J.Adj v w ∧ ¬ J'.Adj v w)).card : ℝ) ≤ d)
    (hd12 : d ≤ β * Fintype.card V / 12) (hJ : CN6 p J β) : CN6 p J' (β / 2) :=
  commonNbrRich_of_delete p J J' hd hdel (by push_cast; linarith) hJ

/-- Common-neighbour richness with at least two roots implies anti-edgefulness. -/
theorem antiEdgeful_of_commonNbrRich {r : ℕ} (hr : 2 ≤ r) (p : V → Fin 2)
    (J : SimpleGraph V) [DecidableRel J.Adj] {β : ℝ} (hJ : CommonNbrRich r p J β) :
    AntiEdgeful p F0 J β := by
  intro τ _ i j k _ u v _ _ _
  have h := hJ {u, v} ((card_le_two).trans hr) k
  refine h.trans ?_
  exact_mod_cast card_le_card fun w hw => by
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      forall_eq_or_imp, forall_eq] at hw ⊢
    exact ⟨hw.2.1, hw.2.2.symm, hw.1⟩

/-- Each `CN6` vertex has degree at least `β n`. -/
theorem degree_ge_of_commonNbrRich {r : ℕ} (hr : 1 ≤ r) (p : V → Fin 2)
    (J : SimpleGraph V) [DecidableRel J.Adj] {β : ℝ} (hJ : CommonNbrRich r p J β) (v : V) :
    β * Fintype.card V ≤ ((univ.filter (fun w => J.Adj v w)).card : ℝ) := by
  have h := hJ {v} (by simpa using hr) 0
  refine h.trans ?_
  exact_mod_cast card_le_card fun w hw => by simp_all

/-- Two vertices have at least `β n` common neighbours. -/
theorem common_two_ge_of_commonNbrRich {r : ℕ} (hr : 2 ≤ r) (p : V → Fin 2)
    (J : SimpleGraph V) [DecidableRel J.Adj] {β : ℝ} (hJ : CommonNbrRich r p J β) (v x : V) :
    β * Fintype.card V ≤ ((univ.filter (fun w => J.Adj v w ∧ J.Adj x w)).card : ℝ) := by
  have h := hJ {v, x} ((card_le_two).trans hr) 0
  refine h.trans ?_
  exact_mod_cast card_le_card fun w hw => by simp_all

end PartitionedTriangleAbsorption.F0Geometric
