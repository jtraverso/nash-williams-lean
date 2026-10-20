/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadCounterexample
public import PartitionedTriangleAbsorption.TypedLoadReserveObstruction

/-! # Task B validity gate: typed load preparation for F0

* `F0SeedOnlyBoost` is the proposed intermediate target in its seed-only form:
  `b` and the input tolerance `ε` are chosen from `C` and `α` only, then for
  every precision `τ` a threshold `N`, and every graph with a `C`-regular
  `ε`-almost F0 seed which is `α`-anti-edgeful carries capped nonnegative
  weights with `τ`-precise loads. It is **false** (`not_F0SeedOnlyBoost`).
* `F0_balance_necessary` and `F0_face_necessary` give the two missing
  hypotheses, each at the precision `τ` itself.
* `F0BalancedBoostTarget` adds them (with a slack `κ` allowed to depend on
  `τ`). It is **not proved** here: it is the remaining OPEN bridge. Transferring
  its hypotheses from `G` to `J = G - (A ∪ X)` is also OPEN; the necessary
  conditions on the deletion are `reserve_balance_of_near_loads`,
  `deletion_face_of_near_loads` and `not_both_preparable`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLoadPreparation

open Finset TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks TypedLoadCounterexample

/-- The seed-only intermediate target (refuted below). -/
def F0SeedOnlyBoost : Prop :=
  ∀ C α : ℝ, 1 ≤ C → 0 < α →
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧ ∀ τ : ℝ, 0 < τ → ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] (φ : Finset V → ℝ),
        IsRegularAlmostPacking p F0 J C ε φ → AntiEdgeful p F0 J α →
        ∃ ψ : Finset V → ℝ,
          (∀ s, IsCopy p F0 J s → 0 ≤ ψ s ∧ ψ s ≤ b / Fintype.card V) ∧
          ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ

/-- **Validity gate: the seed-only target is false.** -/
theorem not_F0SeedOnlyBoost : ¬ F0SeedOnlyBoost := by
  intro h
  obtain ⟨b, ε, -, hε, H⟩ := h 2 (1 / 6) (by norm_num) (by norm_num)
  refine F0_seed_only_boost_refuted ⟨ε, hε, fun τ hτ => ?_⟩
  obtain ⟨N, hN⟩ := H τ hτ
  refine ⟨N, fun V _ _ hV p J _ φ hs ha => ?_⟩
  obtain ⟨ψ, -, hl⟩ := hN V hV p J φ hs ha
  exact ⟨ψ, hl⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem abs_groupPair_g0_pairVec_le (p : V → Fin 2) (e : Sym2 V) :
    |(pairFun (groupPair g0) (pairVec p e) : ℝ)| ≤ 4 := by
  induction e using Sym2.ind with
  | _ a b =>
    have key : ∀ i j : Fin 2, |groupPair g0 i j + groupPair g0 j i| ≤ 4 := by decide
    rw [← Int.cast_abs, pairFun_pairVec_mk]
    exact_mod_cast key _ _

/-- **Global balance is necessary at precision `τ`.** -/
theorem F0_balance_necessary (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (ψ : Finset V → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ) :
    |(pairFun (groupPair g0) (edgeVec p J.edgeFinset) : ℝ)| ≤ 4 * τ * J.edgeFinset.card := by
  refine (annihilator_balance p F0 J ψ annihilates_F0 hload).trans ?_
  have hsum : ∑ e ∈ J.edgeFinset, |(pairFun (groupPair g0) (pairVec p e) : ℝ)| ≤
      4 * J.edgeFinset.card := by
    calc _ ≤ ∑ _e ∈ J.edgeFinset, (4 : ℝ) :=
          Finset.sum_le_sum fun e _ => abs_groupPair_g0_pairVec_le p e
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  nlinarith

omit [Fintype V] in
theorem abs_groupFace_degContrib_le (p : V → Fin 2) (v : V) (e : Sym2 V) :
    |(degFun (groupFace g0 (p v)) (degContrib p v e) : ℝ)| ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [← Int.cast_abs]
    have hsum : degFun (groupFace g0 (p v)) (degContrib p v s(a, b)) =
        (if a = v then groupFace g0 (p v) (p b) else 0) +
          (if b = v then groupFace g0 (p v) (p a) else 0) := by
      simp only [degFun, degContrib, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite,
        mul_one, mul_zero]
      congr 1
      · by_cases ha : a = v
        · rw [Finset.sum_eq_single (p b) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
          simp [ha]
        · simp [ha]
      · by_cases hb : b = v
        · rw [Finset.sum_eq_single (p a) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
          simp [hb]
        · simp [hb]
    rw [hsum]
    have key : ∀ i j : Fin 2, |groupFace g0 i j| ≤ 1 := by decide
    have h1 : |(if a = v then groupFace g0 (p v) (p b) else 0)| ≤ 1 := by
      split_ifs
      · exact key _ _
      · simp
    have h2 : |(if b = v then groupFace g0 (p v) (p a) else 0)| ≤ 1 := by
      split_ifs
      · exact key _ _
      · simp
    have := abs_add_le (if a = v then groupFace g0 (p v) (p b) else 0)
      (if b = v then groupFace g0 (p v) (p a) else 0)
    exact_mod_cast (this.trans (add_le_add h1 h2)).trans (by norm_num)

/-- **Vertex faces are necessary at precision `τ`.** With nonnegative weights,
internal degree minus crossing degree at `v` is at most `2τ |E(J)|`
(a crude but uniform mass bound). -/
theorem F0_face_necessary (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (ψ : Finset V → ℝ) (hψ : ∀ s ∈ copies p F0 J, 0 ≤ ψ s) (v : V) {τ : ℝ} (hτ : 0 ≤ τ)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ) :
    (degFun (groupFace g0 (p v)) (degVec p J.edgeFinset v) : ℝ) ≤
      2 * τ * J.edgeFinset.card := by
  refine (coneFace_balance p F0 J ψ hψ v (coneFace_F0 (p v)) hload).trans ?_
  have hsum : ∑ e ∈ J.edgeFinset, |(degFun (groupFace g0 (p v)) (degContrib p v e) : ℝ)| ≤
      2 * J.edgeFinset.card := by
    calc _ ≤ ∑ _e ∈ J.edgeFinset, (2 : ℝ) :=
          Finset.sum_le_sum fun e _ => abs_groupFace_degContrib_le p v e
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  nlinarith

/-- **OPEN repaired intermediate target (not proved in this project).** The
seed-only target with the two necessary conditions added, each with a slack
`κ` that may depend on the precision `τ`. Its truth, and the transfer of its
hypotheses from `G` to `J = G - (A ∪ X)`, remain open. -/
def F0BalancedBoostTarget : Prop :=
  ∀ C α : ℝ, 1 ≤ C → 0 < α →
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧ ∀ τ : ℝ, 0 < τ → ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] (φ : Finset V → ℝ),
        IsRegularAlmostPacking p F0 J C ε φ → AntiEdgeful p F0 J α →
        |(pairFun (groupPair g0) (edgeVec p J.edgeFinset) : ℝ)| ≤
          κ * (Fintype.card V : ℝ) ^ 2 →
        (∀ v, (degFun (groupFace g0 (p v)) (degVec p J.edgeFinset v) : ℝ) ≤
          κ * Fintype.card V) →
        ∃ ψ : Finset V → ℝ,
          (∀ s, IsCopy p F0 J s → 0 ≤ ψ s ∧ ψ s ≤ b / Fintype.card V) ∧
          ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ

end PartitionedTriangleAbsorption.TypedLoadPreparation
