/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Family

/-! # The constant hierarchy for the simultaneous private-absorber consumer

`family_hierarchy`: fix `m`, `0 < γ ≤ 1` and a root-load bound `Λ ≥ 0`. Then there are
`δ, ε > 0` depending only on `γ, m` and a threshold `N` depending only on `γ, m, Λ`, all
chosen **before** the host, such that for every four-class host with `n ≥ N` vertices and
classes of size `≥ γ n`, every forbidden ledger `R` with `Δ(R) ≤ δ n`, and every preselected
family of `K` bounded structural `F3`-divisible pieces with root load `≤ Λ` and
`|R| + K · C(m) ≤ ε n²`, the sequential consumer produces private absorbers with all
properties of `family_private_absorbers`, auxiliary threshold `T = δ n`, and final global
ledger of maximum degree `≤ 2 δ n`.

Explicitly `δ = γ³ / (4096 (m + 1))` and `ε = γ δ / 4`. Each absorber has at most
`C(m) = 2280 m` edges; nothing depends on `n` except through the threshold `N`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplateStage69

open Finset TypedApplicationLinks SignedHinge ClassRepresentativesStage65 AntiEdgeSelection

universe u

/-- The ledger-degree coefficient `δ(γ, m)`. -/
noncomputable def hierDelta (γ : ℝ) (m : ℕ) : ℝ := γ ^ 3 / (4096 * ((m : ℝ) + 1))

/-- The edge-count coefficient `ε(γ, m)`. -/
noncomputable def hierEps (γ : ℝ) (m : ℕ) : ℝ := γ * hierDelta γ m / 4

/-- The host-size threshold `N(γ, m, Λ)`. -/
noncomputable def hierN (γ : ℝ) (m : ℕ) (Λ : ℝ) : ℕ :=
  ⌈8 / γ ^ 2 + 8 * ((absorberBudget 6 (12 * m) : ℝ) + 1) / γ ^ 2 +
    64 * 2 ^ 21 * ((absorberBudget 6 (12 * m) : ℝ) + 1) / γ ^ 3 +
    ((templateConst m : ℝ) * (1 + Λ) + 2 * m + 1) / hierDelta γ m⌉₊

/-- **Simultaneous private absorbers with a legal constant hierarchy.** -/
theorem family_hierarchy (m : ℕ) (γ Λ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hΛ : 0 ≤ Λ)
    {V : Type u} [Fintype V] [DecidableEq V] (hN : hierN γ m Λ ≤ Fintype.card V)
    (cls : V → Fin 4) (G₀ : SimpleGraph V) [DecidableRel G₀.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (R : Finset (Sym2 V)) (hR : DegBounded R (hierDelta γ m * Fintype.card V))
    (K : ℕ) (P : ℕ → Finset (Sym2 V)) (hPG : ∀ i < K, P i ⊆ G₀.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m) (hdiv : ∀ i < K, IsIntDiv cls F3 (P i))
    (hload : ∀ v, (rootLoad P K v : ℝ) ≤ Λ)
    (hcount : (R.card : ℝ) + K * templateConst m ≤ hierEps γ m * (Fintype.card V : ℝ) ^ 2) :
    ∃ A : ℕ → Finset (Sym2 V),
      (∀ i < K, A i ⊆ G₀.edgeFinset ∧ Disjoint (A i) R ∧ HasDecomp cls F3 (A i) ∧
        HasDecomp cls F3 (A i ∪ P i) ∧ (A i).card ≤ templateConst m ∧
        (vertSet (A i)).card ≤ templateConst m ∧
        ∀ a ∈ vertSet (P i), ∀ b ∈ vertSet (P i), s(a, b) ∉ A i) ∧
      (∀ i < K, ∀ j < K, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ v, (incidentLoad (R ∪ (range K).biUnion A) v : ℝ) ≤
        max (incidentLoad R v : ℝ) (hierDelta γ m * Fintype.card V + templateConst m) +
          templateConst m * rootLoad P K v) ∧
      DegBounded (R ∪ (range K).biUnion A) (2 * hierDelta γ m * Fintype.card V) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set δ := hierDelta γ m with hδdef
  set Bud : ℝ := (absorberBudget 6 (12 * m) : ℝ) with hBud
  set C : ℝ := (templateConst m : ℝ) with hC
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hγ3 : 0 < γ ^ 3 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef, hierDelta]; positivity
  have hδm : ((m : ℝ) + 1) * δ * 4096 = γ ^ 3 := by
    rw [hδdef, hierDelta]
    field_simp
  have hB0 : 0 ≤ Bud := by positivity
  have hC0 : 0 ≤ C := by positivity
  -- the threshold
  have t1 : 0 ≤ 8 / γ ^ 2 := by positivity
  have t2 : 0 ≤ 8 * (Bud + 1) / γ ^ 2 := by positivity
  have t3 : 0 ≤ 64 * 2 ^ 21 * (Bud + 1) / γ ^ 3 := by positivity
  have t4 : 0 < (C * (1 + Λ) + 2 * m + 1) / δ := by positivity
  have hX : 8 / γ ^ 2 + 8 * (Bud + 1) / γ ^ 2 + 64 * 2 ^ 21 * (Bud + 1) / γ ^ 3 +
      (C * (1 + Λ) + 2 * m + 1) / δ ≤ n := by
    have h := Nat.le_ceil (8 / γ ^ 2 + 8 * (Bud + 1) / γ ^ 2 +
      64 * 2 ^ 21 * (Bud + 1) / γ ^ 3 + (C * (1 + Λ) + 2 * m + 1) / δ)
    have hN' : ((hierN γ m Λ : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast hN
    exact h.trans hN'
  have hn8 : 8 ≤ γ ^ 2 * n := by
    have : 8 / γ ^ 2 ≤ n := by linarith
    rw [div_le_iff₀ hγ2] at this
    linarith
  have hnB : 8 * (Bud + 1) ≤ γ ^ 2 * n := by
    have : 8 * (Bud + 1) / γ ^ 2 ≤ n := by linarith
    rw [div_le_iff₀ hγ2] at this
    linarith
  have hnB2 : 64 * 2 ^ 21 * (Bud + 1) ≤ γ ^ 3 * n := by
    have : 64 * 2 ^ 21 * (Bud + 1) / γ ^ 3 ≤ n := by linarith
    rw [div_le_iff₀ hγ3] at this
    linarith
  have hnD : C * (1 + Λ) + 2 * m + 1 ≤ δ * n := by
    have : (C * (1 + Λ) + 2 * m + 1) / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ0] at this
    linarith
  have hn0 : 0 < n := by linarith
  have hγ32 : γ ^ 3 ≤ γ ^ 2 := by
    have : γ ^ 3 = γ ^ 2 * γ := by ring
    rw [this]
    exact mul_le_of_le_one_right hγ2.le hγ1
  -- small-coefficient facts
  have hδsmall : (2 * m + 3 : ℝ) * δ ≤ 3 * γ ^ 3 / 4096 := by nlinarith
  have hδsmall' : δ ≤ γ ^ 3 / 4096 := by nlinarith
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ :=
    family_private_absorbers m cls G₀ hG₀ γ (δ * n) (2 * δ * n) Λ (δ * n) hγ
      (by positivity) hsize
      (by nlinarith [mul_pos hγ2 hn0, mul_le_mul_of_nonneg_right hγ32 hn0.le])
      (by linarith)
      (by nlinarith [mul_pos hγ3 hn0])
      (by nlinarith [mul_pos hγ3 hn0, mul_le_mul_of_nonneg_right hγ32 hn0.le])
      (by linarith) (by linarith)
      R hR
      (by
        rw [max_eq_right (by linarith)]
        nlinarith)
      K P hPG hm hdiv hload
      (by
        have h := hcount
        rw [hierEps] at h
        rw [← hδdef] at h
        nlinarith)
  exact ⟨A, hA1, hA2, hA3, hA4⟩

end PartitionedTriangleAbsorption.PrivateTemplateStage69
