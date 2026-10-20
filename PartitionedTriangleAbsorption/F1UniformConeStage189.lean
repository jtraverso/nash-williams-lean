/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1ConeBudgetStage188

/-! # Uniform physical F1 packing with feasible root cones

All margins, root-family supply and selector budgets are derived from the
host hypotheses. Boundary parity holes and simultaneous links remain separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1UniformConeStage189

open Finset TypedApplicationLinks F1RootCountsStage182 F1WeightedMarginStage187
open F1RootSupplyStage184 F1RootDebtStage185 F1ConeBudgetStage188 TypedF1AssemblyStage179

theorem first1_admissible : ∀ l : Fin 4, admissiblePair l (first1 l) := by decide

theorem uniform_F1_packing_quotas_and_cones (α b ζ : ℝ)
    (hα : 0 < α) (hb : 0 < b) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ α / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Finset V → ℝ),
      (∀ l, α * Fintype.card V ≤ ((univ.filter fun v => p v = l).card : ℝ)) →
      (∀ i j, admissiblePair i j → ∀ x, p x = i →
        ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) →
      (∀ s, IsCopy p F1 G s →
        1 / (b * Fintype.card V) ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
      (∀ e ∈ G.edgeFinset,
        |TypedLoadNecessity.edgeLoad p F1 G φ e - 1| ≤ δ) →
      IsIntDiv p F1 G.edgeFinset → IsFracDiv p F1 G.edgeFinset →
      ∃ D Q, D ⊆ copies p F1 G ∧ Q ⊆ G.edgeFinset ∧ IsDecomp p F1 Q D ∧
        IsIntDiv p F1 (G.edgeFinset \ Q) ∧
        (∃ a : Multiset (Fin 4) → ℕ, edgeVec p (G.edgeFinset \ Q) =
          ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ) ∧
        (∀ v, 0 ≤ surplus p (G.edgeFinset \ Q) v) ∧
        DegBounded (G.edgeFinset \ Q) (ζ * Fintype.card V) := by
  classical
  let σ := α ^ 2 / (36 * b)
  let κ := σ / 4
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨ξ, ρ, hξ, hρ, hρκ, hρζ, hξρ, hslack⟩ := cone_parameters κ ζ hκ hζ
  obtain ⟨δ0, hδ0, hδα, N0, hN0⟩ := uniform_F1_packing_and_quotas α b ξ hα hb hξ
  obtain ⟨N1, hN1⟩ := cone_threshold ξ ρ hξ hρ
  let δ := min δ0 σ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ0' : δ ≤ δ0 := min_le_left _ _
  have hδσ : δ ≤ σ := min_le_right _ _
  refine ⟨δ, hδ, hδ0'.trans hδα, max N0 N1, ?_⟩
  intro V _ _ hn p G _ φ hsize hmiss hw hload hI hR
  have hn1 := hN1 (Fintype.card V) ((le_max_right _ _).trans hn)
  obtain ⟨D, Q, hcopies, hQE, hD, _, hpos, hdeg⟩ :=
    hN0 V ((le_max_left _ _).trans hn) p G φ hsize
      (fun i j hij x hx => (hmiss i j hij x hx).trans
        (mul_le_mul_of_nonneg_right hδ0' (Nat.cast_nonneg _))) hw
      (fun e he => (hload e he).trans hδ0') hI hR
  have hE : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag :=
    fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
  have hmargin : ∀ v, σ * Fintype.card V ≤ (surplus p G.edgeFinset v : ℝ) := by
    intro v
    have h := strict_host_margin p G v α δ b hα.le hδ.le (hδ0'.trans hδα)
      hb hn1.1 (hsize _) (hmiss _ _ (first1_admissible _) v rfl)
      (fun x hx => hmiss _ _ (Or.inl rfl) x hx) φ (fun s hs => (hw s hs).1) hload
    have hf : α ^ 2 / (18 * b) = 2 * σ := by dsimp [σ]; ring
    rw [hf] at h
    have hm := mul_le_mul_of_nonneg_right hδσ (Nat.cast_nonneg (Fintype.card V))
    linarith
  have hξκ : ξ ≤ κ / 32 := hξρ.trans (div_le_div_of_nonneg_right hρκ (by norm_num))
  have hsupply : ∀ v, κ * Fintype.card V ≤ ((singletonFamily p D v).card : ℝ) := by
    intro v
    have h := singleton_supply_from_margin p G.edgeFinset Q D hD hQE hE v
      σ ξ (Fintype.card V) (hmargin v) (hdeg v)
    have hk : σ = 4 * κ := by dsimp [κ]; ring
    rw [hk] at h
    have hn' : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_right hξκ hn'
    linarith
  let d := ⌊ρ * Fintype.card V / 16⌋₊
  let K := ⌈ξ * Fintype.card V⌉₊
  have hM : ((G.edgeFinset \ Q).card : ℝ) ≤ ξ * (Fintype.card V : ℝ) ^ 2 / 2 := by
    have h := TypedCoverDown.card_le_of_degBounded (G.edgeFinset \ Q)
      (TypedCoverDown.not_isDiag_of_mem_edgeFinset G sdiff_subset) _ hdeg
    nlinarith
  have hbudget := fun v => cone_budget (Fintype.card V) (G.edgeFinset \ Q).card
    (singletonFamily p D v).card κ ξ ρ hn1.1 hκ hξ hρ hρκ hξρ hslack
    hn1.2.1 hn1.2.2 hM (hsupply v)
  have hd : 0 < d := Nat.floor_pos.mpr (by linarith [hn1.2.1])
  have hdegK : ∀ v, ((G.edgeFinset \ Q).filter fun e => v ∈ e).card ≤ K := by
    intro v
    have h := (hdeg v).trans (Nat.le_ceil (ξ * Fintype.card V))
    exact_mod_cast h
  obtain ⟨D', Q', hsub, hQsub, hD', hI', hpos', hcones, hdeg'⟩ :=
    physical_cone_repair_from_residual p G.edgeFinset Q D hD hQE hI hE hpos d K hd
      hdegK (fun v => (hbudget v).2.1)
  refine ⟨D', Q', hsub.trans hcopies, hQsub.trans hQE, hD', hI', hpos', hcones, ?_⟩
  intro v
  have h := hdeg' v
  have h' : (((G.edgeFinset \ Q').filter fun e => v ∈ e).card : ℝ) ≤
      ((G.edgeFinset \ Q).filter fun e => v ∈ e).card + (2 * (d + K) : ℕ) := by
    exact_mod_cast h
  have hbnd := (hbudget v).2.2
  have hρn := mul_le_mul_of_nonneg_right hρζ (Nat.cast_nonneg (Fintype.card V))
  have hξζ : ξ ≤ ζ / 32 :=
    hξρ.trans (div_le_div_of_nonneg_right hρζ (by norm_num))
  have hz := mul_le_mul_of_nonneg_right hξζ (Nat.cast_nonneg (Fintype.card V))
  linarith [hdeg v]


end PartitionedTriangleAbsorption.F1UniformConeStage189
