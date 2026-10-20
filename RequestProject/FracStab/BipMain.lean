/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.BipGraph
public import RequestProject.FracStab.BipCut
public import RequestProject.FracStab.BipQuadMain
public import RequestProject.FracStab.Charge

@[expose] public section

/-!
# Lemma 9.5: the extremal neighbourhood is nearly bipartite

Combining the stability theorem for thin weightings with the analysis of the two cases (a cut,
or a nearly matched four part structure) we obtain the abstract form of Lemma 9.5.
-/

namespace NashWilliams.Frac

open Finset

/-- **Lemma 9.5 (abstract form).** For every `η > 0` there is `ε > 0` such that, under the local
facts, if the value of `C` is at least `(1 - ε)|C|²/2` then there is a bipartition of `C` with at
least `(1 - η)|C|²/4 - 2 s₀ |C|` normal pairs across it, where `s₀ ≥ min(|Su|, |Sv|)`. -/
theorem abstract_bip {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ {V : Type} [DecidableEq V] {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop}
      {du dv : V → ℝ} {Su Sv : Finset V}, LocFacts C a g U W A du dv Su Sv → ∀ {s0 : ℝ},
      (1 - ε) * (C.card : ℝ) ^ 2 / 2 ≤ bsum a C C → min (Su.card : ℝ) Sv.card ≤ s0 →
      ∃ B ⊆ C, (1 - η) * (C.card : ℝ) ^ 2 / 4 - 2 * s0 * C.card ≤ (nrm g η B (C \ B) : ℝ) := by
  classical
  set δ : ℝ := min (1/6) (η/8) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1/6 := min_le_left _ _
  have hδ2 : δ ≤ η/8 := min_le_right _ _
  obtain ⟨κ, hκ0, hκ1, τ, hτ0, hτ1, hst⟩ := thin_stability hδ0
  set r : ℝ := min (1/40) (min (τ/2) (η/460)) with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1/40 := min_le_left _ _
  have hr2 : r ≤ τ/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr3 : r ≤ η/460 := le_trans (min_le_right _ _) (min_le_right _ _)
  set β : ℝ := κ ^ 2 * r with hβdef
  set θ : ℝ := β ^ 2 with hθdef
  have hβ0 : 0 < β := by positivity
  have hθ0 : 0 < θ := by positivity
  obtain ⟨ε, hε0, hε⟩ := hst θ hθ0
  refine ⟨ε, hε0, fun {V} _ {C a g U W A du dv Su Sv} L {s0} hval hS => ?_⟩
  have hs0 : 0 ≤ s0 := le_trans (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hS
  have hc0 : (0:ℝ) ≤ C.card := Nat.cast_nonneg _
  have hsc : 0 ≤ s0 * C.card := mul_nonneg hs0 hc0
  rcases hε C a L.thin hval with hcut | hquad
  · obtain ⟨B, hB, hN⟩ := cut_case L hδ0.le hδ1 hcut hS
    refine ⟨B, hB, ?_⟩
    have hmono : nrm g (6 * δ) B (C \ B) ≤ nrm g η B (C \ B) := by
      unfold nrm
      exact card_le_card (monotone_filter_right _ fun p _ hp => by linarith)
    have hmono' : (nrm g (6 * δ) B (C \ B) : ℝ) ≤ nrm g η B (C \ B) := by exact_mod_cast hmono
    have hδsq : δ ^ 2 + δ ≤ η / 4 := by nlinarith
    have hc2 : 0 ≤ (C.card : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  · rcases hc0.lt_or_eq with hc | hc
    swap
    · refine ⟨∅, empty_subset _, ?_⟩
      rw [← hc]; simp
    have hκ2 : κ ^ 2 ≤ κ := by nlinarith
    have hκ4 : 0 < κ ^ 4 := by positivity
    have hθκ : θ = κ ^ 4 * r ^ 2 := by rw [hθdef, hβdef]; ring
    have hθr : θ ≤ r ^ 2 := by
      rw [hθκ]; have : κ ^ 4 ≤ 1 := pow_le_one₀ hκ0.le hκ1
      nlinarith [sq_nonneg r]
    have hq : 48 * θ / κ ^ 4 = 48 * r ^ 2 := by rw [hθκ]; field_simp
    have hr2' : r ^ 2 ≤ r / 40 := by nlinarith
    have hkr : κ ^ 2 * r ≤ κ ^ 2 / 40 := by nlinarith
    have hk2 : 0 < κ ^ 2 := by positivity
    obtain ⟨B, hB, hN⟩ := quad_case L hquad hc hθ0 hβ0 hκ0 le_rfl
      (by linarith only [hkr, hκ2, hβdef, hk2]) (by linarith only [hkr, hβdef, hk2])
      (by linarith only [hθr, hr2', hr2, hr0, hτ0])
      (by rw [hq]; linarith only [hθr, hr2', hr1]) (by rw [hq]; linarith only [hθr, hr2', hr1, hτ1])
      (by linarith only [hθr, hr2', hr1, hτ1])
      (by rw [hq]; linarith only [hθr, hr2', hr3, hη]) hS (η := η)
    refine ⟨B, hB, ?_⟩
    have e1 : 96 * θ / κ ^ 2 = 96 * κ ^ 2 * r ^ 2 := by
      rw [hθκ]; field_simp
    have e2 : 10 * β / κ = 10 * κ * r := by rw [hβdef]; field_simp
    have hθ1 : θ ≤ 1 := by linarith only [hθr, hr2', hr1]
    have hθ2 : θ ^ 2 ≤ r := by
      have := mul_le_mul_of_nonneg_left hθ1 hθ0.le
      rw [sq]; linarith only [this, hθr, hr2', hr0]
    have hk1 : κ ^ 2 ≤ 1 := by linarith only [hκ2, hκ1]
    have hb1 : 8 * β ≤ 8 * r := by
      have := mul_le_mul_of_nonneg_right hk1 hr0.le
      linarith only [this, hβdef]
    have hb2 : 96 * κ ^ 2 * r ^ 2 ≤ 96 * r := by
      have := mul_le_mul_of_nonneg_right hk1 (sq_nonneg r)
      linarith only [this, hr2', hr0]
    have hb3 : 10 * κ * r ≤ 10 * r := by
      have := mul_le_mul_of_nonneg_right hκ1 hr0.le
      linarith only [this]
    have herr : θ ^ 2 + 8 * β + 96 * θ / κ ^ 2 + 10 * β / κ ≤ η / 4 := by
      rw [e1, e2]; linarith only [hθ2, hb1, hb2, hb3, hr3]
    have hc2 : 0 ≤ (C.card : ℝ) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right herr hc2
    linarith only [this, hN, hsc]

/-- The total rescaled value of the common neighbourhood is `ch''_F(uv) / |φ(uv)|`. -/
lemma bsum_aW_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : Sym2 V → ℝ) (u v : V) (hneg : φ s(u, v) < 0) :
    bsum (aW G φ u v) (cn G u v) (cn G u v) = Ival G φ u v / (-φ s(u, v)) := by
  set C := cn G u v
  set F := -φ s(u, v) with hF
  have hF0 : 0 < F := by linarith
  set X := ∑ w ∈ C, ∑ y ∈ C, (if G.Adj w y then valW φ u v w y else 0) with hXdef
  have hY : ∑ w ∈ C, ∑ y ∈ C, (if G.Adj w y then valW φ u v y w else 0) = X := by
    rw [sum_comm]
    refine sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_
    by_cases h : G.Adj y w
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hA : ∑ w ∈ C, ∑ y ∈ C, aW G φ u v w y = (X + ∑ w ∈ C, ∑ y ∈ C,
      (if G.Adj w y then valW φ u v y w else 0)) / (2 * F) := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun w hw => ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun y hy => ?_
    unfold aW
    by_cases h : G.Adj w y
    · rw [if_pos ⟨hw, hy, h⟩, VE_eq]; simp only [h, if_true, hF]
    · rw [if_neg (fun h' => h h'.2.2)]; simp [h]
  have hI : Ival G φ u v = X := rfl
  unfold bsum
  rw [hA, hY, hI]
  field_simp
  ring

end NashWilliams.Frac
