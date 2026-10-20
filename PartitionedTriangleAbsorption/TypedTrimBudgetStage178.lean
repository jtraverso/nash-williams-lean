/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BalancedTrimStage170
public import PartitionedTriangleAbsorption.TypedNibbleAdapter

/-! # Scalar ledger and physical incidence for balanced quota repair

The quota inequalities follow from small residual cardinality, quadratic type
supply and a linear incidence bound. They are not extra existence assumptions.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedTrimBudgetStage178

open Finset BalancedTrimStage170

variable {V : Type} [Fintype V] [DecidableEq V]

theorem packing_incidence_le_order {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (v : V) :
    incidence D v ≤ Fintype.card V := by
  classical
  let A := D.filter fun s => v ∈ s
  have hex : ∀ s ∈ A, ∃ u ∈ s, u ≠ v := by
    intro s hs
    have ht := (hD.1 s (mem_filter.mp hs).1).1
    have he : ∃ u ∈ s.erase v, True := by
      have hc : 0 < (s.erase v).card := by
        rw [card_erase_of_mem (mem_filter.mp hs).2, ht]
        norm_num
      obtain ⟨u, hu⟩ := card_pos.mp hc
      exact ⟨u, hu, trivial⟩
    obtain ⟨u, hu, _⟩ := he
    exact ⟨u, (mem_erase.mp hu).2, (mem_erase.mp hu).1⟩
  let f : A → V := fun s => Classical.choose (hex s.val s.property)
  have hf : Function.Injective f := by
    intro s s' he
    apply Subtype.ext
    by_contra hne
    have hs := Classical.choose_spec (hex s.val s.property)
    have hs' := Classical.choose_spec (hex s'.val s'.property)
    have hdis := hD.2.1 (mem_filter.mp s.property).1 (mem_filter.mp s'.property).1 hne
    have h₁ : s(v, f s) ∈ triEdges s.val :=
      TypedNibble.mem_triEdges_iff.mpr ⟨(mem_filter.mp s.property).2, hs.1, hs.2.symm⟩
    have h₂ : s(v, f s') ∈ triEdges s'.val :=
      TypedNibble.mem_triEdges_iff.mpr ⟨(mem_filter.mp s'.property).2, hs'.1, hs'.2.symm⟩
    rw [← he] at h₂
    exact (disjoint_left.mp hdis h₁ h₂).elim
  simpa only [Fintype.card_coe, A, incidence] using Fintype.card_le_of_injective f hf

theorem trim_budget (n M N b : ℕ) (κ η ζ : ℝ)
    (hn : 0 < n) (hκ : 0 < κ) (hη : 0 ≤ η) (hζ : 0 < ζ)
    (hscale : 32 ≤ ζ * n)
    (hM : (M : ℝ) ≤ η * (n : ℝ) ^ 2 / 2)
    (hN : κ * (n : ℝ) ^ 2 ≤ (N : ℝ)) (hb : b ≤ n)
    (hsmall : η ≤ κ / 8) (hslack : 768 * η < κ * ζ) :
    let d := ⌊ζ * n / 16⌋₊
    0 < d ∧ 16 * M ≤ N ∧ 48 * M * b < d * N ∧ (16 * d : ℕ) ≤ ζ * n := by
  dsimp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : (⌊ζ * n / 16⌋₊ : ℝ) ≤ ζ * n / 16 := Nat.floor_le (by positivity)
  have hfloorlo : ζ * n / 32 ≤ (⌊ζ * n / 16⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (ζ * (n : ℝ) / 16)
    linarith
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (n : ℝ))
    have hr : (16 * M : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hr
  · have hb' : (b : ℝ) ≤ n := by exact_mod_cast hb
    have hMb := mul_le_mul hM hb' (by positivity) (by positivity)
    have hNd := mul_le_mul hfloorlo hN (by positivity) (by positivity)
    have hs := mul_lt_mul_of_pos_right hslack (pow_pos hn' 3)
    have hr : (48 * M * b : ℝ) < (⌊ζ * n / 16⌋₊ : ℝ) * N := by
      nlinarith
    exact_mod_cast hr
  · have hr : 16 * (⌊ζ * n / 16⌋₊ : ℝ) ≤ ζ * n := by linarith
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr

theorem compatible_parameters {ι : Type} [Fintype ι] [Nonempty ι]
    (a ζ : ℝ) (ha : 0 < a) (hζ : 0 < ζ) :
    ∃ γ η κ : ℝ, 0 < γ ∧ γ ≤ 1 / 128 ∧
      γ ≤ 1 / (192 * Fintype.card ι) ∧
      η = 48 * γ ^ 2 ∧ 0 < η ∧ κ = γ * a / 4 ∧ 0 < κ ∧
      24 * γ ^ 2 ≤ η / 2 ∧ η ≤ κ / 8 ∧ 768 * η < κ * ζ := by
  have hr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let γ : ℝ := min (1 / 256) (min (1 / (384 * (Fintype.card ι : ℝ)))
    (min (a / 4096) (a * ζ / 1000000)))
  have hg : 0 < γ := by dsimp [γ]; positivity
  have hg1 : γ ≤ 1 / 256 := min_le_left _ _
  have hgr : γ ≤ 1 / (384 * Fintype.card ι) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hga : γ ≤ a / 4096 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hgz : γ ≤ a * ζ / 1000000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨γ, 48 * γ ^ 2, γ * a / 4, hg, by linarith, ?_, rfl, by positivity,
    rfl, by positivity, by nlinarith, ?_, ?_⟩
  · have h : 1 / (384 * (Fintype.card ι : ℝ)) ≤ 1 / (192 * Fintype.card ι) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact hgr.trans h
  · have h := mul_le_mul_of_nonneg_right hga hg.le
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hgz hg.le
    have hp : 0 < γ * a * ζ := by positivity
    nlinarith

end PartitionedTriangleAbsorption.TypedTrimBudgetStage178

