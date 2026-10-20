/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingReserveUniformStage203

/-! # Uniform physical confinement from a near-complete packing

The reserve is produced rather than assumed. Its whole-triangle retirement has
zero exterior charge. Floor and ceiling losses are paid before cover-down.
The remaining divisible graph inside the reserve is not claimed decomposable.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingConfinementStage204

open Finset

theorem confinement_budget (n r : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hscale : 32 ≤ a * n) (hr : 256 * (r : ℝ) ≤ a ^ 2 * n) :
    let q := ⌊a * n / 16⌋₊
    0 < q ∧ (((r * n) / 2 : ℕ) : ℝ) / q +
      2 * ((r : ℝ) + 2 * q) < a * n := by
  dsimp
  have hn : (0 : ℝ) < n := by nlinarith
  have hhi : (⌊a * n / 16⌋₊ : ℝ) ≤ a * n / 16 := Nat.floor_le (by positivity)
  have hlo : a * n / 32 ≤ (⌊a * n / 16⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (a * (n : ℝ) / 16)
    linarith
  have hq : 0 < ⌊a * n / 16⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hq' : (0 : ℝ) < ⌊a * n / 16⌋₊ := by exact_mod_cast hq
  have hmNat : 2 * ((r * n) / 2) ≤ r * n := by omega
  have hm : 2 * (((r * n) / 2 : ℕ) : ℝ) ≤ (r : ℝ) * n := by
    exact_mod_cast hmNat
  have hrn := mul_le_mul_of_nonneg_right hr hn.le
  have hqn := mul_le_mul_of_nonneg_right hlo (show 0 ≤ a * (n : ℝ) / 16 by positivity)
  have hdiv : (((r * n) / 2 : ℕ) : ℝ) / ⌊a * n / 16⌋₊ ≤ a * n / 16 := by
    apply (div_le_iff₀ hq').mpr
    nlinarith
  have haa : a ^ 2 ≤ a := by nlinarith
  have haan := mul_le_mul_of_nonneg_right haa hn.le
  refine ⟨hq, ?_⟩
  nlinarith

theorem confinement_threshold (a ζ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hζ : 0 ≤ ζ) (hζa : ζ ≤ a ^ 2 / 1024) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < ⌊a * n / 16⌋₊ ∧
      (((⌈ζ * n⌉₊ * n) / 2 : ℕ) : ℝ) / ⌊a * n / 16⌋₊ +
        2 * ((⌈ζ * n⌉₊ : ℝ) + 2 * ⌊a * n / 16⌋₊) < a * n := by
  refine ⟨max ⌈32 / a⌉₊ ⌈1024 / a ^ 2⌉₊, ?_⟩
  intro n hn
  have hn₁ : ⌈32 / a⌉₊ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : ⌈1024 / a ^ 2⌉₊ ≤ n := (le_max_right _ _).trans hn
  have h₁ := (Nat.le_ceil (32 / a)).trans (show (⌈32 / a⌉₊ : ℝ) ≤ n by
    exact_mod_cast hn₁)
  have h₂ := (Nat.le_ceil (1024 / a ^ 2)).trans (show (⌈1024 / a ^ 2⌉₊ : ℝ) ≤ n by
    exact_mod_cast hn₂)
  have hs : 32 ≤ a * n := by
    have h := (div_le_iff₀ ha).mp h₁
    nlinarith
  have hlarge : 1024 ≤ a ^ 2 * n := by
    have h := (div_le_iff₀ (sq_pos_of_pos ha)).mp h₂
    nlinarith
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hζ (Nat.cast_nonneg n))
  have hζn := mul_le_mul_of_nonneg_right hζa (Nat.cast_nonneg n)
  have hr : 256 * (⌈ζ * n⌉₊ : ℝ) ≤ a ^ 2 * n := by nlinarith
  exact confinement_budget n ⌈ζ * n⌉₊ a ha ha1 hs hr

theorem exists_uniform_confinement (t : ℕ) (γ ρ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (p : V → Fin t) (F : Finset (Multiset (Fin t)))
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (Q : Finset (Sym2 V)) (D : Finset (Finset V)),
      N ≤ Fintype.card V → IsDecomp p F Q D → Q ⊆ G.edgeFinset →
      AntiEdgeful p F G γ → IsIntDiv p F G.edgeFinset →
      (∀ u v : V, G.Adj u v →
        ∃ k : Fin t, ({p u, p v, k} : Multiset (Fin t)) ∈ F) →
      (∃ c : Multiset (Fin t) → ℕ,
        edgeVec p (G.edgeFinset \ Q) = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ) →
      DegBounded (G.edgeFinset \ Q) (ζ * Fintype.card V) →
      ∃ B : Finset (Finset V), B ⊆ D ∧
        DegBounded (B.biUnion triEdges) (2 * ρ * Fintype.card V) ∧
        HasDecomp p F (B.biUnion triEdges) ∧
        ∃ EQ, EQ ⊆ G.edgeFinset ∧ HasDecomp p F EQ ∧
          G.edgeFinset \ EQ ⊆ B.biUnion triEdges ∧
          IsIntDiv p F (G.edgeFinset \ EQ) := by
  classical
  let a := γ * ρ ^ 2 / 24
  let ζ := min (γ / 4) (a ^ 2 / 1024)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
    have hp := mul_le_mul hγ1 hρsq (sq_nonneg ρ) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [a]
    nlinarith
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨N₁, hN₁⟩ :=
    PackingReserveUniformStage203.exists_reserve_uniform t γ ρ hγ hρ hρ1
  obtain ⟨N₂, hN₂⟩ := confinement_threshold a ζ ha ha1 hζ.le (min_le_right _ _)
  refine ⟨ζ, hζ, max N₁ N₂, ?_⟩
  intro V _ _ p F G _ Q D hn hD hQ hG hI htype hpos hR
  have hR' : DegBounded (G.edgeFinset \ Q) (γ / 4 * Fintype.card V) := by
    intro v
    exact (hR v).trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Nat.cast_nonneg _))
  obtain ⟨B, hBD, hdegree, hres, hdecomp, hzero⟩ :=
    hN₁ V p F G Q D ((le_max_left _ _).trans hn) hD hQ hG hR'
  let X := B.biUnion triEdges
  have hX : X ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    have heQ : e ∈ Q := hD.2.2 ▸ mem_biUnion.mpr ⟨s, hBD hs, hes⟩
    exact hQ heQ
  obtain ⟨hq, hbudget⟩ := hN₂ (Fintype.card V) ((le_max_right _ _).trans hn)
  have hcharge : ∀ v, (((G.edgeFinset \ Q) \ X).filter fun e => v ∈ e).card +
      ReserveConfinementStage195.outsideCharge D X v ≤ ⌈ζ * Fintype.card V⌉₊ := by
    intro v
    rw [hzero v, add_zero]
    have hsub := card_le_card (filter_subset_filter (fun e => v ∈ e)
      (sdiff_subset : (G.edgeFinset \ Q) \ X ⊆ G.edgeFinset \ Q))
    have hbound := (hR v).trans (Nat.le_ceil (ζ * Fintype.card V))
    have hnat : ((G.edgeFinset \ Q).filter fun e => v ∈ e).card ≤
        ⌈ζ * Fintype.card V⌉₊ := by exact_mod_cast hbound
    exact hsub.trans hnat
  obtain ⟨EQ, hEQ, hdec, hconf, hdiv⟩ :=
    ReserveConfinementStage195.confine_with_charged_reserve p F G Q X D
      hD hQ hX hI hpos a hres htype
      ⌈ζ * Fintype.card V⌉₊ ⌊a * Fintype.card V / 16⌋₊ hq hcharge hbudget
  exact ⟨B, hBD, hdegree, hdecomp, EQ, hEQ, hdec, hconf, hdiv⟩


end PartitionedTriangleAbsorption.PackingConfinementStage204
