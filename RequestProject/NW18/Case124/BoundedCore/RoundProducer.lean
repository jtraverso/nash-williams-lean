/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.BoundedCore.RoundDeterministic
public import RequestProject.NW18.Case124.BoundedCore.RoundNibble
public import RequestProject.NW18.Case124.BoundedCore.RoundConstants
public import RequestProject.NW18.Case124.BoundedCore.RoundTransport

@[expose] public section

/-!
# The unconditional protected round `RoundUnivSpec124`

`roundUnivSpec124_holds` proves the exact residual proposition `RoundUnivSpec124` of
`RoundTransport.lean`.  Constants, in the quantifier order of the specification:

* from `β`: `β' = min (β/4) β₀` for the protected nibble (`IsExtremal.mono` by contrapositive), the
  nibble's `θₙ`, and `θ = min θₙ (1/100)`, `q₀ = min (θₙ/8) (1/100)`;
* from `q`: `κ = q/1000`, `ρ = q²/4000`, `σ = ρ⁴ q² / 10⁴` (sampling error and nibble leftover);
  `N₀` is the maximum of the nibble cutoff at `σ`, the sampler cutoff at `σ`, a logarithmic cutoff
  and `⌈1/σ⌉ + 1`.

For a graph: the radial reserve `Res` is sampled by `SpreadK3.crossResK3_exists` on the available
edges `E(G) \ F`; the protected nibble (`protected_nibble_max_degree`) runs on
`J = G - (F ∪ Res ∪ W.sym2)` with the actual degree budgets of `F` and `Res`; then
`round_of_sample` builds the apex cover, the targets and the root cover.
-/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption NashWilliams18 RoundConst

variable {V : Type} [Fintype V] [DecidableEq V]

lemma mem_del_edgeFinset_iff (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (F Res : Finset (Sym2 V)) [Fintype (del G (F ∪ Res ∪ W.sym2)).edgeSet] (e : Sym2 V) :
    e ∈ (del G (F ∪ Res ∪ W.sym2)).edgeFinset ↔
      e ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ Res := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges]
  simp only [Set.mem_diff, coe_union, Set.mem_union, mem_coe, mem_sdiff, insideEdges, mem_inter,
    triEdges, mem_filter, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨he, hn⟩
    exact ⟨⟨⟨he, fun h => hn (Or.inl (Or.inl h))⟩, fun h => hn (Or.inr h.2.1)⟩,
      fun h => hn (Or.inl (Or.inr h))⟩
  · rintro ⟨⟨⟨he, hF⟩, hW⟩, hR⟩
    refine ⟨he, ?_⟩
    rintro ((h | h) | h)
    · exact hF h
    · exact hR h
    · exact hW ⟨he, h, G.not_isDiag_of_mem_edgeSet he⟩

end NashWilliams18.Case124.BoundedCore

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption Case124.BoundedCore Case124.BoundedCore.RoundConst

set_option maxHeartbeats 1000000 in
/-- **The protected round on a whole vertex type** (unconditional). -/
theorem roundUnivSpec124_holds : RoundUnivSpec124 := by
  intro β hβ
  obtain ⟨β₀, hβ₀, hnib⟩ := protected_nibble_max_degree
  have hβ'pos : 0 < min (β / 4) β₀ := lt_min (by positivity) hβ₀
  obtain ⟨θn, hθn, hnib⟩ := hnib (min (β / 4) β₀) hβ'pos (min_le_right _ _)
  refine ⟨min θn (1 / 100), lt_min hθn (by norm_num), (min_le_right _ _).trans (by norm_num),
    min (θn / 8) (1 / 100), lt_min (by positivity) (by norm_num), fun q hq hqq₀ => ?_⟩
  set θ := min θn (1 / 100)
  have hθθn : θ ≤ θn := min_le_left _ _
  have hθ1 : θ ≤ 1 / 100 := min_le_right _ _
  have hq1 : q ≤ 1 / 100 := hqq₀.trans (min_le_right _ _)
  have hqθ : q ≤ θn / 8 := hqq₀.trans (min_le_left _ _)
  set ρ : ℝ := q ^ 2 / 4000 with hρ
  set σ : ℝ := ρ ^ 4 * q ^ 2 / 10 ^ 4 with hσ
  have hρ0 : 0 < ρ := rho_pos hq hρ
  have hσ0 : 0 < σ := by positivity
  have hρq : ρ ≤ q / 400000 := rho_le hq hq1 hρ
  have hσρ : σ ≤ ρ * q / 10 ^ 4 := sig_le hq hq1 hρ hσ
  have h4σ : 4 * σ ≤ ρ ^ 2 * (7 * q / 8) / 100 := four_sig_le hq hq1 hρ hσ
  have hθ0 : 0 ≤ θ := le_min hθn.le (by norm_num)
  clear_value θ σ ρ
  refine ⟨q / 1000, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := hnib σ hσ0
  obtain ⟨N₂, hN₂⟩ := SpreadK3.crossResK3_exists σ hσ0
  obtain ⟨N₃, hN₃⟩ := exists_log_cutoff (ρ * q / 20) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ (⌈1 / σ⌉₊ + 1)), ?_⟩
  intro V _ _ G _ W Z F hN hZW hW1 hW2 hZ hdeg hnx hpar hFW hFd heven
  have hN₁' : N₁ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃' : N₃ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₄' : ⌈1 / σ⌉₊ + 1 ≤ Fintype.card V :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set u : ℝ := (W.card : ℝ) with hu
  have hn1 : 1 ≤ n := by
    have : (1 : ℕ) ≤ Fintype.card V := by omega
    rw [hn]; exact_mod_cast this
  have hnpos : 0 < n := by linarith
  have hσn : 1 ≤ σ * n := by
    have h1 : 1 / σ ≤ (⌈1 / σ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / σ⌉₊ : ℕ) : ℝ) ≤ n := by
      have : ⌈1 / σ⌉₊ ≤ Fintype.card V := by omega
      rw [hn]; exact_mod_cast this
    have h3 : 1 / σ ≤ n := h1.trans h2
    rw [div_le_iff₀ hσ0] at h3
    linarith
  have hlog : 4 * Real.log n + 8 ≤ ρ * q / 20 * n := hN₃ _ hN₃'
  have hu0 : 0 ≤ u := Nat.cast_nonneg _
  have hz0 : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
  -- the radial reserve
  have hXS : Disjoint (univ \ W) (W \ Z) := by
    rw [disjoint_left]; intro a ha hb; exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  obtain ⟨Res, hgood⟩ := hN₂ V G (G.edgeFinset \ F) (univ \ W) (W \ Z) ρ hXS hρ0.le
    (by linarith) hN₂'
  have hResdeg := reserve_degree_bound G (G.edgeFinset \ F) W Z Res ρ σ hρ0.le hσ0.le hgood
  -- the protected nibble on `G - (F ∪ Res ∪ W.sym2)`
  have hbudget : ((⌊q / 1000 * n⌋₊ + ⌊ρ * n + σ * n⌋₊ + W.card : ℕ) : ℝ) ≤ θn * n := by
    push_cast
    have h1 : (⌊q / 1000 * n⌋₊ : ℝ) ≤ q / 1000 * n := Nat.floor_le (by positivity)
    have h2 : (⌊ρ * n + σ * n⌋₊ : ℝ) ≤ ρ * n + σ * n := Nat.floor_le (by positivity)
    have h3 : σ ≤ q := by
      have : ρ * q / 10 ^ 4 ≤ q := by nlinarith
      linarith
    have h4 : (q / 1000 + ρ + σ + 9 * q / 8) * n ≤ θn * n := by
      apply mul_le_mul_of_nonneg_right _ hnpos.le
      linarith
    nlinarith
  obtain ⟨Ep, hEpsub, hEpdec, hEpdeg⟩ := hN₁ V G F Res W ⌊q / 1000 * n⌋₊ ⌊ρ * n + σ * n⌋₊
    hN₁' (le_trans (mul_le_mul_of_nonneg_right (by linarith) hnpos.le) hdeg)
    (fun h => hnx (h.mono (min_le_left _ _))) (fun v => Nat.le_floor (hFd v))
    (fun v => Nat.le_floor (hResdeg v)) hbudget
  -- the nibble statement carries its own decidability instance for `del`; `Fintype` is a
  -- subsingleton, so we pass to the generic instance
  have hEpsub₀ : Ep ⊆ (del G (F ∪ Res ∪ W.sym2)).edgeFinset := by convert hEpsub
  have hEpdeg₀ : ∀ v, ((((del G (F ∪ Res ∪ W.sym2)).edgeFinset \ Ep).filter
      (fun e => v ∈ e)).card : ℝ) ≤ σ * Fintype.card V := fun v => by convert hEpdeg v
  have hEpsub' : Ep ⊆ ((G.edgeFinset \ F) \ insideEdges G W) \ Res := fun e he =>
    (mem_del_edgeFinset_iff G W F Res e).mp (hEpsub₀ he)
  obtain ⟨D, hDdef⟩ : ∃ m : ℕ, m = ⌊σ * n⌋₊ := ⟨_, rfl⟩
  have hσn0 : 0 ≤ σ * n := mul_nonneg hσ0.le hnpos.le
  have hD : ∀ v, (((((G.edgeFinset \ F) \ insideEdges G W) \ Res) \ Ep).filter
      (fun e => v ∈ e)).card ≤ D := by
    intro v
    have hiff : ∀ e, e ∈ (del G (F ∪ Res ∪ W.sym2)).edgeFinset \ Ep ↔
        e ∈ (((G.edgeFinset \ F) \ insideEdges G W) \ Res) \ Ep := fun e => by
      rw [mem_sdiff, mem_sdiff, mem_del_edgeFinset_iff]
    have hset : ((del G (F ∪ Res ∪ W.sym2)).edgeFinset \ Ep).filter (fun e => v ∈ e) =
        ((((G.edgeFinset \ F) \ insideEdges G W) \ Res) \ Ep).filter (fun e => v ∈ e) := by
      ext e; rw [mem_filter, mem_filter, hiff e]
    have := hEpdeg₀ v
    rw [hset] at this
    rw [hDdef]
    exact Nat.le_floor this
  have hD1 : (D : ℝ) ≤ σ * n := by rw [hDdef]; exact Nat.floor_le hσn0
  clear hDdef
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  clear_value n u
  -- the rounded budgets
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hρu : ρ ^ 2 * (7 * q / 8 * n) ≤ ρ ^ 2 * u := mul_le_mul_of_nonneg_left hW1 hρ2
  have hsig4 : 4 * (σ * n) ≤ ρ ^ 2 * u / 100 := by
    have := mul_le_mul_of_nonneg_right h4σ hnpos.le
    have e : ρ ^ 2 * (7 * q / 8) / 100 * n = ρ ^ 2 * (7 * q / 8 * n) / 100 := by ring
    linarith
  have hρu0 : 0 ≤ ρ * u := mul_nonneg hρ0.le hu0
  have hρ2u0 : 0 ≤ ρ ^ 2 * u := mul_nonneg hρ2 hu0
  have hρn0 : 0 ≤ ρ * n := mul_nonneg hρ0.le hnpos.le
  have hρ2n : 0 < ρ ^ 2 * n := mul_pos (pow_pos hρ0 2) hnpos
  -- γ₀
  have hγ0 : 0 ≤ ρ * (1 / 4 + θ) * u + 2 * (σ * n) + D + 1 := by
    have : 0 ≤ ρ * (1 / 4 + θ) * u := mul_nonneg (mul_nonneg hρ0.le (by linarith only [hθ0])) hu0
    linarith only [this, hσn0, hD0]
  obtain ⟨γ₀, hγdef⟩ : ∃ m : ℕ, m = ⌈ρ * (1 / 4 + θ) * u + 2 * (σ * n) + D + 1⌉₊ := ⟨_, rfl⟩
  have hγ1 : (γ₀ : ℝ) ≤ ρ * (1 / 4 + θ) * u + 2 * (σ * n) + D + 2 := by
    rw [hγdef]; exact le_trans (Nat.ceil_lt_add_one hγ0).le (by linarith only [])
  have hγ2 : ρ * (1 / 4 + θ) * u + 2 * (σ * n) + D + 1 ≤ (γ₀ : ℝ) := by
    rw [hγdef]; exact Nat.le_ceil _
  clear hγdef
  -- K
  obtain ⟨K, hKdef⟩ : ∃ m : ℕ, m = ⌈800 * ρ ^ 2 * n⌉₊ := ⟨_, rfl⟩
  have hK1 : (K : ℝ) ≤ 800 * ρ ^ 2 * n + 1 := by
    rw [hKdef]; exact (Nat.ceil_lt_add_one (by linarith only [hρ2n])).le
  have hK2 : 800 * ρ ^ 2 * n ≤ (K : ℝ) := by rw [hKdef]; exact Nat.le_ceil _
  have hKpos : 0 < K := by rw [hKdef]; exact Nat.ceil_pos.mpr (by linarith only [hρ2n])
  clear hKdef
  -- ω
  have hω0 : 0 ≤ ρ ^ 2 * u + σ * n + 2 * D := by linarith only [hρ2u0, hσn0, hD0]
  obtain ⟨ω, hωdef⟩ : ∃ m : ℕ, m = ⌈ρ ^ 2 * u + σ * n + 2 * D⌉₊ := ⟨_, rfl⟩
  have hω1 : (ω : ℝ) ≤ 2 * ρ ^ 2 * u := by
    rw [hωdef]; exact le_trans (Nat.ceil_lt_add_one hω0).le
      (by linarith only [hsig4, hD1, hσn, hρ2u0])
  have hω2 : ρ ^ 2 * u + σ * n + 2 * D ≤ (ω : ℝ) := by
    rw [hωdef]; exact Nat.le_ceil _
  clear hωdef
  -- Lv
  have hL0 : 0 ≤ ρ * n + σ * n + D := by linarith only [hρn0, hσn0, hD0]
  obtain ⟨Lv, hLvdef⟩ : ∃ m : ℕ, m = ⌈ρ * n + σ * n + D⌉₊ := ⟨_, rfl⟩
  have hLv1 : (Lv : ℝ) ≤ 2 * ρ * n := by
    have h5 : 4 * (σ * n) ≤ ρ * n := by
      have h6 : 4 * σ ≤ ρ := by
        have : ρ * q / 10 ^ 4 ≤ ρ / 4 := by
          have h7 := mul_le_mul_of_nonneg_left hq1 hρ0.le
          linarith only [h7, hρ0]
        linarith only [this, hσρ]
      have h8 := mul_le_mul_of_nonneg_right h6 hnpos.le
      linarith only [h8]
    rw [hLvdef]; exact le_trans (Nat.ceil_lt_add_one hL0).le (by linarith only [h5, hD1, hσn])
  have hLv2 : ρ * n + σ * n + D ≤ (Lv : ℝ) := by
    rw [hLvdef]; exact Nat.le_ceil _
  clear hLvdef
  -- B
  have hpot := potential_bound hρ0 hnpos hu0 (Nat.cast_nonneg ω) hω1 (Nat.cast_nonneg Lv) hLv1 hK2
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hB0 : 0 ≤ (Real.exp 1 - 1) * ω * Lv / K + 2 * Real.log n := by
    have he : 0 ≤ Real.exp 1 - 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have : 0 ≤ (Real.exp 1 - 1) * ω * Lv / K :=
      div_nonneg (mul_nonneg (mul_nonneg he (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    linarith only [this, hl0]
  obtain ⟨B, hBdef⟩ : ∃ m : ℕ, m = ⌈(Real.exp 1 - 1) * ω * Lv / K + 2 * Real.log n⌉₊ :=
    ⟨_, rfl⟩
  have hB1 : (B : ℝ) ≤ ρ * u / 100 + 2 * Real.log n + 1 := by
    rw [hBdef]; exact le_trans (Nat.ceil_lt_add_one hB0).le (by linarith only [hpot])
  have hB2 : (Real.exp 1 - 1) * ω * Lv / K + 2 * Real.log n ≤ (B : ℝ) := by
    rw [hBdef]; exact Nat.le_ceil _
  clear hBdef
  -- the Dirac margin
  have hσρn : σ * n ≤ ρ * q / 10 ^ 4 * n := mul_le_mul_of_nonneg_right hσρ hnpos.le
  have hmarg := marg_bound (γ := (γ₀ : ℝ)) (B := (B : ℝ)) (K := (K : ℝ)) (lg := Real.log n)
    (z := (Z.card : ℝ)) hq hq1 hρ hθ1 hnpos.le hW1 hz0 hZ hσρ (hD1.trans hσρn) hγ1 hK1 hB1
    (by linarith only [hlog])
  have hLκ : (Lv : ℝ) ≤ q / 1000 * u := by
    have h1 : 2 * ρ * n ≤ q / 1000 * (7 * q / 8 * n) := by
      rw [hρ]
      have : 0 ≤ q ^ 2 * n := mul_nonneg (sq_nonneg q) hnpos.le
      linarith only [this]
    have h2 : q / 1000 * (7 * q / 8 * n) ≤ q / 1000 * u :=
      mul_le_mul_of_nonneg_left hW1 (by linarith only [hq])
    linarith only [h1, h2, hLv1]
  -- apex supply and the greedy inequality
  have hsupply := apex_supply_bound (ε := σ) hq hq1 hρ hσ hθ1 hnpos.le hW1 hZ le_rfl
  have hM0 : 0 ≤ ρ ^ 2 * ((1 / 2 - 2 * θ) * u - 2 * Z.card - 2 * (q / 1000 * n)) - σ * n := by
    linarith only [hsupply, hρ2u0]
  obtain ⟨M, hMdef⟩ : ∃ m : ℕ,
      m = ⌊ρ ^ 2 * ((1 / 2 - 2 * θ) * u - 2 * Z.card - 2 * (q / 1000 * n)) - σ * n⌋₊ :=
    ⟨_, rfl⟩
  have hM1 : (M : ℝ) ≤ ρ ^ 2 * ((1 / 2 - 2 * θ) * u - 2 * Z.card -
      2 * (q / 1000 * n)) - σ * n := by
    rw [hMdef]; exact Nat.floor_le hM0
  have hM2 : 44 / 100 * (ρ ^ 2 * u) - 1 ≤ (M : ℝ) := by
    rw [hMdef]; exact le_trans (by linarith only [hsupply]) (Nat.sub_one_lt_floor _).le
  clear hMdef
  obtain ⟨Kg, hKgdef⟩ : ∃ m : ℕ, m = ⌊ρ ^ 2 * u / 40⌋₊ := ⟨_, rfl⟩
  have hKg1 : ρ ^ 2 * u / 40 - 1 ≤ (Kg : ℝ) := by
    rw [hKgdef]; exact (Nat.sub_one_lt_floor _).le
  have hKg2 : (Kg : ℝ) ≤ ρ ^ 2 * u / 40 := by
    rw [hKgdef]; exact Nat.floor_le (by linarith only [hρ2u0])
  clear hKgdef
  have hKgR := greedy_bound hq hq1 hρ hσ hnpos hW1 hσn hD1 hKg1 hKg2 hM2
  subst hn hu
  have hKg : 3 * (Fintype.card V * D) + 12 * (Kg * (Kg + D)) < 2 * (Kg * M) := by
    exact_mod_cast hKgR
  exact round_of_sample G W Z F Res Ep ρ σ θ (q / 1000) (q / 1000 * W.card) D γ₀ B K ω Lv M Kg
    hZW hFW hFd hpar heven hgood hρ0.le hσ0.le hEpdec hEpsub' hD hγ2 hmarg
    hω2 hLv2 hLκ hKpos hB2 hM1 hKg

end NashWilliams18
