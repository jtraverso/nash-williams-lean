/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.ExceptionalStage

@[expose] public section

/-!
# Case (5): proof of the exceptional pre-clean and of Theorem 12.8

`exceptional_cleanup_128` proves `ExceptionalCleanup128`: for a locally optimal partition `p`
(fewest internal edges) and the exceptional set `S = exceptional G p τ` we apply the exceptional
stage (pre-clean of the edges inside `S`, then the stars at `S`) and the final balanced cleanup.
The parameters are `ε' = min ε (1/16)`, `τ = ε'/8`, `α = ρ = ε'²/(64·10⁶)` and
`n₀ = ⌈10⁹/ε'⌉`.  Theorem 12.8 follows by `theorem_12_8_of_exceptional_cleanup`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 ExceptionalQuotaStage142
open ExceptionalGeometryStage141 C128

/-- The arithmetic of the parameters. -/
lemma case128_numerics (ε n x s ρ τ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    (hx : x = ε * n) (hx9 : 10 ^ 9 ≤ x) (hρ : ρ = ε ^ 2 / (64 * 10 ^ 6)) (hτ : τ = ε / 8)
    (hs : s ≤ x / (4 * 10 ^ 6)) :
    ρ < 1 / 1920 ∧
    11 * ρ * n + 3 * s / 2 ≤ n / 120 ∧
    12 * ρ * n + s / 2 ≤ τ * n / 180 ∧
    s ≤ τ * n / 1800 ∧
    8 * (s + 1) + s ≤ n / 20 ∧
    112 * ρ * n + 4 * τ * n + 22 * s + 16 < n / 4 ∧
    72 * ρ * n + 2 * τ * n + 12 * s + 4 ≤ n / 20 ∧
    s ≤ ε * n ∧
    3 * s + 1 + τ * n + ε * n / 4 ≤ ε * n := by
  have hn : 16 * x ≤ n := by
    rw [hx]
    have hn0 : 0 ≤ n := by
      by_contra h
      push_neg at h
      have : ε * n < 0 := mul_neg_of_pos_of_neg hε h
      linarith
    nlinarith
  have hρn : ρ * n ≤ x / (1024 * 10 ^ 6) := by
    rw [hρ, hx]
    have hn0 : 0 ≤ n := by linarith
    have : ε * (ε * n) ≤ 1 / 16 * (ε * n) := mul_le_mul_of_nonneg_right hε1 (by linarith)
    have e : ε ^ 2 / (64 * 10 ^ 6) * n = ε * (ε * n) / (64 * 10 ^ 6) := by ring
    rw [e]
    have : ε * (ε * n) / (64 * 10 ^ 6) ≤ 1 / 16 * (ε * n) / (64 * 10 ^ 6) :=
      div_le_div_of_nonneg_right this (by norm_num)
    linarith
  have hτn : τ * n = x / 8 := by rw [hτ, hx]; ring
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ]
    have : ε ^ 2 ≤ 1 / 256 := by nlinarith
    have : ε ^ 2 / (64 * 10 ^ 6) ≤ 1 / 256 / (64 * 10 ^ 6) :=
      div_le_div_of_nonneg_right this (by norm_num)
    linarith
  · linarith
  · rw [hτn]; linarith
  · rw [hτn]; linarith
  · linarith
  · rw [mul_assoc 4 τ n, hτn]
    have : 112 * ρ * n = 112 * (ρ * n) := by ring
    rw [this]; linarith
  · rw [mul_assoc 2 τ n, hτn]
    have : 72 * ρ * n = 72 * (ρ * n) := by ring
    rw [this]; linarith
  · rw [← hx]; linarith
  · rw [hτn, ← hx]; linarith

/-- The budget inequality of the final cleanup. -/
lemma case128_budget (e n ρ d q b : ℝ) (he0 : 0 < e) (he1 : e ≤ 1 / 16) (hx9 : 10 ^ 9 ≤ e * n)
    (hρ : ρ = e ^ 2 / (64 * 10 ^ 6)) (hdle : d ≤ e * n / 8)
    (hqle : q ≤ e * n / 4) (hqge : e * n / 4 - 1 < q) (hbge : n / 5 - 1 < b) :
    2 * ρ * n ^ 2 + 2 * (d + 2 * q) * q < b * q := by
  have hn0 : 0 ≤ n := by
    by_contra h
    push_neg at h
    have : e * n < 0 := mul_neg_of_pos_of_neg he0 h
    linarith
  have hn16 : 16 * (e * n) ≤ n := by
    have := mul_le_mul_of_nonneg_right he1 hn0
    linarith
  have hq0 : 0 ≤ q := by linarith
  have hgap : n / 10 ≤ b - 2 * d - 4 * q := by linarith
  have hqn : e * n / 5 ≤ q := by linarith
  have hρn2 : 2 * ρ * n ^ 2 = (e * n) * (e * n) / (32 * 10 ^ 6) := by rw [hρ]; ring
  have hen0 : 0 ≤ e * n := by linarith
  have h7 : (e * n) * (e * n) ≤ (e * n) * (n / 16) :=
    mul_le_mul_of_nonneg_left (by linarith) hen0
  have h8 : (e * n / 5) * (n / 10) ≤ q * (b - 2 * d - 4 * q) :=
    mul_le_mul hqn hgap (by positivity) hq0
  have h9 : 0 < (e * n) * n := by
    have : 0 < n := by
      rcases hn0.lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hx9; norm_num at hx9
    positivity
  have e1 : (e * n) * (n / 16) = (e * n) * n / 16 := by ring
  have e2 : (e * n / 5) * (n / 10) = (e * n) * n / 50 := by ring
  have e3 : q * (b - 2 * d - 4 * q) = b * q - 2 * (d + 2 * q) * q := by ring
  rw [hρn2]
  rw [e1] at h7
  rw [e2, e3] at h8
  have : (e * n) * (e * n) / (32 * 10 ^ 6) ≤ (e * n) * n / 16 / (32 * 10 ^ 6) :=
    div_le_div_of_nonneg_right h7 (by norm_num)
  linarith

/-- **The exceptional pre-clean for case (5)** (the residual obligation of Theorem 12.8). -/
theorem exceptional_cleanup_128 : ExceptionalCleanup128 := by
  intro ε hε
  set e := min ε (1 / 16) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 / 16 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  set ρ : ℝ := e ^ 2 / (64 * 10 ^ 6) with hρdef
  set τ : ℝ := e / 8 with hτdef
  have hρ0 : 0 < ρ := by positivity
  have hτ0 : 0 < τ := by positivity
  refine ⟨ρ, hρ0, ⌈(10 : ℝ) ^ 9 / e⌉₊, fun V _ _ G _ hn₀ hdivG hδ hc => ?_⟩
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hnR : (10 : ℝ) ^ 9 / e ≤ n := (Nat.le_ceil _).trans (by
    rw [hndef]; exact_mod_cast hn₀)
  have hx9 : (10 : ℝ) ^ 9 ≤ e * n := by
    have := mul_le_mul_of_nonneg_left hnR he0.le
    rwa [mul_div_cancel₀ _ he0.ne'] at this
  have hnpos : 0 < Fintype.card V := by
    have : (0 : ℝ) < n := by
      by_contra h
      push_neg at h
      have : e * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0.le h
      linarith
    rw [hndef] at this
    exact_mod_cast this
  obtain ⟨p, hint, hloc⟩ := exists_localMin_partition G ρ hc
  have hmin : (3 / 4 : ℝ) * n ≤ G.minDegree := by
    have : (3 * Fintype.card V : ℝ) ≤ 4 * G.minDegree := by exact_mod_cast hδ
    rw [hndef]; linarith
  have hdeg : ∀ v, (3 / 4 : ℝ) * n ≤ G.degree v :=
    fun v => hmin.trans (by exact_mod_cast G.minDegree_le_degree v)
  have hdiv := isIntDiv_part1_of_triangleDivisible G hdivG
  set S := exceptional G p τ with hSdef
  set s : ℝ := (S.card : ℝ) with hsdef
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hsx : s ≤ e * n / (4 * 10 ^ 6) := by
    have h := exceptional_card_average G p ρ τ hnpos hint
    have e1 : 2 * ρ * n = τ * (e * n / (4 * 10 ^ 6)) := by
      rw [hρdef, hτdef]; ring
    rw [← hsdef, ← hndef, e1] at h
    exact le_of_mul_le_mul_left h hτ0
  obtain ⟨hρ1920, h1, h2, h3, h4, h5, h6, hSε, hload⟩ :=
    case128_numerics e n (e * n) s ρ τ he0 he1 rfl hx9 rfl rfl hsx
  -- the parameters of the stages
  set L := ⌈(1 / 4 + 8 * ρ) * n⌉₊ with hLdef
  set D := ⌈(24 * ρ + τ) * n + 4 * s + 2⌉₊ with hDdef
  set d := ⌊τ * n⌋₊ with hddef
  set q := ⌊e * n / 4⌋₊ with hqdef
  set b := ⌊n / 5⌋₊ with hbdef
  have hL1 : (L : ℝ) < (1 / 4 + 8 * ρ) * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hD1 : (D : ℝ) < (24 * ρ + τ) * n + 4 * s + 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  obtain ⟨P, hPcl, hPdis, hPcov, hPload, hPside⟩ :=
    stage_exceptional G p ρ τ L D hρ0.le hρ1920 hτ0 hnpos hdiv hmin hint hloc h1 h2 h3 h4
      (Nat.le_ceil _) (Nat.le_ceil _) (by
        have : 2 * (L : ℝ) + 4 * ((D : ℝ) + s) + 2 <
            2 * ((1 / 4 + 8 * ρ) * n + 1) + 4 * (((24 * ρ + τ) * n + 4 * s + 2 + 1) + s) + 2 := by
          linarith
        linarith)
  -- the final cleanup
  have hd : τ * n < d + 1 := Nat.lt_floor_add_one _
  have hdle : (d : ℝ) ≤ τ * n := Nat.floor_le (by positivity)
  have hqle : (q : ℝ) ≤ e * n / 4 := Nat.floor_le (by positivity)
  have hqge : e * n / 4 - 1 < q := by
    have := Nat.lt_floor_add_one (e * n / 4); linarith
  have hble : (b : ℝ) ≤ n / 5 := Nat.floor_le (by positivity)
  have hbge : n / 5 - 1 < b := by
    have := Nat.lt_floor_add_one (n / 5); linarith
  have hτn : τ * n = e * n / 8 := by rw [hτdef]; ring
  have hcand : ∀ u v, u ∉ S → v ∉ S → ∀ j, j ≠ p u → j ≠ p v →
      (b : ℝ) + 4 * ((3 * S.card + 1 : ℕ) : ℝ) ≤ (candidates G p u v j).card := by
    intro u v hu hv j hju hjv
    have := typical_candidates_lower G p ρ τ hρ0.le hnpos hdeg hint u v hu hv j hju hjv
    push_cast
    rw [← hsdef]
    linarith
  have hbudget : 2 * ρ * n ^ 2 + 2 * (d + 2 * q) * q < b * q :=
    case128_budget e n ρ d q b he0 he1 hx9 rfl (hτn ▸ hdle) hqle hqge hbge
  obtain ⟨Q, hQcl, hQdis, hQcov, hQload, hb1, hb2⟩ :=
    stage_final G p S ρ τ (3 * S.card + 1) b d q hdiv hint
      (fun v hv => by
        have := outside_internal_bound G p τ v hv
        rwa [internalNeighbours_card] at this)
      hcand hd hbudget P hPcl hPdis hPcov hPload hPside
  refine ⟨p, S, Q, hSε.trans (mul_le_mul_of_nonneg_right heε (by positivity)), hQcl, hQdis,
    hQcov, fun x hx => ?_, hb1, hb2⟩
  have h := hQload x hx
  have h' : ((Q.filter (fun s => x ∈ s)).card : ℝ) ≤ (3 * S.card + 1 : ℕ) + d + q := by
    exact_mod_cast h
  push_cast at h'
  rw [← hsdef] at h'
  have : e * n ≤ ε * n := mul_le_mul_of_nonneg_right heε (by positivity)
  linarith

/-- **Theorem 12.8** (case (5): close to `T₂(n/2)+T₂(n/2)`, family `F₃`).
Derived from `exceptional_cleanup_128` via `theorem_12_8_of_exceptional_cleanup`.
Theorem 13.16 is not used in this case. -/
theorem theorem_12_8 :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2T2 (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G :=
  theorem_12_8_of_exceptional_cleanup exceptional_cleanup_128

end NashWilliams18
