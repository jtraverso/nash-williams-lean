/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1BoundaryPoolsStage233
public import PartitionedTriangleAbsorption.ClassReserveStage65.Threshold

/-! # Balance repair directly from the host graph

The two correcting pools are built on the boundary. A single scalar tail
bound and rooted missing/reserved degree bounds replace abstract pool data.
The parameter inequalities remain explicit; this is not vortex iteration.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1GraphReserveStage234

open Finset F1BalanceGateStage228 F1ReserveCorrectionStage231 F1BoundaryPoolsStage233
open Filter Topology
open scoped NNReal

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem supported_card_le (W : Finset V) (E : Finset (Sym2 V))
    (hs : ∀ e ∈ E, ∀ v ∈ e, v ∈ W) : E.card ≤ W.card ^ 2 := by
  classical
  have hsub : E ⊆ (W ×ˢ W).image (fun xy => s(xy.1,xy.2)) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      exact mem_image.mpr ⟨(x,y), mem_product.mpr
        ⟨hs _ he x (Sym2.mem_mk_left _ _), hs _ he y (Sym2.mem_mk_right _ _)⟩, rfl⟩
  have := (card_le_card hsub).trans card_image_le
  simpa only [card_product, pow_two] using this

theorem tail_of_card_upper (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≤ n ^ 2) (a b : ℝ)
    (htail : 2 * Real.exp (-2 * a ^ 2 / (n : ℝ) ^ 2) +
      n * (2 * Real.exp (-2 * b ^ 2 / n)) < 1) :
    2 * Real.exp (-2 * a ^ 2 / m) + n * (2 * Real.exp (-2 * b ^ 2 / n)) < 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hmn' : (m : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hmn
  have hdiv : -2 * a ^ 2 / m ≤ -2 * a ^ 2 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hm' hn').mpr
    exact mul_le_mul_of_nonpos_left hmn' (by nlinarith [sq_nonneg a])
  have hexp := Real.exp_le_exp.mpr hdiv
  linarith

/-- The scalar sampling condition has a threshold fixed before the graph.
The size tolerance is quadratic, the degree tolerance linear in the active
order, so the factor in the union bound never involves the original host. -/
theorem exists_tail_threshold (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n ∧
      2 * Real.exp (-2 * (a * (n : ℝ) ^ 2) ^ 2 / (n : ℝ) ^ 2) +
        n * (2 * Real.exp (-2 * (b * n) ^ 2 / n)) < 1 := by
  have h1 := (ClassReserveStage65.tendsto_pow_mul_exp_neg (2 * a ^ 2) (by positivity) 0).const_mul 2
  have h2 := (ClassReserveStage65.tendsto_pow_mul_exp_neg (2 * b ^ 2) (by positivity) 1).const_mul 2
  have h := h1.add h2
  simp only [pow_zero, one_mul, pow_one, mul_zero, add_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have he1 : -2 * (a * (n : ℝ) ^ 2) ^ 2 / (n : ℝ) ^ 2 = -(2 * a ^ 2 * (n : ℝ) ^ 2) := by
    field_simp
  have he2 : -2 * (b * (n : ℝ)) ^ 2 / n = -(2 * b ^ 2 * n) := by
    field_simp
  have he : Real.exp (-(2 * a ^ 2 * (n : ℝ) ^ 2)) ≤ Real.exp (-(2 * a ^ 2 * n)) := by
    apply Real.exp_le_exp.mpr
    have hh : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * a ^ 2 by positivity)
    linarith
  refine ⟨hn0, ?_⟩
  rw [he1, he2]
  have ht := hN n ((le_max_left _ _).trans hn)
  linarith

/-- A graph-derived, boundary-supported reserve correction. Both pools and
their support, disjointness, charges and degree bounds are conclusions of
the construction. Only rooted geometry and scalar budgets are inputs. -/
theorem balanced_reserve_from_graph [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → Fin 4)
    (W U A : Finset V) (R : Finset (Sym2 V)) (i j : Fin 4)
    (hW : 0 < W.card) (hU : U ⊆ W) (hA : A ⊆ W \ U)
    (hsupport : ∀ e ∈ G.edgeFinset, ∀ v ∈ e, v ∈ W)
    (hlabel : ∀ x ∈ A, label x = i) (hcross : pairCharge i j = 1)
    (hbalance : balance label G.edgeFinset = 0)
    (hR : R ⊆ G.edgeFinset \ (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U))
    (d r : ℝ) (prob : ℝ≥0) (hprob : prob ≤ 1) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmiss : ∀ x ∈ A, ∀ k ∈ ({i,j} : Finset (Fin 4)),
      ((U.filter fun y => label y = k ∧ ¬ G.Adj x y).card : ℝ) ≤ d)
    (hres : ∀ x ∈ A, ((R.filter fun e => x ∈ e).card : ℝ) ≤ r)
    (hsize : ∀ k ∈ ({i,j} : Finset (Fin 4)),
      (((-integerBalance label (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U)
        - integerBalance label R).natAbs + 1 : ℕ) : ℝ) ≤
      prob * ((A.card : ℝ) * ((U.filter fun y => label y = k).card - d - r)) - a)
    (htail : 2 * Real.exp (-2 * a ^ 2 / (W.card : ℝ) ^ 2) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / W.card)) < 1) :
    ∃ R', R ⊆ R' ∧
      R' ⊆ G.edgeFinset \ (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U) ∧
      balance label ((G.edgeFinset \ (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U)) \ R') = 0 ∧
      (∀ e ∈ R' \ R, ∃ x ∈ W \ U, ∃ y ∈ U, s(x,y) = e) ∧
      (R' \ R).card ≤ 2 * ((-integerBalance label
        (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U) - integerBalance label R).natAbs + 1) ∧
      (∀ v, (((R' \ R).filter fun e => v ∈ e).card : ℝ) ≤ 2 * (prob * W.card + b)) ∧
      (∀ v, ((R'.filter fun e => v ∈ e).card : ℝ) ≤
        (R.filter fun e => v ∈ e).card + 2 * (prob * W.card + b)) := by
  obtain ⟨P,M,hpools,hPM,hPcharge,hMcharge,hbd,hPsize,hMsize,hPdeg,hMdeg⟩ :=
    boundary_pools_from_graph G label W U A R i j hU hA hlabel hcross d r hmiss hres
  let I := G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U
  let q := -integerBalance label I - integerBalance label R
  have hPsize' : ((q.natAbs + 1 : ℕ) : ℝ) ≤ prob * P.card - a := by
    have h := mul_le_mul_of_nonneg_left hPsize (NNReal.coe_nonneg prob)
    have hs := hsize j (by simp)
    dsimp [q, I]
    linarith
  have hMsize' : ((q.natAbs + 1 : ℕ) : ℝ) ≤ prob * M.card - a := by
    have h := mul_le_mul_of_nonneg_left hMsize (NNReal.coe_nonneg prob)
    have hs := hsize i (by simp)
    dsimp [q, I]
    linarith
  have hpos (S : Finset (Sym2 V))
      (h : ((q.natAbs + 1 : ℕ) : ℝ) ≤ prob * S.card - a) : 0 < S.card := by
    by_contra hn
    have hz : S.card = 0 := by omega
    rw [hz, Nat.cast_zero, mul_zero, zero_sub] at h
    have : (0 : ℝ) ≤ ((q.natAbs + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hsub : P ∪ M ⊆ G.edgeFinset := hpools.trans (sdiff_subset.trans sdiff_subset)
  have hsP := fun e he => hsupport e (hsub (mem_union_left M he))
  have hsM := fun e he => hsupport e (hsub (mem_union_right P he))
  have htP := tail_of_card_upper P.card W.card (hpos P hPsize') hW
    (supported_card_le W P hsP) a b htail
  have htM := tail_of_card_upper M.card W.card (hpos M hMsize') hW
    (supported_card_le W M hsM) a b htail
  obtain ⟨R',hRR',hR'E,hnew,hbal,hcard,hdeg,hfull⟩ :=
    exists_balanced_reserve_extension label W G.edgeFinset I R P M prob hprob a b W.card
      ha hb (by exact_mod_cast hW) (filter_subset _ _) hR hbalance hsupport hpools
      (hpos P hPsize') (hpos M hMsize') hPM hPcharge hMcharge
      (fun v => by exact_mod_cast hPdeg v) (fun v => by exact_mod_cast hMdeg v)
      hPsize' hMsize' htP htM
  exact ⟨R',hRR',hR'E,hbal,fun e he => hbd e (hnew he),hcard,hdeg,hfull⟩

/-- Explicit budget choice: pools of size at least sigma n^2 can correct
charge demand at most kappa n^2 with added degree at most 6 kappa n / sigma.
The preceding threshold theorem pays the two sampling tails uniformly. -/
theorem correction_parameters (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hκσ : 2 * κ ≤ σ) :
    0 < 2 * κ / σ ∧ 2 * κ / σ ≤ 1 ∧
      ∀ n : ℝ, 0 < n → 0 < κ * n ^ 2 ∧ 0 < κ / σ * n ∧
        (∀ m k : ℝ, σ * n ^ 2 ≤ m → k ≤ κ * n ^ 2 →
          k ≤ (2 * κ / σ) * m - κ * n ^ 2) ∧
        2 * ((2 * κ / σ) * n + (κ / σ) * n) = 6 * κ / σ * n := by
  refine ⟨by positivity, (div_le_one hσ).mpr hκσ, fun n hn =>
    ⟨by positivity, by positivity, ?_, by ring⟩⟩
  intro m k hm hk
  have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * κ / σ by positivity)
  have heq : (2 * κ / σ) * (σ * n ^ 2) = 2 * κ * n ^ 2 := by
    rw [← mul_assoc, div_mul_cancel₀ _ hσ.ne']
  rw [heq] at h
  linarith

end PartitionedTriangleAbsorption.F1GraphReserveStage234
