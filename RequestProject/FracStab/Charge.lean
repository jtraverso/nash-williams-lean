/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Key

@[expose] public section

/-!
# Final charges of negative edges under `δ(G) ≥ (3/4 - ε) n` (Part II of the paper)

For a negative edge `f = uv` we write `chNeg G φ u v = φ(f) + (charge received by f)`; this is
the final charge `ch_F(f)` of the paper (Definition 4.11 and the Demand Proportional rule).

* `recv_master` — the exact form of Proposition 4.15 + Lemma 4.21 (no degree assumption), with
  the contribution of the vertices outside the common neighbourhood kept explicit;
* `chNeg_lb` — Lemma 10.4: `ch_F(f) ≥ -4ε |φ(f)|`;
* `chNeg_cleaning` — Lemma 10.2 (cleaning lemma);
* `small_charge_cn` and `small_charge_value` — the first part of Lemma 9.6: an edge with small
  final charge has a common neighbourhood of size about `n/2` and nearly maximal value.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- Charge received by the edge `uv`. -/
noncomputable def recv (u v : V) : ℝ := ∑ w, (trans G φ u w v + trans G φ v w u)

/-- Final charge `ch_F` of the (negative) edge `uv`. -/
noncomputable def chNeg (u v : V) : ℝ := φ s(u, v) + recv G φ u v

/-- The value `ch''_F(f)` of the common neighbourhood (Definition 4.20). -/
noncomputable def Ival (u v : V) : ℝ :=
  ∑ w ∈ cn G u v, ∑ y ∈ cn G u v, (if G.Adj w y then valW φ u v w y else 0)

/-- Contribution of the vertices outside `N(u) ∩ N(v)` to the demand on the edge `uw`. -/
noncomputable def outS (u v w : V) : ℝ :=
  ∑ y ∈ (cn G u w).filter (fun y => y ∉ cn G u v),
    dem φ u w v * normT (φ s(u, w)) (φ s(u, y)) (φ s(w, y))

/-- `N(a) ∖ N(b)`. -/
def nd (a b : V) : Finset V := univ.filter fun y => G.Adj a y ∧ ¬ G.Adj b y

omit [DecidableEq V] in
lemma mem_nd {a b y : V} : y ∈ nd G a b ↔ G.Adj a y ∧ ¬ G.Adj b y := by simp [nd]

omit [DecidableEq V] in
lemma recv_comm (u v : V) : recv G φ u v = recv G φ v u := by
  unfold recv; exact sum_congr rfl fun w _ => add_comm _ _

omit [DecidableEq V] in
lemma chNeg_comm (u v : V) : chNeg G φ u v = chNeg G φ v u := by
  unfold chNeg; rw [recv_comm, Sym2.eq_swap]

/-- The demand-sum identity used in Lemma 4.21, for one side. -/
lemma side_eq {u v w : V} (hw : w ∈ cn G u v) :
    dem φ u w v * Dtot G φ u w / φ s(u, w) =
      ∑ y ∈ cn G u v, (if G.Adj w y then
        dem φ u w v * normT (φ s(u, w)) (φ s(u, y)) (φ s(w, y)) else 0) + outS G φ u v w := by
  rw [dem_mul_Dtot_div, ← sum_filter_add_sum_filter_not (cn G u w) (fun y => y ∈ cn G u v)]
  have hset : (cn G u w).filter (fun y => y ∈ cn G u v) = (cn G u v).filter (G.Adj w) := by
    ext y; simp only [mem_filter, mem_cn]; have := (mem_cn G).1 hw; tauto
  rw [hset, ← sum_filter]
  rfl

/-- Per-vertex form of Proposition 4.15 and Lemma 4.21 (exact outer part). -/
lemma per_w_gen {n : ℝ} (hn : 0 < n) {u v : V} (huv : G.Adj u v) {w : V} (hw : w ∈ cn G u v) :
    4 / n * (dem φ u w v + dem φ v w u) - 4 / n ^ 2 *
      (∑ y ∈ cn G u v, (if G.Adj w y then valW φ u v w y else 0) +
        (outS G φ u v w + outS G φ v u w)) ≤
      trans G φ u w v + trans G φ v w u := by
  have hw' := (mem_cn G).1 hw
  have t1 := trans_lb G φ hn hw'.1 huv hw'.2.symm
  have t2 := trans_lb G φ hn hw'.2 huv.symm hw'.1.symm
  have s1 := side_eq G φ hw
  have s2 := side_eq G φ (u := v) (v := u) (by rw [cn_comm]; exact hw)
  rw [cn_comm G v u] at s2
  have hsplit : ∑ y ∈ cn G u v, (if G.Adj w y then valW φ u v w y else 0) =
      ∑ y ∈ cn G u v, (if G.Adj w y then
        dem φ u w v * normT (φ s(u, w)) (φ s(u, y)) (φ s(w, y)) else 0) +
      ∑ y ∈ cn G u v, (if G.Adj w y then
        dem φ v w u * normT (φ s(v, w)) (φ s(v, y)) (φ s(w, y)) else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    split_ifs
    · unfold valW vterm dem
      rw [show s(w, v) = s(v, w) from Sym2.eq_swap, show s(v, u) = s(u, v) from Sym2.eq_swap,
        show s(w, u) = s(u, w) from Sym2.eq_swap]
    · simp
  rw [hsplit]
  rw [s1] at t1; rw [s2] at t2
  linarith

/-- **Master inequality** (Proposition 4.15 and Lemma 4.21, exact form): for a negative edge
`uv`, the received charge is at least `4 c F / n - 4 (ch''_F + outer) / n²`. -/
lemma recv_master (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0) :
    4 / (Fintype.card V : ℝ) * ((cn G u v).card * (-φ s(u, v))) -
      4 / (Fintype.card V : ℝ) ^ 2 *
        (Ival G φ u v + ∑ w ∈ cn G u v, (outS G φ u v w + outS G φ v u w)) ≤
      recv G φ u v := by
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  set C := cn G u v with hC
  have hsub : recv G φ u v = ∑ w ∈ C, (trans G φ u w v + trans G φ v w u) := by
    refine (sum_subset (subset_univ C) fun w _ hw => ?_).symm
    rw [hC, mem_cn] at hw
    unfold trans
    rw [if_neg (fun h => hw ⟨h.1, h.2.2.symm⟩), if_neg (fun h => hw ⟨h.2.2.symm, h.1⟩)]
    ring
  rw [hsub]
  have hsum := sum_le_sum fun w (hw : w ∈ C) => per_w_gen G φ hn huv hw
  have hp : ∀ w ∈ C, dem φ u w v + dem φ v w u = -φ s(u, v) := fun w hw =>
    dem_pair_sum G φ hφ huv hneg hw
  rw [sum_congr rfl fun w hw => by rw [hp w hw]] at hsum
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  unfold Ival
  linarith

/-- In a triangle-covered weighting, the normalized demand is at most the total weight of the
negative edges divided by the weight of the positive edge. -/
lemma normT_le_neg {pe p1 p2 : ℝ} (he : 0 < pe) :
    normT pe p1 p2 ≤ (max (-p1) 0 + max (-p2) 0) / pe := by
  unfold normT
  apply div_le_div_of_nonneg_right _ he.le
  have h1 : demF pe p1 p2 ≤ max (-p1) 0 := by
    rcases lt_or_ge p1 0 with h | h
    · exact (demF_le _ _ _ h).trans (le_max_left _ _)
    · rw [demF_of_nonneg_f h]; exact le_max_right _ _
  have h2 : demF pe p2 p1 ≤ max (-p2) 0 := by
    rcases lt_or_ge p2 0 with h | h
    · exact (demF_le _ _ _ h).trans (le_max_left _ _)
    · rw [demF_of_nonneg_f h]; exact le_max_right _ _
  linarith

/-- The outer contribution of one side is at most `dem · |N(u) ∖ N(v)|`. -/
lemma outS_le (hφ : GoodWeighting G φ) (u v w : V) (huw : G.Adj u w) :
    outS G φ u v w ≤ dem φ u w v * (nd G u v).card := by
  have hd := dem_nonneg φ u w v
  unfold outS
  calc ∑ y ∈ (cn G u w).filter (fun y => y ∉ cn G u v),
        dem φ u w v * normT (φ s(u, w)) (φ s(u, y)) (φ s(w, y))
      ≤ ∑ y ∈ (cn G u w).filter (fun y => y ∉ cn G u v), dem φ u w v := by
        refine sum_le_sum fun y hy => ?_
        simp only [mem_filter, mem_cn] at hy
        exact mul_le_of_le_one_right hd
          (normT_le_one _ _ _ (hφ.cov u w y huw hy.1.1 hy.1.2))
    _ = ((cn G u w).filter (fun y => y ∉ cn G u v)).card * dem φ u w v := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((nd G u v).card : ℝ) * dem φ u w v := by
        refine mul_le_mul_of_nonneg_right ?_ hd
        exact_mod_cast card_le_card (fun y hy => by
          simp only [mem_filter, mem_cn, mem_nd, not_and] at hy ⊢
          exact ⟨hy.1.1, hy.2 hy.1.1⟩)
    _ = _ := mul_comm _ _

/-- `|N(a) ∖ N(b)| ≤ n - deg(b)`. -/
lemma card_nd_le (a b : V) : (nd G a b).card + G.degree b ≤ Fintype.card V := by
  have hdisj : Disjoint (nd G a b) (G.neighborFinset b) := by
    rw [disjoint_left]; intro y hy hy'
    rw [mem_nd] at hy; rw [SimpleGraph.mem_neighborFinset] at hy'; exact hy.2 hy'
  rw [← G.card_neighborFinset_eq_degree, ← card_union_of_disjoint hdisj]
  exact card_le_univ _

/-- `N(a) ∖ N(b)` and `N(a) ∩ N(b)` are disjoint. -/
lemma card_nd_add_cn_le (a b : V) : (nd G a b).card + (cn G a b).card ≤ Fintype.card V := by
  have hdisj : Disjoint (nd G a b) (cn G a b) := by
    rw [disjoint_left]; intro y hy hy'
    rw [mem_nd] at hy; rw [mem_cn] at hy'; exact hy.2 hy'.2
  rw [← card_union_of_disjoint hdisj]
  exact card_le_univ _

/-- `|N(u) ∩ N(v)| ≥ deg u + deg v - n`. -/
lemma card_cn_ge_deg (u v : V) : G.degree u + G.degree v ≤ (cn G u v).card + Fintype.card V := by
  have e : cn G u v = G.neighborFinset u ∩ G.neighborFinset v := by
    ext x; simp [cn]
  have h1 := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h2 : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V := card_le_univ _
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h1
  rw [e]; omega

/-- Real form of the two degree consequences of `δ(G) ≥ (3/4 - ε) n`. -/
lemma cn_bounds_of_minDegree {ε : ℝ} (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    (u v : V) :
    (1 / 2 - 2 * ε) * (Fintype.card V : ℝ) ≤ (cn G u v).card ∧
      ((nd G u v).card : ℝ) ≤ (1 / 4 + ε) * Fintype.card V := by
  have h1 := card_cn_ge_deg G u v
  have h2 := card_nd_le G u v
  have hu := G.minDegree_le_degree u
  have hv := G.minDegree_le_degree v
  have h1' : (G.degree u : ℝ) + G.degree v ≤ (cn G u v).card + Fintype.card V := by
    exact_mod_cast h1
  have h2' : ((nd G u v).card : ℝ) + G.degree v ≤ Fintype.card V := by exact_mod_cast h2
  have hu' : (G.minDegree : ℝ) ≤ G.degree u := by exact_mod_cast hu
  have hv' : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast hv
  constructor <;> linarith

/-- The total outer contribution is at most `c F m` where `m` bounds both `|N(u) ∖ N(v)|` and
`|N(v) ∖ N(u)|`. -/
lemma sum_outS_le (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    {M : ℝ} (hMu : ((nd G u v).card : ℝ) ≤ M) (hMv : ((nd G v u).card : ℝ) ≤ M) :
    ∑ w ∈ cn G u v, (outS G φ u v w + outS G φ v u w) ≤
      (cn G u v).card * (-φ s(u, v)) * M := by
  have : ∀ w ∈ cn G u v, outS G φ u v w + outS G φ v u w ≤ (-φ s(u, v)) * M := by
    intro w hw
    have hw' := (mem_cn G).1 hw
    have o1 := outS_le G φ hφ u v w hw'.1
    have o2 := outS_le G φ hφ v u w hw'.2
    have d1 := dem_nonneg φ u w v
    have d2 := dem_nonneg φ v w u
    have hp := dem_pair_sum G φ hφ huv hneg hw
    have m1 := mul_le_mul_of_nonneg_left hMu d1
    have m2 := mul_le_mul_of_nonneg_left hMv d2
    rw [← hp]; nlinarith
  calc _ ≤ ∑ w ∈ cn G u v, (-φ s(u, v)) * M := sum_le_sum this
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- `ch''_F(f) ≤ |φ(f)| c² / 2` (Lemmas 4.29 and 4.31). -/
lemma Ival_le (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0) :
    Ival G φ u v ≤ (-φ s(u, v)) * ((cn G u v).card : ℝ) ^ 2 / 2 :=
  inner_value_bound G φ hφ huv hneg

/-- The master inequality in normalized form: with `d = c/n`, `S = c²F/2 - ch''_F ≥ 0` and an
upper bound `M` for the outer neighbourhoods,
`ch_F(f) ≥ F (4d - 4dM/n - 2d² - 1) + 4 S / n²`. -/
lemma chNeg_master (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    {M : ℝ} (hMu : ((nd G u v).card : ℝ) ≤ M) (hMv : ((nd G v u).card : ℝ) ≤ M) :
    (-φ s(u, v)) * (4 * ((cn G u v).card / (Fintype.card V : ℝ)) -
        4 * ((cn G u v).card / (Fintype.card V : ℝ)) * (M / Fintype.card V) -
        2 * ((cn G u v).card / (Fintype.card V : ℝ)) ^ 2 - 1) +
      4 / (Fintype.card V : ℝ) ^ 2 *
        ((-φ s(u, v)) * ((cn G u v).card : ℝ) ^ 2 / 2 - Ival G φ u v) ≤
      chNeg G φ u v := by
  have hm := recv_master G φ hφ huv hneg
  have ho := sum_outS_le G φ hφ huv hneg hMu hMv
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  unfold chNeg
  set c : ℝ := ((cn G u v).card : ℝ)
  set F := -φ s(u, v)
  have hc4 : (0 : ℝ) ≤ 4 / n ^ 2 := by positivity
  have m := mul_le_mul_of_nonneg_left ho hc4
  have e : F * (4 * (c / n) - 4 * (c / n) * (M / n) - 2 * (c / n) ^ 2 - 1) +
      4 / n ^ 2 * (F * c ^ 2 / 2 - Ival G φ u v) =
      4 / n * (c * F) - 4 / n ^ 2 * (Ival G φ u v + c * F * M) - F := by
    field_simp; ring
  rw [e]
  linarith

/-- **Lemma 10.4.** If `δ(G) ≥ (3/4 - ε) n`, every negative edge has final
charge at least `-4ε |φ(f)|`. -/
theorem chNeg_lb (hφ : GoodWeighting G φ) {ε : ℝ}
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0) :
    -4 * ε * (-φ s(u, v)) ≤ chNeg G φ u v := by
  obtain ⟨hc, hmu⟩ := cn_bounds_of_minDegree G hδ u v
  obtain ⟨-, hmv⟩ := cn_bounds_of_minDegree G hδ v u
  have hM := chNeg_master G φ hφ huv hneg hmu hmv
  have hI := Ival_le G φ hφ huv hneg
  have hcle := card_cn_le G u v
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  set c : ℝ := ((cn G u v).card : ℝ)
  set F := -φ s(u, v)
  have hF : 0 < F := by simp only [F]; linarith
  have hS : 0 ≤ 4 / n ^ 2 * (F * c ^ 2 / 2 - Ival G φ u v) :=
    mul_nonneg (by positivity) (by linarith)
  have hd1 : c / n ≤ 1 := (div_le_one hn).2 hcle
  have hd0 : 1 / 2 - 2 * ε ≤ c / n := (le_div_iff₀ hn).2 hc
  have e : (1 / 4 + ε) * n / n = 1 / 4 + ε := by field_simp
  rw [e] at hM
  have key : 0 ≤ F * ((1 - c / n) * (2 * (c / n) - 1 + 4 * ε)) :=
    mul_nonneg hF.le (mul_nonneg (by linarith) (by linarith))
  nlinarith

/-- A vertex `z ∈ N(u) ∖ N(v)` is `α`-unclean for the `u`-obtuse vertex `x` (Definition 10.1). -/
def UncleanFor (α : ℝ) (u x z : V) : Prop :=
  ¬ G.Adj x z ∨ max (-φ s(x, z)) 0 + max (-φ s(u, z)) 0 < (1 - α) * φ s(u, x)

open Classical in
/-- The `u`-obtuse vertex `x` of the negative edge `uv` is `α`-unclean (Definition 10.1). -/
def IsUnclean (α : ℝ) (u v x : V) : Prop :=
  0 < φ s(u, x) ∧ φ s(v, x) < 0 ∧
    α * Fintype.card V ≤ (((nd G u v).filter fun z => UncleanFor G φ α u x z).card : ℝ)

open Classical in
/-- Outer contribution of an `α`-unclean `u`-obtuse vertex. -/
lemma outS_unclean (hφ : GoodWeighting G φ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {u v x : V}
    (hneg : φ s(u, v) < 0) (hx : x ∈ cn G u v) (hun : IsUnclean G φ α u v x) :
    outS G φ u v x ≤ (-φ s(u, v)) * ((nd G u v).card - α * (α * Fintype.card V)) := by
  obtain ⟨hux, hvx, hcnt⟩ := hun
  have hx' := (mem_cn G).1 hx
  have hdem : dem φ u x v = -φ s(u, v) := by
    unfold dem
    rw [show s(x, v) = s(v, x) from Sym2.eq_swap]
    exact demF_obtuse hux hneg hvx
  have hF : 0 < -φ s(u, v) := by linarith
  set U := (nd G u v).filter fun z => UncleanFor G φ α u x z
  have hterm : ∀ y ∈ nd G u v,
      (if y ∈ cn G u x then normT (φ s(u, x)) (φ s(u, y)) (φ s(x, y)) else 0) ≤
        if y ∈ U then 1 - α else 1 := by
    intro y _
    split_ifs with h1 h2 h2
    · have h1' := (mem_cn G).1 h1
      have hunc : UncleanFor G φ α u x y :=
        (Finset.mem_filter.mp (show y ∈ (nd G u v).filter
          (fun z => UncleanFor G φ α u x z) from h2)).2
      rcases hunc with h | h
      · exact absurd h1'.2 h
      · have h3 := normT_le_neg (p1 := φ s(u, y)) (p2 := φ s(x, y)) hux
        exact h3.trans ((div_le_iff₀ hux).2 (by linarith))
    · have h1' := (mem_cn G).1 h1
      exact normT_le_one _ _ _ (hφ.cov u x y hx'.1 h1'.1 h1'.2)
    · linarith
    · exact zero_le_one
  have hset : (cn G u x).filter (fun y => y ∉ cn G u v) = (nd G u v).filter (· ∈ cn G u x) := by
    ext y; simp only [mem_filter, mem_cn, mem_nd]; tauto
  unfold outS
  rw [hset, sum_filter]
  have e1 : ∑ y ∈ nd G u v, (if y ∈ cn G u x then
        dem φ u x v * normT (φ s(u, x)) (φ s(u, y)) (φ s(x, y)) else 0) =
      dem φ u x v * ∑ y ∈ nd G u v,
        (if y ∈ cn G u x then normT (φ s(u, x)) (φ s(u, y)) (φ s(x, y)) else 0) := by
    rw [mul_sum]; exact sum_congr rfl fun y _ => by split_ifs <;> simp
  have e2 : ∑ y ∈ nd G u v, (if y ∈ U then 1 - α else 1) = (nd G u v).card - α * U.card := by
    have : ∀ y, (if y ∈ U then 1 - α else (1 : ℝ)) = 1 - (if y ∈ U then α else 0) := by
      intro y; split_ifs <;> ring
    simp only [this, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hU : (nd G u v).filter (· ∈ U) = U := by
      ext y; simp only [mem_filter, U]; tauto
    rw [hU]; ring
  rw [e1, hdem]
  have hs := sum_le_sum hterm
  rw [e2] at hs
  have hα' : α * (α * Fintype.card V) ≤ α * U.card := mul_le_mul_of_nonneg_left hcnt hα
  have := mul_le_mul_of_nonneg_left hs hF.le
  nlinarith

/-- Both sides of an unclean vertex: the outer contribution drops by `α² n`. -/
lemma outS_pair_unclean (hφ : GoodWeighting G φ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {u v x : V}
    (hneg : φ s(u, v) < 0) (hx : x ∈ cn G u v) {M : ℝ} (hMu : ((nd G u v).card : ℝ) ≤ M)
    (hMv : ((nd G v u).card : ℝ) ≤ M) (hun : IsUnclean G φ α u v x ∨ IsUnclean G φ α v u x) :
    outS G φ u v x + outS G φ v u x ≤ (-φ s(u, v)) * (M - α * (α * Fintype.card V)) := by
  have hx' := (mem_cn G).1 hx
  have hF : 0 < -φ s(u, v) := by linarith
  rcases hun with h | h
  · have h1 := outS_unclean G φ hφ hα hα1 hneg hx h
    have h2 := outS_le G φ hφ v u x hx'.2
    have hd : dem φ v x u = 0 := by
      unfold dem; exact demF_of_nonpos h.2.1.le
    rw [hd, zero_mul] at h2
    nlinarith
  · have hneg' : φ s(v, u) < 0 := by rw [Sym2.eq_swap]; exact hneg
    have hx2 : x ∈ cn G v u := by rw [cn_comm]; exact hx
    have h1 := outS_unclean G φ hφ hα hα1 hneg' hx2 h
    have h2 := outS_le G φ hφ u v x hx'.1
    have hd : dem φ u x v = 0 := by
      unfold dem; exact demF_of_nonpos h.2.1.le
    rw [hd, zero_mul] at h2
    rw [Sym2.eq_swap] at h1
    nlinarith

open Classical in
/-- **Lemma 10.2 (Cleaning).** If `δ(G) ≥ (3/4 - ε) n` and at least `α n` vertices of
`N(u) ∩ N(v)` are `α`-unclean with respect to the negative edge `uv` (on either side), then
`ch_F(uv) ≥ |φ(uv)| (4α³ - 4ε)`. -/
theorem chNeg_cleaning (hφ : GoodWeighting G φ) {ε α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    (hU : α * Fintype.card V ≤
      (((cn G u v).filter fun x => IsUnclean G φ α u v x ∨ IsUnclean G φ α v u x).card : ℝ)) :
    (-φ s(u, v)) * (4 * α ^ 3 - 4 * ε) ≤ chNeg G φ u v := by
  obtain ⟨hc, hmu⟩ := cn_bounds_of_minDegree G hδ u v
  obtain ⟨-, hmv⟩ := cn_bounds_of_minDegree G hδ v u
  have hm := recv_master G φ hφ huv hneg
  have hI := Ival_le G φ hφ huv hneg
  have hcle := card_cn_le G u v
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  set M := (1 / 4 + ε) * n
  set F := -φ s(u, v) with hFdef
  have hF : 0 < F := by simp only [F]; linarith
  set U := (cn G u v).filter fun x => IsUnclean G φ α u v x ∨ IsUnclean G φ α v u x
  -- total outer contribution
  have hout : ∑ w ∈ cn G u v, (outS G φ u v w + outS G φ v u w) ≤
      ∑ w ∈ cn G u v, (F * M - if w ∈ U then F * (α * (α * n)) else 0) := by
    refine sum_le_sum fun w hw => ?_
    split_ifs with hwU
    · have := outS_pair_unclean G φ hφ hα hα1 hneg hw hmu hmv (mem_filter.1 hwU).2
      linarith
    · have hw' := (mem_cn G).1 hw
      have o1 := outS_le G φ hφ u v w hw'.1
      have o2 := outS_le G φ hφ v u w hw'.2
      have hp := dem_pair_sum G φ hφ huv hneg hw
      have m1 := mul_le_mul_of_nonneg_left hmu (dem_nonneg φ u w v)
      have m2 := mul_le_mul_of_nonneg_left hmv (dem_nonneg φ v w u)
      have : dem φ u w v * M + dem φ v w u * M = F * M := by rw [← add_mul, hp]
      linarith
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_filter] at hout
  have hfil : (cn G u v).filter (· ∈ U) = U := by
    ext y; simp only [mem_filter, U]; tauto
  rw [hfil, sum_const, nsmul_eq_mul] at hout
  set c : ℝ := ((cn G u v).card : ℝ)
  have hsave : F * (α * (α * n)) * (α * n) ≤ (U.card : ℝ) * (F * (α * (α * n))) := by
    rw [mul_comm ((U.card : ℝ))]
    exact mul_le_mul_of_nonneg_left hU (by positivity)
  have hd1 : c / n ≤ 1 := (div_le_one hn).2 hcle
  have hd0 : 1 / 2 - 2 * ε ≤ c / n := (le_div_iff₀ hn).2 hc
  unfold chNeg
  have hc4 : (0 : ℝ) ≤ 4 / n ^ 2 := by positivity
  have hI' := mul_le_mul_of_nonneg_left hI hc4
  have ho' := mul_le_mul_of_nonneg_left hout hc4
  have key : 0 ≤ F * ((1 - c / n) * (2 * (c / n) - 1 + 4 * ε)) :=
    mul_nonneg hF.le (mul_nonneg (by linarith) (by linarith))
  have e1 : 4 / n * (c * F) - 4 / n ^ 2 * (F * c ^ 2 / 2 + (c * (F * M) -
      F * (α * (α * n)) * (α * n))) - F =
      F * ((1 - c / n) * (2 * (c / n) - 1 + 4 * ε)) + F * (4 * α ^ 3 - 4 * ε) := by
    simp only [M]; field_simp; ring
  have e2 : 4 / n ^ 2 * (U.card * (F * (α * (α * n)))) ≥
      4 / n ^ 2 * (F * (α * (α * n)) * (α * n)) := mul_le_mul_of_nonneg_left hsave hc4
  nlinarith

/-- Polynomial inequality behind the first part of Lemma 9.6. -/
lemma polyA {d μ ε γ : ℝ} (hε0 : 0 ≤ ε) (hεγ : ε ≤ γ ^ 2) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 20)
    (hd1 : d ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 - d) (hμ2 : μ ≤ 1 / 4 + ε)
    (h : 4 * d - 4 * d * μ - 2 * d ^ 2 - 1 ≤ γ) : d ≤ 1 / 2 + 2 * γ := by
  by_contra hcon
  push_neg at hcon
  have hd0 : 0 ≤ d := by linarith
  rcases le_or_gt (9 / 10) d with h9 | h9
  · have : μ ≤ 1 / 10 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 4 * d)]
  · have hμd := mul_le_mul_of_nonneg_left hμ2 (by linarith : (0:ℝ) ≤ 4 * d)
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - (1 / 2 + 2 * γ))
      (by linarith : (0:ℝ) ≤ 9 / 10 - d), mul_nonneg hε0 hγ0.le, mul_nonneg hγ0.le hγ0.le,
      mul_nonneg hε0 (by linarith : (0:ℝ) ≤ d)]

/-- Polynomial inequality behind the second part of Lemma 9.6. -/
lemma polyB {d ε γ : ℝ} (hε0 : 0 ≤ ε) (hεγ : ε ≤ γ ^ 2) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 20)
    (hd0 : 1 / 2 - 2 * ε ≤ d) (hd1 : d ≤ 1 / 2 + 2 * γ) :
    -γ ≤ 4 * d - 4 * d * (1 / 4 + ε) - 2 * d ^ 2 - 1 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - (1 / 2 - 2 * ε))
      (by linarith : (0:ℝ) ≤ 1 / 2 + 2 * γ - d), mul_nonneg hε0 hγ0.le, mul_nonneg hγ0.le hγ0.le]

/-- **Lemma 9.6, first part.** If `δ(G) ≥ (3/4 - ε) n` with `0 ≤ ε ≤ γ²`, `0 < γ ≤ 1/20` and
the negative edge `uv` has `ch_F(uv) ≤ γ |φ(uv)|`, then `|N(u) ∩ N(v)| ≤ (1/2 + 2γ) n`. -/
theorem small_charge_cn (hφ : GoodWeighting G φ) {ε γ : ℝ} (hε0 : 0 ≤ ε) (hεγ : ε ≤ γ ^ 2)
    (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 20)
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    (hch : chNeg G φ u v ≤ γ * (-φ s(u, v))) :
    ((cn G u v).card : ℝ) ≤ (1 / 2 + 2 * γ) * Fintype.card V := by
  obtain ⟨hc, hmu⟩ := cn_bounds_of_minDegree G hδ u v
  obtain ⟨-, hmv⟩ := cn_bounds_of_minDegree G hδ v u
  set M : ℝ := max ((nd G u v).card : ℝ) ((nd G v u).card)
  have hM := chNeg_master G φ hφ huv hneg (M := M) (le_max_left _ _) (le_max_right _ _)
  have hI := Ival_le G φ hφ huv hneg
  have hcle := card_cn_le G u v
  have h1 := card_nd_add_cn_le G u v
  have h2 := card_nd_add_cn_le G v u
  rw [cn_comm G v u] at h2
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  set c : ℝ := ((cn G u v).card : ℝ)
  set F := -φ s(u, v) with hFdef
  have hF : 0 < F := by simp only [F]; linarith
  have h1' : ((nd G u v).card : ℝ) + c ≤ n := by simp only [c, n]; exact_mod_cast h1
  have h2' : ((nd G v u).card : ℝ) + c ≤ n := by simp only [c, n]; exact_mod_cast h2
  have hM1 : M ≤ n - c := max_le (by linarith) (by linarith)
  have hM2 : M ≤ (1 / 4 + ε) * n := max_le hmu hmv
  have hS : 0 ≤ 4 / n ^ 2 * (F * c ^ 2 / 2 - Ival G φ u v) :=
    mul_nonneg (by positivity) (by linarith)
  set d := c / n with hd
  set μ := M / n with hμ
  have hμ1 : μ ≤ 1 - d := by
    rw [hμ, hd, div_le_iff₀ hn]; rw [sub_mul, div_mul_cancel₀ _ hn.ne']; linarith
  have hμ2 : μ ≤ 1 / 4 + ε := by rw [hμ, div_le_iff₀ hn]; linarith
  have hd1 : d ≤ 1 := (div_le_one hn).2 hcle
  have hd0 : 1 / 2 - 2 * ε ≤ d := (le_div_iff₀ hn).2 hc
  have hμ0 : 0 ≤ μ := div_nonneg (le_trans (Nat.cast_nonneg _) (le_max_left _ _)) hn.le
  have hmain : F * (4 * d - 4 * d * μ - 2 * d ^ 2 - 1) ≤ γ * F := by linarith
  have hmain' : 4 * d - 4 * d * μ - 2 * d ^ 2 - 1 ≤ γ := by
    by_contra h; push_neg at h; nlinarith
  rw [← div_le_iff₀ hn]
  exact polyA hε0 hεγ hγ0 hγ hd1 hμ0 hμ1 hμ2 hmain'

/-- **Lemma 9.6, second part.** Under the same hypotheses the value of the common neighbourhood is
nearly maximal: `ch''_F(uv) ≥ (1 - 26γ) |φ(uv)| c² / 2`. -/
theorem small_charge_value (hφ : GoodWeighting G φ) {ε γ : ℝ} (hε0 : 0 ≤ ε) (hεγ : ε ≤ γ ^ 2)
    (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 20)
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    (hch : chNeg G φ u v ≤ γ * (-φ s(u, v))) :
    (1 - 26 * γ) * (-φ s(u, v)) * ((cn G u v).card : ℝ) ^ 2 / 2 ≤ Ival G φ u v := by
  have hcn := small_charge_cn G φ hφ hε0 hεγ hγ0 hγ hδ huv hneg hch
  obtain ⟨hc, hmu⟩ := cn_bounds_of_minDegree G hδ u v
  obtain ⟨-, hmv⟩ := cn_bounds_of_minDegree G hδ v u
  have hM := chNeg_master G φ hφ huv hneg hmu hmv
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  set c : ℝ := ((cn G u v).card : ℝ)
  set F := -φ s(u, v) with hFdef
  have hF : 0 < F := by simp only [F]; linarith
  set S := F * c ^ 2 / 2 - Ival G φ u v
  have e : (1 / 4 + ε) * n / n = 1 / 4 + ε := by field_simp
  rw [e] at hM
  set d := c / n with hd
  have hd0 : 1 / 2 - 2 * ε ≤ d := (le_div_iff₀ hn).2 hc
  have hd1 : d ≤ 1 / 2 + 2 * γ := (div_le_iff₀ hn).2 hcn
  -- the polynomial part is at least `-γ`
  have hpoly := polyB hε0 hεγ hγ0 hγ hd0 hd1
  have hS : 4 / n ^ 2 * S ≤ 2 * γ * F := by
    have := mul_le_mul_of_nonneg_left hpoly hF.le
    linarith
  have hS' : S ≤ γ * F * n ^ 2 / 2 := by
    have h4 : 4 / n ^ 2 * S * (n ^ 2 / 4) = S := by field_simp
    have := mul_le_mul_of_nonneg_right hS (by positivity : (0:ℝ) ≤ n ^ 2 / 4)
    rw [h4] at this
    linarith
  have hc3 : n / 3 ≤ c := by
    have : ε ≤ 1 / 400 := by nlinarith
    nlinarith
  have hcn2 : n ^ 2 ≤ 26 * c ^ 2 := by
    have h0 : 0 ≤ n / 3 := by positivity
    have := pow_le_pow_left₀ h0 hc3 2
    nlinarith
  have h13 : γ * F * n ^ 2 / 2 ≤ 13 * γ * F * c ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcn2 (by positivity : (0:ℝ) ≤ γ * F / 2)
    linarith
  have hfin : F * c ^ 2 / 2 - Ival G φ u v ≤ 13 * γ * F * c ^ 2 := le_trans hS' h13
  linarith

end NashWilliams.Frac
