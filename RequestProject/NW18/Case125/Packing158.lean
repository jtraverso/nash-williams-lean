/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Surplus

/-!
# Proposition 15.8 and Claim 15.9.3: low-degree subpackings

* `two_mul_card_filter_mem_le`: in a triangle packing, a vertex lies in at most `n/2`
  triangles;
* `card_filter_edges_mem_le`: the edges of a packing at `v` are at most twice the number of
  its triangles at `v`;
* `prop_15_8`: a packing `T` has a subpacking `T'` with at most `k` triangles at every vertex
  and `2k |T| ≤ (2k + 3n) |T'|`;
* `claim_15_9_3`: a packing of at least `2√γ n²` triangles has a subpacking of at least
  `γ n²/2` triangles whose edge set has maximum degree at most `√γ n`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a triangle packing every vertex lies in at most `n/2` triangles. -/
lemma two_mul_card_filter_mem_le (G : SimpleGraph V) {T : Finset (Finset V)}
    (hT : IsTrianglePacking G T) (v : V) :
    2 * (T.filter (fun t => v ∈ t)).card ≤ Fintype.card V := by
  have hdisj : ((T.filter (fun t => v ∈ t)) : Set (Finset V)).PairwiseDisjoint
      (fun t => t.erase v) := by
    intro t ht t' ht' hne
    simp only [coe_filter, Set.mem_setOf_eq] at ht ht'
    refine disjoint_left.mpr fun w hw hw' => hne ?_
    rw [mem_erase] at hw hw'
    by_contra hne'
    have h1 : s(v, w) ∈ triEdges t := mk_mem_triEdges.mpr ⟨ht.2, hw.2, Ne.symm hw.1⟩
    have h2 : s(v, w) ∈ triEdges t' := mk_mem_triEdges.mpr ⟨ht'.2, hw'.2, Ne.symm hw'.1⟩
    exact disjoint_left.mp (hT.2 ht.1 ht'.1 hne') h1 h2
  have hcard := card_biUnion hdisj
  have hle : ((T.filter (fun t => v ∈ t)).biUnion (fun t => t.erase v)).card ≤
      Fintype.card V := card_le_univ _
  rw [hcard] at hle
  have : ∑ t ∈ T.filter (fun t => v ∈ t), (t.erase v).card =
      ∑ _t ∈ T.filter (fun t => v ∈ t), 2 := by
    refine sum_congr rfl fun t ht => ?_
    simp only [mem_filter] at ht
    rw [card_erase_of_mem ht.2, (hT.1 t ht.1).card_eq]
  rw [this, sum_const, smul_eq_mul] at hle
  omega

omit [Fintype V] in
/-- The edges of a packing at `v` are at most twice the number of its triangles at `v`. -/
lemma card_filter_edges_mem_le (G : SimpleGraph V) {T : Finset (Finset V)}
    (hT : IsTrianglePacking G T) (v : V) :
    ((T.biUnion triEdges).filter (fun e => v ∈ e)).card ≤
      2 * (T.filter (fun t => v ∈ t)).card := by
  have hsub : (T.biUnion triEdges).filter (fun e => v ∈ e) ⊆
      (T.filter (fun t => v ∈ t)).biUnion (fun t => (t.erase v).image (fun w => s(v, w))) := by
    intro e he
    simp only [mem_filter, mem_biUnion] at he
    obtain ⟨⟨t, ht, het⟩, hve⟩ := he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_triEdges.mp het
      simp only [mem_biUnion, mem_filter, mem_image, mem_erase]
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact ⟨t, ⟨ht, ha⟩, b, ⟨Ne.symm hab, hb⟩, rfl⟩
      · exact ⟨t, ⟨ht, hb⟩, a, ⟨hab, ha⟩, Sym2.eq_swap⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ t ∈ T.filter (fun t => v ∈ t), ((t.erase v).image (fun w => s(v, w))).card
      ≤ ∑ _t ∈ T.filter (fun t => v ∈ t), 2 := sum_le_sum fun t ht => by
        simp only [mem_filter] at ht
        refine card_image_le.trans ?_
        rw [card_erase_of_mem ht.2, (hT.1 t ht.1).card_eq]
    _ = 2 * (T.filter (fun t => v ∈ t)).card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Double counting of vertex–triangle incidences. -/
lemma sum_card_filter_mem_tri (T : Finset (Finset V)) :
    ∑ v, (T.filter (fun t => v ∈ t)).card = ∑ t ∈ T, t.card := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [← card_filter, filter_mem_eq_inter, univ_inter]

/-- **Proposition 15.8** (counting form).  A triangle packing `T` has a subpacking `T'` with at
most `k` triangles at every vertex and `2k |T| ≤ (2k + 3n) |T'|`. -/
lemma prop_15_8 (G : SimpleGraph V) {T : Finset (Finset V)} (hT : IsTrianglePacking G T)
    (k : ℕ) :
    ∃ T' ⊆ T, (∀ v, (T'.filter (fun t => v ∈ t)).card ≤ k) ∧
      2 * k * T.card ≤ (2 * k + 3 * Fintype.card V) * T'.card := by
  classical
  set P := T.powerset.filter (fun S => ∀ v, (S.filter (fun t => v ∈ t)).card ≤ k) with hP
  have h0 : (∅ : Finset (Finset V)) ∈ P := by simp [hP]
  obtain ⟨T', hT'P, hmax⟩ := exists_max_image P card ⟨∅, h0⟩
  simp only [hP, mem_filter, mem_powerset] at hT'P
  obtain ⟨hT'T, hT'k⟩ := hT'P
  refine ⟨T', hT'T, hT'k, ?_⟩
  set S := univ.filter (fun v => (T'.filter (fun t => v ∈ t)).card = k) with hS
  -- every triangle outside `T'` meets `S`
  have hout : ∀ t ∈ T \ T', ∃ v ∈ t, v ∈ S := by
    intro t ht
    rw [mem_sdiff] at ht
    by_contra hcon
    push_neg at hcon
    have hins : insert t T' ∈ P := by
      simp only [hP, mem_filter, mem_powerset]
      refine ⟨insert_subset ht.1 hT'T, fun v => ?_⟩
      rw [filter_insert]
      split_ifs with hv
      · have h1 := hT'k v
        have h2 : (T'.filter (fun t => v ∈ t)).card ≠ k := by
          intro h; exact hcon v hv (by simp [hS, h])
        have h3 := card_insert_le t (T'.filter (fun t => v ∈ t))
        omega
      · exact hT'k v
    have := hmax _ hins
    rw [card_insert_of_notMem ht.2] at this
    omega
  -- counting
  have hsub : T \ T' ⊆ S.biUnion (fun v => T.filter (fun t => v ∈ t)) := by
    intro t ht
    obtain ⟨v, hvt, hvS⟩ := hout t ht
    exact mem_biUnion.mpr ⟨v, hvS, mem_filter.mpr ⟨(mem_sdiff.mp ht).1, hvt⟩⟩
  have h1 : 2 * (T \ T').card ≤ S.card * Fintype.card V := by
    have := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∑ v ∈ S, 2 * (T.filter (fun t => v ∈ t)).card ≤ ∑ _v ∈ S, Fintype.card V :=
      sum_le_sum fun v _ => two_mul_card_filter_mem_le G hT v
    rw [← mul_sum, sum_const, smul_eq_mul] at h2
    omega
  have h2 : k * S.card ≤ 3 * T'.card := by
    have e1 : ∑ v ∈ S, (T'.filter (fun t => v ∈ t)).card = k * S.card := by
      rw [sum_congr rfl fun v hv => (mem_filter.mp hv).2, sum_const, smul_eq_mul, mul_comm]
    have e2 : ∑ v ∈ S, (T'.filter (fun t => v ∈ t)).card ≤
        ∑ v, (T'.filter (fun t => v ∈ t)).card :=
      sum_le_sum_of_subset (subset_univ S)
    have e3 : ∑ v, (T'.filter (fun t => v ∈ t)).card = 3 * T'.card := by
      rw [sum_card_filter_mem_tri, sum_congr rfl fun t ht => (hT.1 t (hT'T ht)).card_eq,
        sum_const, smul_eq_mul, mul_comm]
    omega
  have hsplit : T.card = T'.card + (T \ T').card := by
    rw [← card_sdiff_add_card_eq_card hT'T]; ring
  have h3 : k * (2 * (T \ T').card) ≤ k * (S.card * Fintype.card V) :=
    Nat.mul_le_mul_left k h1
  have h4 : (k * S.card) * Fintype.card V ≤ (3 * T'.card) * Fintype.card V :=
    Nat.mul_le_mul_right _ h2
  rw [hsplit]
  nlinarith

/-- **Claim 15.9.3.**  If `0 < γ ≤ 1/100`, `20 ≤ √γ n` and `T₀` is a triangle packing with
`|T₀| ≥ 2√γ n²`, then some `T' ⊆ T₀` has `|T'| ≥ γ n²/2` and the edge set of `T'` has maximum
degree at most `√γ n`. -/
lemma claim_15_9_3 (G : SimpleGraph V) {T₀ : Finset (Finset V)} (hT₀ : IsTrianglePacking G T₀)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 100) (hn : 20 ≤ Real.sqrt γ * Fintype.card V)
    (hcard : 2 * Real.sqrt γ * (Fintype.card V : ℝ) ^ 2 ≤ T₀.card) :
    ∃ T' ⊆ T₀, γ * (Fintype.card V : ℝ) ^ 2 / 2 ≤ T'.card ∧
      ∀ v, (((T'.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
        Real.sqrt γ * Fintype.card V := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set r := Real.sqrt γ with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hγ
  have hr1 : r ≤ 1 / 10 := by
    have : r ≤ Real.sqrt ((1 / 10) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hrr : r * r = γ := Real.mul_self_sqrt hγ.le
  have hn0 : 0 < n := by
    by_contra h; push_neg at h; nlinarith
  set k := ⌊r * n / 2⌋₊ with hkdef
  have hk1 : (k : ℝ) ≤ r * n / 2 := Nat.floor_le (by positivity)
  have hk2 : r * n / 2 - 1 < (k : ℝ) := by
    have := Nat.lt_floor_add_one (r * n / 2); linarith
  obtain ⟨T', hT'T, hT'k, hineq⟩ := prop_15_8 G hT₀ k
  have hT'pack : IsTrianglePacking G T' :=
    ⟨fun t ht => hT₀.1 t (hT'T ht), hT₀.2.subset (by exact_mod_cast hT'T)⟩
  refine ⟨T', hT'T, ?_, fun v => ?_⟩
  · have hR : 2 * (k : ℝ) * T₀.card ≤ (2 * (k : ℝ) + 3 * n) * T'.card := by
      rw [hndef]; exact_mod_cast hineq
    have hk3 : 0.9 * (r * n) ≤ 2 * (k : ℝ) := by linarith
    have hden : 2 * (k : ℝ) + 3 * n ≤ 3.1 * n := by
      have : r * n ≤ 1 / 10 * n := mul_le_mul_of_nonneg_right hr1 hn0.le
      linarith
    have hT'0 : (0 : ℝ) ≤ T'.card := Nat.cast_nonneg _
    have hT0c : (0 : ℝ) ≤ T₀.card := Nat.cast_nonneg _
    -- `0.9 r n · 2 r n² ≤ 2k |T₀| ≤ 3.1 n |T'|`
    have h1 : 0.9 * (r * n) * (2 * r * n ^ 2) ≤ 2 * (k : ℝ) * T₀.card :=
      mul_le_mul hk3 hcard (by positivity) (by positivity)
    have h2 : (2 * (k : ℝ) + 3 * n) * (T'.card : ℝ) ≤ 3.1 * n * T'.card :=
      mul_le_mul_of_nonneg_right hden hT'0
    have h3 : 1.8 * γ * n ^ 3 ≤ 3.1 * n * T'.card := by
      have e : 0.9 * (r * n) * (2 * r * n ^ 2) = 1.8 * (r * r) * n ^ 3 := by ring
      rw [e, hrr] at h1; linarith
    have h4 : γ * n ^ 2 / 2 * (3.1 * n) ≤ 3.1 * n * T'.card := by nlinarith
    have h5 := le_of_mul_le_mul_right (by linarith : γ * n ^ 2 / 2 * (3.1 * n) ≤
      T'.card * (3.1 * n)) (by positivity)
    exact h5
  · have h1 := card_filter_edges_mem_le G hT'pack v
    have h2 := hT'k v
    have : (((T'.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤ 2 * k := by
      exact_mod_cast h1.trans (Nat.mul_le_mul_left 2 h2)
    linarith

end NashWilliams18
