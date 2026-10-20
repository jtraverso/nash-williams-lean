/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.Vortex.Chain
import RequestProject.NW18.Sampling.Glue

/-!
# From the level invariant to the literal graph statements on `G[U]`

* `minDegree_induce_ge`: the degree part of the invariant gives
  `δ(G[U]) ≥ (3/4 - a)|U|`.
* `not_ext_i_of_hiSet`: if more than `β|U|` vertices have degree `≥ (3/4 + b)|U|` with `b > β`,
  condition (i) of `IsExtremal β (G[U])` fails.
* `not_ext_ii_of_tup`: if at most `ρ|U|^k` of the `k`-tuples of `U` admit a labelling of doubled
  cut value `≥ θ k²` and `(θ + ρ) k/(k-1) < (1-β)/2`, condition (ii) fails.  This is the averaging
  ("easy") direction `sum_cutQ_tup`.
-/

namespace NashWilliams18.Vortex124

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma induce_degree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V)
    (hv : v ∈ U) : (G.induce (U : Set V)).degree ⟨v, hv⟩ = (U.filter (G.Adj v)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    simp only [mem_filter]
    exact ⟨w.2, by simpa using hw⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro x hx
    rw [mem_filter] at hx
    exact ⟨⟨x, hx.1⟩, by simpa [SimpleGraph.mem_neighborFinset] using hx.2, rfl⟩

omit [Fintype V] [DecidableEq V] in
lemma filter_adj_add_nnb (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V) :
    (U.filter (G.Adj v)).card + nnb G v U = U.card :=
  card_filter_add_card_filter_not _

omit [Fintype V] [DecidableEq V] in
lemma induce_degree_eq_sub (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (x : ↥(U : Set V)) :
    ((G.induce (U : Set V)).degree x : ℝ) = U.card - nnb G x.1 U := by
  have h1 := induce_degree_eq G U x.1 x.2
  have h2 := filter_adj_add_nnb G U x.1
  rw [show (⟨x.1, x.2⟩ : ↥(U : Set V)) = x from rfl] at h1
  rw [h1]
  have : ((U.filter (G.Adj x.1)).card : ℝ) + nnb G x.1 U = U.card := by exact_mod_cast h2
  linarith

omit [Fintype V] [DecidableEq V] in
lemma card_coe_finset (U : Finset V) : Fintype.card ↥(U : Set V) = U.card := by simp

omit [Fintype V] [DecidableEq V] in
/-- **Minimum degree of a level.** -/
theorem minDegree_induce_ge (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU : U.Nonempty) {a : ℝ} (h : ∀ v ∈ U, (nnb G v U : ℝ) ≤ (1 / 4 + a) * U.card) :
    (3 / 4 - a) * (U.card : ℝ) ≤ ((G.induce (U : Set V)).minDegree : ℝ) := by
  obtain ⟨u, hu⟩ := hU
  haveI : Nonempty ↥(U : Set V) := ⟨⟨u, hu⟩⟩
  obtain ⟨w, hw⟩ := (G.induce (U : Set V)).exists_minimal_degree_vertex
  rw [hw, induce_degree_eq_sub]
  have := h w.1 w.2
  linarith

omit [Fintype V] in
/-- **Condition (i) of extremality fails on a level with many high-degree vertices.** -/
theorem not_ext_i_of_hiSet (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU0 : 0 < U.card) {β b c : ℝ} (hβb : β < b) (hβc : β < c)
    (h : c * U.card ≤ ((hiSet G U b).card : ℝ)) :
    ¬ ((1 - β) * (Fintype.card ↥(U : Set V) : ℝ) ≤
      ((univ.filter (fun x : ↥(U : Set V) =>
        ((G.induce (U : Set V)).degree x : ℝ) ≤ (3 / 4 + β) * Fintype.card ↥(U : Set V))).card :
          ℝ)) := by
  intro hi
  rw [card_coe_finset] at hi
  set A := univ.filter (fun x : ↥(U : Set V) =>
    ((G.induce (U : Set V)).degree x : ℝ) ≤ (3 / 4 + β) * U.card)
  have hU : (0 : ℝ) < U.card := by exact_mod_cast hU0
  have hdisj : Disjoint (A.image Subtype.val) (hiSet G U b) := by
    rw [disjoint_left]
    intro v hvA hvH
    obtain ⟨x, hxA, rfl⟩ := mem_image.mp hvA
    have hx := (mem_filter.mp hxA).2
    rw [induce_degree_eq_sub] at hx
    have hH := (mem_filter.mp hvH).2
    nlinarith
  have hsub : A.image Subtype.val ∪ hiSet G U b ⊆ U := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hv; exact x.2
    · exact (mem_filter.mp hv).1
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ Subtype.val_injective] at hcard
  have : (A.card : ℝ) + (hiSet G U b).card ≤ U.card := by exact_mod_cast hcard
  nlinarith [mul_pos (sub_pos.2 hβc) hU]

omit [Fintype V] [DecidableEq V] in
lemma cutQ_le_sq (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (s : Fin k → V)
    (a : Fin k → Bool) : Sampling.cutQ G s a ≤ (k : ℝ) ^ 2 := by
  unfold Sampling.cutQ
  calc (∑ i, ∑ j, if G.Adj (s i) (s j) ∧ a i ≠ a j then (1 : ℝ) else 0)
      ≤ ∑ _i : Fin k, ∑ _j : Fin k, (1 : ℝ) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => by split_ifs <;> norm_num
    _ = (k : ℝ) ^ 2 := by simp [sq]

omit [Fintype V] in
/-- Twice a cut of `G[U]` is at most the doubled cut of the corresponding labelling of `V`. -/
lemma two_cutSize_le_dcut (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (S : Finset ↥(U : Set V)) :
    2 * (cutSize (G.induce (U : Set V)) S : ℝ) ≤
      dcut G U (fun v => decide (∃ h : v ∈ U, (⟨v, h⟩ : ↥(U : Set V)) ∈ S)) := by
  classical
  set X : V → Bool := fun v => decide (∃ h : v ∈ U, (⟨v, h⟩ : ↥(U : Set V)) ∈ S) with hX
  have hXS : ∀ x : ↥(U : Set V), X x.1 = true ↔ x ∈ S := by
    intro x; simp [hX]
  have h1 := Sampling.cutSize_le_pairs (G.induce (U : Set V)) S
  have h2 := Sampling.doubled_eq (fun x y : ↥(U : Set V) => (G.induce (U : Set V)).Adj x y)
    (fun x y h => h.symm) (fun x => X x.1)
  have h3 : (∑ x : ↥(U : Set V), ∑ y : ↥(U : Set V),
      if (G.induce (U : Set V)).Adj x y ∧ x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) =
      ∑ x : ↥(U : Set V), ∑ y : ↥(U : Set V),
      if (G.induce (U : Set V)).Adj x y ∧ X x.1 = true ∧ X y.1 = false then (1 : ℝ) else 0 := by
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    have hx := hXS x
    have hy := hXS y
    have hy' : X y.1 = false ↔ y ∉ S := by
      rw [← hy]; cases X y.1 <;> simp
    simp only [hx, hy']
  have h4 : (∑ x : ↥(U : Set V), ∑ y : ↥(U : Set V),
      if (G.induce (U : Set V)).Adj x y ∧ X x.1 ≠ X y.1 then (1 : ℝ) else 0) = dcut G U X := by
    unfold dcut
    rw [Finset.sum_subtype U (p := fun v => v ∈ (U : Set V)) (fun v => by simp)]
    refine sum_congr rfl fun x _ => ?_
    rw [Finset.sum_subtype U (p := fun v => v ∈ (U : Set V)) (fun v => by simp)]
    refine sum_congr rfl fun y _ => ?_
    rfl
  simp (config := { failIfUnchanged := false }) only at h2
  linarith

omit [Fintype V] in
/-- **Condition (ii) of extremality fails on a level with few bad `k`-tuples.** -/
theorem not_ext_ii_of_tup (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU0 : 0 < U.card) {k : ℕ} (hk : 2 ≤ k) {θ ρ β : ℝ} (hθ0 : 0 ≤ θ)
    (htup : (((tup U k).filter (fun s => ∃ a : Fin k → Bool,
      θ * (k : ℝ) ^ 2 ≤ Sampling.cutQ G s a)).card : ℝ) ≤ ρ * (U.card : ℝ) ^ k)
    (hθρ : (θ + ρ) * k / (k - 1) < (1 - β) / 2) :
    ¬ ∃ S : Finset ↥(U : Set V), (1 - β) * (Fintype.card ↥(U : Set V) : ℝ) ^ 2 / 4 ≤
      (cutSize (G.induce (U : Set V)) S : ℝ) := by
  classical
  rintro ⟨S, hS⟩
  rw [card_coe_finset] at hS
  set X : V → Bool := fun v => decide (∃ h : v ∈ U, (⟨v, h⟩ : ↥(U : Set V)) ∈ S)
  have h2c := two_cutSize_le_dcut G U S
  set f : (Fin k → V) → Prop := fun s => ∃ a : Fin k → Bool, θ * (k : ℝ) ^ 2 ≤ Sampling.cutQ G s a
  have havg := sum_cutQ_tup G U k X
  have hterm : ∀ s ∈ tup U k, Sampling.cutQ G s (fun l => X (s l)) ≤
      (if f s then (k : ℝ) ^ 2 else 0) + θ * (k : ℝ) ^ 2 := by
    intro s _
    by_cases hf : f s
    · rw [if_pos hf]
      have := cutQ_le_sq G s (fun l => X (s l))
      have hθ : 0 ≤ θ * (k : ℝ) ^ 2 := by positivity
      linarith
    · rw [if_neg hf, zero_add]
      simp only [f, not_exists, not_le] at hf
      exact (hf _).le
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_const, card_tup, nsmul_eq_mul, ← sum_filter, sum_const,
    nsmul_eq_mul] at hsum
  rw [havg] at hsum
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hU : (0 : ℝ) < U.card := by exact_mod_cast hU0
  have hUk2 : (0 : ℝ) < (U.card : ℝ) ^ (k - 2) := by positivity
  have hpow : (U.card : ℝ) ^ k = (U.card : ℝ) ^ (k - 2) * (U.card : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  -- `k(k-1)|U|^{k-2} dcut ≤ k² |U|^k (θ + ρ)`
  have hmain : (k * (k - 1) : ℝ) * (U.card : ℝ) ^ (k - 2) * dcut G U X ≤
      (k : ℝ) ^ 2 * (U.card : ℝ) ^ k * (θ + ρ) := by
    have h1 : (((tup U k).filter f).card : ℝ) * (k : ℝ) ^ 2 ≤ ρ * (U.card : ℝ) ^ k * (k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right htup (by positivity)
    push_cast at hsum
    nlinarith
  rw [hpow] at hmain
  have hdcut : dcut G U X * (k - 1) ≤ k * (U.card : ℝ) ^ 2 * (θ + ρ) := by
    have hk0 : (0 : ℝ) < k := by linarith
    have := hmain
    have e : (k * (k - 1) : ℝ) * ((U.card : ℝ) ^ (k - 2)) * dcut G U X =
        ((U.card : ℝ) ^ (k - 2) * k) * (dcut G U X * (k - 1)) := by ring
    have e2 : (k : ℝ) ^ 2 * ((U.card : ℝ) ^ (k - 2) * (U.card : ℝ) ^ 2) * (θ + ρ) =
        ((U.card : ℝ) ^ (k - 2) * k) * (k * (U.card : ℝ) ^ 2 * (θ + ρ)) := by ring
    rw [e, e2] at this
    exact le_of_mul_le_mul_left this (by positivity)
  have hθρ' : (θ + ρ) * k < (1 - β) / 2 * (k - 1) := by
    rwa [div_lt_iff₀ (by linarith)] at hθρ
  have hU2 : (0 : ℝ) < (U.card : ℝ) ^ 2 := by positivity
  have : (1 - β) * (U.card : ℝ) ^ 2 / 2 * (k - 1) ≤ k * (U.card : ℝ) ^ 2 * (θ + ρ) := by
    have h5 : (1 - β) * (U.card : ℝ) ^ 2 / 2 ≤ dcut G U X := by linarith
    have hk1 : (0 : ℝ) ≤ k - 1 := by linarith
    nlinarith
  nlinarith

end NashWilliams18.Vortex124
