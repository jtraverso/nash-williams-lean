/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Furedi
import RequestProject.NW18.Case125.Residual

/-!
# The reserve of interior triangles (Claim 12.5.1)

`claim_12_5_1`: if one side `G[V_i]` is not `θ`-close to `T₂` or `T̄₂`, then `G[V_i ∖ A]`
contains a packing of at least `κ n²` triangles, `κ = θ/1000`.

Proof.  Take a maximal triangle packing `T` of `G[D']`, `D' = V_i ∖ A`
(`exists_maximal_packing_in`).  If `|T| < κ n²`, delete its edges: the remaining graph `H` is
triangle-free on `D'` (`deleteEdges_triangle_free`) and still has degree sum
`≥ |D'| (|V_i| − n/4 − |A|) − 12|T|` on `D'` (minimum degree `3n/4`, `sum_deg_deleteEdges`).
The Füredi step `tf_cost_bound` with a vertex `v` of maximum `H`-degree then shows that
`G[V_i]` is within `θ |V_i|²` edits of the complete bipartite graph with parts `N_H(v) ∩ D'`
(rebalanced to size `⌊|V_i|/2⌋`, `exists_sideCost_rebalance`) and its complement, i.e. `G[V_i]`
is `θ`-close to `T₂(|V_i|)` — a contradiction.  The numerical part is
`claim1251_delta_arith` and `claim1251_final_arith`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

/-- Numerical core of Claim 12.5.1: the total edit cost is at most `2θ m²`. -/
lemma claim1251_final_arith {n s θ m m' a Δ σ t cH k : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 10) (hsθ : s ≤ θ / 100) (hn : 11 ≤ θ * n)
    (hn0 : 0 ≤ n) (hm1 : (1 - s) * n / 2 ≤ m) (hm2 : m ≤ (1 + s) * n / 2)
    (ha : a ≤ 2 * s * n) (hm'1 : m - a ≤ m') (hm'2 : m' ≤ m)
    (hcost : cH + 3 * σ ≤ 6 * Δ * (m' - Δ)) (hσ : m' * (m - n / 4 - a) - 12 * t ≤ σ)
    (ht : t ≤ θ / 1000 * n ^ 2) (hk0 : 0 ≤ k) (hk : k ≤ 3 * s * n + 48 * (θ / 1000) * n + 2) :
    cH + 12 * t + 2 * a * m + 2 * m * k ≤ 2 * θ * m ^ 2 := by
  have h1 : 6 * Δ * (m' - Δ) ≤ 3 / 2 * m' ^ 2 := by
    have := sq_nonneg (m' - 2 * Δ); linarith
  have hsn : 0 ≤ s * n := mul_nonneg hs0 hn0
  have hsn10 : s * n ≤ 1 / 10 * n := mul_le_mul_of_nonneg_right hs1 hn0
  have hm'0 : 0 ≤ m' := by linarith
  have hbr : 3 / 2 * m' - 3 * m + 3 / 4 * n + 3 * a ≤ 27 / 4 * s * n := by linarith
  have h2 : 3 / 2 * m' ^ 2 - 3 * m' * (m - n / 4 - a) ≤ m' * (27 / 4 * s * n) := by
    have := mul_le_mul_of_nonneg_left hbr hm'0
    linarith
  have h3 : m' * (27 / 4 * s * n) ≤ (1 + s) * n / 2 * (27 / 4 * s * n) :=
    mul_le_mul_of_nonneg_right (hm'2.trans hm2) (by positivity)
  have h4 : (1 + s) * n / 2 * (27 / 4 * s * n) ≤ 11 / 20 * (27 / 4 * (s * n ^ 2)) := by
    have : (1 + s) / 2 ≤ 11 / 20 := by linarith
    calc (1 + s) * n / 2 * (27 / 4 * s * n) = (1 + s) / 2 * (27 / 4 * (s * n ^ 2)) := by ring
      _ ≤ 11 / 20 * (27 / 4 * (s * n ^ 2)) := mul_le_mul_of_nonneg_right this (by positivity)
  have hcH : cH ≤ 11 / 20 * (27 / 4 * (s * n ^ 2)) + 36 * t := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hm3 : m ≤ 11 / 20 * n := by linarith
  have ham : a * m ≤ (2 * s * n) * (11 / 20 * n) := mul_le_mul ha hm3 hm0 (by positivity)
  have hmk : m * k ≤ (11 / 20 * n) * (3 * s * n + 48 * (θ / 1000) * n + 2) :=
    mul_le_mul hm3 hk hk0 (by positivity)
  have hm4 : 9 / 20 * n ≤ m := by linarith
  have hθ : 0 ≤ θ := by
    by_contra h; push_neg at h; nlinarith
  have hrhs : 2 * θ * (9 / 20 * n) ^ 2 ≤ 2 * θ * m ^ 2 := by
    have : (9 / 20 * n) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm4 2
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsθn : s * n ^ 2 ≤ θ / 100 * n ^ 2 := mul_le_mul_of_nonneg_right hsθ (sq_nonneg _)
  have h2n : 11 * n ≤ (θ * n) * n := mul_le_mul_of_nonneg_right hn hn0
  linarith

/-- Numerical part of Claim 12.5.1: the maximum degree `Δ` of the triangle-free remainder is
close to `n/4`. -/
lemma claim1251_delta_arith {n s θ m m' a Δ σ t : ℝ}
    (hs1 : s ≤ 1 / 10) (hθ : 0 ≤ θ) (hn : 0 < n) (hm1 : (1 - s) * n / 2 ≤ m)
    (ha : a ≤ 2 * s * n) (hm'1 : m - a ≤ m')
    (hσ : m' * (m - n / 4 - a) - 12 * t ≤ σ) (havg : σ ≤ m' * Δ) (ht : t ≤ θ / 1000 * n ^ 2) :
    m - n / 4 - a - 48 * (θ / 1000) * n ≤ Δ := by
  have hsn10 : s * n ≤ 1 / 10 * n := mul_le_mul_of_nonneg_right hs1 hn.le
  have hm'4 : n / 4 ≤ m' := by linarith
  by_contra h
  push_neg at h
  have h1 := mul_lt_mul_of_pos_left h (by linarith : 0 < m')
  have h2 : 48 * (θ / 1000) * n * (n / 4) ≤ 48 * (θ / 1000) * n * m' :=
    mul_le_mul_of_nonneg_left hm'4 (by positivity)
  nlinarith

section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With minimum degree `≥ 3n/4`, every vertex has at least `|V_{p v}| − n/4` neighbours in its
own part. -/
lemma four_card_partClass_le (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (u : V)
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    4 * (partClass p (p u)).card ≤ 4 * partDeg G p u (p u) + Fintype.card V := by
  have h1 := partDeg_add_partDeg G p u
  have h2 := G.minDegree_le_degree u
  have h3 := partDeg_le_card_partClass G p u 0
  have h4 := partDeg_le_card_partClass G p u 1
  have h5 := card_partClass_add p
  rcases fin2_cases (p u) with h | h <;> rw [h] <;> omega

omit [DecidableEq V] in
lemma filter_adj_partClass (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (u : V) (i : Fin 2) : ((partClass p i).filter (G.Adj u)).card = partDeg G p u i := by
  unfold partDeg partClass
  congr 1; ext w; simp only [mem_filter, mem_univ, true_and]; tauto

end

/-- **Claim 12.5.1.** For every `θ > 0` there are `κ > 0`, `β₂ > 0` and `n₂` such that: if `G`
has `δ(G) ≥ 3n/4`, the bipartition `p` is `β`-extremal (`0 < β ≤ β₂`), `A` has
`|A| ≤ 2√β n`, every vertex outside `A` has `IntDeg ≤ (1/4 + 2√β) n`, every part has size
at least `(1 − √β) n/2`, and some side `G[V_i]` is not `θ`-close to `T₂(|V_i|)` or
`T̄₂(|V_i|)`, then `G − A` contains a packing of at least `κ n²` interior triangles. -/
theorem claim_12_5_1 :
    ∀ θ : ℝ, 0 < θ → ∃ κ : ℝ, 0 < κ ∧ ∃ β₂ : ℝ, 0 < β₂ ∧ ∃ n₂ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 2) (A : Finset V) (β : ℝ), 0 < β → β ≤ β₂ → n₂ ≤ Fintype.card V →
        3 * Fintype.card V ≤ 4 * G.minDegree →
        (A.card : ℝ) ≤ 2 * Real.sqrt β * Fintype.card V →
        (∀ v, v ∉ A → (partDeg G p v (p v) : ℝ) ≤ (1 / 4 + 2 * Real.sqrt β) * Fintype.card V) →
        (∀ i, (1 - Real.sqrt β) * Fintype.card V / 2 ≤ ((partClass p i).card : ℝ)) →
        (∃ i, ¬ IsSideClose θ G (partClass p i)) →
        ∃ T₀ : Finset (Finset V), IsTrianglePacking G T₀ ∧
          (∀ s ∈ T₀, ∃ i, ∀ x ∈ s, p x = i) ∧ (∀ s ∈ T₀, ∀ x ∈ s, x ∉ A) ∧
          κ * (Fintype.card V : ℝ) ^ 2 ≤ (T₀.card : ℝ) := by
  intro θ hθ
  refine ⟨θ / 1000, by positivity, min ((θ / 100) ^ 2) (1 / 100), by positivity,
    ⌈11 / θ⌉₊ + 1, ?_⟩
  intro V _ _ G _ p A β hβ hβ₂ hn hδ hA hint hpart hside
  classical
  set r := Real.sqrt β with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 / 10 := by
    have : r ≤ Real.sqrt ((1 / 10) ^ 2) :=
      Real.sqrt_le_sqrt (hβ₂.trans ((min_le_right _ _).trans (by norm_num)))
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hrθ : r ≤ θ / 100 := by
    have : r ≤ Real.sqrt ((θ / 100) ^ 2) := Real.sqrt_le_sqrt (hβ₂.trans (min_le_left _ _))
    rwa [Real.sqrt_sq (by positivity)] at this
  have hnθ : 11 ≤ θ * (Fintype.card V : ℝ) := by
    have h1 : ((⌈11 / θ⌉₊ + 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    have h2 := Nat.le_ceil (11 / θ)
    push_cast at h1
    have : 11 / θ ≤ Fintype.card V := by linarith
    rw [div_le_iff₀ hθ] at this; linarith
  have hn0 : (0 : ℝ) < Fintype.card V := by
    by_contra h; push_neg at h; nlinarith
  obtain ⟨i, hi⟩ := hside
  set D := partClass p i with hD
  set D' := D \ A with hD'
  obtain ⟨T, hTp, hTD, hTmax⟩ := exists_maximal_packing_in G D'
  by_cases hbig : θ / 1000 * (Fintype.card V : ℝ) ^ 2 ≤ T.card
  · refine ⟨T, hTp, fun s hs => ⟨i, fun x hx => ?_⟩, fun s hs x hx => ?_, hbig⟩
    · have := (mem_sdiff.mp (hTD s hs hx)).1
      simp only [hD, partClass, mem_filter, mem_univ, true_and] at this
      exact this
    · exact (mem_sdiff.mp (hTD s hs hx)).2
  exfalso
  push_neg at hbig
  apply hi
  -- the triangle-free remainder
  set C := T.biUnion triEdges with hCdef
  set H := G.deleteEdges (↑C : Set (Sym2 V)) with hHdef
  have htf := deleteEdges_triangle_free G D' T hTmax
  have hC : C.card ≤ 6 * T.card := card_biUnion_triEdges_le G T hTp.1
  -- sizes
  have hm1 : (1 - r) * Fintype.card V / 2 ≤ (D.card : ℝ) := hpart i
  have hm2 : (D.card : ℝ) ≤ (1 + r) * Fintype.card V / 2 := by
    have hsum : ((partClass p 0).card : ℝ) + (partClass p 1).card = Fintype.card V := by
      exact_mod_cast card_partClass_add p
    have h0 := hpart 0
    have h1 := hpart 1
    rcases fin2_cases i with rfl | rfl
    · simp only [hD]; linarith
    · simp only [hD]; linarith
  have hDD' : D' ⊆ D := sdiff_subset
  have hDA : (D \ D').card ≤ A.card := card_le_card fun x hx => by
    simp only [hD', mem_sdiff] at hx; tauto
  have hm'1 : (D.card : ℝ) - A.card ≤ D'.card := by
    have h1 := card_sdiff_add_card_eq_card hDD'
    have : ((D \ D').card : ℝ) + D'.card = D.card := by exact_mod_cast h1
    have h2 : ((D \ D').card : ℝ) ≤ A.card := by exact_mod_cast hDA
    linarith
  have hm'2 : (D'.card : ℝ) ≤ D.card := by exact_mod_cast card_le_card hDD'
  have hrn10 : r * Fintype.card V ≤ 1 / 10 * Fintype.card V :=
    mul_le_mul_of_nonneg_right hr1 hn0.le
  have hne : D'.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < D'.card := by linarith
    exact_mod_cast this
  -- a vertex of maximum degree in the remainder
  obtain ⟨v, hvD', hvmax⟩ := exists_max_image D' (fun u => (D'.filter (H.Adj u)).card) hne
  set X := D'.filter (H.Adj v) with hXdef
  have hcost := tf_cost_bound H D' v htf hvD' hvmax
  have hsumdeg := sum_deg_deleteEdges G C D'
  -- degrees of `G` inside `D'`
  have hdegG : ∀ u ∈ D', (D.card : ℝ) - Fintype.card V / 4 - A.card ≤
      (D'.filter (G.Adj u)).card := by
    intro u hu
    have huD : u ∈ D := hDD' hu
    have hpu : p u = i := by simpa [hD, partClass] using huD
    have h4 := four_card_partClass_le G p u hδ
    rw [hpu, ← filter_adj_partClass G p u i] at h4
    have hsub : D.filter (G.Adj u) ⊆ D'.filter (G.Adj u) ∪ A := by
      intro w hw
      simp only [mem_filter] at hw
      simp only [mem_union, mem_filter, hD', mem_sdiff]
      by_cases hwA : w ∈ A
      · exact Or.inr hwA
      · exact Or.inl ⟨⟨hw.1, hwA⟩, hw.2⟩
    have h5 := (card_le_card hsub).trans (card_union_le _ _)
    have h6 : (4 * D.card : ℝ) ≤ 4 * (D.filter (G.Adj u)).card + Fintype.card V := by
      exact_mod_cast h4
    have h7 : ((D.filter (G.Adj u)).card : ℝ) ≤ (D'.filter (G.Adj u)).card + A.card := by
      exact_mod_cast h5
    linarith
  have hσG : (D'.card : ℝ) * ((D.card : ℝ) - Fintype.card V / 4 - A.card) ≤
      ∑ u ∈ D', ((D'.filter (G.Adj u)).card : ℝ) := by
    have := sum_le_sum hdegG
    rwa [sum_const, nsmul_eq_mul] at this
  -- the maximum degree
  have hΔup : (X.card : ℝ) ≤ (1 / 4 + 2 * r) * Fintype.card V := by
    have hvA : v ∉ A := (mem_sdiff.mp hvD').2
    have hpv : p v = i := by simpa [hD, partClass] using hDD' hvD'
    have hsub : X ⊆ D.filter (G.Adj v) := by
      intro w hw
      simp only [hXdef, mem_filter, hHdef, SimpleGraph.deleteEdges_adj] at hw
      exact mem_filter.mpr ⟨hDD' hw.1, hw.2.1⟩
    have h1 := card_le_card hsub
    rw [filter_adj_partClass G p v i, ← hpv] at h1
    have h2 := hint v hvA
    have h3 : (X.card : ℝ) ≤ partDeg G p v (p v) := by exact_mod_cast h1
    linarith
  have havg : ∑ u ∈ D', ((D'.filter (H.Adj u)).card : ℝ) ≤ D'.card * X.card := by
    have := sum_le_sum (fun u hu => (Nat.cast_le (α := ℝ)).mpr (hvmax u hu))
    rwa [sum_const, nsmul_eq_mul] at this
  have hXD' : X.card ≤ D'.card := card_le_card (filter_subset _ _)
  -- real versions
  set σ : ℝ := ∑ u ∈ D', ((D'.filter (H.Adj u)).card : ℝ) with hσdef
  have hσ : (D'.card : ℝ) * ((D.card : ℝ) - Fintype.card V / 4 - A.card) - 12 * T.card ≤ σ := by
    have h1 : (∑ u ∈ D', (D'.filter (G.Adj u)).card : ℝ) ≤
        ∑ u ∈ D', ((D'.filter (H.Adj u)).card : ℝ) + 2 * C.card := by exact_mod_cast hsumdeg
    have h2 : (C.card : ℝ) ≤ 6 * T.card := by exact_mod_cast hC
    push_cast at h1
    linarith
  have hcostR : (sideCost H D' X true : ℝ) + 3 * σ ≤
      6 * X.card * ((D'.card : ℝ) - X.card) := by
    have : ((sideCost H D' X true + 3 * ∑ u ∈ D', (D'.filter (H.Adj u)).card : ℕ) : ℝ) ≤
        ((6 * X.card * (D'.card - X.card) : ℕ) : ℝ) := by exact_mod_cast hcost
    push_cast [hXD'] at this
    linarith
  have htR : (T.card : ℝ) ≤ θ / 1000 * (Fintype.card V : ℝ) ^ 2 := hbig.le
  have hΔlow := claim1251_delta_arith hr1 hθ.le hn0 hm1 hA hm'1 hσ havg htR
  -- rebalancing
  set k := ⌈3 * r * Fintype.card V + 48 * (θ / 1000) * Fintype.card V + 1⌉₊ with hkdef
  have hk1 : 3 * r * Fintype.card V + 48 * (θ / 1000) * Fintype.card V + 1 ≤ (k : ℝ) :=
    Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ 3 * r * Fintype.card V + 48 * (θ / 1000) * Fintype.card V + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * r * (Fintype.card V : ℝ) +
      48 * (θ / 1000) * Fintype.card V + 1 by positivity)
    linarith
  have hhalf1 : ((D.card / 2 : ℕ) : ℝ) ≤ D.card / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self D.card 2
  have hhalf2 : (D.card : ℝ) / 2 - 1 / 2 ≤ ((D.card / 2 : ℕ) : ℝ) := by
    have : D.card ≤ 2 * (D.card / 2) + 1 := by omega
    have : (D.card : ℝ) ≤ 2 * ((D.card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hXk1 : X.card ≤ D.card / 2 + k := by
    have : (X.card : ℝ) ≤ ((D.card / 2 : ℕ) : ℝ) + k := by linarith
    exact_mod_cast this
  have hXk2 : D.card / 2 ≤ X.card + k := by
    have : ((D.card / 2 : ℕ) : ℝ) ≤ X.card + k := by linarith
    exact_mod_cast this
  have hXD : X ⊆ D := (filter_subset _ _).trans hDD'
  obtain ⟨X', hX'D, hX'c, hX'cost⟩ :=
    exists_sideCost_rebalance G true hXD (D.card / 2) (Nat.div_le_self _ _) k hXk1 hXk2
  refine ⟨X', hX'D, hX'c, true, ?_⟩
  -- the cost chain
  have c1 := sideCost_le_of_subset G (D := D) (D' := D') (X := X) true
  have c2 := sideCost_le_graph G H D' X true
  have c3 := card_pairs_deleteEdges_le G C D'
  have hchain : sideCost G D X' true ≤ sideCost H D' X true + 2 * C.card +
      2 * A.card * D.card + 2 * D.card * k := by
    have c23 : sideCost G D' X true ≤ sideCost H D' X true + 2 * C.card := by
      refine c2.trans (Nat.add_le_add_left ?_ _)
      convert c3
    have := Nat.mul_le_mul_right D.card (Nat.mul_le_mul_left 2 hDA)
    omega
  have hchainR : (sideCost G D X' true : ℝ) ≤ sideCost H D' X true + 12 * T.card +
      2 * A.card * D.card + 2 * D.card * k := by
    have h1 : (sideCost G D X' true : ℝ) ≤ sideCost H D' X true + 2 * C.card +
        2 * A.card * D.card + 2 * D.card * k := by exact_mod_cast hchain
    have h2 : (C.card : ℝ) ≤ 6 * T.card := by exact_mod_cast hC
    linarith
  have hfin := claim1251_final_arith hr0 hr1 hrθ hnθ hn0.le hm1 hm2 hA hm'1 hm'2 hcostR hσ htR
    (Nat.cast_nonneg k) hk2
  linarith

end NashWilliams18
