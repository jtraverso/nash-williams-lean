/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Setup
import RequestProject.NW18.Case125.Furedi

/-!
# Many edge-disjoint triangles in a nearly complete vertex set (Proposition 15.15)

If every vertex of `D` is adjacent to all but at most `k` other vertices of `D`, then `G[D]`
contains a triangle packing `T` with `|D| (|D| − 1 − k) − |D|²/2 ≤ 12 |T|`.  A maximal packing
inside `D` leaves a triangle-free graph on `D`, which has at most `|D|²/4` edges (Mantel's
theorem, from the Füredi-type bound `tf_cost_bound`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Mantel's bound: a graph without triangles inside `D` has degree sum inside `D` at most
`|D|²/2`. -/
lemma mantel_sum_le (H : SimpleGraph V) [DecidableRel H.Adj] (D : Finset V)
    (htf : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, H.Adj x y → H.Adj y z → H.Adj x z → False) :
    2 * ∑ u ∈ D, (D.filter (H.Adj u)).card ≤ D.card ^ 2 := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp
  obtain ⟨v, hv, hmax⟩ := exists_max_image D (fun u => (D.filter (H.Adj u)).card) hD
  have h := tf_cost_bound H D v htf hv hmax
  set X := (D.filter (H.Adj v)).card with hX
  have hXD : X ≤ D.card := card_le_card (filter_subset _ _)
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hXD
  have hsub : D.card - X = c := by omega
  rw [hsub] at h
  have hsq : 4 * (X * c) ≤ (X + c) ^ 2 := by nlinarith [sq_nonneg ((X : ℤ) - c)]
  rw [hc]
  nlinarith

/-- **Proposition 15.15** (dense version): a nearly complete set `D` carries many edge-disjoint
triangles. -/
lemma dense_packing (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (k : ℕ)
    (hk : ∀ x ∈ D, (D.filter (fun y => y ≠ x ∧ ¬ G.Adj x y)).card ≤ k) :
    ∃ T : Finset (Finset V), IsTrianglePacking G T ∧ (∀ t ∈ T, t ⊆ D) ∧
      (D.card : ℝ) * ((D.card : ℝ) - 1 - k) - (D.card : ℝ) ^ 2 / 2 ≤ 12 * (T.card : ℝ) := by
  classical
  obtain ⟨T, hT, hTD, hmax⟩ := exists_maximal_packing_in G D
  refine ⟨T, hT, hTD, ?_⟩
  set C := T.biUnion triEdges with hC
  have htf := deleteEdges_triangle_free G D T hmax
  have hM := mantel_sum_le (G.deleteEdges ↑C) D htf
  have hdel := sum_deg_deleteEdges G C D
  have hCc := card_biUnion_triEdges_le G T hT.1
  have hlow : ∀ u ∈ D, D.card ≤ (D.filter (G.Adj u)).card + k + 1 := by
    intro u hu
    have hsub : D ⊆ D.filter (G.Adj u) ∪ D.filter (fun y => y ≠ u ∧ ¬ G.Adj u y) ∪ {u} := by
      intro y hy
      simp only [mem_union, mem_filter, mem_singleton]
      by_cases hyu : y = u
      · exact Or.inr hyu
      · by_cases hadj : G.Adj u y
        · exact Or.inl (Or.inl ⟨hy, hadj⟩)
        · exact Or.inl (Or.inr ⟨hy, hyu, hadj⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le (D.filter (G.Adj u) ∪ D.filter (fun y => y ≠ u ∧ ¬ G.Adj u y)) {u}
    have h3 := card_union_le (D.filter (G.Adj u)) (D.filter (fun y => y ≠ u ∧ ¬ G.Adj u y))
    have h4 := hk u hu
    rw [card_singleton] at h2
    omega
  have hsumlow : D.card * D.card ≤ ∑ u ∈ D, (D.filter (G.Adj u)).card + D.card * (k + 1) := by
    have := sum_le_sum hlow
    simp only [sum_add_distrib, sum_const, smul_eq_mul] at this
    linarith
  have hR1 : ((D.card * D.card : ℕ) : ℝ) ≤
      ((∑ u ∈ D, (D.filter (G.Adj u)).card : ℕ) : ℝ) + ((D.card * (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hsumlow
  have hR2 : ((∑ u ∈ D, (D.filter (G.Adj u)).card : ℕ) : ℝ) ≤
      ((∑ u ∈ D, (D.filter ((G.deleteEdges ↑C).Adj u)).card : ℕ) : ℝ) + 2 * (C.card : ℝ) := by
    exact_mod_cast hdel
  have hR3 : 2 * ((∑ u ∈ D, (D.filter ((G.deleteEdges ↑C).Adj u)).card : ℕ) : ℝ) ≤
      (D.card : ℝ) ^ 2 := by exact_mod_cast hM
  have hR4 : (C.card : ℝ) ≤ 6 * (T.card : ℝ) := by exact_mod_cast hCc
  push_cast at hR1 hR2 hR3
  nlinarith

end NashWilliams18
