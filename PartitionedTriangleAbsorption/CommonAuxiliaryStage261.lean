/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.GoodRemaindersStage261

/-! Choose one physical auxiliary for an entire bounded collection of good
roots. This does not replace the auxiliary at different steps of a walk. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset TriangleFreeCoreStage260

variable {V : Type*} [Fintype V]

/-- A union bound on actual missing neighborhoods constructs one vertex
adjacent to s and to every root in Z. -/
theorem common_neighbor_of_bounded_missing (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) (q t : ℝ)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hmiss : ∀ r ∈ Z, ((S.filter (fun x => ¬ G.Adj r x)).card : ℝ) ≤ t)
    (hmargin : q + Z.card * t < (S.card : ℝ)) (s : V) :
    ∃ x ∈ S, G.Adj s x ∧ ∀ r ∈ Z, G.Adj x r := by
  classical
  let U := Z.biUnion (fun r => S.filter (fun x => ¬ G.Adj r x))
  let A := S.filter (G.Adj s)
  have hU : (U.card : ℝ) ≤ Z.card * t := by
    have hcard : (U.card : ℝ) ≤ ∑ r ∈ Z, ((S.filter (fun x => ¬ G.Adj r x)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := Z) (t := fun r => S.filter (fun x => ¬ G.Adj r x)))
    have hsum := sum_le_sum (fun r hr => hmiss r hr)
    simp only [sum_const, nsmul_eq_mul] at hsum
    exact hcard.trans hsum
  have hA := restricted_degree_lower G q hdeg S s
  have hc : (A.card : ℝ) ≤ (A \ U).card + U.card := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := A) (t := U))
  have hp : 0 < (A \ U).card := by
    have hp' : (0 : ℝ) < (A \ U).card := by
      change (S.card : ℝ) ≤ A.card + q at hA
      linarith
    exact_mod_cast hp'
  obtain ⟨x, hx⟩ := card_pos.mp hp
  obtain ⟨hxA, hxU⟩ := mem_sdiff.mp hx
  obtain ⟨hxS, hsx⟩ := mem_filter.mp hxA
  refine ⟨x, hxS, hsx, ?_⟩
  intro r hr
  by_contra hxr
  have hrx : ¬ G.Adj r x := fun h => hxr h.symm
  exact hxU (mem_biUnion.mpr ⟨r, hr, mem_filter.mpr ⟨hxS, hrx⟩⟩)

/-- The original hierarchy permits seventeen good roots simultaneously.
Only the common-link lower bound is needed here, not triangle-freeness. -/
theorem common_auxiliary_for_seventeen_roots (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (_he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + e) * Fintype.card V)
    (u v : V) (Z : Finset V) (hZ : Z.card ≤ 17)
    (hmiss : ∀ r ∈ Z,
      (((univ.filter (fun x => G.Adj u x ∧ G.Adj v x)).filter
        (fun x => ¬ G.Adj r x)).card : ℝ) ≤ a * Fintype.card V / 100)
    (s : V) :
    ∃ x ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      G.Adj s x ∧ ∀ r ∈ Z, G.Adj x r := by
  classical
  let n : ℝ := Fintype.card V
  have hn' : 0 < n := by dsimp [n]; exact_mod_cast hn
  have he1 : e ≤ 1 / 1000000 := by nlinarith
  have hm : 0 < 1 / 4 - 3 * e - 17 * a / 100 := by linarith
  have hm' := mul_pos hm hn'
  have hz : (Z.card : ℝ) ≤ 17 := by exact_mod_cast hZ
  have ht : 0 ≤ a * n / 100 := div_nonneg (mul_nonneg ha.le hn'.le) (by norm_num)
  have hzt := mul_le_mul_of_nonneg_right hz ht
  have hS := common_link_size_lower G ((1 / 4 + e) * n) hdeg u v
  apply common_neighbor_of_bounded_missing G
    (univ.filter (fun x => G.Adj u x ∧ G.Adj v x)) Z
    ((1 / 4 + e) * n) (a * n / 100) hdeg hmiss
  · change n - 2 * ((1 / 4 + e) * n) ≤ _ at hS
    nlinarith

omit [Fintype V] in
/-- A walk of length at most 14 and a triangle at its endpoint use at most
17 vertices: the endpoint is already in the walk support. -/
theorem walk_triangle_support_bound [DecidableEq V] (G : SimpleGraph V) {w x : V}
    (p : G.Walk w x) (y z : V) (hlen : p.length ≤ 14) :
    (p.support.toFinset ∪ {x, y, z}).card ≤ 17 := by
  have hx : x ∈ p.support.toFinset := List.mem_toFinset.mpr p.end_mem_support
  have hsub : p.support.toFinset ∪ {x, y, z} ⊆ insert y (insert z p.support.toFinset) := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact mem_insert_of_mem (mem_insert_of_mem ha)
    · simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [hx]
  have hcard := card_le_card hsub
  have hy := card_insert_le y (insert z p.support.toFinset)
  have hz := card_insert_le z p.support.toFinset
  have hp := List.toFinset_card_le p.support
  have hlength := p.length_support
  omega

end PartitionedTriangleAbsorption.GoodRemaindersStage261
