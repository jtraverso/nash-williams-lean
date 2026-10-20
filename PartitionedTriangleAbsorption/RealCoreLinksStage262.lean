/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PathSpokesStage261

/-! Real-valued degree deficits avoid an unnecessary rounding loss when
connecting link edges and reattaching exceptional edges. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoreAssemblyStage262

open Finset TriangleFreeCoreStage260 OppositeEdgeTransportStage259

variable {V : Type*} [Fintype V]

theorem large_set_has_edge_real (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (J : Finset V) (hJ : q < (J.card : ℝ)) :
    ∃ x ∈ J, ∃ y ∈ J, G.Adj x y := by
  have hpos : 0 < J.card := by exact_mod_cast (lt_of_le_of_lt hq hJ)
  obtain ⟨x, hx⟩ := card_pos.mp hpos
  have hlo := restricted_degree_lower G q hdeg J x
  have hp : 0 < (J.filter (G.Adj x)).card := by
    have : (0 : ℝ) < (J.filter (G.Adj x)).card := by linarith
    exact_mod_cast this
  obtain ⟨y, hy⟩ := card_pos.mp hp
  exact ⟨x, hx, y, (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩

/-- A remainder with few missing neighbors at each of two roots contains
an edge in their common link, provided its residual order exceeds q. -/
theorem common_edge_in_remainder (G : SimpleGraph V) [DecidableRel G.Adj]
    (q d : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (R : Finset V) (u v : V)
    (hu : ((R.filter (fun x => ¬ G.Adj u x)).card : ℝ) ≤ d)
    (hv : ((R.filter (fun x => ¬ G.Adj v x)).card : ℝ) ≤ d)
    (hmargin : q + 2 * d < (R.card : ℝ)) :
    ∃ x ∈ R, ∃ y ∈ R, G.Adj x y ∧
      G.Adj u x ∧ G.Adj u y ∧ G.Adj v x ∧ G.Adj v y := by
  classical
  let U := R.filter (fun x => ¬ G.Adj u x) ∪ R.filter (fun x => ¬ G.Adj v x)
  let J := R \ U
  have hU : (U.card : ℝ) ≤ 2 * d := by
    have h := card_union_le (R.filter (fun x => ¬ G.Adj u x))
      (R.filter (fun x => ¬ G.Adj v x))
    have h' : (U.card : ℝ) ≤ (R.filter (fun x => ¬ G.Adj u x)).card +
        (R.filter (fun x => ¬ G.Adj v x)).card := by exact_mod_cast h
    linarith
  have hc : (R.card : ℝ) ≤ J.card + U.card := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := R) (t := U))
  have hJ : q < (J.card : ℝ) := by linarith
  obtain ⟨x, hx, y, hy, hxy⟩ := large_set_has_edge_real G q hq hdeg J hJ
  have hmem (z : V) (hz : z ∈ J) : z ∈ R ∧ G.Adj u z ∧ G.Adj v z := by
    obtain ⟨hzR, hzU⟩ := mem_sdiff.mp hz
    refine ⟨hzR, ?_, ?_⟩
    · by_contra h
      exact hzU (mem_union_left _ (mem_filter.mpr ⟨hzR, h⟩))
    · by_contra h
      exact hzU (mem_union_right _ (mem_filter.mpr ⟨hzR, h⟩))
  obtain ⟨hxR, hux, hvx⟩ := hmem x hx
  obtain ⟨hyR, huy, hvy⟩ := hmem y hy
  exact ⟨x, hxR, y, hyR, hxy, hux, huy, hvx, hvy⟩

/-- Common-link edge avoiding a small vertex set, without rounding q. -/
theorem common_edge_avoiding_real (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (B : Finset V) (hB : 3 * q + B.card < Fintype.card V) (u v : V) :
    ∃ x y, x ∉ B ∧ y ∉ B ∧ G.Adj x y ∧
      G.Adj u x ∧ G.Adj u y ∧ G.Adj v x ∧ G.Adj v y := by
  classical
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hlo := common_link_size_lower G q hdeg u v
  have hc : (S.card : ℝ) ≤ (S \ B).card + B.card := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := S) (t := B))
  have hJ : q < ((S \ B).card : ℝ) := by
    change (Fintype.card V : ℝ) - 2 * q ≤ S.card at hlo
    linarith
  obtain ⟨x, hx, y, hy, hxy⟩ := large_set_has_edge_real G q hq hdeg (S \ B) hJ
  obtain ⟨hxS, hxB⟩ := mem_sdiff.mp hx
  obtain ⟨hyS, hyB⟩ := mem_sdiff.mp hy
  exact ⟨x, y, hxB, hyB, hxy, (mem_filter.mp hxS).2.1,
    (mem_filter.mp hyS).2.1, (mem_filter.mp hxS).2.2, (mem_filter.mp hyS).2.2⟩

end PartitionedTriangleAbsorption.CoreAssemblyStage262
