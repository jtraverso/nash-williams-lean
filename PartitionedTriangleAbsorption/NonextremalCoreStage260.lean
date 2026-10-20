/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TriangleFreeCoreProducerStage260

/-! The large cut supplied by a triangle-free link and the exact
degree-population/cut contradiction used by NW extremality.
The cut expression is the defining expression of NashWilliams18.cutSize;
no alternative extremality or cut structure is introduced here.
The ordered-pair injection follows NW18/Sampling/Glue.lean. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.TriangleFreeCoreStage260

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count crossing edges from their unique endpoint in S. -/
theorem cross_degree_sum_le_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (∑ x ∈ S, ((univ.filter (fun y => G.Adj x y ∧ y ∉ S)).card : ℝ)) ≤
      ((G.edgeFinset.filter
        (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card : ℝ) := by
  classical
  have hsum : (∑ x, ∑ y, if G.Adj x y ∧ x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) =
      ((univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S)).card : ℝ) := by
    rw [card_filter]
    push_cast
    rw [← univ_product_univ, sum_product]
  have hpairs :
      ((univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S)).card : ℝ) ≤
      ((G.edgeFinset.filter
        (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card : ℝ) := by
    exact_mod_cast card_le_card_of_injOn (fun p : V × V => s(p.1, p.2)) (by
      intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [coe_filter, Set.mem_setOf_eq, SimpleGraph.mem_edgeFinset]
      exact ⟨hp.1, p.1, p.2, rfl, hp.2.1, hp.2.2⟩) (by
      intro p hp q hq h
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hq
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.2.1) hq.2.2)
  have hrow : ∀ x, (∑ y, if G.Adj x y ∧ x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) =
      if x ∈ S then ((univ.filter (fun y => G.Adj x y ∧ y ∉ S)).card : ℝ) else 0 := by
    intro x
    split_ifs with hx
    · rw [card_filter]; push_cast; simp [hx]
    · simp [hx]
  rw [← hsum, sum_congr rfl (fun x _ => hrow x), sum_ite_mem, univ_inter] at hpairs
  exact hpairs

/-- Every vertex of a triangle-free set larger than q sends at least n-2q
edges outside it. This gives a cut bound without a separate missing-edge
error estimate. -/
theorem triangle_free_cut_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S : Finset V) (hS : q < (S.card : ℝ))
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z) :
    (S.card : ℝ) * (Fintype.card V - 2 * q) ≤
      ((G.edgeFinset.filter
        (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card : ℝ) := by
  classical
  have hlower : ∀ x ∈ S, (Fintype.card V : ℝ) - 2 * q ≤
      (univ.filter (fun y => G.Adj x y ∧ y ∉ S)).card := by
    intro x hx
    have hc := card_filter_add_card_filter_not (s := G.neighborFinset x)
      (p := fun y => y ∈ S)
    have h1 : (G.neighborFinset x).filter (fun y => y ∈ S) = S.filter (G.Adj x) := by
      ext y
      simp [and_comm]
    have h2 : (G.neighborFinset x).filter (fun y => y ∉ S) =
        univ.filter (fun y => G.Adj x y ∧ y ∉ S) := by ext y; simp
    rw [h1, h2] at hc
    have hc' : ((S.filter (G.Adj x)).card : ℝ) +
        (univ.filter (fun y => G.Adj x y ∧ y ∉ S)).card = G.degree x := by
      exact_mod_cast hc
    linarith [hdeg x, triangle_free_internal_upper G q hdeg S hS htri hx]
  have hs := sum_le_sum hlower
  simp only [sum_const, nsmul_eq_mul] at hs
  exact hs.trans (cross_degree_sum_le_cut G S)

/-- A triangle-free common link forces a large cut in the original graph. -/
theorem triangle_free_link_cut_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hdense : 3 * q < Fintype.card V) (u v : V)
    (htri : ∀ x ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ y ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ z ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      G.Adj x y → G.Adj x z → ¬ G.Adj y z) :
    let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
    ((Fintype.card V : ℝ) - 2 * q) ^ 2 ≤
      ((G.edgeFinset.filter
        (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card : ℝ) := by
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hlo : (Fintype.card V : ℝ) - 2 * q ≤ S.card :=
    common_link_size_lower G q hdeg u v
  have hS : q < (S.card : ℝ) := by linarith
  have hnonneg : 0 ≤ (Fintype.card V : ℝ) - 2 * q := by linarith
  have hm := mul_le_mul_of_nonneg_right hlo hnonneg
  have hcut := triangle_free_cut_lower G q hdeg S hS htri
  dsimp (config := { failIfUnchanged := false }) only
  nlinarith

/-- Exact use of the NW extremality predicate, expanded in place to avoid
importing the external project's incompatible toolchain. Once the surviving
set J is large enough, non-extremality forces a physical triangle in J.
The hypotheses on J are numeric size bounds, not a triangle or connectivity
oracle. The cut required for the contradiction is constructed above. -/
theorem triangle_in_survivor_of_nonextremal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hdense : 3 * q < Fintype.card V) (u v : V)
    (htri : ∀ x ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ y ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ z ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (hnot : ¬ ((1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun e => ∃ x y, e = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)))
    (hcut : (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
      ((Fintype.card V : ℝ) - 2 * q) ^ 2)
    (J : Finset V)
    (hdis : Disjoint (univ.filter (fun x => G.Adj u x ∧ G.Adj v x)) J)
    (hJ : q < (J.card : ℝ))
    (hDS : 3 * q ≤ (3 / 4 + a) * Fintype.card V)
    (hDJ : (Fintype.card V : ℝ) - J.card + q ≤
      (3 / 4 + a) * Fintype.card V)
    (hcover : (1 - a) * Fintype.card V ≤
      ((univ.filter (fun x => G.Adj u x ∧ G.Adj v x)).card : ℝ) + J.card) :
    ∃ x ∈ J, ∃ y ∈ J, ∃ z ∈ J, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  classical
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hlo : (Fintype.card V : ℝ) - 2 * q ≤ S.card :=
    common_link_size_lower G q hdeg u v
  have hS : q < (S.card : ℝ) := by linarith
  have hDS' : (Fintype.card V : ℝ) - S.card + q ≤
      (3 / 4 + a) * Fintype.card V := by linarith
  have hphysicalcut := triangle_free_link_cut_lower G q hq hdeg hdense u v htri
  apply triangle_in_survivor_of_low_degree_obstruction G q hq hdeg S J hdis
    hS hJ htri ((3 / 4 + a) * Fintype.card V) hDS' hDJ
  by_contra hn
  have hcount : S.card + J.card ≤
      (univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card := by omega
  have hcount' : (S.card : ℝ) + J.card ≤
      (univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card := by exact_mod_cast hcount
  exact hnot ⟨hcover.trans hcount', S, hcut.trans hphysicalcut⟩

/-- Producer form: delete at most d vertices from the complement of the
triangle-free link. The numerical margins and non-extremality then construct
a triangle in the remaining J; its cardinality is not assumed separately. -/
theorem triangle_in_survivor_of_small_deletion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a q d : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hdense : 3 * q + d < Fintype.card V) (u v : V)
    (htri : ∀ x ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ y ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ z ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (hnot : ¬ ((1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun e => ∃ x y, e = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)))
    (hcut : (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
      ((Fintype.card V : ℝ) - 2 * q) ^ 2)
    (hlow : 3 * q + d ≤ (3 / 4 + a) * Fintype.card V)
    (hcover : d ≤ a * Fintype.card V)
    (J : Finset V)
    (hdis : Disjoint (univ.filter (fun x => G.Adj u x ∧ G.Adj v x)) J)
    (hremoved : ((univ \ ((univ.filter (fun x => G.Adj u x ∧ G.Adj v x)) ∪ J)).card : ℝ) ≤ d) :
    ∃ x ∈ J, ∃ y ∈ J, ∃ z ∈ J, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  classical
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hdense' : 3 * q < Fintype.card V := by linarith
  obtain ⟨_, hsize, _⟩ := triangle_free_link_geometry G q hq hdeg hdense' u v htri
  have hpartition := card_sdiff_add_card_eq_card (s := S ∪ J)
    (t := (univ : Finset V)) (subset_univ _)
  rw [card_union_of_disjoint hdis] at hpartition
  have hpartition' : ((univ \ (S ∪ J)).card : ℝ) + (S.card + J.card) =
      Fintype.card V := by exact_mod_cast hpartition
  apply triangle_in_survivor_of_nonextremal G a q hq hdeg hdense' u v htri
    hnot hcut J hdis
  · change (S.card : ℝ) ≤ 2 * q at hsize
    linarith
  · linarith
  · change (S.card : ℝ) ≤ 2 * q at hsize
    linarith
  · change (1 - a) * Fintype.card V ≤ (S.card : ℝ) + J.card
    nlinarith

end PartitionedTriangleAbsorption.TriangleFreeCoreStage260
