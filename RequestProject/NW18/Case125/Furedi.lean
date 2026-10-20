/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.SideCost

@[expose] public section

/-!
# Stability of triangle-free graphs (the Füredi step behind Claim 12.5.1)

* `sideCost_eq_sum`: the edit cost `sideCost` as a sum of per-vertex mismatch counts;
* `tf_cost_bound`: if `H` has no triangle inside `D` and `v ∈ D` has maximum degree inside
  `D`, then with `X = N_H(v) ∩ D`
  `sideCost H D X true + 3 ∑_{u ∈ D} d_D(u) ≤ 6 |X| (|D| − |X|)`.
  (Every edge of `H[D]` has an end in `Y = D ∖ X`, so `∑_{y ∈ Y} d(y) ≤ |Y| Δ` controls the
  number of edges inside `Y` and the missing edges between `X` and `Y`.)
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
open Classical in
/-- `sideCost` as a sum of per-vertex mismatch counts. -/
lemma sideCost_eq_sum (G : SimpleGraph V) (D X : Finset V) (b : Bool) :
    sideCost G D X b =
      ∑ x ∈ D, (D.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget X b x y))).card := by
  classical
  unfold sideCost
  rw [card_filter, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [card_filter]

omit [Fintype V] [DecidableEq V] in
/-- Double counting of the edges between two sets. -/
lemma sum_card_filter_adj_comm (H : SimpleGraph V) [DecidableRel H.Adj] (X Y : Finset V) :
    ∑ u ∈ Y, (X.filter (H.Adj u)).card = ∑ x ∈ X, (Y.filter (H.Adj x)).card := by
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun u _ => ?_
  by_cases h : H.Adj u x
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

omit [Fintype V] in
open Classical in
/-- **Füredi-type stability step.** -/
lemma tf_cost_bound (H : SimpleGraph V) [DecidableRel H.Adj] (D : Finset V) (v : V)
    (htf : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, H.Adj x y → H.Adj y z → H.Adj x z → False)
    (hv : v ∈ D)
    (hmax : ∀ u ∈ D, (D.filter (H.Adj u)).card ≤ (D.filter (H.Adj v)).card) :
    sideCost H D (D.filter (H.Adj v)) true + 3 * ∑ u ∈ D, (D.filter (H.Adj u)).card ≤
      6 * (D.filter (H.Adj v)).card * (D.card - (D.filter (H.Adj v)).card) := by
  set X := D.filter (H.Adj v) with hXdef
  set Y := D \ X with hYdef
  have hXD : X ⊆ D := filter_subset _ _
  have hYc : Y.card = D.card - X.card := card_sdiff_of_subset hXD
  set d : V → ℕ := fun u => (D.filter (H.Adj u)).card with hd
  set c : V → ℕ := fun u => (D.filter (fun y => u ≠ y ∧
    ¬ (H.Adj u y ↔ sideTarget X true u y))).card with hc
  -- no edges inside `X`
  have hXX : ∀ x ∈ X, ∀ y ∈ X, ¬ H.Adj x y := by
    intro x hx y hy hxy
    simp only [hXdef, mem_filter] at hx hy
    exact htf v hv x hx.1 y hy.1 hx.2 hxy hy.2
  -- vertices of `X`
  have hcX : ∀ u ∈ X, c u + d u ≤ Y.card := by
    intro u hu
    have hdisj : Disjoint (D.filter (fun y => u ≠ y ∧ ¬ (H.Adj u y ↔ sideTarget X true u y)))
        (D.filter (H.Adj u)) := by
      refine disjoint_filter.mpr fun y _ h1 h2 => h1.2 ?_
      have hyX : y ∉ X := fun hy => hXX u hu y hy h2
      simp only [sideTarget, if_true, hu, true_iff]
      exact ⟨fun _ => hyX, fun _ => h2⟩
    rw [hc, hd]; dsimp (config := { failIfUnchanged := false }) only
    rw [← card_union_of_disjoint hdisj]
    refine card_le_card fun y hy => ?_
    rw [mem_union] at hy
    rcases hy with hy | hy
    · simp only [mem_filter] at hy
      refine mem_sdiff.mpr ⟨hy.1, fun hyX => hy.2.2 ?_⟩
      simp only [sideTarget, if_true, hu, hyX, not_true_eq_false, iff_false]
      exact hXX u hu y hyX
    · simp only [mem_filter] at hy
      exact mem_sdiff.mpr ⟨hy.1, fun hyX => hXX u hu y hyX hy.2⟩
  -- vertices of `Y`
  have hcY : ∀ u ∈ Y, c u + 2 * (X.filter (H.Adj u)).card ≤ d u + X.card := by
    intro u hu
    have huX : u ∉ X := (mem_sdiff.mp hu).2
    have h1 : c u ≤ (Y.filter (H.Adj u)).card + (X.filter (fun y => ¬ H.Adj u y)).card := by
      rw [hc]; dsimp (config := { failIfUnchanged := false }) only
      refine (card_le_card ?_).trans (card_union_le _ _)
      intro y hy
      simp only [mem_filter] at hy
      simp only [mem_union, mem_filter]
      have ht : sideTarget X true u y ↔ y ∈ X := by
        simp only [sideTarget, if_true, huX, false_iff, not_not]
      rw [ht] at hy
      by_cases hyX : y ∈ X
      · exact Or.inr ⟨hyX, fun ha => hy.2.2 ⟨fun _ => hyX, fun _ => ha⟩⟩
      · exact Or.inl ⟨mem_sdiff.mpr ⟨hy.1, hyX⟩, by tauto⟩
    have h2 : d u = (Y.filter (H.Adj u)).card + (X.filter (H.Adj u)).card := by
      rw [hd]; dsimp (config := { failIfUnchanged := false }) only
      rw [← card_union_of_disjoint (disjoint_filter_filter sdiff_disjoint)]
      congr 1; ext y; simp only [mem_filter, mem_union, mem_sdiff]
      by_cases hyX : y ∈ X
      · simp [hyX, hXD hyX]
      · simp [hyX]
    have h3 := card_filter_add_card_filter_not (s := X) (H.Adj u)
    omega
  -- neighbours of vertices of `X` lie in `Y`
  have hXY : ∀ x ∈ X, (Y.filter (H.Adj x)).card = d x := by
    intro x hx
    rw [hd]; dsimp (config := { failIfUnchanged := false }) only
    congr 1; ext y; simp only [mem_filter, hYdef, mem_sdiff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun hy => hXX x hx y hy h2⟩, h2⟩
  have hdc := sum_card_filter_adj_comm H X Y
  rw [sum_congr rfl hXY] at hdc
  have hsplit : ∀ f : V → ℕ, ∑ u ∈ D, f u = ∑ u ∈ Y, f u + ∑ u ∈ X, f u :=
    fun f => (sum_sdiff hXD).symm
  have hdmax : ∀ u ∈ Y, d u ≤ X.card := fun u hu => hmax u (mem_sdiff.mp hu).1
  have hS : sideCost H D X true = ∑ u ∈ D, c u := by
    rw [sideCost_eq_sum]
    exact sum_congr rfl fun u _ => by simp only [hc]; congr 1; ext y; simp only [mem_filter]
  rw [hS]
  rw [hsplit c, hsplit d, ← hYc]
  have s1 : ∑ u ∈ X, c u + ∑ u ∈ X, d u ≤ X.card * Y.card := by
    rw [← sum_add_distrib]
    calc ∑ u ∈ X, (c u + d u) ≤ ∑ _u ∈ X, Y.card := sum_le_sum hcX
      _ = X.card * Y.card := by rw [sum_const, smul_eq_mul]
  have s2 : ∑ u ∈ Y, c u + 2 * ∑ u ∈ Y, (X.filter (H.Adj u)).card ≤
      ∑ u ∈ Y, d u + Y.card * X.card := by
    rw [mul_sum, ← sum_add_distrib]
    calc ∑ u ∈ Y, (c u + 2 * (X.filter (H.Adj u)).card) ≤ ∑ u ∈ Y, (d u + X.card) :=
          sum_le_sum hcY
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have s3 : ∑ u ∈ Y, d u ≤ Y.card * X.card := by
    calc ∑ u ∈ Y, d u ≤ ∑ _u ∈ Y, X.card := sum_le_sum hdmax
      _ = Y.card * X.card := by rw [sum_const, smul_eq_mul]
  rw [hdc] at s2
  have e : Y.card * X.card = X.card * Y.card := mul_comm _ _
  nlinarith

omit [Fintype V] in
open Classical in
/-- A triangle packing inside `D` that is maximal: every triangle of `G` inside `D` shares an
edge with one of its triangles. -/
lemma exists_maximal_packing_in (G : SimpleGraph V) (D : Finset V) :
    ∃ T : Finset (Finset V), IsTrianglePacking G T ∧ (∀ s ∈ T, s ⊆ D) ∧
      ∀ t ⊆ D, G.IsNClique 3 t → ∃ s ∈ T, ¬ Disjoint (triEdges s) (triEdges t) := by
  set P := D.powerset.powerset.filter (fun T => IsTrianglePacking G T) with hP
  have h0 : (∅ : Finset (Finset V)) ∈ P := by
    change (∅ : Finset (Finset V)) ∈
      D.powerset.powerset.filter (fun T => IsTrianglePacking G T)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
    exact ⟨fun s hs => absurd hs (notMem_empty s), by simp⟩
  obtain ⟨T, hT, hmax⟩ := exists_max_image P card ⟨∅, h0⟩
  simp only [hP, mem_filter, mem_powerset] at hT
  refine ⟨T, hT.2, fun s hs => mem_powerset.mp (hT.1 hs), fun t htD ht => ?_⟩
  by_contra hcon
  push_neg at hcon
  have htT : t ∉ T := by
    intro htT
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by rw [ht.card_eq]; omega)
    have hm : s(x, y) ∈ triEdges t := mk_mem_triEdges.mpr ⟨hx, hy, hxy⟩
    exact disjoint_left.mp (hcon t htT) hm hm
  have hins : insert t T ∈ P := by
    simp only [hP, mem_filter, mem_powerset]
    refine ⟨insert_subset (mem_powerset.mpr htD) hT.1, fun s hs => ?_, ?_⟩
    · rcases mem_insert.mp hs with h | h
      · exact h ▸ ht
      · exact hT.2.1 s h
    · rw [coe_insert]
      exact hT.2.2.insert fun j hj _ => (hcon j hj).symm
  have := hmax _ hins
  rw [card_insert_of_notMem htT] at this
  omega

omit [Fintype V] in
/-- After deleting the edges of a maximal packing inside `D`, no triangle is left inside `D`. -/
lemma deleteEdges_triangle_free (G : SimpleGraph V) (D : Finset V) (T : Finset (Finset V))
    (hT : ∀ t ⊆ D, G.IsNClique 3 t → ∃ s ∈ T, ¬ Disjoint (triEdges s) (triEdges t)) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, (G.deleteEdges ↑(T.biUnion triEdges)).Adj x y →
      (G.deleteEdges ↑(T.biUnion triEdges)).Adj y z →
      (G.deleteEdges ↑(T.biUnion triEdges)).Adj x z → False := by
  intro x hx y hy z hz hxy hyz hxz
  rw [SimpleGraph.deleteEdges_adj] at hxy hyz hxz
  have hcl : G.IsNClique 3 {x, y, z} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy.1, hxz.1, hyz.1⟩
  have hsub : ({x, y, z} : Finset V) ⊆ D := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  obtain ⟨s, hs, hst⟩ := hT _ hsub hcl
  obtain ⟨e, he1, he2⟩ := not_disjoint_iff.mp hst
  have heC : e ∈ T.biUnion triEdges := mem_biUnion.mpr ⟨s, hs, he1⟩
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_triEdges.mp he2
    simp only [mem_insert, mem_singleton] at ha hb
    have hyx : s(y, x) = s(x, y) := Sym2.eq_swap
    have hzy : s(z, y) = s(y, z) := Sym2.eq_swap
    have hzx : s(z, x) = s(x, z) := Sym2.eq_swap
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact hab rfl
      | exact hxy.2 (by simpa using heC)
      | exact hyz.2 (by simpa using heC)
      | exact hxz.2 (by simpa using heC)
      | exact hxy.2 (by rw [← hyx]; simpa using heC)
      | exact hyz.2 (by rw [← hzy]; simpa using heC)
      | exact hxz.2 (by rw [← hzx]; simpa using heC)

omit [Fintype V] in
/-- A packing of `T` triangles has at most `6 |T|` edges (crudely, `|sym2| = 6`). -/
lemma card_biUnion_triEdges_le (G : SimpleGraph V) (T : Finset (Finset V))
    (hT : ∀ s ∈ T, G.IsNClique 3 s) : (T.biUnion triEdges).card ≤ 6 * T.card := by
  refine card_biUnion_le.trans ?_
  calc ∑ s ∈ T, (triEdges s).card ≤ ∑ _s ∈ T, 6 := sum_le_sum fun s hs => by
        refine (card_filter_le _ _).trans ?_
        rw [card_sym2, (hT s hs).card_eq]; decide
    _ = 6 * T.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Deleting the edge set `C` changes at most `2 |C|` ordered pairs. -/
lemma card_pairs_deleteEdges_le (G : SimpleGraph V) (C : Finset (Sym2 V)) (D : Finset V)
    [DecidablePred fun q : V × V => q.1 ≠ q.2 ∧ ¬ (G.Adj q.1 q.2 ↔ (G.deleteEdges ↑C).Adj q.1 q.2)] :
    ((D ×ˢ D).filter (fun q => q.1 ≠ q.2 ∧
      ¬ (G.Adj q.1 q.2 ↔ (G.deleteEdges ↑C).Adj q.1 q.2))).card ≤ 2 * C.card := by
  refine le_trans (card_le_card ?_) (card_pairs_in_le C)
  intro q hq
  simp only [mem_filter, mem_product, mem_univ, and_self, true_and] at hq ⊢
  by_contra hC
  apply hq.2.2
  rw [SimpleGraph.deleteEdges_adj]
  exact ⟨fun h => ⟨h, by simpa using hC⟩, fun h => h.1⟩

/-- Deleting the edge set `C` lowers the degree sum inside `D` by at most `2 |C|`. -/
lemma sum_deg_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset (Sym2 V))
    (D : Finset V) [DecidableRel (G.deleteEdges ↑C).Adj] :
    ∑ u ∈ D, (D.filter (G.Adj u)).card ≤
      ∑ u ∈ D, (D.filter ((G.deleteEdges ↑C).Adj u)).card + 2 * C.card := by
  have hpair : ∑ u ∈ D, (D.filter (fun w => s(u, w) ∈ C)).card ≤ 2 * C.card := by
    have e : ∑ u ∈ D, (D.filter (fun w => s(u, w) ∈ C)).card =
        ((D ×ˢ D).filter (fun q : V × V => s(q.1, q.2) ∈ C)).card := by
      rw [card_filter, sum_product]
      exact sum_congr rfl fun u _ => by rw [card_filter]
    rw [e]
    refine le_trans (card_le_card ?_) (card_pairs_in_le C)
    intro q hq
    simp only [mem_filter, mem_product, mem_univ, true_and] at hq ⊢
    exact hq.2
  calc ∑ u ∈ D, (D.filter (G.Adj u)).card
      ≤ ∑ u ∈ D, ((D.filter ((G.deleteEdges ↑C).Adj u)).card +
          (D.filter (fun w => s(u, w) ∈ C)).card) := by
        refine sum_le_sum fun u _ => (card_le_card ?_).trans (card_union_le _ _)
        intro w hw
        simp only [mem_filter] at hw
        simp only [mem_union, mem_filter, SimpleGraph.deleteEdges_adj, mem_coe]
        by_cases hC : s(u, w) ∈ C
        · exact Or.inr ⟨hw.1, hC⟩
        · exact Or.inl ⟨hw.1, hw.2, hC⟩
    _ = _ := sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left hpair _

end NashWilliams18
