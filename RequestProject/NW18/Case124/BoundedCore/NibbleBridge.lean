/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import RequestProject.NW18.Case124.BoundedCore.RoundSizes
public import Mathlib.Tactic.Tauto

@[expose] public section

/-! Physical output of a nibble with star monitors. All small stars are
included; this bridge uses no decomposition theorem as an external premise. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption

theorem physical_nibble_bridge {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (P : Finset (Finset V)) (a : ℝ) (ha : 0 < a)
    (hP : ∀ t ∈ P, J.IsNClique 3 t)
    (hdisj : (P : Set (Finset V)).PairwiseDisjoint triEdges)
    (hcut : 6 * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ a * Fintype.card V)
    (hmon : ∀ v, 6 * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤
        ((J.edgeFinset.filter (fun e => v ∈ e)).card : ℝ) →
      (((J.edgeFinset.filter (fun e => v ∈ e)) \ P.biUnion triEdges).card : ℝ) ≤
        a * (J.edgeFinset.filter (fun e => v ∈ e)).card) :
    ∃ Ep ⊆ J.edgeFinset,
      HasDecomp (fun _ : V => (0 : Fin 1)) ({{0, 0, 0}} : Finset (Multiset (Fin 1))) Ep ∧
      ∀ v, (((J.edgeFinset \ Ep).filter (fun e => v ∈ e)).card : ℝ) ≤ a * Fintype.card V := by
  classical
  let Ep := P.biUnion triEdges
  have hsub : Ep ⊆ J.edgeFinset := by
    intro e he
    obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ∈ t ∧ y ∈ t ∧ x ≠ y := by simpa [triEdges, and_assoc] using het
      simpa using (hP t ht).1 hxy.1 hxy.2.1 hxy.2.2
  have hdecomp : HasDecomp (fun _ : V => (0 : Fin 1))
      ({{0, 0, 0}} : Finset (Multiset (Fin 1))) Ep := by
    refine ⟨P, fun t ht => ⟨(hP t ht).2, ?_⟩, hdisj, rfl⟩
    have hm : t.val.map (fun _ : V => (0 : Fin 1)) = Multiset.replicate 3 0 := by
      rw [Multiset.eq_replicate]
      exact ⟨by simpa using (hP t ht).2, fun b _ => Subsingleton.elim _ _⟩
    rw [hm]
    simp
  refine ⟨Ep, hsub, hdecomp, fun v => ?_⟩
  have heq : (J.edgeFinset \ Ep).filter (fun e => v ∈ e) =
      (J.edgeFinset.filter (fun e => v ∈ e)) \ Ep := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [heq]
  apply residual_of_monitor ha.le (card_le_card sdiff_subset)
  · have hcard : (J.edgeFinset.filter (fun e => v ∈ e)).card = J.degree v := by
      rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]
    rw [hcard]
    exact (J.degree_lt_card_verts v).le
  · exact hcut
  · exact hmon v

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.physical_nibble_bridge
