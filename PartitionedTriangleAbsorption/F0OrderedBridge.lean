/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.Geometry
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Ordered-pair interface used by NW18.Case125.Defs, without importing its
unrelated 4.28 project. This is not a redefinition of Theorem146Statement. -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def orderedSideTarget (X : Finset V) (b : Bool) (x y : V) : Prop :=
  if b then (x ∈ X ↔ y ∉ X) else (x ∈ X ↔ y ∈ X)

open Classical in
noncomputable def orderedSideCost (G : SimpleGraph V) (D X : Finset V) (b : Bool) : ℕ :=
  ((D ×ˢ D).filter (fun q => q.1 ≠ q.2 ∧
    ¬ (G.Adj q.1 q.2 ↔ orderedSideTarget X b q.1 q.2))).card

set_option maxHeartbeats 1000000 in
-- The two symmetric-difference cases expand several nested Boolean conditions.
theorem orderedSideCost_eq_twice_editDistance
    (G : SimpleGraph V) [DecidableRel G.Adj] (D X : Finset V)
    (hXD : X ⊆ D) (b : Bool) :
    orderedSideCost G D X b = 2 * editDistance (inducedEdges G D)
      (if b then bipartiteModel D X else cliqueModel D X) := by
  classical
  let E := inducedEdges G D
  let M := if b then bipartiteModel D X else cliqueModel D X
  let S := (E \ M) ∪ (M \ E)
  let H := SimpleGraph.fromEdgeSet (S : Set (Sym2 V))
  let : Fintype H.edgeSet := H.fintypeEdgeSet
  have hmem (x y : V) : s(x,y) ∈ S ↔
      x ∈ D ∧ y ∈ D ∧ x ≠ y ∧ ¬ (G.Adj x y ↔ orderedSideTarget X b x y) := by
    have hx := @hXD x
    have hy := @hXD y
    cases b <;>
      simp only [S, E, M, inducedEdges, bipartiteModel, cliqueModel,
        Bool.false_eq_true, ite_false, ite_true, orderedSideTarget,
        mem_union, mem_sdiff, mem_inter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, triEdges, mem_filter, mk_mem_sym2_iff,
        Sym2.mk_isDiag_iff] <;> tauto
  have hHE : H.edgeFinset = S := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [H, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.fromEdgeSet_adj, mem_coe, hmem]
      tauto
  have hfilter : (univ.filter (fun q : V × V => H.Adj q.1 q.2)) =
      (D ×ˢ D).filter (fun q => q.1 ≠ q.2 ∧
        ¬ (G.Adj q.1 q.2 ↔ orderedSideTarget X b q.1 q.2)) := by
    ext q
    simp only [mem_filter, mem_univ, true_and, mem_product, H,
      SimpleGraph.fromEdgeSet_adj, mem_coe, hmem]
    tauto
  have hcard : S.card = editDistance E M := by
    dsimp [S, editDistance]
    exact card_union_of_disjoint (disjoint_sdiff_sdiff)
  have hh : 2 * H.edgeFinset.card =
      (univ.filter (fun q : V × V => H.Adj q.1 q.2)).card :=
    H.two_mul_card_edgeFinset
  rw [hHE, hfilter, hcard] at hh
  convert hh.symm using 1
  unfold orderedSideCost
  congr 1
  ext q
  simp only [mem_filter]

theorem nonextreme_iff_not_orderedClose (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (α : ℝ) :
    Nonextreme G D α ↔ ¬ ∃ X ⊆ D, X.card = D.card / 2 ∧
      ∃ b : Bool, (orderedSideCost G D X b : ℝ) ≤ 2 * α * (D.card : ℝ)^2 := by
  constructor
  · intro h ⟨X, hX, hbal, b, hb⟩
    rw [orderedSideCost_eq_twice_editDistance G D X hX b] at hb
    push_cast at hb
    obtain ⟨hbip, hcl⟩ := h X hX hbal
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hb <;> linarith
  · intro h X hX hbal
    have hb (b : Bool) : 2 * α * (D.card : ℝ)^2 < (orderedSideCost G D X b : ℝ) := by
      exact lt_of_not_ge (fun hh => h ⟨X, hX, hbal, b, hh⟩)
    have ht := hb true
    have hf := hb false
    rw [orderedSideCost_eq_twice_editDistance G D X hX true] at ht
    rw [orderedSideCost_eq_twice_editDistance G D X hX false] at hf
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, ite_true, Bool.false_eq_true, ite_false] at ht hf
    constructor <;> linarith

#print axioms orderedSideCost_eq_twice_editDistance
#print axioms nonextreme_iff_not_orderedClose
end PartitionedTriangleAbsorption.BlowupB.F0Direct
