/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CommonAuxiliaryStage261

/-! Construct a physical edge in the common link adjacent to every member
of a bounded set of good roots. The missing-degree inputs are discharged
from the same exceptional-set definition as the remainder producer. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Good roots share a physical link edge; its first endpoint can also be
required to be adjacent to a prescribed vertex s. All roots use the same
two auxiliary vertices, and no unspecified common-neighbor oracle is used. -/
theorem good_roots_have_common_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + e) * Fintype.card V)
    (u v s : V) (Z : Finset V) (hZ : Z.card ≤ 17) :
    let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
    let B := univ.filter (fun x => x ∉ S ∧ a * Fintype.card V / 100 <
      ((S.filter (fun r => ¬ G.Adj x r)).card : ℝ))
    Z ⊆ univ \ (S ∪ B) →
      ∃ x ∈ S, ∃ y ∈ S, G.Adj s x ∧ G.Adj x y ∧
        ∀ r ∈ Z, G.Adj x r ∧ G.Adj y r := by
  classical
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  let B := univ.filter (fun x => x ∉ S ∧ a * Fintype.card V / 100 <
    ((S.filter (fun r => ¬ G.Adj x r)).card : ℝ))
  change Z ⊆ univ \ (S ∪ B) → _
  intro hgood
  have hmiss : ∀ r ∈ Z, ((S.filter (fun x => ¬ G.Adj r x)).card : ℝ) ≤
      a * Fintype.card V / 100 := by
    intro r hr
    have hrSB : r ∉ S ∪ B := (mem_sdiff.mp (hgood hr)).2
    have hrS : r ∉ S := fun h => hrSB (mem_union_left B h)
    by_contra h
    have hrB : r ∈ B := mem_filter.mpr ⟨mem_univ r, hrS, lt_of_not_ge h⟩
    exact hrSB (mem_union_right S hrB)
  obtain ⟨x, hxS, hsx, hx⟩ :=
    common_auxiliary_for_seventeen_roots G a e ha ha1 he hn hsmall hdeg u v Z hZ hmiss s
  obtain ⟨y, hyS, hxy, hy⟩ :=
    common_auxiliary_for_seventeen_roots G a e ha ha1 he hn hsmall hdeg u v Z hZ hmiss x
  exact ⟨x, hxS, y, hyS, hsx, hxy, fun r hr => ⟨hx r hr, hy r hr⟩⟩

end PartitionedTriangleAbsorption.GoodRemaindersStage261
