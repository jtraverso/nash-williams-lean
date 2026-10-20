/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Transformer
public import PartitionedTriangleAbsorption.ReturnedBridge

/-! # Physical compatibility of successive hinges

Two valid transformers with disjoint hinge edge sets cannot always be composed:
cross-overlap with a residual can leave 17 edges, which cannot be partitioned
into triangles. Choosing a fresh auxiliary vertex repairs this explicit case.
These are finite controls, not a counterexample to the absorption theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- Every exact typed triangle decomposition covers a multiple of three edges. -/
theorem HasDecomp.card_eq_three_mul {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 V)} (h : HasDecomp p F E) : ∃ m : ℕ, E.card = 3 * m := by
  obtain ⟨D, htyped, hdis, hunion⟩ := h
  have hcard : ∀ s ∈ D, (triEdges s).card = 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (htyped s hs).1
    simp [triEdges_three hab hac hbc, hab, hac, hbc]
  refine ⟨D.card, ?_⟩
  rw [← hunion, Finset.card_biUnion hdis]
  calc
    ∑ s ∈ D, (triEdges s).card = ∑ _s ∈ D, 3 := Finset.sum_congr rfl hcard
    _ = 3 * D.card := by simp [Nat.mul_comm]

namespace Compatibility

abbrev Vertex := Fin 9
abbrev Edge := Sym2 Vertex

def p : Vertex → Fin 1 := fun _ => 0
def family : Finset (Multiset (Fin 1)) := {{0, 0, 0}}
def tri (a b c : Vertex) : Finset Vertex := {a, b, c}

def L : Finset Edge := {s(0, 2), s(1, 2)}
def M : Finset Edge := {s(0, 3), s(1, 3)}
def R : Finset Edge := {s(0, 7), s(1, 7)}

def firstHinge : Finset Edge :=
  {s(0, 5), s(4, 1), s(4, 5), s(4, 2), s(4, 3), s(5, 2), s(5, 3)}

/-- Reusing vertex 2 as an auxiliary vertex introduces the edge `12` from `L`. -/
def secondBad : Finset Edge :=
  {s(0, 6), s(2, 1), s(2, 6), s(2, 3), s(2, 7), s(6, 3), s(6, 7)}

/-- Fresh auxiliary vertex 8 avoids the cross-overlap. -/
def secondGood : Finset Edge :=
  {s(0, 6), s(8, 1), s(8, 6), s(8, 3), s(8, 7), s(6, 3), s(6, 7)}

set_option maxRecDepth 4096 in
theorem first_transformer : IsTransformer (p := p) (F := family) firstHinge L M := by
  refine ⟨by decide, ⟨{tri 0 5 2, tri 4 1 2, tri 4 5 3}, ?_⟩,
    ⟨{tri 0 5 3, tri 4 1 3, tri 4 5 2}, ?_⟩⟩ <;>
    simp only [IsDecomp, IsTypedTri, Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe] <;>
    decide

set_option maxRecDepth 4096 in
theorem second_bad_transformer : IsTransformer (p := p) (F := family) secondBad M R := by
  refine ⟨by decide, ⟨{tri 0 6 3, tri 2 1 3, tri 2 6 7}, ?_⟩,
    ⟨{tri 0 6 7, tri 2 1 7, tri 2 6 3}, ?_⟩⟩ <;>
    simp only [IsDecomp, IsTypedTri, Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe] <;>
    decide

theorem bad_cross_overlap :
    Disjoint firstHinge secondBad ∧ Disjoint firstHinge R ∧
    Disjoint M (L ∪ R) ∧ L ∩ secondBad = {s(1, 2)} := by decide

theorem bad_union_card : ((firstHinge ∪ secondBad ∪ M) ∪ L).card = 17 := by decide

theorem bad_union_not_decomposable :
    ¬ HasDecomp p family ((firstHinge ∪ secondBad ∪ M) ∪ L) := by
  intro h
  obtain ⟨m, hm⟩ := h.card_eq_three_mul
  rw [bad_union_card] at hm
  omega

set_option maxRecDepth 4096 in
theorem second_good_transformer : IsTransformer (p := p) (F := family) secondGood M R := by
  refine ⟨by decide, ⟨{tri 0 6 3, tri 8 1 3, tri 8 6 7}, ?_⟩,
    ⟨{tri 0 6 7, tri 8 1 7, tri 8 6 3}, ?_⟩⟩ <;>
    simp only [IsDecomp, IsTypedTri, Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe] <;>
    decide

theorem good_composition :
    IsTransformer (p := p) (F := family) (firstHinge ∪ secondGood ∪ M) L R :=
  first_transformer.compose second_good_transformer (by decide) (by decide)
    (by decide) (by decide)

theorem good_union_card : ((firstHinge ∪ secondGood ∪ M) ∪ L).card = 18 := by decide

end Compatibility
end PartitionedTriangleAbsorption
