/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Template
public import PartitionedTriangleAbsorption.TypedTransformerLabels

/-! # Typed two-edge moves with two exact positive modes

The six template vertices are x, x', y1, y2, w1, w2, in that order.
This supplies the local transformer, not a move sequence for every residue.
The host supply and freshness of successive moves remain explicit obligations.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairMoveStage85

open Finset PhysicalHingeSupply TypedTransformer

def source : Finset (Sym2 (Fin 6)) := {s(0, 2), s(0, 3)}

def target : Finset (Sym2 (Fin 6)) := {s(1, 2), s(1, 3)}

def gadget : Finset (Sym2 (Fin 6)) :=
  {s(0, 4), s(1, 4), s(2, 4), s(0, 5), s(1, 5), s(3, 5), s(4, 5)}

def firstMode : Finset (Finset (Fin 6)) := {{0, 2, 4}, {0, 3, 5}, {1, 4, 5}}

def secondMode : Finset (Finset (Fin 6)) := {{1, 2, 4}, {1, 3, 5}, {0, 4, 5}}

theorem gadget_card : gadget.card = 7 := by decide

theorem gadget_disjoint : Disjoint gadget (source ∪ target) := by
  unfold gadget source target
  decide

theorem modes_cover :
    firstMode.biUnion triEdges = gadget ∪ source ∧
      secondMode.biUnion triEdges = gadget ∪ target := by
  unfold firstMode secondMode gadget source target triEdges
  decide

theorem modes_disjoint :
    (firstMode : Set (Finset (Fin 6))).PairwiseDisjoint triEdges ∧
      (secondMode : Set (Finset (Fin 6))).PairwiseDisjoint triEdges := by
  constructor
  · intro a ha b hb hab
    simp only [firstMode, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)
  · intro a ha b hb hab
    simp only [secondMode, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

variable {t : ℕ} {F : Finset (Multiset (Fin t))}

/-- The supplied move condition is the existing three-step link interface. -/
theorem move_types (hF : ThreeStepLinks F) (i j₁ j₂ : Fin t)
    (h₁ : ∃ k, Link F i j₁ k) (h₂ : ∃ k, Link F i j₂ k) :
    ∃ k₁ k₂, Link F i j₁ k₁ ∧ Link F i j₂ k₂ ∧ Link F i k₁ k₂ := by
  obtain ⟨k₁, k₂, ha, hb, hc⟩ := hF i j₁ j₂ h₁ h₂
  exact ⟨k₁, k₂, ha, (link_swap F i k₂ j₂).mp hc, hb⟩

/-- Both sides are decomposed by three allowed triangles, without signed weights. -/
theorem template_transformer (p : Fin 6 → Fin t) (hlabel : p 1 = p 0)
    (h₁ : Link F (p 0) (p 2) (p 4))
    (h₂ : Link F (p 0) (p 3) (p 5))
    (h₃ : Link F (p 0) (p 4) (p 5)) :
    IsTransformer (p := p) (F := F) gadget source target := by
  refine ⟨gadget_disjoint, ⟨firstMode, ?_, modes_disjoint.1, modes_cover.1⟩,
    ⟨secondMode, ?_, modes_disjoint.2, modes_cover.2⟩⟩
  · intro s hs
    simp only [firstMode, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map p (by decide)]
      exact h₁
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map p (by decide)]
      exact h₂
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map p (by decide), hlabel]
      exact h₃
  · intro s hs
    simp only [secondMode, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map p (by decide), hlabel]
      exact h₁
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map p (by decide), hlabel]
      exact h₂
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map p (by decide)]
      exact h₃

/-- The same exact modes on any six distinct physical vertices. -/
theorem physical_transformer {V : Type*} [DecidableEq V] (f : Fin 6 ↪ V)
    (p : V → Fin t) (hlabel : p (f 1) = p (f 0))
    (h₁ : Link F (p (f 0)) (p (f 2)) (p (f 4)))
    (h₂ : Link F (p (f 0)) (p (f 3)) (p (f 5)))
    (h₃ : Link F (p (f 0)) (p (f 4)) (p (f 5))) :
    IsTransformer (p := p) (F := F) (gadget.map (edgeEmb f))
      (source.map (edgeEmb f)) (target.map (edgeEmb f)) ∧
      (gadget.map (edgeEmb f)).card = 7 := by
  have h := template_transformer (p ∘ f) hlabel h₁ h₂ h₃
  refine ⟨⟨?_, ?_, ?_⟩, by simpa using gadget_card⟩
  · rw [← map_union]
    exact (disjoint_map _).mpr h.1
  · rw [← map_union]
    exact hasDecomp_map f (fun _ => rfl) h.2.1
  · rw [← map_union]
    exact hasDecomp_map f (fun _ => rfl) h.2.2

end PartitionedTriangleAbsorption.PairMoveStage85
