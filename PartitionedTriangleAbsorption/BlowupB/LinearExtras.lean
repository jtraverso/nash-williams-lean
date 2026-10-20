/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LinearAbsorber

/-! # BlowupB.LinearExtras — linear families are exactly where `ThreeStepLinks` fails

* `not_threeStepLinks_of_linear`: no nonempty linear family satisfies `ThreeStepLinks` (the
  link of a class is a matching, so no walk of length `3` returns from `y` to `y`). Hence the
  linear-family absorbers of `LinearAbsorber` cover a class of families disjoint from the one
  covered by the tree's transformer chain.
* Examples: the rainbow type `R3` and the Fano plane `fano` (seven classes, seven types) are
  linear.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer

variable {t : ℕ}

/-- **Linear families never satisfy `ThreeStepLinks`.** -/
theorem not_threeStepLinks_of_linear {F : Finset (Multiset (Fin t))} (hL : IsLinearFam F)
    {τ : Multiset (Fin t)} (hτ : τ ∈ F) : ¬ ThreeStepLinks F := by
  intro h3
  obtain ⟨x, y, z, rfl⟩ := Multiset.card_eq_three.mp (hL.card3 τ hτ)
  obtain ⟨hxy, hxz, hyz⟩ := (nodup_three_iff x y z).mp (hL.nodup _ hτ)
  have hlink : Link F x y z := hτ
  obtain ⟨v, w, h1, h2, h3'⟩ := h3 x y y ⟨z, hlink⟩ ⟨z, hlink⟩
  have h1' : ({x, y, v} : Multiset (Fin t)) ∈ F := h1
  have e1 : ({x, y, v} : Multiset (Fin t)) = {x, y, z} :=
    hL.unique _ h1' _ hτ x y hxy (by simp) (by simp) (by simp) (by simp)
  obtain ⟨_, hxv, hyv⟩ := (nodup_three_iff x y v).mp (hL.nodup _ h1')
  have hv : v = z := by
    have hm : v ∈ ({x, y, z} : Multiset (Fin t)) := by rw [← e1]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    rcases hm with h | h | h
    · exact absurd h.symm hxv
    · exact absurd h.symm hyv
    · exact h
  subst hv
  have h2' : ({x, v, w} : Multiset (Fin t)) ∈ F := h2
  have e2 : ({x, v, w} : Multiset (Fin t)) = {x, y, v} :=
    hL.unique _ h2' _ hτ x v hxz (by simp) (by simp) (by simp) (by simp)
  obtain ⟨_, hxw, hvw⟩ := (nodup_three_iff x v w).mp (hL.nodup _ h2')
  have hw : w = y := by
    have hm : w ∈ ({x, y, v} : Multiset (Fin t)) := by rw [← e2]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    rcases hm with h | h | h
    · exact absurd h.symm hxw
    · exact h
    · exact absurd h.symm hvw
  subst hw
  have h3'' : ({x, w, w} : Multiset (Fin t)) ∈ F := h3'
  exact ((nodup_three_iff x w w).mp (hL.nodup _ h3'')).2.2 rfl

/-- The rainbow type is linear. -/
theorem isLinearFam_R3 : IsLinearFam R3 :=
  ⟨card_R3, by unfold R3; decide, by unfold R3; decide⟩

/-- The Fano plane on seven classes. -/
def fano : Finset (Multiset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The Fano plane is linear. -/
theorem isLinearFam_fano : IsLinearFam fano :=
  ⟨by unfold fano; decide, by unfold fano; decide, by unfold fano; decide⟩

theorem not_threeStepLinks_fano : ¬ ThreeStepLinks fano :=
  not_threeStepLinks_of_linear isLinearFam_fano (τ := {0, 1, 2}) (by unfold fano; decide)

end PartitionedTriangleAbsorption.BlowupB
