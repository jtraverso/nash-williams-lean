/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # Transport a finite physical triangle family to the existing copy API

No completeness or surjectivity of the index family is assumed. Loads are
preserved by summing indexed weights at their actual vertex set. Injectivity
is used only to retain the pointwise coefficient cap.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CopyPushforwardStage74

open Finset TypedLoadNecessity TypedNibble

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def push (shape : I → Finset V) (w : I → ℝ) (s : Finset V) : ℝ :=
  ∑ i, if shape i = s then w i else 0

theorem load_push {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (shape : I → Finset V)
    (hcopy : ∀ i, IsCopy p F G (shape i)) (w : I → ℝ) (e : Sym2 V) :
    edgeLoad p F G (push shape w) e =
      ∑ i, if e ∈ triEdges (shape i) then w i else 0 := by
  classical
  unfold edgeLoad push
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [mem_copies_iff, hcopy i]

theorem load_push_of_zero_outside {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (shape : I → Finset V) (w : I → ℝ)
    (hzero : ∀ i, ¬ IsCopy p F G (shape i) → w i = 0) (e : Sym2 V) :
    edgeLoad p F G (push shape w) e =
      ∑ i, if e ∈ triEdges (shape i) then w i else 0 := by
  classical
  unfold edgeLoad push
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  by_cases hi : IsCopy p F G (shape i)
  · simp [mem_copies_iff, hi]
  · rw [hzero i hi]
    simp

omit [Fintype V] in
theorem push_bound (shape : I → Finset V) (hinj : Function.Injective shape)
    (w : I → ℝ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, |w i| ≤ W) (s : Finset V) :
    |push shape w s| ≤ W := by
  classical
  by_cases hs : ∃ i, shape i = s
  · obtain ⟨i, hi⟩ := hs
    have he : push shape w s = w i := by
      unfold push
      rw [sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have hj : shape j ≠ s := fun hj => hji (hinj (hj.trans hi.symm))
        simp [hj]
      · simp
    rw [he]
    exact hw i
  · have he : push shape w s = 0 := by
      unfold push
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hs ⟨i, hi⟩)
    rw [he, abs_zero]
    exact hW

end PartitionedTriangleAbsorption.CopyPushforwardStage74
