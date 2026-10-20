/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour

/-! # Structural representatives after bounded physical edge deletion

The old query-deletion lemma is reused with an indicator of ONE structural
class. Roots in that class are excluded explicitly; no coarse CN5/CN6 is claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassRepresentativesStage65

open Finset F0Geometric

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

def classSet (cls : V → C) (i : C) : Finset V := univ.filter (fun v => cls v = i)

def classIndicator (cls : V → C) (i : C) (v : V) : Fin 2 :=
  if cls v = i then 0 else 1

theorem card_class_common_delete (cls : V → C) (i : C)
    (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b) (d : ℝ)
    (hdel : ∀ v, ((univ.filter fun w => G₀.Adj v w ∧ ¬ G.Adj v w).card : ℝ) ≤ d)
    (R : Finset V) (hR : ∀ v ∈ R, cls v ≠ i) :
    ((classSet cls i).card : ℝ) - R.card * d ≤
      ((univ.filter fun w => cls w = i ∧ ∀ v ∈ R, G.Adj v w).card : ℝ) := by
  have hbase : (univ.filter fun w => classIndicator cls i w = 0 ∧
      ∀ v ∈ R, G₀.Adj v w) = classSet cls i := by
    ext w
    simp only [mem_filter, mem_univ, true_and, classSet]
    constructor
    · intro h
      simpa [classIndicator] using h.1
    · intro hw
      refine ⟨by simp [classIndicator, hw], ?_⟩
      intro v hv
      exact (hG₀ v w).mpr (hw ▸ hR v hv)
  have h := card_common_delete (classIndicator cls i) G₀ G d hdel R 0
  rw [hbase] at h
  simpa [classIndicator] using h

omit [DecidableEq V] in
theorem exists_class_common (cls : V → C) (i : C)
    (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b) (d : ℝ)
    (hdel : ∀ v, ((univ.filter fun w => G₀.Adj v w ∧ ¬ G.Adj v w).card : ℝ) ≤ d)
    (R : Finset V) (hR : ∀ v ∈ R, cls v ≠ i)
    (hbudget : R.card * d < (classSet cls i).card) :
    ∃ w, cls w = i ∧ ∀ v ∈ R, G.Adj v w := by
  classical
  have h := card_class_common_delete cls i G₀ G hG₀ d hdel R hR
  have hpos : 0 < (univ.filter fun w => cls w = i ∧ ∀ v ∈ R, G.Adj v w).card := by
    have : (0 : ℝ) <
        ((univ.filter fun w => cls w = i ∧ ∀ v ∈ R, G.Adj v w).card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  exact ⟨w, (mem_filter.mp hw).2⟩

omit [DecidableEq V] in
theorem structural_representatives (cls : V → Fin 4)
    (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b) (d : ℝ) (hd : 0 ≤ d)
    (hdel : ∀ v, ((univ.filter fun w => G₀.Adj v w ∧ ¬ G.Adj v w).card : ℝ) ≤ d)
    (S : Finset V) (b : ℝ) (hsize : ∀ i, b ≤ ((classSet cls i).card : ℝ))
    (hbudget : (S.card + 3 : ℕ) * d < b) :
    ∃ r : Fin 4 → V, (∀ i, cls (r i) = i) ∧
      (∀ i, ∀ v ∈ S, cls v ≠ i → G.Adj v (r i)) ∧
      (∀ i j, i ≠ j → G.Adj (r i) (r j)) := by
  classical
  have pick : ∀ i : Fin 4, ∀ W : Finset V, W.card ≤ S.card + 3 →
      ∃ w, cls w = i ∧ ∀ v ∈ W, cls v ≠ i → G.Adj v w := by
    intro i W hW
    let R := W.filter fun v => cls v ≠ i
    have hR : R.card ≤ S.card + 3 := (card_filter_le _ _).trans hW
    obtain ⟨w, hw, hroot⟩ := exists_class_common cls i G₀ G hG₀ d hdel R
      (fun v hv => (mem_filter.mp hv).2) (by
        have hc : (R.card : ℝ) * d ≤ (S.card + 3 : ℕ) * d :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hR) hd
        exact (hc.trans_lt hbudget).trans_le (hsize i))
    exact ⟨w, hw, fun v hv hi => hroot v (mem_filter.mpr ⟨hv, hi⟩)⟩
  obtain ⟨r₀, hc₀, h₀⟩ := pick 0 S (by omega)
  obtain ⟨r₁, hc₁, h₁⟩ := pick 1 (S ∪ {r₀}) (by
    have := card_union_le S {r₀}; simp only [card_singleton] at this; omega)
  obtain ⟨r₂, hc₂, h₂⟩ := pick 2 (S ∪ {r₀, r₁}) (by
    have := card_union_le S {r₀, r₁}; have := card_le_two (a := r₀) (b := r₁); omega)
  obtain ⟨r₃, hc₃, h₃⟩ := pick 3 (S ∪ {r₀, r₁, r₂}) (by
    have := card_union_le S {r₀, r₁, r₂}
    have := card_le_three (a := r₀) (b := r₁) (c := r₂)
    omega)
  let r : Fin 4 → V := ![r₀, r₁, r₂, r₃]
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [r, hc₀, hc₁, hc₂, hc₃]
  · intro i v hv hi
    fin_cases i
    · exact h₀ v hv hi
    · exact h₁ v (mem_union_left _ hv) hi
    · exact h₂ v (mem_union_left _ hv) hi
    · exact h₃ v (mem_union_left _ hv) hi
  · have h₀₁ : G.Adj r₀ r₁ := h₁ r₀ (by simp) (by simp [hc₀])
    have h₀₂ : G.Adj r₀ r₂ := h₂ r₀ (by simp) (by simp [hc₀])
    have h₁₂ : G.Adj r₁ r₂ := h₂ r₁ (by simp) (by simp [hc₁])
    have h₀₃ : G.Adj r₀ r₃ := h₃ r₀ (by simp) (by simp [hc₀])
    have h₁₃ : G.Adj r₁ r₃ := h₃ r₁ (by simp) (by simp [hc₁])
    have h₂₃ : G.Adj r₂ r₃ := h₃ r₂ (by simp) (by simp [hc₂])
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hij rfl)
      | exact h₀₁ | exact h₀₁.symm | exact h₀₂ | exact h₀₂.symm
      | exact h₁₂ | exact h₁₂.symm | exact h₀₃ | exact h₀₃.symm
      | exact h₁₃ | exact h₁₃.symm | exact h₂₃ | exact h₂₃.symm

end PartitionedTriangleAbsorption.ClassRepresentativesStage65
