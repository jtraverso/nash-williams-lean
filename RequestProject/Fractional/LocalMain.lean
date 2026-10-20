/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Case1
public import RequestProject.Fractional.Case2

@[expose] public section

/-!
# Lemma 4.31 of Delcourt–Postle (the triangle-thin lemma for strict sponsorship)

For every configuration of ten weights on a `K₅` as in `LH`, the value of the triangle
`wxy` is at most `4 |φ(f)|`.  The configurations not covered by Lemma 6.1 contain an edge of
value `0` (Proposition 4.26); the others are reduced to Lemma 6.1 by symmetry.
-/

namespace NashWilliams.Frac

/-- Close a goal `a = 0 ∨ (b < 0 ∧ c < 0)`-shaped side condition by linear arithmetic. -/
macro "zero_side" : tactic =>
  `(tactic| first | (left; linarith) | (right; constructor <;> linarith))

/-- Transport the hypotheses `LH` along a relabelling of the vertices. -/
macro "lh_perm " h:ident : tactic => `(tactic| (
  obtain ⟨hf, nd, ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩
    := $h
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (List.Perm.nodup_iff (by
      rw [List.perm_iff_count]; intro z; simp only [List.count_cons, List.count_nil]; omega)).1 nd
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> assumption
  all_goals linarith))

/-- **Lemma 4.31** (in the local form): `Val_f(T) ≤ 4 |φ(f)|`. -/
theorem local_bound {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) :
    ValT f aw bw ax bx ay b_y qwx qwy qxy ≤ -4 * f := by
  have hf := h.hf
  have cw := h.cw; have cx := h.cx; have cy := h.cy
  have c1 := h.cuwx; have c2 := h.cuwy; have c3 := h.cuxy
  have c4 := h.cvwx; have c5 := h.cvwy; have c6 := h.cvxy
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := h.nz
  rcases type_cases hf cw n1 n2 with ⟨tw1, tw2⟩ | ⟨tw1, tw2⟩ | ⟨tw1, tw2⟩ <;>
  rcases type_cases hf cx n3 n4 with ⟨tx1, tx2⟩ | ⟨tx1, tx2⟩ | ⟨tx1, tx2⟩ <;>
  rcases type_cases hf cy n5 n6 with ⟨ty1, ty2⟩ | ⟨ty1, ty2⟩ | ⟨ty1, ty2⟩
  · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f aw bw ax bx ay b_y qwx qwy qxy := rfl
      _ ≤ -4 * f := core1 h (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f aw bw ay b_y ax bx qwy qwx qxy := by unfold ValT ValE; ring
      _ ≤ -4 * f := core1 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · rcases (show qxy ≠ 0 by assumption).lt_or_gt with qq | qq
    · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f aw bw ax bx ay b_y qwx qwy qxy := rfl
        _ ≤ -4 * f := core2 h (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) qq
    · exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f ax bx aw bw ay b_y qwx qxy qwy := by unfold ValT ValE; ring
      _ ≤ -4 * f := core1 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f ay b_y aw bw ax bx qwy qxy qwx := by unfold ValT ValE; ring
      _ ≤ -4 * f := core1 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · rcases (show qxy ≠ 0 by assumption).lt_or_gt with qq | qq
    · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f bw aw bx ax b_y ay qwx qwy qxy := by unfold ValT ValE; ring
        _ ≤ -4 * f := core2 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) qq
    · exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f ax bx ay b_y aw bw qxy qwx qwy := by unfold ValT ValE; ring
      _ ≤ -4 * f := core1 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · rcases (show qwy ≠ 0 by assumption).lt_or_gt with qq | qq
    · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f ax bx aw bw ay b_y qwx qxy qwy := by unfold ValT ValE; ring
        _ ≤ -4 * f := core2 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) qq
    · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f ay b_y ax bx aw bw qxy qwy qwx := by unfold ValT ValE; ring
      _ ≤ -4 * f := core1 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · rcases (show qwy ≠ 0 by assumption).lt_or_gt with qq | qq
    · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f bx ax bw aw b_y ay qwx qxy qwy := by unfold ValT ValE; ring
        _ ≤ -4 * f := core2 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) qq
    · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
  · rcases (show qwx ≠ 0 by assumption).lt_or_gt with qq | qq
    · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f ay b_y aw bw ax bx qwy qxy qwx := by unfold ValT ValE; ring
        _ ≤ -4 * f := core2 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) qq
    · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · rcases (show qwx ≠ 0 by assumption).lt_or_gt with qq | qq
    · calc ValT f aw bw ax bx ay b_y qwx qwy qxy = ValT f b_y ay bw aw bx ax qwy qxy qwx := by unfold ValT ValE; ring
        _ ≤ -4 * f := core2 (by lh_perm h) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) qq
    · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))
  · rcases n7.lt_or_gt with q1 | q1
    · rcases n8.lt_or_gt with q2 | q2
      · have q3 : 0 < qxy := by linarith [h.cwxy]
        exact h.bound_of_zero (Or.inr (Or.inr (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
      · exact h.bound_of_zero (Or.inr (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side))))
    · exact h.bound_of_zero (Or.inl (ValE_eq_zero (by zero_side) (by zero_side) (by zero_side) (by zero_side)))

end NashWilliams.Frac
