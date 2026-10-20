/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# The strict sponsorship demand function (Delcourt–Postle, Definition 4.11)

Everything here is a statement about real numbers: the weights of the three edges of a
triangle.  For a triangle with edges `e`, `f`, `o` (where `e` and `f` share a vertex),
`demF pe pf po` is the demand of the edge `f` on the edge `e`, where
`pe`, `pf`, `po` are the weights of `e`, `f`, `o`.
-/

namespace NashWilliams.Frac

/-- Strict sponsorship demand of `f` (weight `pf`) on `e` (weight `pe`) inside a triangle
whose third edge has weight `po`. -/
noncomputable def demF (pe pf po : ℝ) : ℝ :=
  if 0 < pe ∧ pf < 0 then
    if po < 0 then -pf
    else if -pf ≤ max pe po then (if po < pe then -pf else 0)
    else -pf * pe / (pe + po)
  else 0

/-- Normalized demand of a triangle on its edge `e`: the triangle has edges `e`, `p1`, `p2`. -/
noncomputable def normT (pe p1 p2 : ℝ) : ℝ := (demF pe p1 p2 + demF pe p2 p1) / pe

lemma demF_of_nonpos {pe pf po : ℝ} (h : pe ≤ 0) : demF pe pf po = 0 := by
  unfold demF; rw [if_neg]; intro h'; linarith [h'.1]

lemma demF_of_nonneg_f {pe pf po : ℝ} (h : 0 ≤ pf) : demF pe pf po = 0 := by
  unfold demF; rw [if_neg]; intro h'; linarith [h'.2]

lemma demF_obtuse {pe pf po : ℝ} (he : 0 < pe) (hf : pf < 0) (ho : po < 0) :
    demF pe pf po = -pf := by
  unfold demF; rw [if_pos ⟨he, hf⟩, if_pos ho]

lemma demF_sponsor {pe pf po : ℝ} (he : 0 < pe) (hf : pf < 0) (ho : 0 ≤ po) (hlt : po < pe)
    (hs : -pf ≤ pe) : demF pe pf po = -pf := by
  unfold demF
  rw [if_pos ⟨he, hf⟩, if_neg (by linarith), if_pos (le_trans hs (le_max_left _ _)), if_pos hlt]

lemma demF_nonsponsor {pe pf po : ℝ} (he : 0 < pe) (hf : pf < 0) (hlt : pe < po)
    (hs : -pf ≤ po) : demF pe pf po = 0 := by
  unfold demF
  rw [if_pos ⟨he, hf⟩, if_neg (by linarith), if_pos (le_trans hs (le_max_right _ _)),
    if_neg (by linarith)]

lemma demF_unsponsored {pe pf po : ℝ} (he : 0 < pe) (hf : pf < 0) (ho : 0 ≤ po)
    (h1 : pe < -pf) (h2 : po < -pf) : demF pe pf po = -pf * pe / (pe + po) := by
  unfold demF
  rw [if_pos ⟨he, hf⟩, if_neg (by linarith), if_neg (by rw [not_le, max_lt_iff]; exact ⟨h1, h2⟩)]

lemma demF_nonneg (pe pf po : ℝ) : 0 ≤ demF pe pf po := by
  unfold demF
  split_ifs with h1 h2 h3 h4 <;> try linarith [h1.2]
  · push_neg at h2
    apply div_nonneg
    · nlinarith [h1.1, h1.2]
    · linarith [h1.1]
  · exact le_refl _

lemma demF_le (pe pf po : ℝ) (hf : pf < 0) : demF pe pf po ≤ -pf := by
  unfold demF
  split_ifs with h1 h2 h3 h4 <;> try linarith
  push_neg at h2 h3
  rw [div_le_iff₀ (by linarith [h1.1])]
  nlinarith [h1.1]

/-- In a triangle-covered triangle, the demand on `e` is at most the weight of `e`. -/
lemma demF_le_pe (pe pf po : ℝ) (hcov : 0 ≤ pe + pf + po) : demF pe pf po ≤ max pe 0 := by
  unfold demF
  split_ifs with h1 h2 h3 h4
  · linarith [le_max_left pe 0]
  · rw [max_def] at h3
    split_ifs at h3 <;> linarith [le_max_left pe 0]
  · exact le_max_right _ _
  · push_neg at h2 h3
    rw [div_le_iff₀ (by linarith [h1.1])]
    nlinarith [le_max_left pe 0, h1.1]
  · exact le_max_right _ _

/-- The two demands of `f` on the two other edges of a triangle add up to `|f|`. -/
lemma demF_pair {pf pe po : ℝ} (hf : pf < 0) (he : pe ≠ 0) (ho : po ≠ 0) (hne : pe ≠ po)
    (hcov : 0 ≤ pf + pe + po) : demF pe pf po + demF po pf pe = -pf := by
  rcases he.lt_or_gt with he | he <;> rcases ho.lt_or_gt with ho | ho
  · linarith
  · rw [demF_of_nonpos he.le, demF_obtuse ho hf he]; ring
  · rw [demF_of_nonpos ho.le, demF_obtuse he hf ho]; ring
  · rcases hne.lt_or_gt with hlt | hlt
    · by_cases hs : -pf ≤ po
      · rw [demF_nonsponsor he hf hlt hs, demF_sponsor ho hf he.le hlt hs]; ring
      · push_neg at hs
        rw [demF_unsponsored he hf ho.le (by linarith) hs,
          demF_unsponsored ho hf he.le hs (by linarith)]
        field_simp
        ring
    · by_cases hs : -pf ≤ pe
      · rw [demF_sponsor he hf ho.le hlt hs, demF_nonsponsor ho hf hlt hs]; ring
      · push_neg at hs
        rw [demF_unsponsored he hf ho.le hs (by linarith),
          demF_unsponsored ho hf he.le (by linarith) hs]
        field_simp
        ring

lemma normT_nonneg (pe p1 p2 : ℝ) : 0 ≤ normT pe p1 p2 := by
  unfold normT
  rcases le_or_gt pe 0 with h | h
  · rw [demF_of_nonpos h, demF_of_nonpos h]; simp
  · exact div_nonneg (add_nonneg (demF_nonneg _ _ _) (demF_nonneg _ _ _)) h.le

/-- Proposition 4.19 (core): the normalized demand of a triangle on an edge is at most `1`. -/
lemma normT_le_one (pe p1 p2 : ℝ) (hcov : 0 ≤ pe + p1 + p2) : normT pe p1 p2 ≤ 1 := by
  unfold normT
  rcases le_or_gt pe 0 with h | h
  · rw [demF_of_nonpos h, demF_of_nonpos h]; simp
  rw [div_le_one h]
  rcases lt_or_ge p1 0 with h1 | h1 <;> rcases lt_or_ge p2 0 with h2 | h2
  · rw [demF_obtuse h h1 h2, demF_obtuse h h2 h1]; linarith
  · rw [demF_of_nonneg_f h2]
    have := demF_le_pe pe p1 p2 hcov
    rw [max_eq_left h.le] at this; linarith
  · rw [demF_of_nonneg_f h1]
    have := demF_le_pe pe p2 p1 (by linarith)
    rw [max_eq_left h.le] at this; linarith
  · rw [demF_of_nonneg_f h1, demF_of_nonneg_f h2]; linarith

lemma normT_comm (pe p1 p2 : ℝ) : normT pe p1 p2 = normT pe p2 p1 := by
  unfold normT; ring

/-- A triangle all of whose edges are positive has normalized demand `0`. -/
lemma normT_of_nonneg {pe p1 p2 : ℝ} (h1 : 0 ≤ p1) (h2 : 0 ≤ p2) : normT pe p1 p2 = 0 := by
  unfold normT; rw [demF_of_nonneg_f h1, demF_of_nonneg_f h2]; simp

end NashWilliams.Frac
