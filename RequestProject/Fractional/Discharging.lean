/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.LocalMain
public import RequestProject.Fractional.ValueLemma

@[expose] public section

/-!
# The discharging argument (Section 4 of Delcourt–Postle)

`φ : Sym2 V → ℝ` is an edge weighting of `G` (only its values on edges matter).
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- A nonzero, untied, triangle-covered edge weighting (Definitions 4.3 and 4.6). -/
structure GoodWeighting : Prop where
  cov : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → 0 ≤ φ s(a, b) + φ s(a, c) + φ s(b, c)
  nz : ∀ e, φ e ≠ 0
  inj : Function.Injective φ

/-- Common neighbourhood. -/
def cn (a b : V) : Finset V := univ.filter (fun x => G.Adj a x ∧ G.Adj b x)

/-- Demand of the edge `ax` on the edge `ab` (in the triangle `abx`). -/
noncomputable def dem (a b x : V) : ℝ := demF (φ s(a, b)) (φ s(a, x)) (φ s(b, x))

/-- Total demand on the edge `ab`. -/
noncomputable def Dtot (a b : V) : ℝ := ∑ x ∈ cn G a b, (dem φ a b x + dem φ b a x)

/-- Charge sent by the edge `ab` to the edge `ax` (Demand Proportional rule). -/
noncomputable def trans (a b x : V) : ℝ :=
  if G.Adj a b ∧ G.Adj a x ∧ G.Adj b x then φ s(a, b) * dem φ a b x / Dtot G φ a b else 0

omit [DecidableEq V] in
lemma mem_cn {a b x : V} : x ∈ cn G a b ↔ G.Adj a x ∧ G.Adj b x := by simp [cn]

omit [DecidableEq V] in
lemma cn_comm (a b : V) : cn G a b = cn G b a := by
  ext x; simp [cn, and_comm]

omit [Fintype V] [DecidableEq V] in
lemma dem_nonneg (a b x : V) : 0 ≤ dem φ a b x := demF_nonneg _ _ _

omit [DecidableEq V] in
lemma Dtot_nonneg (a b : V) : 0 ≤ Dtot G φ a b :=
  sum_nonneg fun x _ => add_nonneg (dem_nonneg φ a b x) (dem_nonneg φ b a x)

omit [DecidableEq V] in
lemma Dtot_comm (a b : V) : Dtot G φ a b = Dtot G φ b a := by
  unfold Dtot; rw [cn_comm]; exact sum_congr rfl fun x _ => add_comm _ _

omit [Fintype V] [DecidableEq V] in
lemma dem_eq_zero_of_nonpos {a b x : V} (h : φ s(a, b) ≤ 0) : dem φ a b x = 0 :=
  demF_of_nonpos h

omit [DecidableEq V] in
lemma trans_nonneg (a b x : V) : 0 ≤ trans G φ a b x := by
  unfold trans
  split_ifs
  · rcases le_or_gt (φ s(a, b)) 0 with h | h
    · rw [dem_eq_zero_of_nonpos φ h]; simp
    · exact div_nonneg (mul_nonneg h.le (dem_nonneg φ a b x)) (Dtot_nonneg G φ a b)
  · exact le_rfl

/-- Positive part of the weight of `ab` (as an ordered pair). -/
noncomputable def posPart (a b : V) : ℝ := if G.Adj a b ∧ 0 < φ s(a, b) then φ s(a, b) else 0

/-- Negative part of the weight of `ab` (as an ordered pair). -/
noncomputable def negPart (a b : V) : ℝ := if G.Adj a b ∧ φ s(a, b) < 0 then -φ s(a, b) else 0

/-- A positive edge sends out at most its weight. -/
lemma sum_trans_le_pos (a b : V) :
    ∑ x, (trans G φ a b x + trans G φ b a x) ≤ posPart G φ a b := by
  by_cases hab : G.Adj a b
  · have e : ∀ x, trans G φ a b x + trans G φ b a x =
        if x ∈ cn G a b then φ s(a, b) * (dem φ a b x + dem φ b a x) / Dtot G φ a b else 0 := by
      intro x
      unfold trans
      simp only [mem_cn]
      rw [show s(b, a) = s(a, b) from Sym2.eq_swap, Dtot_comm G φ b a]
      by_cases hx : G.Adj a x ∧ G.Adj b x
      · rw [if_pos ⟨hab, hx.1, hx.2⟩, if_pos ⟨hab.symm, hx.2, hx.1⟩, if_pos hx]; ring
      · rw [if_neg (fun h => hx ⟨h.2.1, h.2.2⟩), if_neg (fun h => hx ⟨h.2.2, h.2.1⟩),
          if_neg hx]; ring
    rw [sum_congr rfl fun x _ => e x, ← sum_filter, ← sum_div, ← mul_sum]
    have hfil : (univ.filter fun x => x ∈ cn G a b) = cn G a b := by ext; simp
    rw [hfil]
    change φ s(a, b) * Dtot G φ a b / Dtot G φ a b ≤ _
    unfold posPart
    have hD := Dtot_nonneg G φ a b
    rcases le_or_gt (φ s(a, b)) 0 with h | h
    · rw [if_neg (fun h' => absurd h'.2 (not_lt.2 h))]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h hD) hD
    · rw [if_pos ⟨hab, h⟩]
      rcases hD.lt_or_eq with hD | hD
      · rw [mul_div_assoc, div_self hD.ne', mul_one]
      · rw [← hD]; simp; exact h.le
  · have : ∀ x, trans G φ a b x + trans G φ b a x = 0 := by
      intro x; unfold trans
      rw [if_neg (fun h => hab h.1), if_neg (fun h => hab h.1.symm)]; ring
    simp only [this, sum_const_zero]
    unfold posPart; rw [if_neg (fun h => hab h.1)]

end NashWilliams.Frac
