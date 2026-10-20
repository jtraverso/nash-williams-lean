/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.BipAbs

/-!
# Lemma 9.5: transversals all of whose pairs are typical (Claim 9.5.7)
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

namespace LocFacts

variable {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ} {Su Sv : Finset V}

/-- The local facts are symmetric under exchanging `u` and `v`. -/
lemma swap (L : LocFacts C a g U W A du dv Su Sv) : LocFacts C a g W U A dv du Sv Su where
  thin := L.thin
  gsymm := L.gsymm
  g0 := L.g0
  cov := fun x hx => by rcases L.cov x hx with h | h | h <;> tauto
  AU := L.AW
  AW := L.AU
  UW := fun x hW hU => L.UW x hU hW
  SuU := L.SvW
  SvW := L.SuU
  UU := L.WW
  WW := L.UU
  AA := L.AA
  tri := L.tri
  du0 := L.dv0
  dv0 := L.du0
  dsum := fun y hy => by linarith [L.dsum y hy]
  F4u := L.F4w
  F4w := L.F4u
  F5u := L.F5w
  F5w := L.F5u
  F6u := L.F6w
  F6w := L.F6u
  F7 := fun x hx y hy e he0 he1 h => by
    rcases L.F7 x hx y hy e he0 he1 h with h' | h' | h' <;> tauto

omit [DecidableEq V] in
lemma g_zero_or_pos (L : LocFacts C a g U W A du dv Su Sv) (x y : V) :
    g x y = 0 ∨ 0 < g x y := by
  rcases (L.g0 x y).lt_or_eq with h | h
  · exact Or.inr h
  · exact Or.inl h.symm

omit [DecidableEq V] in
lemma du_le_one (L : LocFacts C a g U W A du dv Su Sv) {y : V} (hy : y ∈ C) : du y ≤ 1 := by
  linarith [L.dsum y hy, L.dv0 y]

omit [DecidableEq V] in
lemma dv_le_one (L : LocFacts C a g U W A du dv Su Sv) {y : V} (hy : y ∈ C) : dv y ≤ 1 := by
  linarith [L.dsum y hy, L.du0 y]

end LocFacts

/-- Membership and types of a transversal `(w₁, w₂, w₃, w₄)`. -/
structure QuadT (C : Finset V) (U W A : V → Prop) (w1 w2 w3 w4 : V) : Prop where
  m1 : w1 ∈ C
  m2 : w2 ∈ C
  m3 : w3 ∈ C
  m4 : w4 ∈ C
  t1 : U w1
  t2 : W w2
  t3 : A w3
  t4 : A w4

/-- Typical weights of a transversal and the relations between the averages. -/
structure QuadH (a : V → V → ℝ) (w1 w2 w3 w4 : V) (M12 M13 M14 M23 M24 M34 θ ζ : ℝ) : Prop where
  c12 : |a w1 w2 - M12| ≤ θ
  c13 : |a w1 w3 - M13| ≤ θ
  c14 : |a w1 w4 - M14| ≤ θ
  c23 : |a w2 w3 - M23| ≤ θ
  c24 : |a w2 w4 - M24| ≤ θ
  c34 : |a w3 w4 - M34| ≤ θ
  hT : 2 - θ ≤ M12 + M13 + M23
  hA1 : 1 - θ ≤ M13 + M23
  hA2 : M13 + M23 ≤ 1 + ζ
  mt1 : |M24 - M13| ≤ θ
  mt2 : |M14 - M23| ≤ θ
  mt3 : |M34 - M12| ≤ θ

variable {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ} {Su Sv : Finset V}
  {w1 w2 w3 w4 : V} {M12 M13 M14 M23 M24 M34 θ ζ : ℝ}

omit [DecidableEq V] in
lemma QuadT.swap (T : QuadT C U W A w1 w2 w3 w4) : QuadT C W U A w2 w1 w3 w4 :=
  ⟨T.m2, T.m1, T.m3, T.m4, T.t2, T.t1, T.t3, T.t4⟩

omit [DecidableEq V] in
lemma QuadH.swap (hs : ∀ x y, a x y = a y x) (H : QuadH a w1 w2 w3 w4 M12 M13 M14 M23 M24 M34 θ ζ) :
    QuadH a w2 w1 w3 w4 M12 M23 M24 M13 M14 M34 θ ζ where
  c12 := by rw [hs]; exact H.c12
  c13 := H.c23
  c14 := H.c24
  c23 := H.c13
  c24 := H.c14
  c34 := H.c34
  hT := by linarith [H.hT]
  hA1 := by linarith [H.hA1]
  hA2 := by linarith [H.hA2]
  mt1 := H.mt2
  mt2 := H.mt1
  mt3 := H.mt3

omit [DecidableEq V] in
/-- The pairs `w₃w₄` and (unless `w₁ ∈ Su`, `w₂ ∈ Sv`) `w₁w₂` are normal. -/
lemma quad_E (L : LocFacts C a g U W A du dv Su Sv) (T : QuadT C U W A w1 w2 w3 w4)
    (H : QuadH a w1 w2 w3 w4 M12 M13 M14 M23 M24 M34 θ ζ) (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ)
    (he : ζ + 3 * θ ≤ 1/6) :
    1 - 6 * (ζ + 3 * θ) ≤ g w3 w4 ∧
      ((w1 ∈ Su ∧ w2 ∈ Sv) ∨ 1 - 6 * (ζ + 3 * θ) ≤ g w1 w2) := by
  have c12 := (abs_le.1 H.c12).1
  have c34 := (abs_le.1 H.c34).1
  have m3 := (abs_le.1 H.mt3).1
  have hT := H.hT
  have hA2 := H.hA2
  constructor
  · rcases L.F7 w3 T.m3 w4 T.m4 (ζ + 3 * θ) (by linarith) he (by linarith) with h | h | h
    · exact absurd (L.SuU _ h.1) (L.AU _ T.t3)
    · exact absurd (L.SvW _ h.1) (L.AW _ T.t3)
    · exact h
  · rcases L.F7 w1 T.m1 w2 T.m2 (ζ + 3 * θ) (by linarith) he (by linarith) with h | h | h
    · exact Or.inl h
    · exact absurd (L.SvW _ h.1) (L.UW _ T.t1)
    · exact Or.inr h

omit [DecidableEq V] in
/-- Case `m₁₃ > 1/2 + b`: the matching `{w₁w₃, w₂w₄}` is normal. -/
lemma quad_case1 (L : LocFacts C a g U W A du dv Su Sv) (T : QuadT C U W A w1 w2 w3 w4)
    (H : QuadH a w1 w2 w3 w4 M12 M13 M14 M23 M24 M34 θ ζ) {b : ℝ} (hb : 2 * θ ≤ b)
    (hM : 1/2 + b < M13) (hg34 : 0 < g w3 w4) :
    1 - 10 * θ ≤ g w1 w3 ∧ 1 - 10 * θ ≤ g w2 w4 := by
  have c13 := (abs_le.1 H.c13).1
  have c14 := (abs_le.1 H.c14).1
  have c23 := (abs_le.1 H.c23).1
  have c24 := (abs_le.1 H.c24).1
  have m1 := (abs_le.1 H.mt1).1
  have m2 := (abs_le.1 H.mt2).1
  have hA1 := H.hA1
  have hθ : 0 ≤ θ := le_trans (abs_nonneg _) H.c13
  -- `w₁w₃` and `w₂w₄` are negative
  have g13 : 0 < g w1 w3 := by
    rcases L.g_zero_or_pos w1 w3 with h | h
    · have := L.F4u w1 T.m1 w3 T.m3 T.t1 T.t3 h
      linarith [L.dv_le_one T.m3]
    · exact h
  have g24 : 0 < g w2 w4 := by
    rcases L.g_zero_or_pos w2 w4 with h | h
    · have := L.F4w w2 T.m2 w4 T.m4 T.t2 T.t4 h
      linarith [L.du_le_one T.m4]
    · exact h
  have g14 : g w1 w4 = 0 := by
    rcases L.g_zero_or_pos w1 w4 with h | h
    · exact h
    · exact (L.tri w1 w3 w4 g13 h hg34).elim
  have g23 : g w2 w3 = 0 := by
    rcases L.g_zero_or_pos w2 w3 with h | h
    · exact h
    · exact (L.tri w2 w4 w3 g24 h (by rw [L.gsymm]; exact hg34)).elim
  have f14 := L.F4u w1 T.m1 w4 T.m4 T.t1 T.t4 g14
  have f23 := L.F4w w2 T.m2 w3 T.m3 T.t2 T.t3 g23
  have f24 := L.F6w w2 T.m2 w4 T.m4 T.t2 T.t4 g24
  have f13 := L.F6u w1 T.m1 w3 T.m3 T.t1 T.t3 g13
  have d3 := L.dsum w3 T.m3
  have d4 := L.dsum w4 T.m4
  constructor <;> linarith

/-- Case `m₂₃ > 1/2 + b`: the matching `{w₂w₃, w₁w₄}` is normal. -/
lemma quad_case2 (L : LocFacts C a g U W A du dv Su Sv) (T : QuadT C U W A w1 w2 w3 w4)
    (H : QuadH a w1 w2 w3 w4 M12 M13 M14 M23 M24 M34 θ ζ) {b : ℝ} (hb : 2 * θ ≤ b)
    (hM : 1/2 + b < M23) (hg34 : 0 < g w3 w4) :
    1 - 10 * θ ≤ g w2 w3 ∧ 1 - 10 * θ ≤ g w1 w4 :=
  quad_case1 L.swap T.swap (H.swap L.thin.symm) hb hM hg34

omit [DecidableEq V] in
/-- Case `m₁₃, m₂₃ ≤ 1/2 + b`: one of the two matchings is normal, and the demands of `w₃, w₄`
determine which. -/
lemma quad_case_mid (L : LocFacts C a g U W A du dv Su Sv) (T : QuadT C U W A w1 w2 w3 w4)
    (H : QuadH a w1 w2 w3 w4 M12 M13 M14 M23 M24 M34 θ ζ) {b : ℝ}
    (h13 : M13 ≤ 1/2 + b) (h23 : M23 ≤ 1/2 + b) (hg34 : 0 < g w3 w4)
    (hsmall : 4 * b + 12 * θ < 1) :
    (1 - (4 * b + 12 * θ) ≤ g w1 w3 ∧ 1 - (4 * b + 12 * θ) ≤ g w2 w4 ∧
      1 - (2 * b + 6 * θ) ≤ du w3 ∧ 1 - (2 * b + 6 * θ) ≤ dv w4) ∨
    (1 - (4 * b + 12 * θ) ≤ g w2 w3 ∧ 1 - (4 * b + 12 * θ) ≤ g w1 w4 ∧
      1 - (2 * b + 6 * θ) ≤ dv w3 ∧ 1 - (2 * b + 6 * θ) ≤ du w4) := by
  have c13 := (abs_le.1 H.c13).1
  have c14 := (abs_le.1 H.c14).1
  have c23 := (abs_le.1 H.c23).1
  have c24 := (abs_le.1 H.c24).1
  have m1 := (abs_le.1 H.mt1).1
  have m2 := (abs_le.1 H.mt2).1
  have hA1 := H.hA1
  have hθ : 0 ≤ θ := le_trans (abs_nonneg _) H.c13
  have d3 := L.dsum w3 T.m3
  have d4 := L.dsum w4 T.m4
  have hg43 : 0 < g w4 w3 := by rw [L.gsymm]; exact hg34
  rcases L.g_zero_or_pos w1 w3 with g13 | g13
  · -- `w₁w₃` is not negative: the matching `{w₂w₃, w₁w₄}`
    right
    have f13 := L.F4u w1 T.m1 w3 T.m3 T.t1 T.t3 g13
    have g23 : 0 < g w2 w3 := by
      rcases L.g_zero_or_pos w2 w3 with h | h
      · have := L.F4w w2 T.m2 w3 T.m3 T.t2 T.t3 h
        linarith
      · exact h
    have g24 : g w2 w4 = 0 := by
      rcases L.g_zero_or_pos w2 w4 with h | h
      · exact h
      · exact (L.tri w3 w2 w4 (by rw [L.gsymm]; exact g23) hg34 h).elim
    have f24 := L.F4w w2 T.m2 w4 T.m4 T.t2 T.t4 g24
    have g14 : 0 < g w1 w4 := by
      rcases L.g_zero_or_pos w1 w4 with h | h
      · have := L.F4u w1 T.m1 w4 T.m4 T.t1 T.t4 h
        linarith
      · exact h
    have f23 := L.F6w w2 T.m2 w3 T.m3 T.t2 T.t3 g23
    have f14 := L.F6u w1 T.m1 w4 T.m4 T.t1 T.t4 g14
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- `w₁w₃` is negative: the matching `{w₁w₃, w₂w₄}`
    left
    have g14 : g w1 w4 = 0 := by
      rcases L.g_zero_or_pos w1 w4 with h | h
      · exact h
      · exact (L.tri w1 w3 w4 g13 h hg34).elim
    have f14 := L.F4u w1 T.m1 w4 T.m4 T.t1 T.t4 g14
    have g24 : 0 < g w2 w4 := by
      rcases L.g_zero_or_pos w2 w4 with h | h
      · have := L.F4w w2 T.m2 w4 T.m4 T.t2 T.t4 h
        linarith
      · exact h
    have g23 : g w2 w3 = 0 := by
      rcases L.g_zero_or_pos w2 w3 with h | h
      · exact h
      · exact (L.tri w4 w2 w3 (by rw [L.gsymm]; exact g24) hg43 h).elim
    have f23 := L.F4w w2 T.m2 w3 T.m3 T.t2 T.t3 g23
    have f24 := L.F6w w2 T.m2 w4 T.m4 T.t2 T.t4 g24
    have f13 := L.F6u w1 T.m1 w3 T.m3 T.t1 T.t3 g13
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end NashWilliams.Frac
