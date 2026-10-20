/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.StabW

@[expose] public section

/-!
# Symmetry bookkeeping for four part configurations indexed by `Fin 4`
-/

namespace NashWilliams.Frac

open Finset

/-- Sum of the six pair weights. -/
def sum6 (m : Fin 4 → Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  m i j + m i k + m i l + m j k + m j l + m k l

lemma sum6_perm {m : Fin 4 → Fin 4 → ℝ} (hs : ∀ i j, m i j = m j i) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    sum6 m i j k l = sum6 m 0 1 2 3 := by
  have h01 := hs 0 1; have h02 := hs 0 2; have h03 := hs 0 3
  have h12 := hs 1 2; have h13 := hs 1 3; have h23 := hs 2 3
  unfold sum6
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp (config := {decide := true}) at hij hik hil hjk hjl hkl ⊢ <;>
    linarith only [h01, h02, h03, h12, h13, h23]

lemma val4_perm {x : Fin 4 → ℝ} {m : Fin 4 → Fin 4 → ℝ} (hs : ∀ i j, m i j = m j i)
    {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    val4 (x i) (x j) (x k) (x l) (m i j) (m i k) (m i l) (m j k) (m j l) (m k l) =
      val4 (x 0) (x 1) (x 2) (x 3) (m 0 1) (m 0 2) (m 0 3) (m 1 2) (m 1 3) (m 2 3) := by
  have h01 := hs 0 1; have h02 := hs 0 2; have h03 := hs 0 3
  have h12 := hs 1 2; have h13 := hs 1 3; have h23 := hs 2 3
  unfold val4
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp (config := {decide := true}) at hij hik hil hjk hjl hkl ⊢ <;>
    simp only [h01, h02, h03, h12, h13, h23] <;> ring

lemma sum_x_perm {x : Fin 4 → ℝ} {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    x i + x j + x k + x l = x 0 + x 1 + x 2 + x 3 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp (config := {decide := true}) at hij hik hil hjk hjl hkl ⊢ <;> ring

lemma compl_pair {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({i, j} : Finset (Fin 4))ᶜ = {k, l} := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp (config := {decide := true}) at hij hik hil hjk hjl hkl ⊢

lemma exists_other_two {i j : Fin 4} (hij : i ≠ j) :
    ∃ k l : Fin 4, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) at hij ⊢

end NashWilliams.Frac

namespace NashWilliams.Frac

/-- A four part configuration: part sizes `x` summing to `1` and a symmetric triangle-thin
`[0,1]`-weighting `m` of the pairs. -/
structure Cfg4 (x : Fin 4 → ℝ) (m : Fin 4 → Fin 4 → ℝ) : Prop where
  x0 : ∀ i, 0 ≤ x i
  sum : x 0 + x 1 + x 2 + x 3 = 1
  symm : ∀ i j, m i j = m j i
  nonneg : ∀ i j, 0 ≤ m i j
  le1 : ∀ i j, m i j ≤ 1
  thin : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → m i j + m i k + m j k ≤ 2

namespace Cfg4

variable {x : Fin 4 → ℝ} {m : Fin 4 → Fin 4 → ℝ}

lemma thinK4 (H : Cfg4 x m) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ThinK4 (m i j) (m i k) (m i l) (m j k) (m j l) (m k l) where
  n12 := H.nonneg _ _
  n13 := H.nonneg _ _
  n14 := H.nonneg _ _
  n23 := H.nonneg _ _
  n24 := H.nonneg _ _
  n34 := H.nonneg _ _
  l12 := H.le1 _ _
  l13 := H.le1 _ _
  l14 := H.le1 _ _
  l23 := H.le1 _ _
  l24 := H.le1 _ _
  l34 := H.le1 _ _
  t123 := H.thin _ _ _ hij hik hjk
  t124 := H.thin _ _ _ hij hil hjl
  t134 := H.thin _ _ _ hik hil hkl
  t234 := H.thin _ _ _ hjk hjl hkl

lemma slack_all (H : Cfg4 x m) {s : ℝ}
    (h0 : 2 - m 0 1 - m 0 2 - m 1 2 ≤ s) (h1 : 2 - m 0 1 - m 0 3 - m 1 3 ≤ s)
    (h2 : 2 - m 0 2 - m 0 3 - m 2 3 ≤ s) (h3 : 2 - m 1 2 - m 1 3 - m 2 3 ≤ s) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 2 - m i j - m i k - m j k ≤ s := by
  have hs := H.symm
  have h01 := hs 0 1; have h02 := hs 0 2; have h03 := hs 0 3
  have h12 := hs 1 2; have h13 := hs 1 3; have h23 := hs 2 3
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp (config := {decide := true}) at hij hik hjk ⊢ <;>
    linarith only [h01, h02, h03, h12, h13, h23, h0, h1, h2, h3]

lemma nearMatched (H : Cfg4 x m) {s : ℝ}
    (hs : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 2 - m i j - m i k - m j k ≤ s) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    NearMatched (x i) (x j) (x k) (x l) (m i j) (m i k) (m i l) (m j k) (m j l) (m k l) s where
  xi0 := H.x0 _
  xj0 := H.x0 _
  xk0 := H.x0 _
  xl0 := H.x0 _
  sum := by rw [sum_x_perm hij hik hil hjk hjl hkl]; exact H.sum
  thin := H.thinK4 hij hik hil hjk hjl hkl
  sijk := hs _ _ _ hij hik hjk
  sijl := hs _ _ _ hij hil hjl
  sikl := hs _ _ _ hik hil hkl
  sjkl := hs _ _ _ hjk hjl hkl

end Cfg4

end NashWilliams.Frac
