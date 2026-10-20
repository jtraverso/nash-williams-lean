/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FractionalAveragingStage72

/-! # An explicit right inverse for the complete four-class incidence map

Edge coordinates are normalized by the product of the two class sizes.
Triangle coordinates are normalized by the product of the three class sizes.
Thus the boundary uses finite means. This constructs the complete inverse,
rather than assuming an inverse or supplying an arbitrary correction.
The adapter to physical copies after edge deletion is a separate obligation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassInverseStage73

open Finset FractionalAveragingStage72

variable {A B C D : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]

structure EdgeData (A B C D : Type*) where
  ab : A → B → ℝ
  ac : A → C → ℝ
  ad : A → D → ℝ
  bc : B → C → ℝ
  bd : B → D → ℝ
  cd : C → D → ℝ

structure TriangleData (A B C D : Type*) where
  abc : A → B → C → ℝ
  abd : A → B → D → ℝ
  acd : A → C → D → ℝ
  bcd : B → C → D → ℝ

noncomputable def boundary (w : TriangleData A B C D) : EdgeData A B C D where
  ab a b := mean (w.abc a b) + mean (w.abd a b)
  ac a c := mean (fun b => w.abc a b c) + mean (w.acd a c)
  ad a d := mean (fun b => w.abd a b d) + mean (fun c => w.acd a c d)
  bc b c := mean (fun a => w.abc a b c) + mean (w.bcd b c)
  bd b d := mean (fun a => w.abd a b d) + mean (fun c => w.bcd b c d)
  cd c d := mean (fun a => w.acd a c d) + mean (fun b => w.bcd b c d)

def Balanced (x : EdgeData A B C D) : Prop :=
  grandMean x.ab + grandMean x.cd = grandMean x.ac + grandMean x.bd ∧
  grandMean x.ab + grandMean x.cd = grandMean x.ad + grandMean x.bc

omit [Nonempty A] in
theorem mean_div (f : A → ℝ) (z : ℝ) :
    mean (fun a => f a / z) = mean f / z := by
  simp only [mean, ← sum_div, div_div]
  rw [mul_comm z]

omit [Nonempty B] in
theorem mean_row (f : A → B → ℝ) : mean (rowFluctuation f) = 0 := by
  change mean (fun a => mean (f a) - grandMean f) = 0
  rw [mean_sub, mean_const]
  change grandMean f - grandMean f = 0
  ring

omit [Nonempty A] in
theorem mean_col (f : A → B → ℝ) : mean (colFluctuation f) = 0 := by
  change mean (fun b => mean (fun a => f a b) - grandMean f) = 0
  rw [mean_sub, mean_const]
  rw [← mean_comm]
  change grandMean f - grandMean f = 0
  ring

/-- A root contributes to the two types through each incident pair. -/
noncomputable def star (x y z : ℝ) : ℝ := (x + y - z) / 2

noncomputable def inverse (x : EdgeData A B C D) : TriangleData A B C D where
  abc a b c :=
    star (grandMean x.ab) (grandMean x.ac) (grandMean x.ad) +
    star (rowFluctuation x.ab a) (rowFluctuation x.ac a) (rowFluctuation x.ad a) +
    star (colFluctuation x.ab b) (rowFluctuation x.bc b) (rowFluctuation x.bd b) +
    star (colFluctuation x.ac c) (colFluctuation x.bc c) (rowFluctuation x.cd c) +
    pairFluctuation x.ab a b / 2 + pairFluctuation x.ac a c / 2 +
    pairFluctuation x.bc b c / 2
  abd a b d :=
    star (grandMean x.ab) (grandMean x.ad) (grandMean x.ac) +
    star (rowFluctuation x.ab a) (rowFluctuation x.ad a) (rowFluctuation x.ac a) +
    star (colFluctuation x.ab b) (rowFluctuation x.bd b) (rowFluctuation x.bc b) +
    star (colFluctuation x.ad d) (colFluctuation x.bd d) (colFluctuation x.cd d) +
    pairFluctuation x.ab a b / 2 + pairFluctuation x.ad a d / 2 +
    pairFluctuation x.bd b d / 2
  acd a c d :=
    star (grandMean x.ac) (grandMean x.ad) (grandMean x.ab) +
    star (rowFluctuation x.ac a) (rowFluctuation x.ad a) (rowFluctuation x.ab a) +
    star (colFluctuation x.ac c) (rowFluctuation x.cd c) (colFluctuation x.bc c) +
    star (colFluctuation x.ad d) (colFluctuation x.cd d) (colFluctuation x.bd d) +
    pairFluctuation x.ac a c / 2 + pairFluctuation x.ad a d / 2 +
    pairFluctuation x.cd c d / 2
  bcd b c d :=
    grandMean x.bc - star (grandMean x.ab) (grandMean x.ac) (grandMean x.ad) +
    star (rowFluctuation x.bc b) (rowFluctuation x.bd b) (colFluctuation x.ab b) +
    star (colFluctuation x.bc c) (rowFluctuation x.cd c) (colFluctuation x.ac c) +
    star (colFluctuation x.bd d) (colFluctuation x.cd d) (colFluctuation x.ad d) +
    pairFluctuation x.bc b c / 2 + pairFluctuation x.bd b d / 2 +
    pairFluctuation x.cd c d / 2

theorem boundary_inverse (x : EdgeData A B C D) (hx : Balanced x) :
    boundary (inverse x) = x := by
  obtain ⟨ha, hb⟩ := hx
  cases x with
  | mk ab ac ad bc bd cd =>
    change EdgeData.mk _ _ _ _ _ _ = EdgeData.mk ab ac ad bc bd cd
    congr 1
    · funext a b
      simp only [inverse, star, mean_add, mean_sub, mean_div, mean_const,
        mean_row, mean_col, pair_mean_row, sub_self, zero_div, add_zero]
      have hs := demand_split ab a b
      linarith
    · funext a c
      simp only [inverse, star, mean_add, mean_sub, mean_div, mean_const,
        mean_row, mean_col, pair_mean_row, pair_mean_col, sub_self, zero_div, add_zero]
      have hs := demand_split ac a c
      linarith
    · funext a d
      simp only [inverse, star, mean_add, mean_sub, mean_div, mean_const,
        mean_row, mean_col, pair_mean_row, pair_mean_col, sub_self, zero_div, add_zero]
      have hs := demand_split ad a d
      linarith
    · funext b c
      simp only [inverse, star, mean_add, mean_sub, mean_div, mean_const,
        mean_row, mean_col, pair_mean_row, pair_mean_col, sub_self, zero_div, add_zero]
      have hs := demand_split bc b c
      linarith
    · funext b d
      simp only [inverse, star, mean_add, mean_sub, mean_div, mean_const,
        mean_row, mean_col, pair_mean_row, pair_mean_col, sub_self, zero_div, add_zero]
      have hs := demand_split bd b d
      change grandMean ab + grandMean cd = grandMean ac + grandMean bd at ha
      change grandMean ab + grandMean cd = grandMean ad + grandMean bc at hb
      linarith
    · funext c d
      simp only [inverse, star, mean_add, mean_sub, mean_div, mean_const,
        mean_row, mean_col, pair_mean_col, sub_self, zero_div, add_zero]
      have hs := demand_split cd c d
      change grandMean ab + grandMean cd = grandMean ac + grandMean bd at ha
      change grandMean ab + grandMean cd = grandMean ad + grandMean bc at hb
      linarith

end PartitionedTriangleAbsorption.FourClassInverseStage73

