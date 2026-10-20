/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassInverseStage73

/-! # Uniform bound for the constructed four-class inverse

The inverse uses no division by a demand and needs no positivity of demands.
The normalized coefficient bound is 18 times the maximum edge demand.
Rescaling therefore gives O(M/n) for classes of linear size.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassInverseStage73

open Finset FractionalAveragingStage72

variable {A B C D : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]

def EdgeBound (x : EdgeData A B C D) (M : ℝ) : Prop :=
  (∀ a b, |x.ab a b| ≤ M) ∧ (∀ a c, |x.ac a c| ≤ M) ∧
  (∀ a d, |x.ad a d| ≤ M) ∧ (∀ b c, |x.bc b c| ≤ M) ∧
  (∀ b d, |x.bd b d| ≤ M) ∧ (∀ c d, |x.cd c d| ≤ M)

def TriangleBound (w : TriangleData A B C D) (M : ℝ) : Prop :=
  (∀ a b c, |w.abc a b c| ≤ M) ∧ (∀ a b d, |w.abd a b d| ≤ M) ∧
  (∀ a c d, |w.acd a c d| ≤ M) ∧ (∀ b c d, |w.bcd b c d| ≤ M)

theorem component_bounds (f : A → B → ℝ) (M : ℝ) (hf : ∀ a b, |f a b| ≤ M) :
    |grandMean f| ≤ M ∧ (∀ a, |rowFluctuation f a| ≤ 2 * M) ∧
    (∀ b, |colFluctuation f b| ≤ 2 * M) ∧
    (∀ a b, |pairFluctuation f a b| ≤ 4 * M) := by
  have hm := abs_mean_le (fun a => mean (f a)) M
    (fun a => abs_mean_le (f a) M (hf a))
  change |grandMean f| ≤ M at hm
  refine ⟨hm, ?_, ?_, pair_abs_le f M hf⟩
  · intro a
    have hr := abs_mean_le (f a) M (hf a)
    have hs := abs_add_le (mean (f a)) (-grandMean f)
    rw [abs_neg, ← sub_eq_add_neg] at hs
    change |mean (f a) - grandMean f| ≤ 2 * M
    linarith
  · intro b
    have hc := abs_mean_le (fun a => f a b) M (fun a => hf a b)
    have hs := abs_add_le (mean (fun a => f a b)) (-grandMean f)
    rw [abs_neg, ← sub_eq_add_neg] at hs
    change |mean (fun a => f a b) - grandMean f| ≤ 2 * M
    linarith

theorem star_bound (x y z M : ℝ) (hx : |x| ≤ M) (hy : |y| ≤ M) (hz : |z| ≤ M) :
    |star x y z| ≤ 3 * M / 2 := by
  obtain ⟨hx0, hx1⟩ := abs_le.mp hx
  obtain ⟨hy0, hy1⟩ := abs_le.mp hy
  obtain ⟨hz0, hz1⟩ := abs_le.mp hz
  unfold star
  apply abs_le.mpr
  constructor <;> linarith

theorem half_bound (x M : ℝ) (hx : |x| ≤ 4 * M) : |x / 2| ≤ 2 * M := by
  rw [abs_div]
  norm_num
  linarith

theorem seven_term_bound (M u a b c x y z : ℝ)
    (hu : |u| ≤ 5 * M / 2) (ha : |a| ≤ 3 * M) (hb : |b| ≤ 3 * M)
    (hc : |c| ≤ 3 * M) (hx : |x| ≤ 2 * M) (hy : |y| ≤ 2 * M)
    (hz : |z| ≤ 2 * M) (hM : 0 ≤ M) :
    |u + a + b + c + x + y + z| ≤ 18 * M := by
  obtain ⟨hu0, hu1⟩ := abs_le.mp hu
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  obtain ⟨hb0, hb1⟩ := abs_le.mp hb
  obtain ⟨hc0, hc1⟩ := abs_le.mp hc
  obtain ⟨hx0, hx1⟩ := abs_le.mp hx
  obtain ⟨hy0, hy1⟩ := abs_le.mp hy
  obtain ⟨hz0, hz1⟩ := abs_le.mp hz
  apply abs_le.mpr
  constructor <;> linarith

theorem inverse_bound (x : EdgeData A B C D) (M : ℝ) (hM : 0 ≤ M)
    (hx : EdgeBound x M) : TriangleBound (inverse x) (18 * M) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hx
  obtain ⟨mab, rab, cab, qab⟩ := component_bounds x.ab M hab
  obtain ⟨mac, rac, cac, qac⟩ := component_bounds x.ac M hac
  obtain ⟨mad, rad, cad, qad⟩ := component_bounds x.ad M had
  obtain ⟨mbc, rbc, cbc, qbc⟩ := component_bounds x.bc M hbc
  obtain ⟨mbd, rbd, cbd, qbd⟩ := component_bounds x.bd M hbd
  obtain ⟨mcd, rcd, ccd, qcd⟩ := component_bounds x.cd M hcd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    have ht : |star (grandMean x.ab) (grandMean x.ac) (grandMean x.ad)| ≤ 5 * M / 2 := by
      have hh := star_bound _ _ _ M mab mac mad
      linarith
    apply seven_term_bound _ _ _ _ _ _ _ _ ht
    · have hh := star_bound _ _ _ (2 * M) (rab a) (rac a) (rad a)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cab b) (rbc b) (rbd b)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cac c) (cbc c) (rcd c)
      linarith
    · exact half_bound _ M (qab a b)
    · exact half_bound _ M (qac a c)
    · exact half_bound _ M (qbc b c)
    · exact hM
  · intro a b d
    have ht : |star (grandMean x.ab) (grandMean x.ad) (grandMean x.ac)| ≤ 5 * M / 2 := by
      have hh := star_bound _ _ _ M mab mad mac
      linarith
    apply seven_term_bound _ _ _ _ _ _ _ _ ht
    · have hh := star_bound _ _ _ (2 * M) (rab a) (rad a) (rac a)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cab b) (rbd b) (rbc b)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cad d) (cbd d) (ccd d)
      linarith
    · exact half_bound _ M (qab a b)
    · exact half_bound _ M (qad a d)
    · exact half_bound _ M (qbd b d)
    · exact hM
  · intro a c d
    have ht : |star (grandMean x.ac) (grandMean x.ad) (grandMean x.ab)| ≤ 5 * M / 2 := by
      have hh := star_bound _ _ _ M mac mad mab
      linarith
    apply seven_term_bound _ _ _ _ _ _ _ _ ht
    · have hh := star_bound _ _ _ (2 * M) (rac a) (rad a) (rab a)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cac c) (rcd c) (cbc c)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cad d) (ccd d) (cbd d)
      linarith
    · exact half_bound _ M (qac a c)
    · exact half_bound _ M (qad a d)
    · exact half_bound _ M (qcd c d)
    · exact hM
  · intro b c d
    have ht : |grandMean x.bc -
        star (grandMean x.ab) (grandMean x.ac) (grandMean x.ad)| ≤ 5 * M / 2 := by
      have hh := star_bound _ _ _ M mab mac mad
      have hs := abs_add_le (grandMean x.bc)
        (-star (grandMean x.ab) (grandMean x.ac) (grandMean x.ad))
      rw [abs_neg, ← sub_eq_add_neg] at hs
      change |grandMean x.bc - star (grandMean x.ab) (grandMean x.ac) (grandMean x.ad)| ≤ _
      linarith
    apply seven_term_bound _ _ _ _ _ _ _ _ ht
    · have hh := star_bound _ _ _ (2 * M) (rbc b) (rbd b) (cab b)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cbc c) (rcd c) (cac c)
      linarith
    · have hh := star_bound _ _ _ (2 * M) (cbd d) (ccd d) (cad d)
      linarith
    · exact half_bound _ M (qbc b c)
    · exact half_bound _ M (qbd b d)
    · exact half_bound _ M (qcd c d)
    · exact hM

/-- Constructs the normalized inverse and proves its six loads and four caps. -/
theorem exists_bounded_inverse (x : EdgeData A B C D) (hx : Balanced x)
    (M : ℝ) (hM : 0 ≤ M) (hbound : EdgeBound x M) :
    ∃ w : TriangleData A B C D, boundary w = x ∧ TriangleBound w (18 * M) :=
  ⟨inverse x, boundary_inverse x hx, inverse_bound x M hM hbound⟩

end PartitionedTriangleAbsorption.FourClassInverseStage73

