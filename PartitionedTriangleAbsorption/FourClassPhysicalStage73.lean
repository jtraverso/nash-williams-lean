/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassBoundStage73

/-! # Actual marginal sums for the four-class inverse

Product coordinates name vertices in three distinct classes; the boundary
counts each triangle once at each of its three edges. This removes normalized
means and proves the uniform 18 M / (gamma^3 n) cap. Conversion to arbitrary
vertex labels and to the existing copies/edgeLoad API remains separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassInverseStage73

open Finset FractionalAveragingStage72

variable {A B C D : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]

noncomputable def normalize (x : EdgeData A B C D) : EdgeData A B C D where
  ab a b := (Fintype.card A : ℝ) * Fintype.card B * x.ab a b
  ac a c := (Fintype.card A : ℝ) * Fintype.card C * x.ac a c
  ad a d := (Fintype.card A : ℝ) * Fintype.card D * x.ad a d
  bc b c := (Fintype.card B : ℝ) * Fintype.card C * x.bc b c
  bd b d := (Fintype.card B : ℝ) * Fintype.card D * x.bd b d
  cd c d := (Fintype.card C : ℝ) * Fintype.card D * x.cd c d

def RawBalanced (x : EdgeData A B C D) : Prop :=
  (∑ a, ∑ b, x.ab a b) + (∑ c, ∑ d, x.cd c d) =
    (∑ a, ∑ c, x.ac a c) + (∑ b, ∑ d, x.bd b d) ∧
  (∑ a, ∑ b, x.ab a b) + (∑ c, ∑ d, x.cd c d) =
    (∑ a, ∑ d, x.ad a d) + (∑ b, ∑ c, x.bc b c)

theorem normalize_grandMean (f : A → B → ℝ) :
    grandMean (fun a b => (Fintype.card A : ℝ) * Fintype.card B * f a b) =
      ∑ a, ∑ b, f a b := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold grandMean mean
  simp only [← sum_div, ← mul_sum]
  field_simp

theorem balanced_normalize_iff (x : EdgeData A B C D) :
    Balanced (normalize x) ↔ RawBalanced x := by
  simp only [Balanced, normalize, normalize_grandMean, RawBalanced]

noncomputable def descaleEdges (x : EdgeData A B C D) : EdgeData A B C D where
  ab a b := x.ab a b / ((Fintype.card A : ℝ) * Fintype.card B)
  ac a c := x.ac a c / ((Fintype.card A : ℝ) * Fintype.card C)
  ad a d := x.ad a d / ((Fintype.card A : ℝ) * Fintype.card D)
  bc b c := x.bc b c / ((Fintype.card B : ℝ) * Fintype.card C)
  bd b d := x.bd b d / ((Fintype.card B : ℝ) * Fintype.card D)
  cd c d := x.cd c d / ((Fintype.card C : ℝ) * Fintype.card D)

noncomputable def descale (w : TriangleData A B C D) : TriangleData A B C D where
  abc a b c := w.abc a b c /
    ((Fintype.card A : ℝ) * Fintype.card B * Fintype.card C)
  abd a b d := w.abd a b d /
    ((Fintype.card A : ℝ) * Fintype.card B * Fintype.card D)
  acd a c d := w.acd a c d /
    ((Fintype.card A : ℝ) * Fintype.card C * Fintype.card D)
  bcd b c d := w.bcd b c d /
    ((Fintype.card B : ℝ) * Fintype.card C * Fintype.card D)

noncomputable def physicalBoundary (w : TriangleData A B C D) : EdgeData A B C D where
  ab a b := (∑ c, w.abc a b c) + ∑ d, w.abd a b d
  ac a c := (∑ b, w.abc a b c) + ∑ d, w.acd a c d
  ad a d := (∑ b, w.abd a b d) + ∑ c, w.acd a c d
  bc b c := (∑ a, w.abc a b c) + ∑ d, w.bcd b c d
  bd b d := (∑ a, w.abd a b d) + ∑ c, w.bcd b c d
  cd c d := (∑ a, w.acd a c d) + ∑ b, w.bcd b c d

omit [Nonempty A] [Nonempty B] in
theorem weighted_marginal (f : A → ℝ) (g : B → ℝ) (a b : ℝ) :
    (∑ u, f u / (a * b * Fintype.card A)) +
      (∑ v, g v / (a * b * Fintype.card B)) =
      (mean f + mean g) / (a * b) := by
  simp only [← sum_div, mean, add_div, div_div]
  congr 1 <;> congr 1 <;> ring

omit [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] in
theorem physical_boundary_descale (w : TriangleData A B C D) :
    physicalBoundary (descale w) = descaleEdges (boundary w) := by
  change EdgeData.mk _ _ _ _ _ _ = EdgeData.mk _ _ _ _ _ _
  congr 1
  · funext a b
    simpa only [descale, boundary, descaleEdges, mul_assoc, mul_left_comm, mul_comm] using
      weighted_marginal (w.abc a b) (w.abd a b)
        (Fintype.card A : ℝ) (Fintype.card B : ℝ)
  · funext a c
    simpa only [descale, boundary, descaleEdges, mul_assoc, mul_left_comm, mul_comm] using
      weighted_marginal (fun b => w.abc a b c) (w.acd a c)
        (Fintype.card A : ℝ) (Fintype.card C : ℝ)
  · funext a d
    simpa only [descale, boundary, descaleEdges, mul_assoc, mul_left_comm, mul_comm] using
      weighted_marginal (fun b => w.abd a b d) (fun c => w.acd a c d)
        (Fintype.card A : ℝ) (Fintype.card D : ℝ)
  · funext b c
    simpa only [descale, boundary, descaleEdges, mul_assoc, mul_left_comm, mul_comm] using
      weighted_marginal (fun a => w.abc a b c) (w.bcd b c)
        (Fintype.card B : ℝ) (Fintype.card C : ℝ)
  · funext b d
    simpa only [descale, boundary, descaleEdges, mul_assoc, mul_left_comm, mul_comm] using
      weighted_marginal (fun a => w.abd a b d) (fun c => w.bcd b c d)
        (Fintype.card B : ℝ) (Fintype.card D : ℝ)
  · funext c d
    simpa only [descale, boundary, descaleEdges, mul_assoc, mul_left_comm, mul_comm] using
      weighted_marginal (fun a => w.acd a c d) (fun b => w.bcd b c d)
        (Fintype.card C : ℝ) (Fintype.card D : ℝ)

theorem descale_normalize (x : EdgeData A B C D) : descaleEdges (normalize x) = x := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hC : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  cases x
  change EdgeData.mk _ _ _ _ _ _ = EdgeData.mk _ _ _ _ _ _
  congr 1
  · funext a b
    simp only [normalize]
    field_simp
  · funext a c
    simp only [normalize]
    field_simp
  · funext a d
    simp only [normalize]
    field_simp
  · funext b c
    simp only [normalize]
    field_simp
  · funext b d
    simp only [normalize]
    field_simp
  · funext c d
    simp only [normalize]
    field_simp

theorem pair_scale_bound (a b n M x : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ n) (hb : b ≤ n) (hM : 0 ≤ M) (hx : |x| ≤ M) :
    |a * b * x| ≤ n ^ 2 * M := by
  rw [abs_mul, abs_of_nonneg (mul_nonneg ha0 hb0)]
  have hp : a * b ≤ n * n := mul_le_mul ha hb hb0 (ha0.trans ha)
  calc
    a * b * |x| ≤ a * b * M := mul_le_mul_of_nonneg_left hx (mul_nonneg ha0 hb0)
    _ ≤ n * n * M := mul_le_mul_of_nonneg_right hp hM
    _ = n ^ 2 * M := by ring

omit [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] in
theorem normalize_bound (x : EdgeData A B C D) (n M : ℝ) (hM : 0 ≤ M)
    (hA : (Fintype.card A : ℝ) ≤ n) (hB : (Fintype.card B : ℝ) ≤ n)
    (hC : (Fintype.card C : ℝ) ≤ n) (hD : (Fintype.card D : ℝ) ≤ n)
    (hx : EdgeBound x M) : EdgeBound (normalize x) (n ^ 2 * M) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact pair_scale_bound _ _ n M _ (by positivity) (by positivity)
      hA hB hM (hab a b)
  · intro a c
    exact pair_scale_bound _ _ n M _ (by positivity) (by positivity)
      hA hC hM (hac a c)
  · intro a d
    exact pair_scale_bound _ _ n M _ (by positivity) (by positivity)
      hA hD hM (had a d)
  · intro b c
    exact pair_scale_bound _ _ n M _ (by positivity) (by positivity)
      hB hC hM (hbc b c)
  · intro b d
    exact pair_scale_bound _ _ n M _ (by positivity) (by positivity)
      hB hD hM (hbd b d)
  · intro c d
    exact pair_scale_bound _ _ n M _ (by positivity) (by positivity)
      hC hD hM (hcd c d)

theorem triple_descale_bound (a b c n gamma M w : ℝ)
    (hn : 0 < n) (hg : 0 < gamma) (hM : 0 ≤ M)
    (ha : gamma * n ≤ a) (hb : gamma * n ≤ b) (hc : gamma * n ≤ c)
    (hw : |w| ≤ 18 * (n ^ 2 * M)) :
    |w / (a * b * c)| ≤ 18 * M / (gamma ^ 3 * n) := by
  have hgn : 0 < gamma * n := by positivity
  have ha0 : 0 < a := hgn.trans_le ha
  have hb0 : 0 < b := hgn.trans_le hb
  have hc0 : 0 < c := hgn.trans_le hc
  have hp : gamma * n * (gamma * n) * (gamma * n) ≤ a * b * c :=
    mul_le_mul (mul_le_mul ha hb hgn.le ha0.le) hc hgn.le
      (mul_nonneg ha0.le hb0.le)
  rw [abs_div, abs_of_pos (show 0 < a * b * c by positivity)]
  calc
    |w| / (a * b * c) ≤ 18 * (n ^ 2 * M) / (a * b * c) :=
      div_le_div_of_nonneg_right hw (by positivity)
    _ ≤ 18 * (n ^ 2 * M) / (gamma * n * (gamma * n) * (gamma * n)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = 18 * M / (gamma ^ 3 * n) := by field_simp

/-- Constructs signed weights with actual six marginal sums and an n-uniform cap.
The balance is exactly on the six total edge demands, not on individual rows. -/
theorem complete_four_class_inverse (x : EdgeData A B C D) (hx : Balanced (normalize x))
    (n gamma M : ℝ) (hn : 0 < n) (hg : 0 < gamma) (hM : 0 ≤ M)
    (hA : (Fintype.card A : ℝ) ≤ n) (hB : (Fintype.card B : ℝ) ≤ n)
    (hC : (Fintype.card C : ℝ) ≤ n) (hD : (Fintype.card D : ℝ) ≤ n)
    (ha : gamma * n ≤ (Fintype.card A : ℝ))
    (hb : gamma * n ≤ (Fintype.card B : ℝ))
    (hc : gamma * n ≤ (Fintype.card C : ℝ))
    (hd : gamma * n ≤ (Fintype.card D : ℝ)) (hbound : EdgeBound x M) :
    ∃ w : TriangleData A B C D, physicalBoundary w = x ∧
      TriangleBound w (18 * M / (gamma ^ 3 * n)) := by
  have hnorm := normalize_bound x n M hM hA hB hC hD hbound
  obtain ⟨w, hw, hcap⟩ := exists_bounded_inverse (normalize x) hx (n ^ 2 * M)
    (by positivity) hnorm
  refine ⟨descale w, ?_, ?_⟩
  · rw [physical_boundary_descale, hw, descale_normalize]
  · obtain ⟨habc, habd, hacd, hbcd⟩ := hcap
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b c
      exact triple_descale_bound _ _ _ n gamma M _ hn hg hM
        ha hb hc (habc a b c)
    · intro a b d
      exact triple_descale_bound _ _ _ n gamma M _ hn hg hM
        ha hb hd (habd a b d)
    · intro a c d
      exact triple_descale_bound _ _ _ n gamma M _ hn hg hM
        ha hc hd (hacd a c d)
    · intro b c d
      exact triple_descale_bound _ _ _ n gamma M _ hn hg hM
        hb hc hd (hbcd b c d)

end PartitionedTriangleAbsorption.FourClassInverseStage73

