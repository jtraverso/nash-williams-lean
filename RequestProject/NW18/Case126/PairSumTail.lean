/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.MaxCut
public import RequestProject.NW18.Sampling.Counts

@[expose] public section

/-!
# Concentration of sums of two-coordinate indicators in a Bernoulli product space

Used to sample the protected cross reserve of an `F₁` vortex level.  A sum
`∑_{z ∈ C} g (ω (k₁ z)) (ω (k₂ z))` with `g ∈ [0, 1]`, where different `z` read disjoint
coordinates, has coordinate gaps `≤ 1` on at most `2 |C|` coordinates, so it is within `t` of its
mean except with probability `≤ 2 exp(-t² / (2 (2|C| + t)))` (`pairSum_tail`).
-/

namespace NashWilliams18.SpreadF1

open Finset Pseudorandom NashWilliams18.Sampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*} [DecidableEq V]

/-- Independent Bernoulli(`ρ`) coordinates. -/
noncomputable def bern (ρ : ℝ) : ι → Bool → ℝ := fun _ x => if x then ρ else 1 - ρ

omit [Fintype ι] [DecidableEq ι] in
lemma bern_isPMF {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : IsPMF (bern (ι := ι) ρ) := by
  refine ⟨fun _ x => ?_, fun _ => ?_⟩
  · cases x <;> simp [bern] <;> linarith
  · simp [bern]

/-- A sum of two-coordinate terms. -/
def pairSum (k₁ k₂ : V → ι) (C : Finset V) (g : Bool → Bool → ℝ) (ω : ι → Bool) : ℝ :=
  ∑ z ∈ C, g (ω (k₁ z)) (ω (k₂ z))

/-- The coordinates read by a pair sum. -/
noncomputable def pairCoef (k₁ k₂ : V → ι) (C : Finset V) (i : ι) : ℝ := by
  classical exact if ∃ z ∈ C, k₁ z = i ∨ k₂ z = i then 1 else 0

omit [Fintype ι] [DecidableEq V] in
lemma pairSum_coordGap (k₁ k₂ : V → ι) (C : Finset V) (g : Bool → Bool → ℝ)
    (hg0 : ∀ x y, 0 ≤ g x y) (hg1 : ∀ x y, g x y ≤ 1)
    (hk₁ : Set.InjOn k₁ C) (hk₂ : Set.InjOn k₂ C)
    (hk : ∀ z ∈ C, ∀ z' ∈ C, k₁ z = k₂ z' → z = z') :
    CoordGap (pairSum k₁ k₂ C g) (pairCoef k₁ k₂ C) := by
  classical
  intro i ω u v
  unfold pairSum pairCoef
  rw [← sum_sub_distrib]
  split_ifs with hi
  · obtain ⟨z₀, hz₀, hz₀i⟩ := hi
    rw [sum_eq_single z₀]
    · have a1 := hg0 (Function.update ω i u (k₁ z₀)) (Function.update ω i u (k₂ z₀))
      have a2 := hg1 (Function.update ω i u (k₁ z₀)) (Function.update ω i u (k₂ z₀))
      have a3 := hg0 (Function.update ω i v (k₁ z₀)) (Function.update ω i v (k₂ z₀))
      have a4 := hg1 (Function.update ω i v (k₁ z₀)) (Function.update ω i v (k₂ z₀))
      rw [abs_le]; constructor <;> linarith
    · intro z hz hne
      have h1 : k₁ z ≠ i := by
        intro h
        rcases hz₀i with h' | h'
        · exact hne (hk₁ hz hz₀ (h.trans h'.symm))
        · exact hne (hk z hz z₀ hz₀ (h.trans h'.symm))
      have h2 : k₂ z ≠ i := by
        intro h
        rcases hz₀i with h' | h'
        · exact hne (hk z₀ hz₀ z hz (h'.trans h.symm)).symm
        · exact hne (hk₂ hz hz₀ (h.trans h'.symm))
      simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · intro h; exact absurd hz₀ h
  · push_neg at hi
    rw [sum_eq_zero]
    · simp
    · intro z hz
      simp [Function.update_of_ne (hi z hz).1, Function.update_of_ne (hi z hz).2]

omit [DecidableEq V] in
lemma pairCoef_sq_sum (k₁ k₂ : V → ι) (C : Finset V) :
    ∑ i, pairCoef k₁ k₂ C i ^ 2 ≤ 2 * C.card := by
  classical
  have e : ∀ i, pairCoef k₁ k₂ C i ^ 2 =
      if ∃ z ∈ C, k₁ z = i ∨ k₂ z = i then (1 : ℝ) else 0 := by
    intro i; unfold pairCoef; split_ifs <;> norm_num
  simp_rw [e]
  rw [sum_boole]
  have hsub : (univ.filter fun i => ∃ z ∈ C, k₁ z = i ∨ k₂ z = i) ⊆
      C.image k₁ ∪ C.image k₂ := by
    intro i hi
    obtain ⟨z, hz, h | h⟩ := (mem_filter.mp hi).2
    · exact mem_union_left _ (mem_image.mpr ⟨z, hz, h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨z, hz, h⟩)
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 := card_image_le (s := C) (f := k₁)
  have h3 := card_image_le (s := C) (f := k₂)
  have : ((univ.filter fun i => ∃ z ∈ C, k₁ z = i ∨ k₂ z = i).card : ℝ) ≤ 2 * C.card := by
    have : (univ.filter fun i => ∃ z ∈ C, k₁ z = i ∨ k₂ z = i).card ≤ 2 * C.card := by omega
    exact_mod_cast this
  simpa using this

omit [DecidableEq V] in
/-- **Two-sided tail of a pair sum.** -/
theorem pairSum_tail {P : ι → Bool → ℝ} (hP : IsPMF P) (k₁ k₂ : V → ι) (C : Finset V)
    (g : Bool → Bool → ℝ) (hg0 : ∀ x y, 0 ≤ g x y) (hg1 : ∀ x y, g x y ≤ 1)
    (hk₁ : Set.InjOn k₁ C) (hk₂ : Set.InjOn k₂ C)
    (hk : ∀ z ∈ C, ∀ z' ∈ C, k₁ z = k₂ z' → z = z') (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ |pairSum k₁ k₂ C g ω - pE P (pairSum k₁ k₂ C g)|) ≤
      2 * Real.exp (-(t ^ 2 / (2 * (2 * C.card + t)))) := by
  classical
  have hgap := pairSum_coordGap k₁ k₂ C g hg0 hg1 hk₁ hk₂ hk
  have hc : ∀ i, 0 ≤ pairCoef k₁ k₂ C i ∧ pairCoef k₁ k₂ C i ≤ 1 := by
    intro i; unfold pairCoef; split_ifs <;> norm_num
  have hu := upper_tail hP (pairSum k₁ k₂ C g) (pairCoef k₁ k₂ C) 1 one_pos hc hgap t ht
  have hl := lower_tail hP (pairSum k₁ k₂ C g) (pairCoef k₁ k₂ C) 1 one_pos hc hgap t ht
  have hS := pairCoef_sq_sum k₁ k₂ C
  have hS0 : 0 ≤ ∑ i, pairCoef k₁ k₂ C i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hmono := exp_mono_aux (t := t) (A := ∑ i, pairCoef k₁ k₂ C i ^ 2)
    (B := 2 * C.card) (by linarith) hS
  rw [one_mul] at hu hl
  calc pProb P (fun ω => t ≤ |pairSum k₁ k₂ C g ω - pE P (pairSum k₁ k₂ C g)|)
      ≤ pProb P (fun ω => t ≤ pairSum k₁ k₂ C g ω - pE P (pairSum k₁ k₂ C g) ∨
          t ≤ pE P (pairSum k₁ k₂ C g) - pairSum k₁ k₂ C g ω) := by
        refine pProb_mono hP fun ω hω => ?_
        rcases le_abs'.mp hω with h | h
        · right; linarith
        · left; exact h
    _ ≤ _ := pProb_or_le hP _ _
    _ ≤ 2 * Real.exp (-(t ^ 2 / (2 * (2 * C.card + t)))) := by linarith

end NashWilliams18.SpreadF1
