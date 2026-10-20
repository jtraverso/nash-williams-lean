/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.LocalInverseBound
public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealProfileBounds

@[expose] public section

/-! # Typed ternary weights for the general real inverse

Ordered-triple weights of the form `∑ τ ∈ F, χ_τ(a,b,c) * X_τ(a,b,c)` are
symmetric and supported on admissible triples. They are transported to actual
`TriangleChain`s supported on permitted copies of `activeCompleteGraph p F`,
with boundary equal to the ternary edge load. The basic third-vertex sum is
computed exactly. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Indicator of an ordered triple of distinct vertices of type `τ`. -/
def chi (p : V → Fin 4) (τ : Multiset (Fin 4)) (a b c : V) : ℝ :=
  if a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ({p a, p b, p c} : Multiset (Fin 4)) = τ then 1 else 0

omit [Fintype V] in
theorem chi_swap12 (p : V → Fin 4) (τ : Multiset (Fin 4)) (a b c : V) :
    chi p τ a b c = chi p τ b a c := by
  have hm : ({p a, p b, p c} : Multiset (Fin 4)) = {p b, p a, p c} :=
    Multiset.cons_swap _ _ _
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ({p a, p b, p c} : Multiset (Fin 4)) = τ
  · have h' : b ≠ a ∧ b ≠ c ∧ a ≠ c ∧ ({p b, p a, p c} : Multiset (Fin 4)) = τ :=
      ⟨h.1.symm, h.2.2.1, h.2.1, hm ▸ h.2.2.2⟩
    rw [chi, chi, if_pos h, if_pos h']
  · have h' : ¬ (b ≠ a ∧ b ≠ c ∧ a ≠ c ∧ ({p b, p a, p c} : Multiset (Fin 4)) = τ) :=
      fun h' => h ⟨h'.1.symm, h'.2.2.1, h'.2.1, hm.symm ▸ h'.2.2.2⟩
    rw [chi, chi, if_neg h, if_neg h']

omit [Fintype V] in
theorem chi_swap23 (p : V → Fin 4) (τ : Multiset (Fin 4)) (a b c : V) :
    chi p τ a b c = chi p τ a c b := by
  have hm : ({p a, p b, p c} : Multiset (Fin 4)) = {p a, p c, p b} := by
    show p a ::ₘ ({p b, p c} : Multiset (Fin 4)) = p a ::ₘ {p c, p b}
    rw [Multiset.pair_comm]
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ({p a, p b, p c} : Multiset (Fin 4)) = τ
  · have h' : a ≠ c ∧ a ≠ b ∧ c ≠ b ∧ ({p a, p c, p b} : Multiset (Fin 4)) = τ :=
      ⟨h.2.1, h.1, h.2.2.1.symm, hm ▸ h.2.2.2⟩
    rw [chi, chi, if_pos h, if_pos h']
  · have h' : ¬ (a ≠ c ∧ a ≠ b ∧ c ≠ b ∧ ({p a, p c, p b} : Multiset (Fin 4)) = τ) :=
      fun h' => h ⟨h'.2.1, h'.1, h'.2.2.1.symm, hm.symm ▸ h'.2.2.2⟩
    rw [chi, chi, if_neg h, if_neg h']

omit [Fintype V] in
theorem chi_self12 (p : V → Fin 4) (τ : Multiset (Fin 4)) (a c : V) : chi p τ a a c = 0 := by
  simp [chi]

/-- The typed ternary weight with components `X τ`. -/
def typedWeight (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (X : Multiset (Fin 4) → V → V → V → ℝ) (a b c : V) : ℝ :=
  ∑ τ ∈ F, chi p τ a b c * X τ a b c

omit [Fintype V] in
theorem typedWeight_eq (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (X : Multiset (Fin 4) → V → V → V → ℝ) (a b c : V) :
    typedWeight p F X a b c =
      if a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ({p a, p b, p c} : Multiset (Fin 4)) ∈ F then
        X {p a, p b, p c} a b c else 0 := by
  unfold typedWeight chi
  by_cases hd : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨h1, h2, h3⟩ := hd
    simp only [h1, h2, h3, ne_eq, not_false_eq_true, true_and, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq]
  · have : ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ({p a, p b, p c} : Multiset (Fin 4)) ∈ F) :=
      fun h => hd ⟨h.1, h.2.1, h.2.2.1⟩
    rw [if_neg this]
    apply sum_eq_zero
    intro τ _
    rw [if_neg (fun h => hd ⟨h.1, h.2.1, h.2.2.1⟩), zero_mul]

omit [Fintype V] in
theorem typedWeight_supported (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (X : Multiset (Fin 4) → V → V → V → ℝ) :
    TernarySupported p F (typedWeight p F X) := by
  intro a b c h
  rw [typedWeight_eq, if_neg]
  intro h'
  exact h ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩

omit [Fintype V] in
theorem typedWeight_symmetric (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (X : Multiset (Fin 4) → V → V → V → ℝ) (hX : ∀ τ, TernarySymmetric (X τ)) :
    TernarySymmetric (typedWeight p F X) := by
  constructor
  · intro a b c
    unfold typedWeight
    apply sum_congr rfl
    intro τ _
    rw [chi_swap12, (hX τ).1 a b c]
  · intro a b c
    unfold typedWeight
    apply sum_congr rfl
    intro τ _
    rw [chi_swap23, (hX τ).2 a b c]

omit [Fintype V] in
theorem typedWeight_bound (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (X : Multiset (Fin 4) → V → V → V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hX : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ({p a, p b, p c} : Multiset (Fin 4)) ∈ F →
      |X {p a, p b, p c} a b c| ≤ M) (a b c : V) :
    |typedWeight p F X a b c| ≤ M := by
  rw [typedWeight_eq]
  split_ifs with h
  · exact hX a b c h.1 h.2.1 h.2.2.1 h.2.2.2
  · simpa using hM

theorem load_typedWeight (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (X : Multiset (Fin 4) → V → V → V → ℝ) (x y : V) :
    ternaryLoad (typedWeight p F X) x y =
      ∑ τ ∈ F, ternaryLoad (fun a b c => chi p τ a b c * X τ a b c) x y := by
  unfold ternaryLoad typedWeight
  exact sum_comm

omit [DecidableEq V] in
theorem abs_ternaryLoad_le (w : V → V → V → ℝ) (M : ℝ)
    (hM : ∀ a b c, |w a b c| ≤ M) (x y : V) :
    |ternaryLoad w x y| ≤ (Fintype.card V : ℝ) * M := by
  unfold ternaryLoad
  calc
    |∑ c, w x y c| ≤ ∑ c, |w x y c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : V, M := sum_le_sum fun c _ => hM x y c
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-! ### Transport to actual triangle chains -/

/-- The actual triangle chain of a ternary weight. -/
def chainOf (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (w : V → V → V → ℝ) : TriangleChain V :=
  copyRestriction p F (activeCompleteGraph p F) (ternaryToWeight w)

theorem chainOf_supported (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (w : V → V → V → ℝ) :
    CopySupported p F (activeCompleteGraph p F) (chainOf p F w) :=
  copyRestriction_supported p F _ _

theorem chainOf_boundary (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    {w : V → V → V → ℝ} (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    (a b : V) : boundary (chainOf p F w) s(a, b) = ternaryLoad w a b := by
  unfold chainOf
  rw [copyRestriction_boundary]
  by_cases hab : a = b
  · subst b
    rw [copy_load_diag, hsup.load_diag]
  · exact ternaryToWeight_load p F hsym hsup hab

omit [Fintype V] in
theorem chainOf_bound (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    {w : V → V → V → ℝ} (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ a b c, |w a b c| ≤ M) (T : Finset V) :
    |chainOf p F w T| ≤ M := by
  unfold chainOf copyRestriction
  split_ifs with hT
  · exact ternaryToWeight_bound hsym hsup hM hT
  · simpa using hM0

omit [Fintype V] in
theorem chainOf_three (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    {w : V → V → V → ℝ} (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : IsCopy p F (activeCompleteGraph p F) {a, b, c}) :
    chainOf p F w {a, b, c} = w a b c := by
  unfold chainOf copyRestriction
  rw [if_pos hT, ternaryToWeight_three hsym hsup hab hac hbc]

/-! ### The third-vertex sum -/

omit [Fintype V] in
theorem sum_avoid_two (s : Finset V) {x y : V} (hxy : x ≠ y) (φ : V → ℝ) :
    (∑ c ∈ s, if x ≠ c ∧ y ≠ c then φ c else 0) =
      (∑ c ∈ s, φ c) - (if x ∈ s then φ x else 0) - (if y ∈ s then φ y else 0) := by
  have hpt : ∀ c, φ c = (if x ≠ c ∧ y ≠ c then φ c else 0) +
      (if x = c then φ c else 0) + (if y = c then φ c else 0) := by
    intro c
    by_cases hx : x = c
    · subst c
      simp [Ne.symm hxy]
    · by_cases hy : y = c
      · subst c
        simp [hx]
      · simp [hx, hy]
  have hs : (∑ c ∈ s, φ c) = (∑ c ∈ s, if x ≠ c ∧ y ≠ c then φ c else 0) +
      (∑ c ∈ s, if x = c then φ c else 0) + (∑ c ∈ s, if y = c then φ c else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => hpt c
  rw [hs, sum_ite_eq, sum_ite_eq]
  ring

omit [Fintype V] in
theorem sum_avoid_one (s : Finset V) (u : V) (φ : V → ℝ) :
    (∑ c ∈ s, if c ≠ u then φ c else 0) = (∑ c ∈ s, φ c) - (if u ∈ s then φ u else 0) := by
  have hs : (∑ c ∈ s, φ c) = (∑ c ∈ s, if c ≠ u then φ c else 0) +
      (∑ c ∈ s, if u = c then φ c else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    by_cases h : c = u
    · subst c; simp
    · simp [h, Ne.symm h]
  rw [hs, sum_ite_eq]
  ring

theorem sum_chi_mul (p : V → Fin 4) (τ : Multiset (Fin 4)) {x y : V} (hxy : x ≠ y)
    (φ : V → ℝ) :
    (∑ c, chi p τ x y c * φ c) =
      ∑ z : Fin 4, if ({p x, p y, z} : Multiset (Fin 4)) = τ then
        (∑ c ∈ classVertices p z, φ c) - (if p x = z then φ x else 0) -
          (if p y = z then φ y else 0) else 0 := by
  rw [← sum_fiberwise (univ : Finset V) p]
  apply sum_congr rfl
  intro z _
  have hcv : (univ.filter fun c => p c = z) = classVertices p z := rfl
  rw [hcv]
  by_cases hτ : ({p x, p y, z} : Multiset (Fin 4)) = τ
  · rw [if_pos hτ]
    have hx : (x ∈ classVertices p z) ↔ p x = z := mem_classVertices p z x
    have hy : (y ∈ classVertices p z) ↔ p y = z := mem_classVertices p z y
    have e1 : (if p x = z then φ x else 0) = (if x ∈ classVertices p z then φ x else 0) := by
      simp only [mem_classVertices]
    have e2 : (if p y = z then φ y else 0) = (if y ∈ classVertices p z then φ y else 0) := by
      simp only [mem_classVertices]
    rw [e1, e2, ← sum_avoid_two (classVertices p z) hxy φ]
    apply sum_congr rfl
    intro c hc
    have hpc : p c = z := (mem_classVertices p z c).mp hc
    unfold chi
    rw [hpc]
    by_cases hxc : x ≠ c ∧ y ≠ c
    · rw [if_pos ⟨hxy, hxc.1, hxc.2, hτ⟩, if_pos hxc, one_mul]
    · rw [if_neg (fun h => hxc ⟨h.2.1, h.2.2.1⟩), if_neg hxc, zero_mul]
  · rw [if_neg hτ]
    apply sum_eq_zero
    intro c hc
    have hpc : p c = z := (mem_classVertices p z c).mp hc
    unfold chi
    rw [hpc, if_neg (fun h => hτ h.2.2.2), zero_mul]

end PaddedGeneral.RealInverse
