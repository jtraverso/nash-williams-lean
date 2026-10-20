/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.SequentialHost

@[expose] public section

/-!
# Finite means for adaptive placements

The mean is defined by finite sums at each node of a choice tree. Linearity,
positivity, and the cylinder estimates are proved directly, including when
the choices at later nodes depend on all preceding choices.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

universe u

namespace CoordinateMask

variable {V : Type u}

def Accepts : {n : ℕ} → CoordinateMask V n → (Fin n → V) → Prop
  | _, .nil, _ => True
  | _, .any tail, f => Accepts tail (fun i => f i.succ)
  | _, .fixed value tail, f => f 0 = value ∧ Accepts tail (fun i => f i.succ)

noncomputable instance {n : ℕ} (M : CoordinateMask V n) (f : Fin n → V) :
    Decidable (M.Accepts f) := Classical.propDecidable _

end CoordinateMask

namespace ChoiceTree

variable {V : Type u}

noncomputable def mean : {n : ℕ} → ChoiceTree V n → ((Fin n → V) → ℝ) → ℝ
  | _, .leaf, f => f Fin.elim0
  | _, .step choices next, f =>
      (∑ v ∈ choices, mean (next v) (fun path => f (Fin.cons v path))) / choices.card

theorem mean_add {n : ℕ} (T : ChoiceTree V n) (f g : (Fin n → V) → ℝ) :
    mean T (fun path => f path + g path) = mean T f + mean T g := by
  induction T with
  | leaf => rfl
  | step choices next ih => simp only [mean, ih, sum_add_distrib, add_div]

theorem mean_smul {n : ℕ} (T : ChoiceTree V n) (c : ℝ) (f : (Fin n → V) → ℝ) :
    mean T (fun path => c * f path) = c * mean T f := by
  induction T with
  | leaf => rfl
  | step choices next ih =>
    simp only [mean, ih, ← mul_sum]
    ring

theorem mean_neg {n : ℕ} (T : ChoiceTree V n) (f : (Fin n → V) → ℝ) :
    mean T (fun path => -f path) = -mean T f := by
  simpa only [neg_one_mul] using mean_smul T (-1) f

theorem mean_sub {n : ℕ} (T : ChoiceTree V n) (f g : (Fin n → V) → ℝ) :
    mean T (fun path => f path - g path) = mean T f - mean T g := by
  simp only [sub_eq_add_neg, mean_add, mean_neg]

theorem mean_sum {n : ℕ} (T : ChoiceTree V n) {ι : Type*}
    (s : Finset ι) (f : ι → (Fin n → V) → ℝ) :
    mean T (fun path => ∑ i ∈ s, f i path) = ∑ i ∈ s, mean T (f i) := by
  induction T with
  | leaf => rfl
  | step choices next ih =>
    simp only [mean, ih, sum_div]
    exact sum_comm

theorem mean_mono {n : ℕ} (T : ChoiceTree V n) (f g : (Fin n → V) → ℝ)
    (h : ∀ path, Supports T path → f path ≤ g path) : mean T f ≤ mean T g := by
  induction T with
  | leaf => exact h _ trivial
  | step choices next ih =>
    change (∑ v ∈ choices, mean (next v) _) / (choices.card : ℝ) ≤ _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro v hv
    apply ih v
    intro path hpath
    apply h (Fin.cons v path)
    simpa only [Supports, Fin.cons_zero, Fin.cons_succ] using And.intro hv hpath

theorem mean_congr {n : ℕ} (T : ChoiceTree V n) (f g : (Fin n → V) → ℝ)
    (h : ∀ path, Supports T path → f path = g path) : mean T f = mean T g := by
  apply le_antisymm
  · exact mean_mono T f g fun path hp => (h path hp).le
  · exact mean_mono T g f fun path hp => (h path hp).ge

theorem mean_zero {n : ℕ} (T : ChoiceTree V n) : mean T (fun _ => (0 : ℝ)) = 0 := by
  induction T with
  | leaf => rfl
  | step choices next ih => simp only [mean, ih, sum_const_zero, zero_div]

theorem mean_nonneg {n : ℕ} (T : ChoiceTree V n) (f : (Fin n → V) → ℝ)
    (h : ∀ path, Supports T path → 0 ≤ f path) : 0 ≤ mean T f := by
  rw [← mean_zero T]
  exact mean_mono T (fun _ => 0) f h

theorem mean_const {n : ℕ} (T : ChoiceTree V n) (a : ℝ) (ha : 0 < a)
    (hT : Lower a T) (c : ℝ) : mean T (fun _ => c) = c := by
  induction T with
  | leaf => rfl
  | step choices next ih =>
    have hc : (choices.card : ℝ) ≠ 0 := (lt_of_lt_of_le ha hT.1).ne'
    change (∑ v ∈ choices, mean (next v) (fun _ => c)) / (choices.card : ℝ) = c
    have hs : (∑ v ∈ choices, mean (next v) (fun _ => c)) = choices.card * c := by
      calc
        _ = ∑ _v ∈ choices, c := sum_congr rfl fun v hv => ih v (hT.2 v hv)
        _ = _ := by simp
    rw [hs]
    exact mul_div_cancel_left₀ c hc

theorem abs_mean_le {n : ℕ} (T : ChoiceTree V n) (f : (Fin n → V) → ℝ) :
    |mean T f| ≤ mean T (fun path => |f path|) := by
  rw [abs_le]
  constructor
  · have h := mean_mono T (fun path => -|f path|) f (fun path _ => neg_abs_le _)
    have he : mean T (fun path => -|f path|) = -mean T (fun path => |f path|) := by
      simpa only [neg_one_mul] using mean_smul T (-1) (fun path => |f path|)
    rw [he] at h
    exact h
  · exact mean_mono T f (fun path => |f path|) (fun path _ => le_abs_self _)

theorem abs_mean_le_const {n : ℕ} (T : ChoiceTree V n) (a : ℝ) (ha : 0 < a)
    (hT : Lower a T) (f : (Fin n → V) → ℝ) (c : ℝ)
    (hf : ∀ path, Supports T path → |f path| ≤ c) : |mean T f| ≤ c := by
  calc
    |mean T f| ≤ mean T (fun path => |f path|) := abs_mean_le T f
    _ ≤ mean T (fun _ => c) := mean_mono T _ _ hf
    _ = c := mean_const T a ha hT c

theorem mean_indicator [DecidableEq V] {n : ℕ} (T : ChoiceTree V n)
    (M : CoordinateMask V n) :
    mean T (fun path => if M.Accepts path then 1 else 0) = mass T M := by
  classical
  induction T with
  | leaf => cases M; simp [mean, mass, CoordinateMask.Accepts]
  | step choices next ih =>
    cases M with
    | any tail =>
      simpa only [mean, mass, CoordinateMask.Accepts, Fin.cons_succ] using
        congrArg (fun f : V → ℝ => (∑ v ∈ choices, f v) / choices.card)
          (funext fun v => ih v tail)
    | fixed value tail =>
      simp only [mean, CoordinateMask.Accepts, Fin.cons_zero, Fin.cons_succ]
      have hs : (∑ v ∈ choices, mean (next v)
          (fun path => if v = value ∧ tail.Accepts path then 1 else 0)) =
          if value ∈ choices then mass (next value) tail else 0 := by
        classical
        calc
          _ = ∑ v ∈ choices, if v = value then mass (next v) tail else 0 := by
            apply sum_congr rfl
            intro v hv
            by_cases he : v = value
            · subst v
              simpa only [true_and, ite_true] using ih value tail
            · simp only [he, false_and, ite_false, mean_zero]
          _ = _ := by simp
      rw [hs]
      by_cases hv : value ∈ choices <;> simp [mass, hv]

/-- A bounded contribution supported by `k` prescribed auxiliary images has
mean at most its amplitude times `a⁻ᵏ`. -/
theorem mean_cylinder_bound [DecidableEq V] {n : ℕ} (T : ChoiceTree V n)
    (M : CoordinateMask V n) (a : ℝ) (ha : 0 < a) (hT : Lower a T)
    (f : (Fin n → V) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ path, Supports T path →
      |f path| ≤ c * (if M.Accepts path then 1 else 0)) :
    |mean T f| ≤ c * (1 / a) ^ M.count := by
  classical
  calc
    |mean T f| ≤ mean T (fun path => |f path|) := abs_mean_le T f
    _ ≤ mean T (fun path => c * (if M.Accepts path then 1 else 0)) :=
      mean_mono T _ _ hf
    _ = c * mass T M := by rw [mean_smul, mean_indicator]
    _ ≤ c * (1 / a) ^ M.count := mul_le_mul_of_nonneg_left (mass_le T M a ha hT) hc

#print axioms mean_add
#print axioms mean_sum
#print axioms mean_mono
#print axioms mean_const
#print axioms abs_mean_le
#print axioms mean_indicator
#print axioms mean_cylinder_bound

end ChoiceTree

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
