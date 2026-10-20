/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveMean

/-!
# Marginals of an adaptive placement

A single auxiliary coordinate has a probability distribution with atom mass
at most `1/a`. Its expectation is exactly the corresponding coordinate
expectation in the original choice tree. These identities permit a separate
local coupling for each edge while preserving every original marginal.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

namespace CoordinateMask

variable {V : Type*}

theorem unrestricted_count (n : ℕ) : (unrestricted V n).count = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem accepts_unrestricted (n : ℕ) (f : Fin n → V) : (unrestricted V n).Accepts f := by
  induction n with
  | zero => trivial
  | succ n ih => exact ih _

def single (V : Type*) : (n : ℕ) → Fin n → V → CoordinateMask V n
  | 0, i, _ => i.elim0
  | n + 1, i, v => Fin.cases (.fixed v (unrestricted V n)) (fun j => .any (single V n j v)) i

theorem single_count (n : ℕ) (i : Fin n) (v : V) : (single V n i v).count = 1 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [single, count, unrestricted_count]
    · simpa [single, count] using ih j

theorem accepts_single (n : ℕ) (i : Fin n) (v : V) (f : Fin n → V) :
    (single V n i v).Accepts f ↔ f i = v := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [single, Accepts, accepts_unrestricted]
    · simpa [single, Accepts] using ih j (fun k => f k.succ)

end CoordinateMask

structure FiniteDistribution (V : Type*) [Fintype V] where
  mass : V → ℝ
  nonneg : ∀ v, 0 ≤ mass v
  total : ∑ v, mass v = 1

namespace FiniteDistribution

variable {V : Type*} [Fintype V]

noncomputable def average (μ : FiniteDistribution V) (f : V → ℝ) : ℝ :=
  ∑ v, μ.mass v * f v

theorem average_const (μ : FiniteDistribution V) (c : ℝ) : μ.average (fun _ => c) = c := by
  simp only [average, ← sum_mul, μ.total, one_mul]

theorem average_add (μ : FiniteDistribution V) (f g : V → ℝ) :
    μ.average (fun v => f v + g v) = μ.average f + μ.average g := by
  simp only [average, mul_add, sum_add_distrib]

theorem average_sub (μ : FiniteDistribution V) (f g : V → ℝ) :
    μ.average (fun v => f v - g v) = μ.average f - μ.average g := by
  simp only [average, mul_sub, sum_sub_distrib]

theorem average_smul (μ : FiniteDistribution V) (c : ℝ) (f : V → ℝ) :
    μ.average (fun v => c * f v) = c * μ.average f := by
  simp only [average, ← mul_sum, mul_left_comm]

theorem average_sum (μ : FiniteDistribution V) {ι : Type*}
    (s : Finset ι) (f : ι → V → ℝ) :
    μ.average (fun v => ∑ i ∈ s, f i v) = ∑ i ∈ s, μ.average (f i) := by
  simp only [average, mul_sum]
  exact sum_comm

theorem average_mono (μ : FiniteDistribution V) (f g : V → ℝ)
    (h : ∀ v, μ.mass v ≠ 0 → f v ≤ g v) : μ.average f ≤ μ.average g := by
  apply sum_le_sum
  intro v hv
  by_cases hm : μ.mass v = 0
  · simp only [hm, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h v hm) (μ.nonneg v)

theorem average_congr (μ : FiniteDistribution V) (f g : V → ℝ)
    (h : ∀ v, μ.mass v ≠ 0 → f v = g v) : μ.average f = μ.average g := by
  apply le_antisymm
  · exact μ.average_mono f g fun v hv => (h v hv).le
  · exact μ.average_mono g f fun v hv => (h v hv).ge

theorem average_nonneg (μ : FiniteDistribution V) (f : V → ℝ)
    (h : ∀ v, μ.mass v ≠ 0 → 0 ≤ f v) : 0 ≤ μ.average f := by
  rw [← μ.average_const 0]
  exact μ.average_mono _ _ h

theorem abs_average_le (μ : FiniteDistribution V) (f : V → ℝ) :
    |μ.average f| ≤ μ.average (fun v => |f v|) := by
  calc
    _ ≤ ∑ v, |μ.mass v * f v| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (μ.nonneg _), average]

theorem average_window (μ : FiniteDistribution V) [DecidableEq V]
    (W : Finset V) (a : ℝ) (_ha : 0 < a) (hcap : ∀ v, μ.mass v ≤ 1 / a) :
    μ.average (fun v => if v ∈ W then 1 else 0) ≤ W.card / a := by
  classical
  calc
    _ = ∑ v ∈ W, μ.mass v := by simp [average]
    _ ≤ ∑ _v ∈ W, (1 / a : ℝ) := sum_le_sum fun v _ => hcap v
    _ = _ := by simp [div_eq_mul_inv]

end FiniteDistribution

namespace ChoiceTree

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def coordinateMass {n : ℕ} (T : ChoiceTree V n) (i : Fin n) (v : V) : ℝ :=
  mean T (fun path => if path i = v then 1 else 0)

omit [Fintype V] in
theorem coordinateMass_nonneg {n : ℕ} (T : ChoiceTree V n) (i : Fin n) (v : V) :
    0 ≤ coordinateMass T i v := by
  exact mean_nonneg T _ fun path _ => by split_ifs <;> norm_num

omit [Fintype V] in
theorem coordinateMass_eq {n : ℕ} (T : ChoiceTree V n) (i : Fin n) (v : V) :
    coordinateMass T i v = mass T (CoordinateMask.single V n i v) := by
  classical
  rw [← mean_indicator]
  simp only [coordinateMass, CoordinateMask.accepts_single]

omit [Fintype V] in
theorem coordinateMass_le {n : ℕ} (T : ChoiceTree V n) (i : Fin n) (v : V)
    (a : ℝ) (ha : 0 < a) (hT : Lower a T) : coordinateMass T i v ≤ 1 / a := by
  rw [coordinateMass_eq]
  have h := mass_le T (CoordinateMask.single V n i v) a ha hT
  simpa only [CoordinateMask.single_count, pow_one] using h

theorem coordinateMass_total {n : ℕ} (T : ChoiceTree V n) (i : Fin n)
    (a : ℝ) (ha : 0 < a) (hT : Lower a T) : ∑ v, coordinateMass T i v = 1 := by
  classical
  simp only [coordinateMass, ← mean_sum]
  have hf : (fun path : Fin n → V => ∑ v : V, if path i = v then (1 : ℝ) else 0) =
      (fun _ => 1) := by funext path; simp
  rw [hf]
  exact mean_const T a ha hT 1

omit [Fintype V] in
theorem coordinateMass_support {n : ℕ} (T : ChoiceTree V n) (i : Fin n)
    (P : V → Prop) (hP : ∀ path, Supports T path → P (path i)) (v : V)
    (hv : coordinateMass T i v ≠ 0) : P v := by
  classical
  by_contra h
  apply hv
  change mean T (fun path => if path i = v then 1 else 0) = 0
  calc
    _ = mean T (fun _ => 0) := by
      apply mean_congr
      intro path hp
      have hn : path i ≠ v := fun he => h (he ▸ hP path hp)
      simp only [hn, ite_false]
    _ = 0 := mean_zero T

noncomputable def marginal {n : ℕ} (T : ChoiceTree V n) (i : Fin n)
    (a : ℝ) (ha : 0 < a) (hT : Lower a T) : FiniteDistribution V where
  mass := coordinateMass T i
  nonneg := coordinateMass_nonneg T i
  total := coordinateMass_total T i a ha hT

theorem marginal_average {n : ℕ} (T : ChoiceTree V n) (i : Fin n)
    (a : ℝ) (ha : 0 < a) (hT : Lower a T) (f : V → ℝ) :
    (marginal T i a ha hT).average f = mean T (fun path => f (path i)) := by
  classical
  change (∑ v, coordinateMass T i v * f v) = _
  simp only [coordinateMass]
  calc
    _ = ∑ v : V, mean T (fun path => f v * (if path i = v then 1 else 0)) := by
      apply sum_congr rfl
      intro v hv
      rw [mean_smul]
      ring
    _ = mean T (fun path => ∑ v : V, f v * (if path i = v then 1 else 0)) :=
      (mean_sum T univ _).symm
    _ = mean T (fun path => f (path i)) := by
      apply mean_congr
      intro path hp
      simp

#print axioms coordinateMass_total
#print axioms coordinateMass_le
#print axioms coordinateMass_support
#print axioms marginal_average

end ChoiceTree

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
