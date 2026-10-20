/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A finite adaptive averaging lemma

Every node chooses uniformly from a finite set which can depend on the whole
previous path.  If every such set has at least `a > 0` members, prescribing any
`k` coordinates has mass at most `(1/a)^k`.  The proof is over a finite tree;
it requires no independence assumption on consecutive choices.

This is the averaging ingredient for placing a bounded-degree signed
correction.  It does not by itself construct that correction or prove the
final decomposition interface.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

universe u

inductive ChoiceTree (V : Type u) : ℕ → Type u
  | leaf : ChoiceTree V 0
  | step {n : ℕ} (choices : Finset V) (next : V → ChoiceTree V n) : ChoiceTree V (n + 1)

inductive CoordinateMask (V : Type u) : ℕ → Type u
  | nil : CoordinateMask V 0
  | any {n : ℕ} (tail : CoordinateMask V n) : CoordinateMask V (n + 1)
  | fixed {n : ℕ} (value : V) (tail : CoordinateMask V n) : CoordinateMask V (n + 1)

namespace CoordinateMask

def count {V : Type u} : {n : ℕ} → CoordinateMask V n → ℕ
  | _, .nil => 0
  | _, .any tail => count tail
  | _, .fixed _ tail => count tail + 1

def unrestricted (V : Type u) : (n : ℕ) → CoordinateMask V n
  | 0 => .nil
  | n + 1 => .any (unrestricted V n)

end CoordinateMask

namespace ChoiceTree

variable {V : Type u}

/-- A branch lower bound, asserted only on branches which can be selected. -/
def Lower (a : ℝ) : {n : ℕ} → ChoiceTree V n → Prop
  | _, .leaf => True
  | _, .step choices next =>
      a ≤ (choices.card : ℝ) ∧ ∀ v ∈ choices, Lower a (next v)

/-- The mass of a cylinder event under uniform successive choices. -/
noncomputable def mass [DecidableEq V] :
    {n : ℕ} → ChoiceTree V n → CoordinateMask V n → ℝ
  | _, .leaf, .nil => 1
  | _, .step choices next, .any tail =>
      (∑ v ∈ choices, mass (next v) tail) / choices.card
  | _, .step choices next, .fixed value tail =>
      if value ∈ choices then mass (next value) tail / choices.card else 0

theorem mass_nonneg [DecidableEq V] {n : ℕ} (T : ChoiceTree V n)
    (M : CoordinateMask V n) : 0 ≤ mass T M := by
  induction T with
  | leaf => cases M; norm_num [mass]
  | step choices next ih =>
    cases M with
    | any tail =>
      exact div_nonneg (sum_nonneg fun v _ => ih v tail) (Nat.cast_nonneg _)
    | fixed value tail =>
      simp only [mass]
      split_ifs
      · exact div_nonneg (ih value tail) (Nat.cast_nonneg _)
      · exact le_rfl

/-- Total mass is exactly one even when later choice sets depend on earlier choices. -/
theorem mass_unrestricted [DecidableEq V] {n : ℕ} (T : ChoiceTree V n)
    (a : ℝ) (ha : 0 < a) (hT : Lower a T) :
    mass T (CoordinateMask.unrestricted V n) = 1 := by
  induction T with
  | leaf => rfl
  | step choices next ih =>
    have hc : (choices.card : ℝ) ≠ 0 := (lt_of_lt_of_le ha hT.1).ne'
    simp only [CoordinateMask.unrestricted, mass]
    have hs : (∑ v ∈ choices, mass (next v) (CoordinateMask.unrestricted V _)) =
        (choices.card : ℝ) := by
      calc
        _ = ∑ _v ∈ choices, (1 : ℝ) :=
          sum_congr rfl fun v hv => ih v (hT.2 v hv)
        _ = _ := by simp
    rw [hs, div_self hc]

/-- Prescribing `k` values costs at least `k` factors of the branch lower bound. -/
theorem mass_le [DecidableEq V] {n : ℕ} (T : ChoiceTree V n)
    (M : CoordinateMask V n) (a : ℝ) (ha : 0 < a) (hT : Lower a T) :
    mass T M ≤ (1 / a) ^ M.count := by
  induction T with
  | leaf => cases M; simp [mass, CoordinateMask.count]
  | step choices next ih =>
    have hc : (0 : ℝ) < choices.card := lt_of_lt_of_le ha hT.1
    cases M with
    | any tail =>
      change (∑ v ∈ choices, mass (next v) tail) / (choices.card : ℝ) ≤
        (1 / a) ^ tail.count
      rw [div_le_iff₀ hc]
      calc
        _ ≤ ∑ _v ∈ choices, (1 / a) ^ tail.count :=
          sum_le_sum fun v hv => ih v tail (hT.2 v hv)
        _ = _ := by simp [mul_comm]
    | fixed value tail =>
      change (if value ∈ choices then mass (next value) tail / (choices.card : ℝ) else 0) ≤
        (1 / a) ^ (tail.count + 1)
      by_cases hv : value ∈ choices
      · rw [ite_eq_left hv]
        calc
          _ ≤ (1 / a) ^ tail.count / (choices.card : ℝ) :=
            div_le_div_of_nonneg_right (ih value tail (hT.2 value hv)) hc.le
          _ ≤ (1 / a) ^ tail.count / a :=
            div_le_div_of_nonneg_left (by positivity) ha hT.1
          _ = _ := by rw [pow_succ]; ring
      · rw [ite_eq_right hv]
        positivity

/-- The useful triple-marginal specialization. -/
theorem mass_le_three [DecidableEq V] {n : ℕ} (T : ChoiceTree V n)
    (M : CoordinateMask V n) (a : ℝ) (ha : 0 < a) (hT : Lower a T)
    (hM : M.count = 3) : mass T M ≤ 1 / a ^ 3 := by
  have h := mass_le T M a ha hT
  rw [hM, div_pow, one_pow] at h
  exact h

#print axioms mass_nonneg
#print axioms mass_unrestricted
#print axioms mass_le
#print axioms mass_le_three

end ChoiceTree

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
