/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveMean

/-!
# Several adaptive coordinates in a prescribed finite set

Requiring `k` specified coordinates to lie in a finite set of at most `b`
vertices has probability at most `(b/a)^k`. This loose form avoids any
assumption that auxiliary coordinates are independent or globally injective.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

inductive SelectionMask : ℕ → Type
  | nil : SelectionMask 0
  | any {n : ℕ} (tail : SelectionMask n) : SelectionMask (n + 1)
  | selected {n : ℕ} (tail : SelectionMask n) : SelectionMask (n + 1)

namespace SelectionMask

def count : {n : ℕ} → SelectionMask n → ℕ
  | _, .nil => 0
  | _, .any tail => count tail
  | _, .selected tail => count tail + 1

def Accepts {V : Type*} (W : Finset V) :
    {n : ℕ} → SelectionMask n → (Fin n → V) → Prop
  | _, .nil, _ => True
  | _, .any tail, f => Accepts W tail (fun i => f i.succ)
  | _, .selected tail, f => f 0 ∈ W ∧ Accepts W tail (fun i => f i.succ)

noncomputable instance {V : Type*} (W : Finset V) {n : ℕ}
    (M : SelectionMask n) (f : Fin n → V) : Decidable (M.Accepts W f) :=
  Classical.propDecidable _

end SelectionMask

namespace ChoiceTree

variable {V : Type*} [DecidableEq V]

noncomputable def windowMass (W : Finset V) :
    {n : ℕ} → ChoiceTree V n → SelectionMask n → ℝ
  | _, .leaf, .nil => 1
  | _, .step choices next, .any tail =>
      (∑ v ∈ choices, windowMass W (next v) tail) / choices.card
  | _, .step choices next, .selected tail =>
      (∑ v ∈ choices ∩ W, windowMass W (next v) tail) / choices.card

theorem windowMass_nonneg (W : Finset V) {n : ℕ} (T : ChoiceTree V n)
    (M : SelectionMask n) : 0 ≤ windowMass W T M := by
  induction T with
  | leaf => cases M; norm_num [windowMass]
  | step choices next ih =>
    cases M with
    | any tail => exact div_nonneg (sum_nonneg fun v _ => ih v tail) (Nat.cast_nonneg _)
    | selected tail => exact div_nonneg (sum_nonneg fun v _ => ih v tail) (Nat.cast_nonneg _)

theorem windowMass_le (W : Finset V) {n : ℕ} (T : ChoiceTree V n)
    (M : SelectionMask n) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hT : Lower a T) (hW : (W.card : ℝ) ≤ b) :
    windowMass W T M ≤ (b / a) ^ M.count := by
  induction T with
  | leaf => cases M; simp [windowMass, SelectionMask.count]
  | step choices next ih =>
    have hc : (0 : ℝ) < choices.card := lt_of_lt_of_le ha hT.1
    cases M with
    | any tail =>
      change (∑ v ∈ choices, windowMass W (next v) tail) / (choices.card : ℝ) ≤
        (b / a) ^ tail.count
      rw [div_le_iff₀ hc]
      calc
        _ ≤ ∑ _v ∈ choices, (b / a) ^ tail.count :=
          sum_le_sum fun v hv => ih v tail (hT.2 v hv)
        _ = _ := by simp [mul_comm]
    | selected tail =>
      change (∑ v ∈ choices ∩ W, windowMass W (next v) tail) / (choices.card : ℝ) ≤
        (b / a) ^ (tail.count + 1)
      have hcW : ((choices ∩ W).card : ℝ) ≤ b :=
        (show ((choices ∩ W).card : ℝ) ≤ W.card by
          exact_mod_cast card_le_card inter_subset_right).trans hW
      calc
        _ ≤ (∑ _v ∈ choices ∩ W, (b / a) ^ tail.count) / (choices.card : ℝ) :=
          div_le_div_of_nonneg_right (sum_le_sum fun v hv =>
            ih v tail (hT.2 v (mem_inter.mp hv).1)) hc.le
        _ = (choices ∩ W).card * (b / a) ^ tail.count / choices.card := by simp
        _ ≤ b * (b / a) ^ tail.count / a :=
          div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_right hcW (by positivity)) ha hT.1
        _ = _ := by rw [pow_succ]; ring

theorem mean_window_indicator (W : Finset V) {n : ℕ} (T : ChoiceTree V n)
    (M : SelectionMask n) :
    mean T (fun path => if M.Accepts W path then 1 else 0) = windowMass W T M := by
  classical
  induction T with
  | leaf => cases M; simp [mean, windowMass, SelectionMask.Accepts]
  | step choices next ih =>
    cases M with
    | any tail =>
      simp only [mean, windowMass, SelectionMask.Accepts, Fin.cons_succ, ih]
    | selected tail =>
      simp only [mean, windowMass, SelectionMask.Accepts, Fin.cons_zero, Fin.cons_succ]
      apply congrArg (fun x : ℝ => x / choices.card)
      calc
        _ = ∑ v ∈ choices, if v ∈ W then windowMass W (next v) tail else 0 := by
          apply sum_congr rfl
          intro v hv
          by_cases hvW : v ∈ W
          · simpa only [hvW, true_and, ite_true] using ih v tail
          · simp only [hvW, false_and, ite_false, mean_zero]
        _ = _ := by simp only [← sum_filter, filter_mem_eq_inter]

theorem mean_window_bound (W : Finset V) {n : ℕ} (T : ChoiceTree V n)
    (M : SelectionMask n) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hT : Lower a T) (hW : (W.card : ℝ) ≤ b)
    (f : (Fin n → V) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ path, Supports T path →
      |f path| ≤ c * (if M.Accepts W path then 1 else 0)) :
    |mean T f| ≤ c * (b / a) ^ M.count := by
  classical
  calc
    |mean T f| ≤ mean T (fun path => |f path|) := abs_mean_le T f
    _ ≤ mean T (fun path => c * (if M.Accepts W path then 1 else 0)) := mean_mono T _ _ hf
    _ = c * windowMass W T M := by rw [mean_smul, mean_window_indicator]
    _ ≤ c * (b / a) ^ M.count :=
      mul_le_mul_of_nonneg_left (windowMass_le W T M a b ha hb hT hW) hc

#print axioms windowMass_nonneg
#print axioms windowMass_le
#print axioms mean_window_indicator
#print axioms mean_window_bound

end ChoiceTree

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
