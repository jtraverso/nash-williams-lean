/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.Freedman

@[expose] public section

/-!
# Sampling toolkit for Lemma 11.6

Finite product probability spaces (from `RequestProject.Pseudorandom.FiniteProb`) specialised
to uniformly random sequences, together with:

* conditioning on the values of some coordinates (`pProb_le_of_update`, `pProb_le_of_updOn`);
* expectations of functions of two distinct coordinates (`pE_pair`);
* the Bernstein/McDiarmid bound with `R i = univ` (`upper_tail`, `lower_tail`);
* `exists_le_pE`: some outcome is at most the expectation.
-/

namespace NashWilliams18.Sampling

open Finset Pseudorandom

section General

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}

/-- Conditioning on one coordinate: if the event has probability at most `r` whatever value
is put on coordinate `i`, then it has probability at most `r`. -/
lemma pProb_le_of_update (hP : IsPMF P) (i : ι) (S : (ι → α) → Prop) (r : ℝ)
    (h : ∀ a, pProb P (fun ω => S (Function.update ω i a)) ≤ r) : pProb P S ≤ r := by
  classical
  unfold pProb at *
  rw [← pE_resample hP i]
  have : pE P (fun ω => ∑ a, P i a * (if S (Function.update ω i a) then (1 : ℝ) else 0)) =
      ∑ a, P i a * pE P (fun ω => if S (Function.update ω i a) then (1 : ℝ) else 0) := by
    rw [pE_sum]
    exact sum_congr rfl fun a _ => pE_const_mul _ _
  rw [this]
  calc ∑ a, P i a * pE P (fun ω => if S (Function.update ω i a) then (1 : ℝ) else 0)
      ≤ ∑ a, P i a * r := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hP.1 i a)
    _ = r := by rw [← sum_mul, hP.2 i, one_mul]

/-- Overwrite the coordinates in `π` by those of `z`. -/
def updOn (π : Finset ι) (z ω : ι → α) : ι → α := fun i => if i ∈ π then z i else ω i

lemma nonempty_of_isPMF (hP : IsPMF P) : Nonempty (ι → α) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_pw hP
  rw [Finset.univ_eq_empty, sum_empty] at this
  exact zero_ne_one this

/-- Conditioning on a set of coordinates. -/
lemma pProb_le_of_updOn (hP : IsPMF P) (π : Finset ι) (r : ℝ) :
    ∀ S : (ι → α) → Prop, (∀ z, pProb P (fun ω => S (updOn π z ω)) ≤ r) → pProb P S ≤ r := by
  induction π using Finset.induction_on with
  | empty =>
    intro S h
    obtain ⟨z⟩ := nonempty_of_isPMF hP
    have he : (fun ω => S (updOn ∅ z ω)) = S := by
      funext ω
      congr 1
      all_goals (funext i; exact if_neg (Finset.notMem_empty i))
    simpa only [he] using h z
  | insert i π hi ih =>
    intro S h
    refine ih S fun z => ?_
    refine pProb_le_of_update hP i _ r fun a => ?_
    have e : ∀ ω, updOn π z (Function.update ω i a) =
        updOn (insert i π) (Function.update z i a) ω := by
      intro ω
      funext j
      by_cases hj : j = i
      · subst hj; simp [updOn, hi]
      · by_cases hjπ : j ∈ π
        · simp [updOn, hjπ, hj]
        · simp [updOn, hjπ, hj]
    simp_rw [e]
    exact h _

/-- Expectation of a function of two distinct coordinates. -/
lemma pE_pair (hP : IsPMF P) {i j : ι} (hij : i ≠ j) (g : α → α → ℝ) :
    pE P (fun ω => g (ω i) (ω j)) = ∑ a, ∑ b, P i a * P j b * g a b := by
  rw [← pE_resample hP i]
  have e : ∀ (ω : ι → α) (a : α), g (Function.update ω i a i) (Function.update ω i a j) = g a (ω j) := by
    intro ω a; simp [Function.update_of_ne hij.symm]
  simp_rw [e]
  rw [pE_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [pE_const_mul, pE_coord hP j, mul_sum]
  exact sum_congr rfl fun b _ => by ring

/-- Some outcome is at most the expectation. -/
lemma exists_le_pE (hP : IsPMF P) (f : (ι → α) → ℝ) :
    ∃ ω, f ω ≤ pE P f := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∃ ω, 0 < pw P ω := by
    by_contra h0
    push_neg at h0
    have : ∑ ω, pw P ω = 0 :=
      sum_eq_zero fun ω _ => le_antisymm (h0 ω) (pw_nonneg hP ω)
    rw [sum_pw hP] at this
    exact one_ne_zero this
  obtain ⟨ω₀, hω₀⟩ := hpos
  have : pE P (fun _ => pE P f) < pE P f := by
    unfold pE
    refine sum_lt_sum (fun ω _ => mul_le_mul_of_nonneg_left (hcon ω).le (pw_nonneg hP ω))
      ⟨ω₀, mem_univ _, mul_lt_mul_of_pos_left (hcon ω₀) hω₀⟩
  rw [pE_const hP] at this
  exact lt_irrefl _ this

/-- Bernstein/McDiarmid upper tail with `R i = univ`. -/
lemma upper_tail (hP : IsPMF P) (f : (ι → α) → ℝ) (c : ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, c i ^ 2) + L * t)))) := by
  have h := pE_upper_tail P hP f c (fun _ => 1) (fun _ => univ) L hL hc hf
    (fun i ω a b ha => absurd (mem_univ a) ha) (fun i => by rw [hP.2 i]) t ht
  simpa using h

/-- Bernstein/McDiarmid lower tail with `R i = univ`. -/
lemma lower_tail (hP : IsPMF P) (f : (ι → α) → ℝ) (c : ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ pE P f - f ω) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, c i ^ 2) + L * t)))) := by
  have h := pE_lower_tail P hP f c (fun _ => 1) (fun _ => univ) L hL hc hf
    (fun i ω a b ha => absurd (mem_univ a) ha) (fun i => by rw [hP.2 i]) t ht
  simpa using h

end General

section Uniform

variable (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Uniform distribution on each coordinate. -/
noncomputable def unif : ι → α → ℝ := fun _ _ => 1 / (Fintype.card α : ℝ)

variable {ι α}

omit [Fintype ι] [DecidableEq ι] in
lemma unif_isPMF [Nonempty α] : IsPMF (unif ι α) := by
  refine ⟨fun _ _ => by unfold unif; positivity, fun _ => ?_⟩
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [unif, this]

omit [DecidableEq ι] in
lemma pw_unif (ω : ι → α) :
    pw (unif ι α) ω = 1 / (Fintype.card α : ℝ) ^ Fintype.card ι := by
  simp [pw, unif]

/-- Probabilities in the uniform product space are proportions. -/
lemma pProb_unif (S : (ι → α) → Prop) [DecidablePred S] :
    pProb (unif ι α) S =
      ((univ.filter S).card : ℝ) / (Fintype.card α : ℝ) ^ Fintype.card ι := by
  classical
  unfold pProb pE
  simp_rw [pw_unif]
  rw [← mul_sum]
  simp only [one_div]
  rw [inv_mul_eq_div]
  congr 1
  rw [Finset.card_filter]
  push_cast
  exact sum_congr rfl fun ω _ => by split_ifs <;> simp_all

end Uniform

end NashWilliams18.Sampling
