/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega

/-! # Counting permutations that send a set into a set

For finite sets `P, Q` of a finite type of size `N`, the number of permutations `σ` with
`σ '' P ⊆ Q` is `N! · C(|Q|, |P|) / C(N, |P|)`, hence at most `N! · (|Q| / N) ^ |P|`.
This is the only probabilistic input of the robust matching construction; it is proved by
symmetry and double counting.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Permutations sending every element of `P` into `Q`. -/
noncomputable def permsInto (P Q : Finset α) : Finset (Equiv.Perm α) :=
  univ.filter fun σ => ∀ x ∈ P, σ x ∈ Q

theorem mem_permsInto {P Q : Finset α} {σ : Equiv.Perm α} :
    σ ∈ permsInto P Q ↔ ∀ x ∈ P, σ x ∈ Q := by
  simp [permsInto]

theorem card_permsInto_le_of_card_eq {P P' Q : Finset α} (h : P'.card = P.card) :
    (permsInto P Q).card ≤ (permsInto P' Q).card := by
  classical
  let e : {x // x ∈ P'} ≃ {x // x ∈ P} := Finset.equivOfCardEq h
  let π : Equiv.Perm α := e.extendSubtype
  have hπ : ∀ x ∈ P', π x ∈ P := fun x hx => e.extendSubtype_mem x hx
  refine card_le_card_of_injOn (fun σ => π.trans σ) ?_ ?_
  · intro σ hσ
    rw [mem_coe, mem_permsInto] at hσ ⊢
    intro x hx
    exact hσ _ (hπ x hx)
  · intro σ _ τ _ hστ
    ext x
    have := congrArg (fun ρ : Equiv.Perm α => ρ (π.symm x)) hστ
    simpa using this

theorem card_permsInto_eq_of_card_eq {P P' Q : Finset α} (h : P'.card = P.card) :
    (permsInto P Q).card = (permsInto P' Q).card :=
  le_antisymm (card_permsInto_le_of_card_eq h) (card_permsInto_le_of_card_eq h.symm)

/-- Double counting: `C(N,p) · #{σ : σ P ⊆ Q} = N! · C(|Q|, p)`. -/
theorem choose_mul_card_permsInto (P Q : Finset α) :
    (Fintype.card α).choose P.card * (permsInto P Q).card =
      (Fintype.card α).factorial * Q.card.choose P.card := by
  classical
  set p := P.card
  have hsum : ∑ P' ∈ powersetCard p (univ : Finset α), (permsInto P' Q).card =
      ∑ σ : Equiv.Perm α, ((powersetCard p (univ : Finset α)).filter
        fun P' => ∀ x ∈ P', σ x ∈ Q).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun P' _ => ?_
    simp [permsInto]
  have hconst : ∀ P' ∈ powersetCard p (univ : Finset α),
      (permsInto P' Q).card = (permsInto P Q).card := by
    intro P' hP'
    exact (card_permsInto_eq_of_card_eq (mem_powersetCard.mp hP').2).symm
  have hfib : ∀ σ : Equiv.Perm α, ((powersetCard p (univ : Finset α)).filter
      fun P' => ∀ x ∈ P', σ x ∈ Q).card = Q.card.choose p := by
    intro σ
    have : (powersetCard p (univ : Finset α)).filter (fun P' => ∀ x ∈ P', σ x ∈ Q) =
        powersetCard p (univ.filter fun x => σ x ∈ Q) := by
      ext P'
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun x hx => mem_filter.mpr ⟨mem_univ _, h2 x hx⟩, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, fun x hx => (mem_filter.mp (h1 hx)).2⟩
    rw [this, card_powersetCard]
    congr 1
    refine card_bij (fun x _ => σ x) (fun x hx => (mem_filter.mp hx).2)
      (fun x _ y _ h => σ.injective h) ?_
    intro y hy
    exact ⟨σ.symm y, mem_filter.mpr ⟨mem_univ _, by simpa using hy⟩, by simp⟩
  rw [sum_congr rfl hconst, sum_congr rfl fun σ _ => hfib σ] at hsum
  simp only [sum_const, card_powersetCard, card_univ, smul_eq_mul, Fintype.card_perm] at hsum
  exact hsum

/-- `C(q,p) · N^p ≤ C(N,p) · q^p` for `q ≤ N`. -/
theorem descFactorial_mul_pow_le {q N : ℕ} (hqN : q ≤ N) (p : ℕ) :
    q.descFactorial p * N ^ p ≤ N.descFactorial p * q ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have key : (q - p) * N ≤ (N - p) * q := by
      rcases Nat.lt_or_ge q p with h | h
      · rw [Nat.sub_eq_zero_of_le h.le]; simp
      · have h1 : (q - p) * N + p * N = q * N := by
          rw [← add_mul, Nat.sub_add_cancel h]
        have h2 : (N - p) * q + p * q = N * q := by
          rw [← add_mul, Nat.sub_add_cancel (h.trans hqN)]
        have h3 : p * q ≤ p * N := Nat.mul_le_mul_left p hqN
        nlinarith
    calc (q - p) * q.descFactorial p * (N ^ p * N)
        = (q.descFactorial p * N ^ p) * ((q - p) * N) := by ring
      _ ≤ (N.descFactorial p * q ^ p) * ((N - p) * q) := Nat.mul_le_mul ih key
      _ = (N - p) * N.descFactorial p * (q ^ p * q) := by ring

theorem choose_mul_pow_le {q N : ℕ} (hqN : q ≤ N) (p : ℕ) :
    q.choose p * N ^ p ≤ N.choose p * q ^ p := by
  have h := descFactorial_mul_pow_le hqN p
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos p)

/-- **Permutation count.** `#{σ : σ P ⊆ Q} ≤ N! · (|Q| / N) ^ |P|`. -/
theorem card_permsInto_le (P Q : Finset α) :
    ((permsInto P Q).card : ℝ) ≤
      (Fintype.card α).factorial * ((Q.card : ℝ) / Fintype.card α) ^ P.card := by
  set N := Fintype.card α
  have hp : P.card ≤ N := card_le_univ P
  have hq : Q.card ≤ N := card_le_univ Q
  have hpos : 0 < N.choose P.card := Nat.choose_pos hp
  have h1 := choose_mul_card_permsInto P Q
  have h2 := choose_mul_pow_le hq P.card
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hP : P.card = 0 := by omega
    have := card_le_univ (permsInto P Q)
    rw [Fintype.card_perm] at this
    rw [hP, pow_zero, mul_one]
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcR : (0 : ℝ) < N.choose P.card := by exact_mod_cast hpos
  have h1R : (N.choose P.card : ℝ) * (permsInto P Q).card =
      N.factorial * Q.card.choose P.card := by exact_mod_cast h1
  have h2R : (Q.card.choose P.card : ℝ) * (N : ℝ) ^ P.card ≤
      (N.choose P.card : ℝ) * (Q.card : ℝ) ^ P.card := by exact_mod_cast h2
  rw [div_pow, mul_div_assoc']
  rw [le_div_iff₀ (by positivity)]
  have hfac : (0 : ℝ) ≤ N.factorial := by positivity
  have : (N.choose P.card : ℝ) * ((permsInto P Q).card * (N : ℝ) ^ P.card) ≤
      (N.choose P.card : ℝ) * (N.factorial * (Q.card : ℝ) ^ P.card) := by
    calc (N.choose P.card : ℝ) * ((permsInto P Q).card * (N : ℝ) ^ P.card)
        = N.factorial * ((Q.card.choose P.card : ℝ) * (N : ℝ) ^ P.card) := by
          rw [← mul_assoc, h1R]; ring
      _ ≤ N.factorial * ((N.choose P.card : ℝ) * (Q.card : ℝ) ^ P.card) :=
          mul_le_mul_of_nonneg_left h2R hfac
      _ = (N.choose P.card : ℝ) * (N.factorial * (Q.card : ℝ) ^ P.card) := by ring
  exact le_of_mul_le_mul_left this hcR

/-- The same count for the condition `σ⁻¹ P ⊆ Q`. -/
theorem card_permsInto_inv (P Q : Finset α) :
    (univ.filter fun σ : Equiv.Perm α => ∀ x ∈ P, σ.symm x ∈ Q).card =
      (permsInto P Q).card := by
  refine card_bij (fun σ _ => σ.symm) ?_ ?_ ?_
  · intro σ hσ
    rw [mem_permsInto]
    exact (mem_filter.mp hσ).2
  · intro σ _ τ _ h
    simpa using congrArg Equiv.symm h
  · intro τ hτ
    refine ⟨τ.symm, mem_filter.mpr ⟨mem_univ _, ?_⟩, by simp⟩
    simpa using (mem_permsInto.mp hτ)

end PartitionedTriangleAbsorption.TypedRefinerF0
