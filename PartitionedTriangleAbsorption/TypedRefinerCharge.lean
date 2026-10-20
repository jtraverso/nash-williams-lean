/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationLinks
public import PartitionedTriangleAbsorption.RefinerAssembly
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # Conserved global charges of the typed families F0--F3

A *charge* is an integer weight matrix `χ` on ordered part pairs which vanishes on the
(ordered) edge vector of every permitted triangle type. Its value on an edge set is then
zero for every integrally divisible edge set, and for every piece that admits a private
typed absorber. Each of F0--F3 has such a charge which is nonzero on an active edge, so the
global type constraint of a leftover is an exact linear conservation law, not merely a
congruence. This file only records these facts; it constructs no refiner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerCharge

open Finset TypedApplicationLinks

variable {t : ℕ}

/-- Pair a weight matrix with an ordered edge-type vector. -/
def pair (χ M : Fin t → Fin t → ℤ) : ℤ := ∑ i, ∑ j, χ i j * M i j

/-- `χ` vanishes on the edge vector of every type of `F`. -/
def Kills (χ : Fin t → Fin t → ℤ) (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ τ ∈ F, pair χ (typeEdgeVec τ) = 0

theorem pair_add (χ M N : Fin t → Fin t → ℤ) : pair χ (M + N) = pair χ M + pair χ N := by
  simp only [pair, Pi.add_apply, mul_add, sum_add_distrib]

theorem pair_zero (χ : Fin t → Fin t → ℤ) : pair χ 0 = 0 := by
  simp [pair]

theorem pair_zsmul (χ M : Fin t → Fin t → ℤ) (c : ℤ) : pair χ (c • M) = c * pair χ M := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem pair_sum {ι : Type*} (χ : Fin t → Fin t → ℤ) (s : Finset ι)
    (M : ι → Fin t → Fin t → ℤ) : pair χ (∑ i ∈ s, M i) = ∑ i ∈ s, pair χ (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, pair_add, ih]

theorem pair_lattice {χ : Fin t → Fin t → ℤ} {F : Finset (Multiset (Fin t))}
    (hχ : Kills χ F) (c : Multiset (Fin t) → ℤ) :
    pair χ (∑ τ ∈ F, c τ • typeEdgeVec τ) = 0 := by
  rw [pair_sum]
  exact sum_eq_zero fun τ hτ => by rw [pair_zsmul, hχ τ hτ, mul_zero]

variable {V : Type*} [DecidableEq V]

/-- The charge of an edge set. -/
def charge (χ : Fin t → Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) : ℤ :=
  pair χ (edgeVec p E)

theorem charge_union (χ : Fin t → Fin t → ℤ) (p : V → Fin t) {A B : Finset (Sym2 V)}
    (h : Disjoint A B) : charge χ p (A ∪ B) = charge χ p A + charge χ p B := by
  rw [charge, edgeVec_union p h, pair_add]; rfl

omit [DecidableEq V] in
theorem charge_empty (χ : Fin t → Fin t → ℤ) (p : V → Fin t) :
    charge χ p (∅ : Finset (Sym2 V)) = 0 := by
  simp [charge, edgeVec, pair_zero]

omit [DecidableEq V] in
theorem charge_eq_sum (χ : Fin t → Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) :
    charge χ p E = ∑ e ∈ E, pair χ (pairVec p e) := by
  rw [charge, edgeVec, pair_sum]

theorem charge_biUnion {ι : Type*} (χ : Fin t → Fin t → ℤ) (p : V → Fin t) (s : Finset ι)
    (E : ι → Finset (Sym2 V)) (hdis : (s : Set ι).PairwiseDisjoint E) :
    charge χ p (s.biUnion E) = ∑ i ∈ s, charge χ p (E i) := by
  rw [charge_eq_sum, sum_biUnion hdis]
  exact sum_congr rfl fun i _ => (charge_eq_sum χ p (E i)).symm

omit [DecidableEq V] in
/-- The charge of one edge `ab` is `χ(p a, p b) + χ(p b, p a)`. -/
theorem pair_pairVec (χ : Fin t → Fin t → ℤ) (p : V → Fin t) (a b : V) :
    pair χ (pairVec p s(a, b)) = χ (p a) (p b) + χ (p b) (p a) := by
  simp only [pair, pairVec, Sym2.lift_mk, mul_add, sum_add_distrib, mul_ite, mul_one,
    mul_zero]
  congr 1
  · rw [Finset.sum_eq_single (p a)]
    · simp
    · intro i _ hi
      exact sum_eq_zero fun j _ => by simp [Ne.symm hi]
    · simp
  · rw [Finset.sum_eq_single (p b)]
    · simp
    · intro i _ hi
      exact sum_eq_zero fun j _ => by simp [Ne.symm hi]
    · simp

omit [DecidableEq V] in
/-- A uniform entry bound gives a uniform bound on the charge of one edge. -/
theorem abs_pair_pairVec_le {χ : Fin t → Fin t → ℤ} {m : ℤ} (hm : ∀ i j, |χ i j| ≤ m)
    (p : V → Fin t) (e : Sym2 V) : |pair χ (pairVec p e)| ≤ 2 * m := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [pair_pairVec]
    have h1 := hm (p a) (p b)
    have h2 := hm (p b) (p a)
    calc |χ (p a) (p b) + χ (p b) (p a)| ≤ |χ (p a) (p b)| + |χ (p b) (p a)| := abs_add_le _ _
      _ ≤ 2 * m := by linarith

omit [DecidableEq V] in
theorem abs_charge_le {χ : Fin t → Fin t → ℤ} {M : ℤ} (p : V → Fin t)
    (hM : ∀ e : Sym2 V, |pair χ (pairVec p e)| ≤ M) (E : Finset (Sym2 V)) :
    |charge χ p E| ≤ M * E.card := by
  rw [charge_eq_sum]
  calc |∑ e ∈ E, pair χ (pairVec p e)| ≤ ∑ e ∈ E, |pair χ (pairVec p e)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ E, M := sum_le_sum fun e _ => hM e
    _ = M * E.card := by rw [sum_const, nsmul_eq_mul, mul_comm]

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Every integrally divisible edge set has zero charge. -/
theorem charge_eq_zero_of_isIntDiv {χ : Fin t → Fin t → ℤ} (hχ : Kills χ F)
    {E : Finset (Sym2 V)} (h : IsIntDiv p F E) : charge χ p E = 0 := by
  obtain ⟨⟨c, hc⟩, -⟩ := h
  rw [charge, hc]
  exact pair_lattice hχ c

/-- Every decomposable edge set has zero charge. -/
theorem charge_eq_zero_of_hasDecomp {χ : Fin t → Fin t → ℤ} (hχ : Kills χ F)
    {E : Finset (Sym2 V)} (h : HasDecomp p F E) : charge χ p E = 0 :=
  charge_eq_zero_of_isIntDiv hχ (isIntDiv_of_hasDecomp h)

/-- A piece with a private absorber (`A` and `A ∪ B` decomposable, `A ∩ B = ∅`) has zero
charge. So zero charge is necessary for every refiner piece, whatever absorber is used. -/
theorem charge_eq_zero_of_absorber {χ : Fin t → Fin t → ℤ} (hχ : Kills χ F)
    {A B : Finset (Sym2 V)} (hdis : Disjoint A B) (hA : HasDecomp p F A)
    (hAB : HasDecomp p F (A ∪ B)) : charge χ p B = 0 := by
  have h1 := charge_eq_zero_of_hasDecomp hχ hAB
  rw [charge_union χ p hdis, charge_eq_zero_of_hasDecomp hχ hA, zero_add] at h1
  exact h1

/-! ### The four charges -/

/-- F0: `2·χ₀ = e₀₁ - 2e₀₀ - 2e₁₁` in unordered counts. -/
def chi0 : Fin 2 → Fin 2 → ℤ := ![![-2, 1], ![1, -2]]

/-- F1: twice the diagonal counts minus the counts between `{0,1}` and `{2,3}`. -/
def chi1 : Fin 4 → Fin 4 → ℤ :=
  ![![2, 0, -1, -1], ![0, 2, -1, -1], ![-1, -1, 2, 0], ![-1, -1, 0, 2]]

/-- F2: twice `e₀₀ + e₁₁ + e₂₃` minus the counts between `{0,1}` and `{2,3}`. -/
def chi2 : Fin 4 → Fin 4 → ℤ :=
  ![![2, 0, -1, -1], ![0, 2, -1, -1], ![-1, -1, 0, 2], ![-1, -1, 2, 0]]

/-- F3, first charge: `e₀₁ + e₂₃ - e₀₂ - e₁₃`. -/
def chi3a : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, -1, 0], ![1, 0, 0, -1], ![-1, 0, 0, 1], ![0, -1, 1, 0]]

/-- F3, second charge: `e₀₁ + e₂₃ - e₀₃ - e₁₂`. -/
def chi3b : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, 0, -1], ![1, 0, -1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

theorem kills_chi0 : Kills chi0 F0 := by
  unfold Kills pair typeEdgeVec chi0 F0
  decide

theorem kills_chi1 : Kills chi1 F1 := by
  unfold Kills pair typeEdgeVec chi1 F1
  decide

theorem kills_chi2 : Kills chi2 F2 := by
  unfold Kills pair typeEdgeVec chi2 F2
  decide

theorem kills_chi3a : Kills chi3a F3 := by
  unfold Kills pair typeEdgeVec chi3a F3
  decide

theorem kills_chi3b : Kills chi3b F3 := by
  unfold Kills pair typeEdgeVec chi3b F3
  decide

/-- Each charge is nonzero on an edge type occurring in a permitted triangle, so it is a
genuine global constraint on leftovers, not an identity. -/
theorem chi0_active : ({0, 0, 1} : Multiset (Fin 2)) ∈ F0 ∧ chi0 0 1 + chi0 1 0 ≠ 0 := by
  decide

theorem chi1_active : ({0, 0, 2} : Multiset (Fin 4)) ∈ F1 ∧ chi1 0 2 + chi1 2 0 ≠ 0 := by
  decide

theorem chi2_active : ({0, 0, 2} : Multiset (Fin 4)) ∈ F2 ∧ chi2 0 2 + chi2 2 0 ≠ 0 := by
  decide

theorem chi3a_active : ({0, 1, 2} : Multiset (Fin 4)) ∈ F3 ∧ chi3a 0 1 + chi3a 1 0 ≠ 0 := by
  decide

theorem chi3b_active : ({0, 1, 3} : Multiset (Fin 4)) ∈ F3 ∧ chi3b 0 1 + chi3b 1 0 ≠ 0 := by
  decide

theorem chi0_bound (i j : Fin 2) : |chi0 i j| ≤ 2 := by
  revert i j; decide

theorem chi1_bound (i j : Fin 4) : |chi1 i j| ≤ 2 := by
  revert i j; decide

theorem chi2_bound (i j : Fin 4) : |chi2 i j| ≤ 2 := by
  revert i j; decide

theorem chi3a_bound (i j : Fin 4) : |chi3a i j| ≤ 1 := by
  revert i j; decide

theorem chi3b_bound (i j : Fin 4) : |chi3b i j| ≤ 1 := by
  revert i j; decide

end PartitionedTriangleAbsorption.TypedRefinerCharge
