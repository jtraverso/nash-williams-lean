/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedTransformerLabels
public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import PartitionedTriangleAbsorption.AntiEdgeSelection
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # The vertex conditions of typed divisibility collapse to parity

For a family whose members have three elements and which satisfies `ThreeStepLinks`
(F0--F3, kernel checked in `TypedTransformerLabels`), a loopless edge set is integrally
divisible exactly when

* every edge lies in some permitted triangle type (`ActiveEdges`),
* every vertex has even degree, and
* the global edge vector lies in the integral lattice of the type edge vectors.

So the per-vertex lattice conditions carry no information beyond parity and activity; the
only non-local constraint is the global one. This is used to certify concrete leftovers and
to identify exactly what a refiner piece must satisfy.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedDivisibilityCollapse

open Finset TypedTransformer AntiEdgeSelection

variable {t : ℕ}

/-- The standard basis vector. -/
def basis (a : Fin t) : Fin t → ℤ := fun j => if a = j then 1 else 0

theorem typeDegVec_triple (r a b : Fin t) :
    typeDegVec ({r, a, b} : Multiset (Fin t)) r = basis a + basis b := by
  funext j
  by_cases hr : r = j <;> by_cases ha : a = j <;> by_cases hb : b = j <;>
    simp [typeDegVec, basis, hr, ha, hb, eq_comm]

/-- The vertex lattice at a root part, as the range of an additive map. -/
def latticeHom (F : Finset (Multiset (Fin t))) (r : Fin t) :
    (Multiset (Fin t) → ℤ) →+ (Fin t → ℤ) where
  toFun c := ∑ τ ∈ F with r ∈ τ, c τ • typeDegVec τ r
  map_zero' := by simp
  map_add' c d := by simp [add_smul, sum_add_distrib]

theorem mem_range_latticeHom {F : Finset (Multiset (Fin t))} {r : Fin t} {d : Fin t → ℤ} :
    d ∈ (latticeHom F r).range ↔ ∃ c : Multiset (Fin t) → ℤ,
      d = ∑ τ ∈ F with r ∈ τ, c τ • typeDegVec τ r := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩

theorem link_mem {F : Finset (Multiset (Fin t))} {r a b : Fin t} (h : Link F r a b) :
    basis a + basis b ∈ (latticeHom F r).range := by
  rw [mem_range_latticeHom]
  refine ⟨fun σ => if σ = {r, a, b} then 1 else 0, ?_⟩
  have hr : r ∈ ({r, a, b} : Multiset (Fin t)) := by simp
  rw [← typeDegVec_triple r a b]
  have hmem : ({r, a, b} : Multiset (Fin t)) ∈ F.filter (r ∈ ·) := mem_filter.mpr ⟨h, hr⟩
  rw [sum_eq_single_of_mem _ hmem]
  · simp
  · intro σ _ hσ; dsimp only; rw [ite_eq_right hσ, zero_smul]

/-- With `ThreeStepLinks`, the sum of two active basis vectors lies in the lattice. -/
theorem active_pair_mem {F : Finset (Multiset (Fin t))} (hF : ThreeStepLinks F) {r a b : Fin t}
    (ha : ∃ c, Link F r a c) (hb : ∃ c, Link F r b c) :
    basis a + basis b ∈ (latticeHom F r).range := by
  obtain ⟨v, w, h1, h2, h3⟩ := hF r a b ha hb
  have m1 := link_mem h1
  have m2 := link_mem h2
  have m3 := link_mem h3
  have e : basis a + basis b = (basis a + basis v) - (basis v + basis w) + (basis w + basis b) := by
    abel
  rw [e]
  exact add_mem (sub_mem m1 m2) m3

/-- An even-sum vector supported on active link vertices lies in the vertex lattice. -/
theorem mem_of_active_even {F : Finset (Multiset (Fin t))} (hF : ThreeStepLinks F) {r : Fin t}
    (d : Fin t → ℤ) (hsupp : ∀ j, d j ≠ 0 → ∃ c, Link F r j c) (heven : Even (∑ j, d j)) :
    d ∈ (latticeHom F r).range := by
  by_cases h0 : ∃ a, ∃ c, Link F r a c
  · obtain ⟨a, ha⟩ := h0
    obtain ⟨m, hm⟩ := heven
    have hsum : (∑ j, d j • (basis j + basis a)) ∈ (latticeHom F r).range := by
      refine sum_mem fun j _ => ?_
      by_cases hj : d j = 0
      · rw [hj, zero_smul]; exact zero_mem _
      · exact zsmul_mem (active_pair_mem hF (hsupp j hj) ha) _
    have hsq : m • (basis a + basis a) ∈ (latticeHom F r).range :=
      zsmul_mem (active_pair_mem hF ha ha) _
    have e : d = (∑ j, d j • (basis j + basis a)) - m • (basis a + basis a) := by
      funext k
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        mul_add, sum_add_distrib, ← sum_mul, hm]
      simp only [basis, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
      split_ifs <;> ring
    rw [e]
    exact sub_mem hsum hsq
  · push Not at h0
    have : d = 0 := by
      funext j
      by_contra hj
      obtain ⟨c, hc⟩ := hsupp j hj
      exact h0 j c hc
    rw [this]
    exact zero_mem _

/-! ### Degree vectors -/

variable {V : Type*} [DecidableEq V]

/-- Every edge lies in some permitted triangle type. -/
def ActiveEdges (F : Finset (Multiset (Fin t))) (p : V → Fin t) (E : Finset (Sym2 V)) : Prop :=
  ∀ a b, s(a, b) ∈ E → ∃ c, Link F (p a) (p b) c

theorem sum_degContrib (p : V → Fin t) (v : V) {e : Sym2 V} (he : ¬ e.IsDiag) :
    ∑ j, degContrib p v e j = if v ∈ e then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (by simp [h])
    simp only [degContrib, Sym2.lift_mk, sum_add_distrib, Sym2.mem_iff]
    by_cases ha : a = v <;> by_cases hb : b = v
    · exact absurd (ha.trans hb.symm) hab
    · have hb' : ¬ v = b := fun h => hb h.symm
      simp [ha, hb, hb']
    · have ha' : ¬ v = a := fun h => ha h.symm
      simp [ha, hb, ha']
    · have h1 : ¬ v = a := fun h => ha h.symm
      have h2 : ¬ v = b := fun h => hb h.symm
      simp [ha, hb, h1, h2]

theorem sum_degVec (p : V → Fin t) (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (v : V) : ∑ j, degVec p E v j = (incidentLoad E v : ℤ) := by
  simp only [degVec, Finset.sum_apply]
  rw [sum_comm]
  rw [sum_congr rfl fun e he => sum_degContrib p v (hloop e he)]
  rw [incidentLoad, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]

theorem degContrib_nonneg (p : V → Fin t) (v : V) (e : Sym2 V) (j : Fin t) :
    0 ≤ degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk]
    split_ifs <;> norm_num

theorem exists_of_degVec_ne_zero {p : V → Fin t} {E : Finset (Sym2 V)} {v : V} {j : Fin t}
    (h : degVec p E v j ≠ 0) : ∃ b, s(v, b) ∈ E ∧ p b = j := by
  simp only [degVec, Finset.sum_apply] at h
  obtain ⟨e, he, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk] at hne
    by_cases h1 : a = v ∧ p b = j
    · obtain ⟨rfl, hb⟩ := h1
      exact ⟨b, he, hb⟩
    · by_cases h2 : b = v ∧ p a = j
      · obtain ⟨rfl, ha⟩ := h2
        exact ⟨a, by rwa [Sym2.eq_swap], ha⟩
      · simp [h1, h2] at hne

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- **Reverse direction.** Activity, parity and the global lattice condition give integral
divisibility, for every family with `ThreeStepLinks`. -/
theorem isIntDiv_of_active_even (hF : ThreeStepLinks F) {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (heven : ∀ v, Even (incidentLoad E v))
    (hedge : ∃ c : Multiset (Fin t) → ℤ, edgeVec p E = ∑ τ ∈ F, c τ • typeEdgeVec τ) :
    IsIntDiv p F E := by
  refine ⟨hedge, fun v => ?_⟩
  rw [← mem_range_latticeHom]
  apply mem_of_active_even hF
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := exists_of_degVec_ne_zero hj
    exact hact v b hb
  · rw [sum_degVec p E hloop v]
    obtain ⟨m, hm⟩ := heven v
    exact ⟨m, by rw [hm]; push_cast; ring⟩

/-- A member of a three-element multiset containing `r`, with a further occurrence of `a`. -/
theorem eq_triple_of_count {τ : Multiset (Fin t)} (hcard : Multiset.card τ = 3) {r a : Fin t}
    (hr : r ∈ τ) (ha : (τ.count a : ℤ) - (if a = r then 1 else 0) ≠ 0) :
    ∃ c, τ = {r, a, c} := by
  obtain ⟨τ', rfl⟩ := Multiset.exists_cons_of_mem hr
  have h2 : Multiset.card τ' = 2 := by simpa using hcard
  have hcount : τ'.count a ≠ 0 := by
    intro h0
    apply ha
    rw [Multiset.count_cons]
    split_ifs <;> simp_all
  obtain ⟨τ'', rfl⟩ := Multiset.exists_cons_of_mem (Multiset.count_ne_zero.mp hcount)
  have h1 : Multiset.card τ'' = 1 := by simpa using h2
  obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp h1
  exact ⟨c, rfl⟩

theorem sum_typeDegVec {τ : Multiset (Fin t)} (hcard : Multiset.card τ = 3) (r : Fin t) :
    ∑ j, typeDegVec τ r j = 2 := by
  simp only [typeDegVec, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]
  have : ∑ j : Fin t, (τ.count j : ℤ) = 3 := by
    exact_mod_cast (Multiset.sum_count_eq_card (by simp)).trans hcard
  rw [this]; norm_num

/-- **Forward direction, parity.** -/
theorem even_of_isIntDiv (hcard : ∀ τ ∈ F, Multiset.card τ = 3) {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (h : IsIntDiv p F E) (v : V) :
    Even (incidentLoad E v) := by
  obtain ⟨c, hc⟩ := h.2 v
  have hs := sum_degVec p E hloop v
  rw [hc] at hs
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [sum_comm] at hs
  rw [sum_congr rfl fun τ hτ => by
    rw [← mul_sum, sum_typeDegVec (hcard τ (mem_filter.mp hτ).1) (p v)]] at hs
  have : (incidentLoad E v : ℤ) = 2 * ∑ τ ∈ F with p v ∈ τ, c τ := by
    rw [← hs, mul_sum]; exact sum_congr rfl fun _ _ => by ring
  have hev : Even (incidentLoad E v : ℤ) := ⟨_, by rw [this]; ring⟩
  exact (Int.even_coe_nat _).mp hev

/-- **Forward direction, activity.** -/
theorem active_of_isIntDiv (hcard : ∀ τ ∈ F, Multiset.card τ = 3) {E : Finset (Sym2 V)}
    (h : IsIntDiv p F E) : ActiveEdges F p E := by
  intro a b hab
  obtain ⟨c, hc⟩ := h.2 a
  have hpos : degVec p E a (p b) ≠ 0 := by
    have hle : degContrib p a s(a, b) (p b) ≤ degVec p E a (p b) := by
      simp only [degVec, Finset.sum_apply]
      exact single_le_sum (fun e _ => degContrib_nonneg p a e (p b)) hab
    have h1 : 1 ≤ degContrib p a s(a, b) (p b) := by
      simp only [degContrib, Sym2.lift_mk]
      split_ifs <;> simp_all
    omega
  rw [hc] at hpos
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpos
  obtain ⟨τ, hτ, hne⟩ := exists_ne_zero_of_sum_ne_zero hpos
  obtain ⟨hτF, hrτ⟩ := mem_filter.mp hτ
  have hne' : typeDegVec τ (p a) (p b) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  obtain ⟨k, rfl⟩ := eq_triple_of_count (hcard τ hτF) hrτ hne'
  exact ⟨k, hτF⟩

/-- **Collapse of the vertex conditions.** -/
theorem isIntDiv_iff (hF : ThreeStepLinks F) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F E ↔ ActiveEdges F p E ∧ (∀ v, Even (incidentLoad E v)) ∧
      ∃ c : Multiset (Fin t) → ℤ, edgeVec p E = ∑ τ ∈ F, c τ • typeEdgeVec τ :=
  ⟨fun h => ⟨active_of_isIntDiv hcard h, even_of_isIntDiv hcard hloop h, h.1⟩,
    fun ⟨ha, he, hc⟩ => isIntDiv_of_active_even hF hloop ha he hc⟩

end PartitionedTriangleAbsorption.TypedDivisibilityCollapse
