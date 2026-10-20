/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Order.WellFoundedSet
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic

@[expose] public section

/-! Finite zero-charge recipes, including torsion in the target group.
This is an algebraic grouping theorem, NOT a physical shared refiner.
Finiteness is Dickson's lemma; no bound on the host order is used. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

def chargeMass (x : ι → ℕ) : ℕ := ∑ i, x i

def ChargeAtom (f : (ι → ℕ) →+ A) (x : ι → ℕ) : Prop :=
  Minimal (fun y => y ≠ 0 ∧ f y = 0) x

theorem chargeAtoms_finite (f : (ι → ℕ) →+ A) :
    {x | ChargeAtom f x}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro a ha b hb hne hab
  exact hne (le_antisymm hab (hb.2 ha.1 hab))

theorem chargeMass_pos {x : ι → ℕ} (hx : x ≠ 0) : 0 < chargeMass x := by
  classical
  by_contra hn
  have hz : chargeMass x = 0 := by omega
  apply hx
  funext i
  have hi : x i ≤ chargeMass x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  change x i = 0
  omega

/-- Every nonnegative zero-charge vector splits into minimal recipes.
The recipes preserve every coordinate exactly, not only the total charge. -/
theorem chargeAtoms_decompose (f : (ι → ℕ) →+ A) (x : ι → ℕ) (hx : f x = 0) :
    ∃ l : List (ι → ℕ), l.sum = x ∧ ∀ a ∈ l, ChargeAtom f a := by
  classical
  generalize hn : chargeMass x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hz : x = 0
    · exact ⟨[], by simp [hz], by simp⟩
    obtain ⟨a, hax, ha⟩ :=
      (Set.isPWO_of_wellQuasiOrderedLE {y : ι → ℕ | y ≠ 0 ∧ f y = 0}).exists_le_minimal
        (show x ∈ {y : ι → ℕ | y ≠ 0 ∧ f y = 0} from ⟨hz, hx⟩)
    have hsum : a + (x - a) = x := by
      funext i
      exact Nat.add_sub_of_le (hax i)
    have hrest : f (x - a) = 0 := by
      have he := congrArg f hsum
      rw [map_add, ha.1.2, zero_add, hx] at he
      exact he
    have hm : chargeMass a + chargeMass (x - a) = chargeMass x := by
      simpa only [chargeMass, Pi.add_apply, sum_add_distrib] using congrArg chargeMass hsum
    have hlt : chargeMass (x - a) < n := by
      have hp := chargeMass_pos ha.1.1
      omega
    obtain ⟨l, hl, hla⟩ := ih _ hlt (x - a) hrest rfl
    refine ⟨a :: l, ?_, ?_⟩
    · simpa only [List.sum_cons, hl] using hsum
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hla b hb

/-- The finite catalog and its size cap are chosen before the demand.
This does not assert a sparse network realizing all selections physically. -/
theorem exists_bounded_charge_catalog (f : (ι → ℕ) →+ A) :
    ∃ (catalog : Finset (ι → ℕ)) (K : ℕ), 0 < K ∧
      (∀ a ∈ catalog, ChargeAtom f a ∧ chargeMass a ≤ K) ∧
      ∀ x, f x = 0 → ∃ l : List (ι → ℕ),
        l.sum = x ∧ ∀ a ∈ l, a ∈ catalog := by
  classical
  let catalog := (chargeAtoms_finite f).toFinset
  refine ⟨catalog, max 1 (catalog.sup chargeMass), by omega, ?_, ?_⟩
  · intro a ha
    have ha' : ChargeAtom f a := by
      simpa only [catalog, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using ha
    refine ⟨ha', ?_⟩
    exact (Finset.le_sup (f := chargeMass) ha).trans (le_max_right _ _)
  · intro x hx
    obtain ⟨l, hl, ha⟩ := chargeAtoms_decompose f x hx
    refine ⟨l, hl, fun a h => ?_⟩
    simpa only [catalog, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using ha a h

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer

#print axioms PartitionedTriangleAbsorption.BlowupB.UniversalProducer.chargeAtoms_finite
#print axioms PartitionedTriangleAbsorption.BlowupB.UniversalProducer.chargeAtoms_decompose
#print axioms PartitionedTriangleAbsorption.BlowupB.UniversalProducer.exists_bounded_charge_catalog
