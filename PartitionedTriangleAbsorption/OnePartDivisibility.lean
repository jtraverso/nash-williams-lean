/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeFamily
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Integral divisibility for the one-part triangle family on arbitrary edge sets

For `t = 1` and `F = {T₀₀₀}` (ordinary triangles), integral divisibility of an edge set
without loops means: the number of edges is divisible by three and every degree is even.
`Sanity.isIntDiv_K3_iff` proves this for `G.edgeFinset`; here it is proved for an arbitrary
loopless edge set, without importing the unfinished `NashWilliams` file.

`part1` and `triFam` have the same bodies as `Sanity.onePart` and `Sanity.K3fam`.
Degrees are `AntiEdgeSelection.incidentLoad`, the number of incident edges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.OnePart

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- The trivial one-part partition. -/
def part1 : V → Fin 1 := fun _ => 0

/-- The one-part triangle family `{T₀₀₀}`. -/
def triFam : Finset (Multiset (Fin 1)) := {{0, 0, 0}}

/-- An edge set has even degrees and a multiple of three edges. -/
def Even3 (E : Finset (Sym2 V)) : Prop :=
  3 ∣ E.card ∧ ∀ v, Even (incidentLoad E v)

omit [DecidableEq V] in
theorem edgeVec_part1 (E : Finset (Sym2 V)) :
    edgeVec part1 E 0 0 = 2 * E.card := by
  rw [edgeVec, Finset.sum_apply, Finset.sum_apply, card_eq_sum_ones, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ u v => simp [pairVec, part1]

theorem degVec_part1 (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag) (v : V) :
    degVec part1 E v 0 = incidentLoad E v := by
  rw [incidentLoad, degVec, Finset.sum_apply, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => hE _ he (by simp [h])
    by_cases ha : a = v
    · subst ha; simp [degContrib, part1, hab.symm]
    · by_cases hb : b = v
      · subst hb; simp [degContrib, part1, ha]
      · simp [degContrib, ha, hb, Ne.symm ha, Ne.symm hb]

/-- **One-part integral divisibility.** For loopless edge sets, integral `{T₀₀₀}`-divisibility
is: three divides the number of edges and every degree is even. -/
theorem isIntDiv_part1_iff (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv part1 triFam E ↔ Even3 E := by
  have hF : ∀ (v : V), ({{0, 0, 0}} : Finset (Multiset (Fin 1))).filter
      (fun τ => part1 v ∈ τ) = {{0, 0, 0}} := by
    intro v
    apply filter_eq_self.mpr
    intro τ hτ
    have hτ := mem_singleton.mp hτ
    subst τ
    change (0 : Fin 1) ∈ ({0, 0, 0} : Multiset (Fin 1))
    decide
  have hEv : typeEdgeVec ({0, 0, 0} : Multiset (Fin 1)) 0 0 = 6 := by decide
  have hD : ∀ v : V, typeDegVec ({0, 0, 0} : Multiset (Fin 1)) (part1 v) 0 = 2 := by
    intro v; simp only [part1]; decide
  have funext2 : ∀ f g : Fin 1 → Fin 1 → ℤ, f = g ↔ f 0 0 = g 0 0 := fun f g =>
    ⟨fun h => by rw [h], fun h => by funext i j; fin_cases i; fin_cases j; exact h⟩
  have funext1 : ∀ f g : Fin 1 → ℤ, f = g ↔ f 0 = g 0 := fun f g =>
    ⟨fun h => by rw [h], fun h => by funext i; fin_cases i; exact h⟩
  simp only [IsIntDiv, hF, triFam, sum_singleton, funext2, funext1, Pi.smul_apply,
    smul_eq_mul, hEv, hD, edgeVec_part1, degVec_part1 E hE, Even3]
  constructor
  · rintro ⟨⟨c, hc⟩, hv⟩
    refine ⟨?_, fun v => ?_⟩
    · have : (3 : ℤ) ∣ E.card := ⟨c _, by linarith⟩
      exact_mod_cast this
    · obtain ⟨c, hc⟩ := hv v
      have : Even (incidentLoad E v : ℤ) := ⟨c _, by linarith⟩
      exact_mod_cast this
  · rintro ⟨⟨k, hk⟩, hv⟩
    refine ⟨⟨fun _ => k, by rw [hk]; push_cast; ring⟩, fun v => ?_⟩
    obtain ⟨m, hm⟩ := hv v
    exact ⟨fun _ => m, by rw [hm]; push_cast; ring⟩

/-- Degrees add over disjoint unions. -/
theorem incidentLoad_union {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    incidentLoad (A ∪ B) v = incidentLoad A v + incidentLoad B v := by
  unfold incidentLoad
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

theorem incidentLoad_empty (v : V) : incidentLoad (∅ : Finset (Sym2 V)) v = 0 := by
  simp [incidentLoad]

/-- Even degrees are preserved by disjoint unions. -/
theorem even_incidentLoad_union {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : ∀ v, Even (incidentLoad A v)) (hB : ∀ v, Even (incidentLoad B v)) (v : V) :
    Even (incidentLoad (A ∪ B) v) := by
  rw [incidentLoad_union h]
  exact (hA v).add (hB v)

/-- Even degrees are preserved by pairwise disjoint finite unions. -/
theorem even_incidentLoad_biUnion {I : Type*} (s : Finset I) (E : I → Finset (Sym2 V))
    (hdis : (s : Set I).PairwiseDisjoint E) (hE : ∀ i ∈ s, ∀ v, Even (incidentLoad (E i) v)) :
    ∀ v, Even (incidentLoad (s.biUnion E) v) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro v; simp [incidentLoad_empty]
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine even_incidentLoad_union ?_ (hE a (mem_insert_self _ _))
      (ih (hdis.subset (by simp)) (fun i hi => hE i (mem_insert_of_mem hi)))
    rw [disjoint_biUnion_right]
    intro i hi
    exact hdis (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

end PartitionedTriangleAbsorption.OnePart

