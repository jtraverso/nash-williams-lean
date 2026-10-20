/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalParity

@[expose] public section

/-!
# Charge units and ordinary divisibility for physical F1/F2 pieces
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge

variable {V : Type*} [DecidableEq V]

theorem F1Good_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F1 E) : F1Good p E := by
  obtain ⟨hact, heven, _⟩ := (TypedPieceConditions.F1_isIntDiv_iff hloop).mp hd
  refine ⟨hloop, hact, heven, ?_⟩
  rw [f1FreeCharge_eq_original p E hact]
  exact charge_eq_zero_of_isIntDiv kills_chi1 hd

theorem F2Good_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F2 E) : F2Good p E := by
  obtain ⟨hact, heven, _⟩ := (TypedPieceConditions.F2_isIntDiv_iff hloop).mp hd
  refine ⟨hloop, hact, heven, ?_⟩
  rw [f2FreeCharge_eq_original p E hact]
  exact charge_eq_zero_of_isIntDiv kills_chi2 hd

theorem F1Good_even3 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hgood : F1Good p E) : OnePart.Even3 E := by
  refine ⟨?_, hgood.2.2.1⟩
  have hthree : (3 : ℤ) ∣ (E.card : ℤ) := by
    rw [f1_total_count p E hgood.2.1]
    exact freeCharge_zero_three_dvd _ _ hgood.2.2.2
  exact_mod_cast hthree

theorem F2Good_even3 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hgood : F2Good p E) : OnePart.Even3 E := by
  refine ⟨?_, hgood.2.2.1⟩
  have hthree : (3 : ℤ) ∣ (E.card : ℤ) := by
    rw [f2_total_count p E hgood.2.1]
    exact freeCharge_zero_three_dvd _ _ hgood.2.2.2
  exact_mod_cast hthree

theorem even3_of_isIntDiv_F1 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F1 E) : OnePart.Even3 E :=
  F1Good_even3 p E (F1Good_of_isIntDiv p E hloop hd)

theorem even3_of_isIntDiv_F2 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F2 E) : OnePart.Even3 E :=
  F2Good_even3 p E (F2Good_of_isIntDiv p E hloop hd)

theorem onePart_of_isIntDiv_F1 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F1 E) :
    IsIntDiv OnePart.part1 OnePart.triFam E :=
  (OnePart.isIntDiv_part1_iff E hloop).mpr (even3_of_isIntDiv_F1 p E hloop hd)

theorem onePart_of_isIntDiv_F2 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hd : IsIntDiv p F2 E) :
    IsIntDiv OnePart.part1 OnePart.triFam E :=
  (OnePart.isIntDiv_part1_iff E hloop).mpr (even3_of_isIntDiv_F2 p E hloop hd)

theorem crossCount_two_dvd_F1 [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F1 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) : (2 : ℤ) ∣ crossCount p E := by
  obtain ⟨h0, h1, _⟩ := f1_class_cut_parities p E hact hloop heven
  simpa only [crossCount, add_assoc] using dvd_add h0 h1

theorem crossCount_two_dvd_F2 [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F2 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) : (2 : ℤ) ∣ crossCount p E := by
  obtain ⟨h0, h1, _⟩ := f2_class_cut_parities p E hact hloop heven
  simpa only [crossCount, add_assoc] using dvd_add h0 h1

/-- Charge is an integer multiple of twelve on every ordinary-divisible active F1 piece. -/
theorem twelve_dvd_chi1 [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F1 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) (hthree : 3 ∣ E.card) :
    (12 : ℤ) ∣ charge chi1 p E := by
  have ht : (3 : ℤ) ∣ f1Base p E + crossCount p E := by
    rw [← f1_total_count p E hact]
    exact_mod_cast hthree
  rw [← f1FreeCharge_eq_original p E hact]
  exact twelve_dvd_freeCharge _ _ ht (crossCount_two_dvd_F1 p E hact hloop heven)

/-- Charge is an integer multiple of twelve on every ordinary-divisible active F2 piece. -/
theorem twelve_dvd_chi2 [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F2 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) (hthree : 3 ∣ E.card) :
    (12 : ℤ) ∣ charge chi2 p E := by
  have ht : (3 : ℤ) ∣ f2Base p E + crossCount p E := by
    rw [← f2_total_count p E hact]
    exact_mod_cast hthree
  rw [← f2FreeCharge_eq_original p E hact]
  exact twelve_dvd_freeCharge _ _ ht (crossCount_two_dvd_F2 p E hact hloop heven)

#print axioms even3_of_isIntDiv_F1
#print axioms even3_of_isIntDiv_F2
#print axioms onePart_of_isIntDiv_F1
#print axioms onePart_of_isIntDiv_F2
#print axioms twelve_dvd_chi1
#print axioms twelve_dvd_chi2

end PaddedF12
