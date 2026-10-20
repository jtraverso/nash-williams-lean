/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Refiner

@[expose] public section

/-! Multiplicities must be counted in the WHOLE fixed library, not in a
selection depending on the leftover. These finite double-counting lemmas
provide the demand weights for routing virtual reserve edges. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption AntiEdgeSelection

variable {I V : Type*} [DecidableEq I] [DecidableEq V]

def libraryMultiplicity (lib : Finset I) (P : I → Finset (Sym2 V))
    (e : Sym2 V) : ℕ := (lib.filter fun j => e ∈ P j).card

theorem sum_libraryMultiplicity (lib : Finset I) (P : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) :
    ∑ e ∈ R, libraryMultiplicity lib P e = ∑ j ∈ lib, (R ∩ P j).card := by
  calc
    ∑ e ∈ R, libraryMultiplicity lib P e =
        ∑ e ∈ R, ∑ j ∈ lib, if e ∈ P j then 1 else 0 := by
      simp only [libraryMultiplicity, card_eq_sum_ones, sum_filter]
    _ = ∑ j ∈ lib, ∑ e ∈ R, if e ∈ P j then 1 else 0 := sum_comm
    _ = ∑ j ∈ lib, (R ∩ P j).card := by
      apply sum_congr rfl
      intro j hj
      rw [show R ∩ P j = R.filter (fun e => e ∈ P j) by ext e; simp]
      simp only [card_eq_sum_ones, sum_filter]

theorem sum_libraryMultiplicity_le (lib : Finset I) (P : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) (m : ℕ) (hm : ∀ j ∈ lib, (P j).card ≤ m) :
    ∑ e ∈ R, libraryMultiplicity lib P e ≤ lib.card * m := by
  rw [sum_libraryMultiplicity]
  calc
    ∑ j ∈ lib, (R ∩ P j).card ≤ ∑ j ∈ lib, m :=
      sum_le_sum fun j hj => (card_le_card inter_subset_right).trans (hm j hj)
    _ = lib.card * m := by simp

theorem libraryMultiplicity_le_incidence (lib : Finset I) (P : I → Finset (Sym2 V))
    (e : Sym2 V) (v : V) (hv : v ∈ e) :
    libraryMultiplicity lib P e ≤ ∑ j ∈ lib, incidentLoad (P j) v := by
  simp only [libraryMultiplicity, card_eq_sum_ones, sum_filter]
  apply sum_le_sum
  intro j hj
  split_ifs with he
  · exact Nat.succ_le_of_lt (card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hv⟩⟩)
  · exact Nat.zero_le _

theorem weighted_root_load_le (lib : Finset I) (P : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) (v : V) :
    ∑ e ∈ R.filter (fun e => v ∈ e), libraryMultiplicity lib P e ≤
      ∑ j ∈ lib, incidentLoad (P j) v := by
  rw [sum_libraryMultiplicity]
  apply sum_le_sum
  intro j hj
  apply card_le_card
  intro e he
  obtain ⟨heR, heP⟩ := mem_inter.mp he
  exact mem_filter.mpr ⟨heP, (mem_filter.mp heR).2⟩

#print axioms sum_libraryMultiplicity
#print axioms sum_libraryMultiplicity_le
#print axioms libraryMultiplicity_le_incidence
#print axioms weighted_root_load_le

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
