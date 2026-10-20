/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.SubdivisionRefiner

@[expose] public section

/-! Exact whole-library accounting for a fixed physical edge substitution.
The auxiliary ledger is separate from the original endpoint incidences.
These lemmas do not assume or construct the required paths. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption AntiEdgeSelection

variable {I V : Type*} [DecidableEq I] [DecidableEq V]

theorem library_weighted_sum (lib : Finset I) (P : I → Finset (Sym2 V))
    (D : Finset (Sym2 V)) (hD : ∀ j ∈ lib, P j ⊆ D) (g : Sym2 V → ℕ) :
    ∑ j ∈ lib, ∑ e ∈ P j, g e =
      ∑ e ∈ D, libraryMultiplicity lib P e * g e := by
  calc
    _ = ∑ j ∈ lib, ∑ e ∈ D, if e ∈ P j then g e else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      congr 1
      ext e
      simp only [mem_filter]
      exact ⟨fun he => ⟨hD j hj he, he⟩, fun he => he.2⟩
    _ = ∑ e ∈ D, ∑ j ∈ lib, if e ∈ P j then g e else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro e he
      simp only [libraryMultiplicity, card_eq_sum_ones, sum_filter, sum_mul]
      apply sum_congr rfl
      intro j hj
      split_ifs <;> simp

theorem subdivide_library_load (lib : Finset I) (P : I → Finset (Sym2 V))
    (D : Finset (Sym2 V)) (hD : ∀ j ∈ lib, P j ⊆ D)
    (f : Sym2 V → Finset (Sym2 V))
    (hf : (D : Set (Sym2 V)).PairwiseDisjoint f) (v : V) :
    ∑ j ∈ lib, incidentLoad (subdivideEdges f (P j)) v =
      ∑ e ∈ D, libraryMultiplicity lib P e * incidentLoad (f e) v := by
  calc
    _ = ∑ j ∈ lib, ∑ e ∈ P j, incidentLoad (f e) v := by
      apply sum_congr rfl
      intro j hj
      exact ModThreeLayer.incidentLoad_biUnion_eq (P j) f
        (hf.subset (by exact_mod_cast hD j hj)) v
    _ = _ := library_weighted_sum lib P D hD _

theorem library_weighted_endpoints (lib : Finset I) (P : I → Finset (Sym2 V))
    (D : Finset (Sym2 V)) (hD : ∀ j ∈ lib, P j ⊆ D) (v : V) :
    ∑ e ∈ D, libraryMultiplicity lib P e * (if v ∈ e then 1 else 0) =
      ∑ j ∈ lib, incidentLoad (P j) v := by
  rw [← library_weighted_sum lib P D hD]
  apply sum_congr rfl
  intro j hj
  simp only [incidentLoad, card_eq_sum_ones, sum_filter]

/-- `aux e` is the excess incidence of the replacement over its endpoints.
For a simple path it is twice the indicator of an internal vertex. -/
theorem subdivide_library_load_le (lib : Finset I) (P : I → Finset (Sym2 V))
    (D : Finset (Sym2 V)) (hD : ∀ j ∈ lib, P j ⊆ D)
    (f : Sym2 V → Finset (Sym2 V))
    (hf : (D : Set (Sym2 V)).PairwiseDisjoint f) (v : V)
    (aux : Sym2 V → ℕ)
    (ha : ∀ e ∈ D, incidentLoad (f e) v ≤ (if v ∈ e then 1 else 0) + aux e) :
    ∑ j ∈ lib, incidentLoad (subdivideEdges f (P j)) v ≤
      (∑ j ∈ lib, incidentLoad (P j) v) +
      ∑ e ∈ D, libraryMultiplicity lib P e * aux e := by
  rw [subdivide_library_load lib P D hD f hf v]
  calc
    _ ≤ ∑ e ∈ D, libraryMultiplicity lib P e *
        ((if v ∈ e then 1 else 0) + aux e) :=
      sum_le_sum fun e he => Nat.mul_le_mul_left _ (ha e he)
    _ = _ := by
      simp only [Nat.mul_add, sum_add_distrib]
      rw [library_weighted_endpoints lib P D hD v]

#print axioms library_weighted_sum
#print axioms subdivide_library_load
#print axioms library_weighted_endpoints
#print axioms subdivide_library_load_le

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
