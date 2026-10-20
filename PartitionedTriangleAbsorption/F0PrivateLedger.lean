/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Family

/-! # Root and auxiliary budgets for actual private absorber families. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0PrivateLedger

open Finset SignedHinge AntiEdgeSelection SparseReserveGeometry PrivateTemplateStage69

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- Count uses as a non-source vertex, rather than incident edges. -/
noncomputable def auxCount (s : Finset I) (P A : I → Finset (Sym2 V)) (v : V) : ℕ :=
  ∑ i ∈ s, if v ∈ vertSet (A i) ∧ v ∉ vertSet (P i) then 1 else 0

noncomputable def roots (s : Finset I) (P : I → Finset (Sym2 V)) (v : V) : ℕ :=
  ∑ i ∈ s, if v ∈ vertSet (P i) then 1 else 0

/-- Every source-root occurrence is paid by a source incidence. -/
theorem roots_le_incidence (s : Finset I) (P : I → Finset (Sym2 V)) (v : V) :
    roots s P v ≤ ∑ i ∈ s, incidentLoad (P i) v := by
  classical
  unfold roots
  refine sum_le_sum fun i _ => ?_
  by_cases hv : v ∈ vertSet (P i)
  · obtain ⟨e, he, hev⟩ := SignedHinge.mem_vertSet.mp hv
    have hp : 0 < incidentLoad (P i) v :=
      card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hev⟩⟩
    simpa only [hv, ite_true] using Nat.succ_le_of_lt hp
  · simp only [hv, ite_false]
    exact Nat.zero_le _

omit [Fintype V] in
/-- Incidences of the union are bounded by the incidences of its pieces. -/
theorem union_incidence_le (s : Finset I) (A : I → Finset (Sym2 V)) (v : V) :
    incidentLoad (s.biUnion A) v ≤ ∑ i ∈ s, incidentLoad (A i) v := by
  classical
  unfold incidentLoad
  rw [filter_biUnion]
  exact card_biUnion_le

/-- Bounded piece size pays root occurrences and auxiliary uses separately. -/
theorem incidence_le_counts (s : Finset I) (P A : I → Finset (Sym2 V)) (b : ℕ)
    (hsize : ∀ i ∈ s, (A i).card ≤ b) (v : V) :
    ∑ i ∈ s, incidentLoad (A i) v ≤ b * (roots s P v + auxCount s P A v) := by
  classical
  rw [roots, auxCount, ← sum_add_distrib, mul_sum]
  refine sum_le_sum fun i hi => ?_
  by_cases hroot : v ∈ vertSet (P i)
  · simpa only [hroot, not_true_eq_false, and_false, ite_true, ite_false,
      Nat.add_zero, Nat.mul_one] using (incidentLoad_le_card (A i) v).trans (hsize i hi)
  · by_cases haux : v ∈ vertSet (A i)
    · simpa only [hroot, haux, not_false_eq_true, and_self, ite_true, ite_false,
        Nat.zero_add, Nat.mul_one] using (incidentLoad_le_card (A i) v).trans (hsize i hi)
    · have hz : incidentLoad (A i) v = 0 := by
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨heA, hev⟩ := mem_filter.mp he
        exact haux (SignedHinge.mem_vertSet.mpr ⟨e, heA, hev⟩)
      simp [hroot, haux, hz]

/-- The total auxiliary mass is bounded by the number of actual pieces. -/
theorem aux_mass_le (s : Finset I) (P A : I → Finset (Sym2 V)) (b : ℕ)
    (hsize : ∀ i ∈ s, (vertSet (A i)).card ≤ b) :
    ∑ v, auxCount s P A v ≤ b * s.card := by
  classical
  unfold auxCount
  rw [sum_comm]
  calc
    (∑ i ∈ s, ∑ v, (if v ∈ vertSet (A i) ∧ v ∉ vertSet (P i) then 1 else 0 : ℕ))
        = ∑ i ∈ s, ((vertSet (A i)) \ vertSet (P i)).card := by
      refine sum_congr rfl fun i _ => ?_
      rw [← card_filter]
      congr 1
      ext v
      simp
    _ ≤ ∑ _i ∈ s, b := sum_le_sum fun i hi =>
      (card_le_card sdiff_subset).trans (hsize i hi)
    _ = b * s.card := by simp [Nat.mul_comm]

/-- The busy set is bounded using the same auxiliary counter as the construction. -/
theorem busy_card_le (s : Finset I) (P A : I → Finset (Sym2 V)) (b q T : ℕ)
    (hq : 0 < q) (hsize : ∀ i ∈ s, (vertSet (A i)).card ≤ b)
    (hbudget : b * s.card ≤ T * q) :
    (univ.filter fun v => q ≤ auxCount s P A v).card ≤ T := by
  classical
  let Z := univ.filter fun v => q ≤ auxCount s P A v
  have hlow : Z.card * q ≤ ∑ v, auxCount s P A v := by
    calc
      Z.card * q = ∑ _v ∈ Z, q := by simp
      _ ≤ ∑ v ∈ Z, auxCount s P A v :=
        sum_le_sum fun v hv => (mem_filter.mp hv).2
      _ ≤ ∑ v, auxCount s P A v := sum_le_sum_of_subset_of_nonneg
        (subset_univ Z) (fun _ _ _ => Nat.zero_le _)
  exact Nat.le_of_mul_le_mul_right ((hlow.trans (aux_mass_le s P A b hsize)).trans hbudget)
    hq

end PartitionedTriangleAbsorption.F0PrivateLedger
