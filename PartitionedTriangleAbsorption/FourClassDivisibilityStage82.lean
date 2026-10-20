/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.StructuralF3.Characterization
public import PartitionedTriangleAbsorption.ClassRepresentativesStage65

/-! # Explicit parity and opposite-pair counts discharge structural divisibility

The lattice characterization is reused. A complete host with class sizes
`a,b,b,b`, all even, is divisible. Deleting an even, opposite-balanced edge
set preserves this fact; no physical decomposition of the deleted set is
assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassDivisibilityStage82

open Finset ClassRepresentativesStage65 TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

theorem isIntDiv_iff_counts [Finite V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : StructuralF3.CrossClass p E) :
    IsIntDiv p F3 E ↔ (∀ v, Even (incidentLoad E v)) ∧
      edgeVec p E 0 1 + edgeVec p E 2 3 = edgeVec p E 0 2 + edgeVec p E 1 3 ∧
      edgeVec p E 0 1 + edgeVec p E 2 3 = edgeVec p E 0 3 + edgeVec p E 1 2 := by
  rw [StructuralF3.isIntDiv_F3_iff hcross,
    StructuralF3.charge_chi3a_eq, StructuralF3.charge_chi3b_eq]
  constructor
  · rintro ⟨heven, ha, hb⟩
    exact ⟨heven, by omega, by omega⟩
  · rintro ⟨heven, ha, hb⟩
    exact ⟨heven, by omega, by omega⟩

omit [DecidableEq V] in
theorem template_cross [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) :
    StructuralF3.CrossClass p G.edgeFinset := by
  intro a b he
  exact (hG a b).mp (SimpleGraph.mem_edgeFinset.mp he)

theorem complete_degVec [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (v : V) (j : Fin 4) :
    degVec p G.edgeFinset v j =
      if p v = j then 0 else ((classSet p j).card : ℤ) := by
  classical
  rw [TypedLoadCounterexample.degVec_edgeFinset]
  by_cases hv : p v = j
  · rw [ite_eq_left hv]
    have hf : univ.filter (fun w => G.Adj v w ∧ p w = j) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro w hw
      have hadj := (mem_filter.mp hw).2.1
      have hwj := (mem_filter.mp hw).2.2
      exact (hG v w).mp hadj (hv.trans hwj.symm)
    rw [hf]
    simp
  · rw [ite_eq_right hv]
    have hf : univ.filter (fun w => G.Adj v w ∧ p w = j) = classSet p j := by
      ext w
      simp only [classSet, mem_filter, mem_univ, true_and, hG]
      constructor
      · exact fun h => h.2
      · intro hw
        exact ⟨by simpa only [hw] using hv, hw⟩
    rw [hf]

omit [DecidableEq V] in
theorem complete_edgeVec [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (i j : Fin 4) :
    edgeVec p G.edgeFinset i j = if i = j then 0 else
      ((classSet p i).card : ℤ) * (classSet p j).card := by
  classical
  rw [TypedLoadCounterexample.edgeVec_eq_sum_degVec]
  have ht : ∀ v ∈ univ.filter (fun v => p v = i),
      degVec p G.edgeFinset v j =
        if i = j then 0 else ((classSet p j).card : ℤ) := by
    intro v hv
    rw [complete_degVec p G hG v j, (mem_filter.mp hv).2]
  rw [sum_congr rfl ht]
  by_cases hij : i = j
  · simp [hij]
  · simp only [ite_eq_right hij, sum_const, nsmul_eq_mul]
    rfl

theorem three_equal_host_isIntDiv [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (a b : ℕ) (ha : Even a) (hb : Even b)
    (hsize : ∀ i, (classSet p i).card = if i = 0 then a else b) :
    IsIntDiv p F3 G.edgeFinset := by
  classical
  have hcross := template_cross p G hG
  refine (isIntDiv_iff_counts p G.edgeFinset hcross).mpr ⟨?_, ?_, ?_⟩
  · intro v
    have hclasses : ∀ j, Even (classSet p j).card := by
      intro j
      rw [hsize]
      split_ifs
      · exact ha
      · exact hb
    have hdeg : Even ((incidentLoad G.edgeFinset v : ℕ) : ℤ) := by
      rw [← TypedDivisibilityCollapse.sum_degVec p G.edgeFinset hcross.loopless v]
      apply even_sum
      intro j _
      rw [complete_degVec p G hG v j]
      split_ifs
      · exact ⟨0, rfl⟩
      · exact (Int.even_coe_nat _).mpr (hclasses j)
    exact (Int.even_coe_nat _).mp hdeg
  · simp [complete_edgeVec p G hG, hsize]
  · simp [complete_edgeVec p G hG, hsize]

theorem three_equal_deleted_isIntDiv [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (a b : ℕ) (ha : Even a) (hb : Even b)
    (hsize : ∀ i, (classSet p i).card = if i = 0 then a else b)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (hFeven : ∀ v, Even (incidentLoad F v))
    (hFa : edgeVec p F 0 1 + edgeVec p F 2 3 = edgeVec p F 0 2 + edgeVec p F 1 3)
    (hFb : edgeVec p F 0 1 + edgeVec p F 2 3 = edgeVec p F 0 3 + edgeVec p F 1 2) :
    IsIntDiv p F3 (G.deleteEdges (F : Set (Sym2 V))).edgeFinset := by
  have hhost := three_equal_host_isIntDiv p G hG a b ha hb hsize
  have hdefect : IsIntDiv p F3 F :=
    (isIntDiv_iff_counts p F ((template_cross p G hG).mono hF)).mpr
      ⟨hFeven, hFa, hFb⟩
  simpa only [SimpleGraph.edgeFinset_deleteEdges] using hhost.sdiff hdefect hF

end PartitionedTriangleAbsorption.FourClassDivisibilityStage82
