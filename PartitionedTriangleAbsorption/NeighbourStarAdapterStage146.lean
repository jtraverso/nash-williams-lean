/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.GraphStarInventoryStage144
public import PartitionedTriangleAbsorption.StarPhysicalMatchingStage145

/-! # Prescribed matchings on the actual neighbours of a centre

The local labels put the centre's class first and retain the three pairing
indices used by the integer allocation. Missing and forbidden edges are
restricted from the ambient graph, not supplied as a relation on new objects.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NeighbourStarAdapterStage146

open Finset MatchedQuotaStage140 GraphStarInventoryStage144
open StarPairProfileStage145 StarPhysicalMatchingStage145
open CleanupSupplyStage140 ClassRepresentativesStage65

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindex the four classes without changing the three quota indices. -/
noncomputable def rootLabels (c : Fin 4) : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (Fin.cases c (fun i : Fin 3 => partner i c))
    (by fin_cases c <;> decide)

theorem rootLabels_zero (c : Fin 4) : rootLabels c 0 = c := rfl

theorem rootLabels_succ (c : Fin 4) (i : Fin 3) :
    rootLabels c i.succ = partner i c := by
  simp [rootLabels]

abbrev Neighbours (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :=
  ↥(G.neighborFinset v)

noncomputable def localLabel (p : V → Fin 4) (v w : V) : Fin 4 :=
  (rootLabels (p v)).symm (p w)

omit [Fintype V] [DecidableEq V] in
theorem localLabel_eq (p : V → Fin 4) (v w : V) (j : Fin 4) :
    localLabel p v w = j ↔ p w = rootLabels (p v) j := by
  exact (rootLabels (p v)).symm_apply_eq

omit [Fintype V] [DecidableEq V] in
/-- Filtering a finite subtype counts exactly the ambient filtered set. -/
theorem subtype_filter_card (s : Finset V) (P : V → Prop) [DecidablePred P] :
    (univ.filter fun w : s => P w).card = (s.filter P).card := by
  apply card_bij (fun w _ => w.val)
  · intro w hw
    exact mem_filter.mpr ⟨w.property, (mem_filter.mp hw).2⟩
  · intro w _ z _ he
    exact Subtype.ext he
  · intro w hw
    obtain ⟨hs, hp⟩ := mem_filter.mp hw
    exact ⟨⟨w, hs⟩, mem_filter.mpr ⟨mem_univ _, hp⟩, rfl⟩

omit [DecidableEq V] in
theorem neighbour_class_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) (j : Fin 4) :
    (univ.filter fun w : Neighbours G v => localLabel p v w = j).card =
      classLoad p G v (rootLabels (p v) j) := by
  classical
  simp_rw [localLabel_eq]
  exact subtype_filter_card (G.neighborFinset v) (fun w => p w = rootLabels (p v) j)

/-- A local missing-neighbour count is bounded by the ambient one. -/
theorem neighbour_missing_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) (w : Neighbours G v) :
    (univ.filter fun z : Neighbours G v =>
      localLabel p v z ≠ localLabel p v w ∧ ¬ G.Adj w z).card ≤
        (missingOutside G p w).card := by
  classical
  rw [subtype_filter_card (G.neighborFinset v)
    (fun z => localLabel p v z ≠ localLabel p v w ∧ ¬ G.Adj w z)]
  apply card_le_card
  intro z hz
  obtain ⟨_, hne, hnot⟩ := mem_filter.mp hz
  have hp : p z ≠ p w := by
    intro he
    exact hne (congrArg (rootLabels (p v)).symm he)
  simp only [missingOutside, mem_sdiff, mem_compl, classSet, mem_filter,
    mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact ⟨hp, hnot⟩

omit [DecidableEq V] in
theorem neighbour_forbidden_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : V → V → Prop) [DecidableRel B] (v : V) (w : Neighbours G v) :
    (univ.filter fun z : Neighbours G v => B w z).card ≤
      (univ.filter fun z : V => B w z).card := by
  rw [subtype_filter_card (G.neighborFinset v) (fun z => B w z)]
  apply card_le_card
  intro z hz
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩

/-- Realize an allocated row by real, unused edges joining actual neighbours. -/
theorem exists_neighbour_star_pairing (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) (x : Fin 3 → ℕ)
    (B : V → V → Prop) [DecidableRel B]
    (hB : ∀ u w, B u w → B w u) (L D U : ℕ)
    (heven : G.degree v = 2 * (G.degree v / 2))
    (ha : classLoad p G v (p v) ≤ G.degree v / 2)
    (hrow : ∑ i, x i = classLoad p G v (p v))
    (hx : ∀ i,
      classLoad p G v (p v) + classLoad p G v (partner i (p v)) -
          G.degree v / 2 ≤ x i ∧ x i ≤ classLoad p G v (partner i (p v)))
    (hclasses : ∀ j, (classSet p j).card ≤ L)
    (hmissing : ∀ w : Neighbours G v, (missingOutside G p w).card ≤ D)
    (hused : ∀ w, (univ.filter fun z => B w z).card ≤ U)
    (hmargin : 2 * L + 4 * (D + U) + 2 < G.degree v) :
    ∃ f : Neighbours G v ≃ Neighbours G v,
      Function.Involutive f ∧ (∀ w : Neighbours G v, p (f w) ≠ p w) ∧
      (∀ w : Neighbours G v, G.Adj w (f w) ∧ ¬ B w (f w)) ∧
      ∀ j k, (univ.filter fun w : Neighbours G v =>
        localLabel p v w = j ∧ localLabel p v (f w) = k).card =
          pairDemand (classLoad p G v (p v)) (G.degree v / 2)
            (fun i => classLoad p G v (partner i (p v))) x j k := by
  classical
  let a := classLoad p G v (p v)
  let b : Fin 3 → ℕ := fun i => classLoad p G v (partner i (p v))
  have hc (j : Fin 4) :
      classLoad p G v (rootLabels (p v) j) = classSize a b j := by
    fin_cases j <;> rfl
  have hu (j : Fin 4) : classSize a b j ≤ L := by
    rw [← hc j]
    exact (classLoad_le_class_card p G v _).trans (hclasses _)
  have hm (w : Neighbours G v) :
      (univ.filter fun z : Neighbours G v =>
        localLabel p v z ≠ localLabel p v w ∧ ¬ G.Adj w z).card ≤ D :=
    (neighbour_missing_le G p v w).trans (hmissing w)
  have hb (w : Neighbours G v) :
      (univ.filter fun z : Neighbours G v => B w z).card ≤ U :=
    (neighbour_forbidden_le G B v w).trans (hused w)
  obtain ⟨f, hf, hp, hphysical, hcount, _, _, _⟩ := exists_star_pairing_of_degree
    (fun w z : Neighbours G v => G.Adj w z ∧ ¬ B w z)
    (fun w z hwz => ⟨hwz.1.symm, fun h => hwz.2 (hB _ _ h)⟩)
    (fun w => localLabel p v w) a (G.degree v / 2) b x
    ((degree_inventory p G v).trans heven) ha hrow hx
    (fun j => (neighbour_class_count G p v j).trans (hc j))
    L (D + U) hu (by omega)
    (PrescribedPhysicalPairingStage145.cross_missing_avoiding _ _ _ D U hm hb)
  refine ⟨f, hf, ?_, hphysical, hcount⟩
  intro w he
  exact hp w (congrArg (rootLabels (p v)).symm he)

end PartitionedTriangleAbsorption.NeighbourStarAdapterStage146
