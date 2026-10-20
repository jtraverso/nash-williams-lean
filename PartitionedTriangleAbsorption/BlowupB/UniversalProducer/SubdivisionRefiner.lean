/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.LibraryWeights
import PartitionedTriangleAbsorption.UniversalRefiner.Physical

/-! Transport a fixed refiner by an edge-disjoint subdivision that fixes X.
This is a proved consumer of explicit edge replacements, not their producer.
The replacement is fixed once for the whole library, before the leftover. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption AntiEdgeSelection StructuralF3General
open UniversalRefiner

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

def subdivideEdges (f : Sym2 V → Finset (Sym2 V)) (E : Finset (Sym2 V)) := E.biUnion f

theorem subdivide_disjoint (f : Sym2 V → Finset (Sym2 V))
    {D A B : Finset (Sym2 V)} (hf : (D : Set (Sym2 V)).PairwiseDisjoint f)
    (hA : A ⊆ D) (hB : B ⊆ D) (hd : Disjoint A B) :
    Disjoint (subdivideEdges f A) (subdivideEdges f B) := by
  unfold subdivideEdges
  rw [disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  exact hf (hA ha) (hB hb) (fun h => disjoint_left.mp hd ha (h ▸ hb))

theorem subdivide_fixed (f : Sym2 V → Finset (Sym2 V)) {X A : Finset (Sym2 V)}
    (hf : ∀ e ∈ X, f e = {e}) (hA : A ⊆ X) : subdivideEdges f A = A := by
  ext e
  simp only [subdivideEdges, mem_biUnion]
  constructor
  · rintro ⟨a, ha, hea⟩
    rw [hf a (hA ha), mem_singleton] at hea
    exact hea ▸ ha
  · intro he
    exact ⟨e, he, by rw [hf e (hA he)]; simp⟩

theorem subdivide_even (f : Sym2 V → Finset (Sym2 V))
    {D A : Finset (Sym2 V)} (hf : (D : Set (Sym2 V)).PairwiseDisjoint f)
    (hp : ∀ e ∈ D, ∀ v, (incidentLoad (f e) v : ZMod 2) = symInd e v)
    (hA : A ⊆ D) (heven : ∀ v, Even (incidentLoad A v)) :
    ∀ v, Even (incidentLoad (subdivideEdges f A) v) := by
  intro v
  have hinc := ModThreeLayer.incidentLoad_biUnion_eq A f
    (hf.subset (by exact_mod_cast hA)) v
  rw [← ZMod.natCast_eq_zero_iff_even]
  change (incidentLoad (A.biUnion f) v : ZMod 2) = 0
  rw [hinc, Nat.cast_sum]
  rw [sum_congr rfl fun e he => hp e (hA he) v]
  have hzero := congrFun (sum_symInd_eq_zero heven) v
  simpa [Finset.sum_apply] using hzero

theorem subdivide_card_le (f : Sym2 V → Finset (Sym2 V))
    {D A : Finset (Sym2 V)} (L : ℕ) (hf : ∀ e ∈ D, (f e).card ≤ L)
    (hA : A ⊆ D) : (subdivideEdges f A).card ≤ A.card * L := by
  calc
    _ ≤ ∑ e ∈ A, (f e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ A, L := sum_le_sum fun e he => hf e (hA he)
    _ = _ := by simp

/-- A single, leftover-independent physical subdivision transports all
selections. Size and load estimates are separate numerical obligations. -/
def subdividePredRefiner {X : Finset (Sym2 V)} {Q : Finset (Sym2 V) → Prop}
    (E : PredRefiner I X Q) (f : Sym2 V → Finset (Sym2 V))
    (hf : ((E.R0 ∪ X : Finset (Sym2 V)) : Set (Sym2 V)).PairwiseDisjoint f)
    (hfix : ∀ e ∈ X, f e = {e})
    (hloop : ∀ e ∈ E.R0 ∪ X, ∀ a ∈ f e, ¬ a.IsDiag)
    (hpar : ∀ e ∈ E.R0 ∪ X, ∀ v, (incidentLoad (f e) v : ZMod 2) = symInd e v) :
    PredRefiner I X Q where
  lib := E.lib
  P := fun j => subdivideEdges f (E.P j)
  R0 := subdivideEdges f E.R0
  loopP := by
    intro j hj a ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    exact hloop e (E.subP j hj he) a hae
  evenP := fun j hj => subdivide_even f hf hpar (E.subP j hj) (E.evenP j hj)
  subP := by
    intro j hj a ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    rcases mem_union.mp (E.subP j hj he) with hr | hx
    · exact mem_union_left _ (mem_biUnion.mpr ⟨e, hr, hae⟩)
    · rw [hfix e hx, mem_singleton] at hae
      exact mem_union_right _ (hae ▸ hx)
  disjRX := by
    have h := subdivide_disjoint f hf (subset_union_left) (subset_union_right) E.disjRX
    rw [subdivide_fixed f hfix (Subset.refl X)] at h
    exact h
  refines := by
    intro L hLX hQL
    obtain ⟨s, hs, hdisj, hcover⟩ := E.refines L hLX hQL
    refine ⟨s, hs, ?_, ?_⟩
    · intro i hi j hj hij
      exact subdivide_disjoint f hf (E.subP i (hs hi)) (E.subP j (hs hj))
        (hdisj hi hj hij)
    · have hjoin : s.biUnion (fun j => subdivideEdges f (E.P j)) =
          subdivideEdges f (s.biUnion E.P) := by
        ext a
        simp only [subdivideEdges, mem_biUnion]
        aesop
      rw [hjoin, hcover]
      change (E.R0 ∪ L).biUnion f = E.R0.biUnion f ∪ L
      have hunion : (E.R0 ∪ L).biUnion f = E.R0.biUnion f ∪ L.biUnion f := by
        ext a
        simp only [mem_biUnion, mem_union]
        aesop
      rw [hunion]
      change subdivideEdges f E.R0 ∪ subdivideEdges f L = subdivideEdges f E.R0 ∪ L
      rw [subdivide_fixed f hfix hLX]

#print axioms subdivide_disjoint
#print axioms subdivide_even
#print axioms subdivide_card_le
#print axioms subdividePredRefiner

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
