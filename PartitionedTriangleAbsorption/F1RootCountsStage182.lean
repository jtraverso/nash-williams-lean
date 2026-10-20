/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalRootTrimStage181

/-! # Exact root-family counts in an F1 physical packing

The cross-minus-same degree surplus counts singleton-root triangles twice.
The same-label degree counts paired-root triangles once. These are physical
identities, not an inference from global type abundance.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1RootCountsStage182

open Finset TypedApplicationLinks

variable {V : Type} [DecidableEq V]

def singletonFamily (p : V → Fin 4) (D : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  D.filter fun s => v ∈ s ∧ (triType p s).count (p v) = 1

def pairedFamily (p : V → Fin 4) (D : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  D.filter fun s => v ∈ s ∧ (triType p s).count (p v) = 2

def surplus (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) : ℤ :=
  degVec p E v (first1 (p v)) + degVec p E v (second1 (p v)) - degVec p E v (p v)

theorem F1_root_charge (τ : Multiset (Fin 4)) (hτ : τ ∈ F1) (r : Fin 4) (hr : r ∈ τ) :
    typeDegVec τ r (first1 r) + typeDegVec τ r (second1 r) - typeDegVec τ r r =
      if τ.count r = 1 then 2 else 0 := by
  have h : ∀ τ ∈ F1, ∀ r : Fin 4, r ∈ τ →
      typeDegVec τ r (first1 r) + typeDegVec τ r (second1 r) - typeDegVec τ r r =
        if τ.count r = 1 then 2 else 0 := by decide
  exact h τ hτ r hr

theorem F1_root_same (τ : Multiset (Fin 4)) (hτ : τ ∈ F1) (r : Fin 4) (hr : r ∈ τ) :
    typeDegVec τ r r = if τ.count r = 2 then 1 else 0 := by
  have h : ∀ τ ∈ F1, ∀ r : Fin 4, r ∈ τ →
      typeDegVec τ r r = if τ.count r = 2 then 1 else 0 := by decide
  exact h τ hτ r hr

theorem packing_degree_sum (p : V → Fin 4) (Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F1 Q D) (v : V) :
    degVec p Q v = ∑ s ∈ D with v ∈ s, typeDegVec (triType p s) (p v) := by
  rw [← hD.2.2]
  simp only [degVec, sum_biUnion hD.2.1, sum_filter]
  apply sum_congr rfl
  intro s hs
  exact degVec_triEdges p (hD.1 s hs).1 v

theorem packing_root_counts (p : V → Fin 4) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F1 Q D) (v : V) :
    surplus p Q v = 2 * ((singletonFamily p D v).card : ℤ) ∧
      degVec p Q v (p v) = ((pairedFamily p D v).card : ℤ) := by
  classical
  have hs := packing_degree_sum p Q D hD v
  constructor
  · simp only [surplus, hs, Finset.sum_apply]
    rw [← sum_add_distrib, ← sum_sub_distrib]
    have heq : (∑ s ∈ D.filter (fun s => v ∈ s),
        (typeDegVec (triType p s) (p v) (first1 (p v)) +
          typeDegVec (triType p s) (p v) (second1 (p v)) -
          typeDegVec (triType p s) (p v) (p v))) =
        ∑ s ∈ D.filter (fun s => v ∈ s), if (triType p s).count (p v) = 1 then (2 : ℤ) else 0 := by
      apply sum_congr rfl
      intro s hsm
      obtain ⟨hsD, hv⟩ := mem_filter.mp hsm
      exact F1_root_charge _ (hD.1 s hsD).2 _ (mem_triType hv)
    rw [heq]
    rw [← sum_filter]
    simp [singletonFamily, filter_filter, mul_comm]
  · rw [hs]
    simp only [Finset.sum_apply]
    have heq : (∑ s ∈ D.filter (fun s => v ∈ s), typeDegVec (triType p s) (p v) (p v)) =
        ∑ s ∈ D.filter (fun s => v ∈ s), if (triType p s).count (p v) = 2 then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro s hsm
      obtain ⟨hsD, hv⟩ := mem_filter.mp hsm
      exact F1_root_same _ (hD.1 s hsD).2 _ (mem_triType hv)
    rw [heq]
    simp [pairedFamily, filter_filter]

end PartitionedTriangleAbsorption.F1RootCountsStage182

