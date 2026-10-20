/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeF0

/-! # Edge-faithful transport without a global vertex injection

One fixed map preserves all unions. Injectivity of its edge map on the
library support suffices for cardinality and disjointness; auxiliary vertices
outside a common piece may be identified. This does not construct that map
or assert looplessness, divisibility, or adjacency without their hypotheses.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SharedLibraryTransport

open Finset TypedRefinerF0 TypedRefinerCharge TypedApplicationLinks

variable {A V I : Type*} [DecidableEq A] [DecidableEq V] [DecidableEq I]

omit [DecidableEq A] in
theorem card_map_on_support (f : A → V) (U E : Finset (Sym2 A))
    (hinj : Set.InjOn (Sym2.map f) (U : Set (Sym2 A))) (hE : E ⊆ U) :
    (mapE f E).card = E.card := by
  exact card_image_iff.mpr (fun x hx y hy h => hinj (hE hx) (hE hy) h)

omit [DecidableEq A] in
theorem disjoint_map_on_support (f : A → V) (U E F : Finset (Sym2 A))
    (hinj : Set.InjOn (Sym2.map f) (U : Set (Sym2 A)))
    (hE : E ⊆ U) (hF : F ⊆ U) (hd : Disjoint E F) :
    Disjoint (mapE f E) (mapE f F) := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨x, hx, hxe⟩ := mem_mapE.mp he
  obtain ⟨y, hy, hye⟩ := mem_mapE.mp hf
  have hxy : x = y := hinj (hE hx) (hF hy) (hxe.trans hye.symm)
  subst y
  exact disjoint_left.mp hd hx hy

omit [DecidableEq I] in
theorem selection_transport (f : A → V) (indices s : Finset I)
    (B : I → Finset (Sym2 A)) (R L : Finset (Sym2 A))
    (hinj : Set.InjOn (Sym2.map f) (indices.biUnion B : Set (Sym2 A)))
    (hs : s ⊆ indices) (hd : (s : Set I).PairwiseDisjoint B)
    (heq : s.biUnion B = R ∪ L) :
    (s : Set I).PairwiseDisjoint (fun j => mapE f (B j)) ∧
      s.biUnion (fun j => mapE f (B j)) = mapE f R ∪ mapE f L := by
  constructor
  · intro i hi j hj hij
    apply disjoint_map_on_support f (indices.biUnion B) (B i) (B j) hinj
    · intro e he
      exact mem_biUnion.mpr ⟨i, hs hi, he⟩
    · intro e he
      exact mem_biUnion.mpr ⟨j, hs hj, he⟩
    · exact hd hi hj hij
  · rw [← mapE_biUnion, heq, mapE_union]

omit [DecidableEq A] in
/-- The F0 charge is unchanged by an edge-faithful map, even with folded vertices. -/
theorem charge_map_on_support (pw : V → Fin 2) (f : A → V)
    (U E : Finset (Sym2 A))
    (hinj : Set.InjOn (Sym2.map f) (U : Set (Sym2 A))) (hE : E ⊆ U) :
    charge chi0 pw (mapE f E) = charge chi0 (pw ∘ f) E := by
  rw [charge_eq_sum, charge_eq_sum, mapE,
    sum_image (fun x hx y hy h => hinj (hE hx) (hE hy) h)]
  simp only [pairVec_map]

end PartitionedTriangleAbsorption.SharedLibraryTransport
