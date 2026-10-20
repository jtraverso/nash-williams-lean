/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeLayer
public import PartitionedTriangleAbsorption.UniversalRefiner.Global
public import PartitionedTriangleAbsorption.UniversalRefiner.Physical

/-! # The parity layer, realised abstractly with labelled middle vertices

The existing atom-level hierarchy `UniversalRefiner.parity_refiner` is realised on the
vertex type `U ⊕ Req U`: a reserve edge stays itself (on `U`), a request `r` with roots
`(a, b)` becomes the path `a – r – b` through its own labelled middle vertex `r`. No host
graph is involved. Distinct atoms are realised edge-disjointly, so the atom refiner becomes
an `EvenRefiner`; the library is restricted to the alternatives of zero boundary, which are
exactly the even ones and contain every alternative a selection can use.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection UniversalRefiner

variable {U : Type*} [DecidableEq U]

/-- The vertex type of the realised parity layer. -/
abbrev WP (U : Type*) := U ⊕ Req U

/-- Realisation of an atom. -/
def physA (rt : Req U → U × U) : Atom U → Finset (Sym2 (WP U))
  | Sum.inl r => {s(Sum.inl (rt r).1, Sum.inr r), s(Sum.inl (rt r).2, Sum.inr r)}
  | Sum.inr e => {Sym2.map Sum.inl e}

/-- Realisation of a set of atoms. -/
def physE (rt : Req U → U × U) (A : Finset (Atom U)) : Finset (Sym2 (WP U)) :=
  A.biUnion (physA rt)

theorem physA_disjoint (rt : Req U → U × U) {a b : Atom U} (h : a ≠ b) :
    Disjoint (physA rt a) (physA rt b) := by
  rw [disjoint_left]
  intro e he he'
  rcases a with r | e1 <;> rcases b with r' | e2
  · simp only [physA, mem_insert, mem_singleton] at he he'
    have hr : r = r' := by
      rcases he with rfl | rfl <;> rcases he' with h' | h' <;>
        simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
          and_false, or_false] at h' <;> exact h'.2
    exact h (by rw [hr])
  · simp only [physA, mem_insert, mem_singleton] at he he'
    subst he'
    induction e2 using Sym2.ind with
    | _ x y => rcases he with h' | h' <;> simp at h'
  · simp only [physA, mem_insert, mem_singleton] at he he'
    subst he
    induction e1 using Sym2.ind with
    | _ x y => rcases he' with h' | h' <;> simp at h'
  · simp only [physA, mem_singleton] at he he'
    rw [he] at he'
    exact h (by rw [Sym2.map.injective Sum.inl_injective he'])

theorem physA_pairwiseDisjoint (rt : Req U → U × U) (A : Finset (Atom U)) :
    (A : Set (Atom U)).PairwiseDisjoint (physA rt) :=
  fun _ _ _ _ h => physA_disjoint rt h

theorem physE_union (rt : Req U → U × U) (A B : Finset (Atom U)) :
    physE rt (A ∪ B) = physE rt A ∪ physE rt B := Finset.union_biUnion

theorem disjoint_physE (rt : Req U → U × U) {A B : Finset (Atom U)} (h : Disjoint A B) :
    Disjoint (physE rt A) (physE rt B) := by
  unfold physE
  rw [disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  exact physA_disjoint rt (fun e => disjoint_left.mp h ha (e ▸ hb))

theorem physE_inr (rt : Req U → U × U) (L : Finset (Sym2 U)) :
    physE rt (L.image Sum.inr) = mapE Sum.inl L := by
  ext e; simp [physE, physA, mapE, eq_comm]

theorem incidentLoad_physE (rt : Req U → U × U) (A : Finset (Atom U)) (w : WP U) :
    incidentLoad (physE rt A) w = ∑ a ∈ A, incidentLoad (physA rt a) w :=
  ModThreeLayer.incidentLoad_biUnion_eq _ _ (physA_pairwiseDisjoint rt A) w

/-- Atoms whose realisation is a genuine path or a genuine edge. -/
def GoodAtom (rt : Req U → U × U) : Atom U → Prop
  | Sum.inl r => (rt r).1 ≠ (rt r).2
  | Sum.inr e => ¬ e.IsDiag

theorem physA_loopless (rt : Req U → U × U) {a : Atom U} (ha : GoodAtom rt a) :
    ∀ e ∈ physA rt a, ¬ e.IsDiag := by
  rcases a with r | e
  · intro e he
    simp only [physA, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl <;> simp
  · intro e' he'
    simp only [physA, mem_singleton] at he'
    subst he'
    rw [Sym2.isDiag_map Sum.inl_injective]
    exact ha

theorem physA_parity_inl (rt : Req U → U × U) {a : Atom U} (ha : GoodAtom rt a) (u : U) :
    (incidentLoad (physA rt a) (Sum.inl u) : ZMod 2) = rbOf rt a u := by
  rcases a with r | e
  · simp only [GoodAtom] at ha
    have hne : s(Sum.inl (rt r).1, Sum.inr r) ≠ (s(Sum.inl (rt r).2, Sum.inr r) : Sym2 (WP U)) := by
      simp [ha]
    simp only [physA, rbOf, Pi.add_apply, ind, incidentLoad]
    rw [filter_insert, filter_singleton]
    by_cases h1 : u = (rt r).1 <;> by_cases h2 : u = (rt r).2
    · exact absurd (h1.symm.trans h2) ha
    · subst h1; simp [Sym2.mem_iff, h2]
    · subst h2; simp [Sym2.mem_iff, h1]
    · simp [Sym2.mem_iff, h1, h2]
  · simp only [physA, rbOf, symInd, incidentLoad, filter_singleton]
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Sym2.map_mk, Sym2.mem_iff, Sum.inl.injEq]
      split_ifs <;> simp_all

theorem physA_even_inr (rt : Req U → U × U) {a : Atom U} (ha : GoodAtom rt a) (r' : Req U) :
    Even (incidentLoad (physA rt a) (Sum.inr r')) := by
  rcases a with r | e
  · simp only [GoodAtom] at ha
    have hne : s(Sum.inl (rt r).1, Sum.inr r) ≠ (s(Sum.inl (rt r).2, Sum.inr r) : Sym2 (WP U)) := by
      simp [ha]
    simp only [physA, incidentLoad]
    rw [filter_insert, filter_singleton]
    by_cases h : r' = r
    · subst h; simp [Sym2.mem_iff, hne]
    · simp [Sym2.mem_iff, h]
  · simp only [physA, incidentLoad, filter_singleton]
    induction e using Sym2.ind with
    | _ x y => simp [Sym2.map_mk, Sym2.mem_iff]

theorem physE_even (rt : Req U → U × U) {A : Finset (Atom U)} (hA : ∀ a ∈ A, GoodAtom rt a)
    (h0 : ∑ a ∈ A, rbOf rt a = 0) : ∀ w, Even (incidentLoad (physE rt A) w) := by
  rintro (u | r')
  · rw [← ZMod.natCast_eq_zero_iff_even, incidentLoad_physE, Nat.cast_sum]
    rw [sum_congr rfl fun a ha => physA_parity_inl rt (hA a ha) u]
    have := congrFun h0 u
    simpa [Finset.sum_apply] using this
  · rw [incidentLoad_physE]
    exact even_sum _ fun a ha => physA_even_inr rt (hA a ha) r'

theorem physE_loopless (rt : Req U → U × U) {A : Finset (Atom U)} (hA : ∀ a ∈ A, GoodAtom rt a) :
    ∀ e ∈ physE rt A, ¬ e.IsDiag := by
  intro e he
  obtain ⟨a, ha, he⟩ := mem_biUnion.mp he
  exact physA_loopless rt (hA a ha) e he

/-! ### The realised parity refiner -/

section Hierarchy

variable [Fintype U] (X : Finset (Sym2 U)) (hmap : ℕ → U → U) (L : ℕ) (base : U)

/-- Roots of the requests (mod-three and adjustment requests are not used). -/
noncomputable def rtP : Req U → U × U := rootPair hmap (fun _ => (base, base)) (base, base)

/-- The even alternatives of the hierarchy. -/
noncomputable def evenLib : Finset (LibIdx U) :=
  (parLib X hmap L).filter fun i =>
    ∑ a ∈ UniversalRefiner.piece X hmap i, rbOf (rtP hmap base) a = 0

variable {X hmap L}

theorem roots_ne_of_mem_parRem (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u)
    {r : Req U} (hr : (Sum.inl r : Atom U) ∈ parRem X hmap L) :
    (rtP hmap base r).1 ≠ (rtP hmap base r).2 := by
  obtain ⟨l, hl, hA⟩ := mem_biUnion.mp hr
  cases r with
  | ep l' u j b =>
    obtain ⟨rfl, hj⟩ := ep_mem_levelAtoms.mp hA
    obtain ⟨π, hπ⟩ : (vChain (links X hmap l') u).Nonempty := card_pos.mp (by omega)
    obtain ⟨hπ, hu⟩ := mem_vChain.mp hπ
    exact (hfix l' (mem_range.mp hl) π hπ u hu).symm
  | pr l' σ j b =>
    obtain ⟨-, hσ, -⟩ := pr_mem_levelAtoms.mp hA
    exact endA_ne_endB (mem_nextLinks.mp hσ).2
  | tm l' σ b =>
    obtain ⟨-, hσ⟩ := tm_mem_levelAtoms.mp hA
    exact endA_ne_endB (mem_nextLinks.mp hσ).2
  | md k c b => exact absurd hA md_not_mem_levelAtoms
  | adj k b => exact absurd hA adj_not_mem_levelAtoms

theorem goodAtom_of_mem (hX : ∀ e ∈ X, ¬ e.IsDiag)
    (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u)
    {a : Atom U} (ha : a ∈ parRem X hmap L ∪ adjRem 0 ∪ X.image Sum.inr) :
    GoodAtom (rtP hmap base) a := by
  rcases mem_union.mp ha with ha | ha
  · rcases mem_union.mp ha with ha | ha
    · rcases a with r | e
      · exact roots_ne_of_mem_parRem base hfix ha
      · obtain ⟨l, -, hl⟩ := mem_biUnion.mp ha
        exact absurd hl inr_not_mem_levelAtoms
    · simp [adjRem] at ha
  · obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    exact hX e he

end Hierarchy


theorem physE_mono (rt : Req U → U × U) {A B : Finset (Atom U)} (h : A ⊆ B) :
    physE rt A ⊆ physE rt B := biUnion_subset_biUnion_of_subset_left _ h

theorem physE_biUnion {κ : Type*} (rt : Req U → U × U) (T : Finset κ) (A : κ → Finset (Atom U)) :
    physE rt (T.biUnion A) = T.biUnion fun i => physE rt (A i) := by
  unfold physE; rw [biUnion_biUnion]

theorem exists_mapE_inl_of_subset {β : Type*} [DecidableEq β] {X : Finset (Sym2 U)}
    {L : Finset (Sym2 (U ⊕ β))} (h : L ⊆ mapE Sum.inl X) :
    ∃ S ⊆ X, L = mapE Sum.inl S := by
  refine ⟨X.filter fun e => Sym2.map Sum.inl e ∈ L, filter_subset _ _, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp (h he)
    exact mem_mapE.mpr ⟨e', mem_filter.mpr ⟨he', he⟩, rfl⟩
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
    exact (mem_filter.mp he').2

section Refiner

variable [Fintype U] {X : Finset (Sym2 U)} {hmap : ℕ → U → U} {L : ℕ} (base : U)

omit [Fintype U] in
theorem adjLib_zero : (adjLib 0 : Finset (LibIdx U)) = ∅ := by simp [adjLib]

omit [Fintype U] in
theorem adjRem_zero : (adjRem 0 : Finset (Atom U)) = ∅ := by simp [adjRem]

theorem evenLib_subset : evenLib X hmap L base ⊆ parLib X hmap L ∪ adjLib 0 := by
  rw [adjLib_zero, union_empty]; exact filter_subset _ _

theorem disjoint_parRem_inr : Disjoint (parRem X hmap L) (X.image Sum.inr) := by
  rw [disjoint_left]
  intro a ha ha'
  obtain ⟨e, -, rfl⟩ := mem_image.mp ha'
  obtain ⟨l, -, hl⟩ := mem_biUnion.mp ha
  exact inr_not_mem_levelAtoms hl

/-- **The realised parity refiner.** On `U ⊕ Req U`, with `R0` the realised hierarchy
atoms, the even alternatives refine every even subset of the reserve. -/
noncomputable def parityRefiner (hX : ∀ e ∈ X, ¬ e.IsDiag) (hlast : links X hmap L = ∅)
    (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u) :
    EvenRefiner (W0 := WP U) (LibIdx U) (mapE Sum.inl X) where
  lib := evenLib X hmap L base
  P i := physE (rtP hmap base) (UniversalRefiner.piece X hmap i)
  R0 := physE (rtP hmap base) (parRem X hmap L)
  loopP i hi := physE_loopless _ fun a ha =>
    goodAtom_of_mem base hX hfix (piece_subset X hmap L 0 (evenLib_subset base hi) ha)
  evenP i hi := physE_even _ (fun a ha =>
    goodAtom_of_mem base hX hfix (piece_subset X hmap L 0 (evenLib_subset base hi) ha))
    (mem_filter.mp hi).2
  subP i hi := by
    refine (physE_mono _ (piece_subset X hmap L 0 (evenLib_subset base hi))).trans ?_
    rw [adjRem_zero, union_empty, physE_union, physE_inr]
  loopX := loopless_mapE Sum.inl_injective hX
  disjRX := by
    rw [← physE_inr (rtP hmap base)]
    exact disjoint_physE _ disjoint_parRem_inr
  refines := by
    intro L' hL' hev
    obtain ⟨S, hS, rfl⟩ := exists_mapE_inl_of_subset hL'
    have hevS : ∀ u, Even (incidentLoad S u) := fun u => by
      simpa [incidentLoad_mapE_apply Sum.inl_injective] using hev (Sum.inl u)
    have h0 : ∑ π ∈ S, rbOf (rootPair hmap (fun _ => (base, base)) (base, base))
        (Sum.inr π) = 0 := by
      simpa [rbOf] using sum_symInd_eq_zero hevS
    obtain ⟨T, hT, hdisj, hzero, hunion⟩ :=
      parity_refiner X hmap L hX hlast (fun _ => (base, base)) (base, base) 0 S hS h0
    refine ⟨T, ?_, ?_, ?_⟩
    · intro i hi
      have hi' := hT hi
      rw [adjLib_zero, union_empty] at hi'
      exact mem_filter.mpr ⟨hi', hzero i hi⟩
    · intro i hi j hj hij
      exact disjoint_physE _ (hdisj hi hj hij)
    · rw [← physE_biUnion, hunion, adjRem_zero, union_empty, physE_union, physE_inr]

end Refiner

end PartitionedTriangleAbsorption.TypedRefinerF0
