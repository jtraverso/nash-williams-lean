/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Physical

/-!
# Assembly of the physical parity library and of the mod-three layer

For a hierarchy of hub maps whose last link family is empty, and for a realisation of all
requests (`Realises`), the physical pieces of the zero-boundary library indices, the physical
remainder and the physical mod-three wires satisfy the hypotheses `ModThreeLayer.LayerData`
(`layerData`).  The adjustment count `adjCount` makes the remainder divisible by three.

Everything (hub maps, library, requests, paths) is fixed before any leftover is given.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- The full parity library: all alternatives and cycle pieces of all levels, and the
adjustment cycles. -/
def fullLib (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a : ℕ) : Finset (LibIdx V) :=
  parLib X hmap L ∪ adjLib a

omit [DecidableEq V] in
/-- An enumeration of a finite set of library indices. -/
noncomputable def enum (C : Finset (LibIdx V)) (k : ℕ) : LibIdx V :=
  if h : k < C.card then (C.equivFin.symm ⟨k, h⟩ : LibIdx V) else LibIdx.adj 0

omit [DecidableEq V] in
theorem enum_mem {C : Finset (LibIdx V)} {k : ℕ} (hk : k < C.card) : enum C k ∈ C := by
  unfold enum
  rw [dite_eq_left hk]
  exact (C.equivFin.symm ⟨k, hk⟩).2

theorem enum_pos {C : Finset (LibIdx V)} {i : LibIdx V} (hi : i ∈ C) : enum C (pos C i) = i := by
  unfold enum
  rw [dite_eq_left (pos_lt hi)]
  unfold pos
  simp only [dite_eq_left hi, Fin.eta, Equiv.symm_apply_apply]

/-- The mod-three wire requests: wire `k < N - 1`, cycle `c`, path `b`. -/
def mdReqs (N : ℕ) : Finset (Req V) :=
  (range (N - 1) ×ˢ (univ : Finset (Fin 3)) ×ˢ (univ : Finset Bool)).image
    fun q => Req.md q.1 q.2.1 q.2.2

theorem physU_union (rt : Req V → V × V) (f : Req V → V) (A B : Finset (Atom V)) :
    physU rt f (A ∪ B) = physU rt f A ∪ physU rt f B := union_biUnion

theorem physU_mono (rt : Req V → V × V) (f : Req V → V) {A B : Finset (Atom V)} (h : A ⊆ B) :
    physU rt f A ⊆ physU rt f B := biUnion_subset_biUnion_of_subset_left _ h

theorem physU_inr (rt : Req V → V × V) (f : Req V → V) (L : Finset (Sym2 V)) :
    physU rt f (L.image Sum.inr) = L := by
  unfold physU
  rw [image_biUnion]
  ext e
  simp [phys]

variable [Fintype V]

/-- The zero-boundary library indices (the only ones that can be active). -/
noncomputable def libF (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a : ℕ)
    (rt : Req V → V × V) : Finset (LibIdx V) :=
  (fullLib X hmap L a).filter fun i => ∑ x ∈ piece X hmap i, rbOf rt x = 0

/-- Number of always-active adjustment cycles: makes the remainder divisible by three. -/
def adjCount (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) : ℕ :=
  (parReqs X hmap L).card % 3

/-- All path requests of the construction. -/
def allReqs (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L N a : ℕ) : Finset (Req V) :=
  parReqs X hmap L ∪ adjReqs a ∪ mdReqs N

/-- The adjustment count, library, requests, pieces, wires and remainder of the construction. -/
noncomputable def theLib (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) (mdr : ℕ → V × V)
    (adr : V × V) : Finset (LibIdx V) :=
  libF X hmap L (adjCount X hmap L) (rootPair hmap mdr adr)

/-- All requests of the construction. -/
noncomputable def theReqs (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) (mdr : ℕ → V × V)
    (adr : V × V) : Finset (Req V) :=
  allReqs X hmap L (theLib X hmap L mdr adr).card (adjCount X hmap L)

/-- The physical parity pieces, enumerated. -/
noncomputable def theB (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) (mdr : ℕ → V × V)
    (adr : V × V) (f : Req V → V) (k : ℕ) : Finset (Sym2 V) :=
  physU (rootPair hmap mdr adr) f (piece X hmap (enum (theLib X hmap L mdr adr) k))

/-- The physical mod-three wire cycles. -/
noncomputable def theW (hmap : ℕ → V → V) (mdr : ℕ → V × V) (adr : V × V) (f : Req V → V)
    (k : ℕ) (c : Fin 3) : Finset (Sym2 V) :=
  physU (rootPair hmap mdr adr) f {Sum.inl (Req.md k c false), Sum.inl (Req.md k c true)}

/-- The physical parity remainder. -/
noncomputable def theRpar (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) (mdr : ℕ → V × V)
    (adr : V × V) (f : Req V → V) : Finset (Sym2 V) :=
  physU (rootPair hmap mdr adr) f (parRem X hmap L ∪ adjRem (adjCount X hmap L))

theorem disjoint_parReqs_adjReqs (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a : ℕ) :
    Disjoint (parReqs X hmap L) (adjReqs a) := by
  rw [disjoint_left]
  intro r hr hr'
  obtain ⟨k, -, hk⟩ := mem_biUnion.mp hr'
  have : (Sum.inl r : Atom V) ∈ parRem X hmap L := by
    rw [parRem_eq]; exact mem_image_of_mem _ hr
  obtain ⟨l, -, hl⟩ := mem_biUnion.mp this
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl <;> exact adj_not_mem_levelAtoms hl

section Layer

variable {G : SimpleGraph V} {X : Finset (Sym2 V)} {hmap : ℕ → V → V} {L : ℕ}
  {mdr : ℕ → V × V} {adr : V × V} {f : Req V → V}

theorem parRem_adjRem_subset_dom :
    parRem X hmap L ∪ adjRem (adjCount X hmap L) ⊆ dom (theReqs X hmap L mdr adr) X := by
  rw [parRem_eq, adjRem_eq, ← image_union]
  refine (image_subset_image ?_).trans subset_union_left
  intro r hr
  simp only [theReqs, allReqs, mem_union]
  rcases mem_union.mp hr with h | h <;> tauto

theorem piece_subset_dom {i : LibIdx V} (hi : i ∈ fullLib X hmap L (adjCount X hmap L)) :
    piece X hmap i ⊆ dom (theReqs X hmap L mdr adr) X := by
  refine (piece_subset X hmap L _ hi).trans (union_subset parRem_adjRem_subset_dom ?_)
  exact subset_union_right

theorem md_mem_theReqs {k : ℕ} (hk : k < (theLib X hmap L mdr adr).card - 1) (c : Fin 3)
    (b : Bool) : Req.md k c b ∈ theReqs X hmap L mdr adr := by
  simp only [theReqs, allReqs, mem_union]
  refine Or.inr (mem_image.mpr ⟨(k, c, b), ?_, rfl⟩)
  simp [hk]

theorem md_subset_dom {k : ℕ} (hk : k < (theLib X hmap L mdr adr).card - 1) (c : Fin 3) :
    ({Sum.inl (Req.md k c false), Sum.inl (Req.md k c true)} : Finset (Atom V)) ⊆
      dom (theReqs X hmap L mdr adr) X := by
  intro a ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl <;> exact mem_union_left _ (mem_image_of_mem _ (md_mem_theReqs hk c _))

theorem md_disjoint_rem (k : ℕ) (c : Fin 3) :
    Disjoint ({Sum.inl (Req.md k c false), Sum.inl (Req.md k c true)} : Finset (Atom V))
      (parRem X hmap L ∪ adjRem (adjCount X hmap L)) := by
  rw [disjoint_left]
  intro a ha ha'
  simp only [mem_insert, mem_singleton] at ha
  rcases mem_union.mp ha' with h | h
  · obtain ⟨l, -, hl⟩ := mem_biUnion.mp h
    rcases ha with rfl | rfl <;> exact md_not_mem_levelAtoms hl
  · obtain ⟨j, -, hj⟩ := mem_biUnion.mp h
    simp only [adjAtoms, mem_insert, mem_singleton] at hj
    rcases ha with rfl | rfl <;> rcases hj with h' | h' <;> simp at h'

/-- **The physical library satisfies the hypotheses of the mod-three layer.** -/
theorem layerData (hlast : links X hmap L = ∅)
    (hR : Realises G X (theReqs X hmap L mdr adr) (rootPair hmap mdr adr) f) :
    ModThreeLayer.LayerData (theLib X hmap L mdr adr).card (theB X hmap L mdr adr f)
      (theW hmap mdr adr f) X (theRpar X hmap L mdr adr f) := by
  set rt := rootPair hmap mdr adr with hrt
  set a := adjCount X hmap L with ha
  set C := theLib X hmap L mdr adr with hC
  have hX : ∀ e ∈ X, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hR.reserve e he)
  have hCfull : C ⊆ fullLib X hmap L a := filter_subset _ _
  have hBk : ∀ k < C.card, theB X hmap L mdr adr f k =
      physU rt f (piece X hmap (enum C k)) := fun k _ => rfl
  have hloop : ∀ e ∈ X ∪ theRpar X hmap L mdr adr f, ¬ e.IsDiag := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hX e he
    · obtain ⟨a', ha', he'⟩ := mem_biUnion.mp he
      exact G.not_isDiag_of_mem_edgeSet (hR.phys_subset (parRem_adjRem_subset_dom ha') e he')
  refine ⟨?_, ?_, ?_, ?_, ?_, hloop, ?_, ?_, ?_, ?_, ?_⟩
  · -- the parity refiner
    intro L' hL' hLev
    have hS0 : ∑ π ∈ L', rbOf rt (Sum.inr π) = 0 := sum_symInd_eq_zero hLev
    obtain ⟨T, hT, hTd, hT0, hTU⟩ :=
      parity_refiner X hmap L hX hlast mdr adr a L' hL' hS0
    have hTC : T ⊆ C := fun i hi => mem_filter.mpr ⟨hT hi, hT0 i hi⟩
    refine ⟨T.image (pos C), ?_, ?_, ?_⟩
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
      exact mem_range.mpr (pos_lt (hTC hi))
    · intro k hk k' hk' hkk'
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_coe.mp hk)
      obtain ⟨i', hi', rfl⟩ := mem_image.mp (mem_coe.mp hk')
      have hne : i ≠ i' := fun h => hkk' (by rw [h])
      change Disjoint (theB X hmap L mdr adr f (pos C i)) (theB X hmap L mdr adr f (pos C i'))
      simp only [theB, ← hC, enum_pos (hTC hi), enum_pos (hTC hi')]
      exact hR.disjoint_physU (piece_subset_dom (hCfull (hTC hi)))
        (piece_subset_dom (hCfull (hTC hi'))) (hTd hi hi' hne)
    · rw [image_biUnion]
      have : ∀ i ∈ T, theB X hmap L mdr adr f (pos C i) = physU rt f (piece X hmap i) := by
        intro i hi
        simp only [theB, ← hC, enum_pos (hTC hi)]
        rfl
      rw [biUnion_congr rfl this]
      have h2 : T.biUnion (fun i => physU rt f (piece X hmap i)) =
          physU rt f (T.biUnion (piece X hmap)) := by
        unfold physU; rw [biUnion_biUnion]
      rw [h2, hTU, physU_union, physU_inr]
      rfl
  · intro k hk
    have hi := hCfull (enum_mem hk)
    refine (physU_mono rt f (piece_subset X hmap L a hi)).trans ?_
    rw [physU_union, physU_inr, union_comm]
    exact subset_refl _
  · intro k hk
    have hi := enum_mem hk
    exact hR.even_physU (piece_subset_dom (hCfull hi)) (mem_filter.mp hi).2
  · rw [disjoint_left]
    intro e he heX
    obtain ⟨a', ha', he'⟩ := mem_biUnion.mp he
    have hd := parRem_adjRem_subset_dom (mdr := mdr) (adr := adr) ha'
    rw [parRem_eq, adjRem_eq, ← image_union] at ha'
    obtain ⟨r, hr, rfl⟩ := mem_image.mp ha'
    have hrs : r ∈ theReqs X hmap L mdr adr := by
      simp only [theReqs, allReqs, mem_union]
      rcases mem_union.mp hr with h | h <;> tauto
    exact disjoint_left.mp (hR.phys_disjoint_X hrs) he' heX
  · change 3 ∣ (physU rt f (parRem X hmap L ∪ adjRem a)).card
    rw [parRem_eq, adjRem_eq, ← image_union, hR.card_physU, card_union_of_disjoint
      (disjoint_parReqs_adjReqs X hmap L a), card_adjReqs]
    · rw [ha, adjCount]
      omega
    · intro r hr
      simp only [theReqs, allReqs, mem_union]
      rcases mem_union.mp hr with h | h <;> tauto
  · intro k hk c v
    refine hR.even_physU (md_subset_dom hk c) ?_ v
    rw [sum_pair (by simp)]
    funext w
    simp only [rbOf, Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · intro k hk c
    have hsub : ({Req.md k c false, Req.md k c true} : Finset (Req V)) ⊆
        theReqs X hmap L mdr adr := by
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> exact md_mem_theReqs hk c _
    have himg : ({Sum.inl (Req.md k c false), Sum.inl (Req.md k c true)} : Finset (Atom V)) =
        ({Req.md k c false, Req.md k c true} : Finset (Req V)).image Sum.inl := by simp
    change (physU rt f _).card % 3 = 1
    rw [himg, hR.card_physU hsub, card_pair (by simp)]
  · intro q hq q' hq' hqq'
    obtain ⟨k, c⟩ := q
    obtain ⟨k', c'⟩ := q'
    simp only [ModThreeLayer.wireIdx, coe_product, Set.mem_prod, mem_coe, mem_range] at hq hq'
    change Disjoint (physU rt f _) (physU rt f _)
    refine hR.disjoint_physU (md_subset_dom hq.1 c) (md_subset_dom hq'.1 c') ?_
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
      simp only [Sum.inl.injEq, Req.md.injEq] at h <;>
      exact hqq' (Prod.ext h.1 h.2.1)
  · intro k hk c
    refine disjoint_union_right.mpr ⟨?_, ?_⟩
    · rw [disjoint_left]
      intro e he heX
      obtain ⟨a', ha', he'⟩ := mem_biUnion.mp he
      simp only [mem_insert, mem_singleton] at ha'
      rcases ha' with rfl | rfl <;>
        exact disjoint_left.mp (hR.phys_disjoint_X (md_mem_theReqs hk c _)) he' heX
    · exact hR.disjoint_physU (md_subset_dom hk c) parRem_adjRem_subset_dom
        (md_disjoint_rem k c)
  · intro k hk c e he
    obtain ⟨a', ha', he'⟩ := mem_biUnion.mp he
    exact G.not_isDiag_of_mem_edgeSet (hR.phys_subset (md_subset_dom hk c ha') e he')

end Layer

end PartitionedTriangleAbsorption.UniversalRefiner
