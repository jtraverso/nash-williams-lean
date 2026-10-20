/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Counting

/-!
# Counting for the whole hierarchy

* `parReqs`, `adjReqs`: the requests of the hierarchy and of the adjustment cycles;
* `piece_subset`: every library piece consists of created atoms and of reserve edges;
* `card_mult_le`: every atom lies in at most `33` library pieces (all alternatives counted);
* `card_parLib_le`, `card_parReqs_le`: sizes, paid by the total number of links;
* `parRootLoad_le`: the root load of the hierarchy at a vertex.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- The alternatives of level `l` attached to the links in `P`. -/
def altsOf (l : ℕ) (P : Finset (Sym2 V)) : Finset (LibIdx V) :=
  (P ×ˢ (univ : Finset (Bool × Bool × Bool × Bool))).image
    fun q => LibIdx.alt l q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

theorem card_altsOf_le (l : ℕ) (P : Finset (Sym2 V)) : (altsOf l P).card ≤ 16 * P.card := by
  unfold altsOf
  refine card_image_le.trans ?_
  simp [card_product, mul_comm]

theorem mem_altsOf {l : ℕ} {P : Finset (Sym2 V)} {π : Sym2 V} {x ca cb cs : Bool}
    (hπ : π ∈ P) : LibIdx.alt l π x ca cb cs ∈ altsOf l P :=
  mem_image.mpr ⟨(π, x, ca, cb, cs), mem_product.mpr ⟨hπ, mem_univ _⟩, rfl⟩

theorem card_filter_pos_le {α : Type*} [DecidableEq α] (C : Finset α) (j : ℕ) :
    (C.filter fun a => pos C a = j ∨ pos C a = j + 1).card ≤ 2 := by
  refine (card_le_card_of_injOn (pos C) (t := {j, j + 1}) ?_ ?_).trans card_le_two
  · intro a ha
    rcases (mem_filter.mp ha).2 with h | h <;> simp [h]
  · intro a ha b hb hab
    exact pos_inj (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab

theorem card_filter_last_le {α : Type*} [DecidableEq α] (C : Finset α) :
    (C.filter fun a => pos C a + 1 = C.card).card ≤ 1 := by
  refine (card_le_card_of_injOn (pos C) (t := {C.card - 1}) ?_ ?_).trans (by simp)
  · intro a ha
    have := (mem_filter.mp ha).2
    simp only [coe_singleton, Set.mem_singleton_iff]
    omega
  · intro a ha b hb hab
    exact pos_inj (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab

/-- Candidate library indices whose piece may contain the atom `a`. -/
noncomputable def candidates (X : Finset (Sym2 V)) (hmap : ℕ → V → V) : Atom V → Finset (LibIdx V)
  | Sum.inr e => altsOf 0 {e}
  | Sum.inl (Req.ep l u j _) => altsOf l ((vChain (links X hmap l) u).filter
      fun π => pos (vChain (links X hmap l) u) π = j ∨ pos (vChain (links X hmap l) u) π = j + 1)
  | Sum.inl (Req.pr l σ j _) => altsOf l ((pChain (links X hmap l) (hmap l) σ).filter
      fun π => pos (pChain (links X hmap l) (hmap l) σ) π = j ∨
        pos (pChain (links X hmap l) (hmap l) σ) π = j + 1)
  | Sum.inl (Req.tm l σ _) => altsOf l ((pChain (links X hmap l) (hmap l) σ).filter
      fun π => pos (pChain (links X hmap l) (hmap l) σ) π + 1 =
        (pChain (links X hmap l) (hmap l) σ).card) ∪ {LibIdx.cyc l σ} ∪ altsOf (l + 1) {σ}
  | Sum.inl (Req.md _ _ _) => ∅
  | Sum.inl (Req.adj k _) => {LibIdx.adj k}

theorem card_candidates_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (a : Atom V) :
    (candidates X hmap a).card ≤ 33 := by
  rcases a with r | e
  · cases r with
    | ep l u j b =>
      have h1 := card_filter_pos_le (vChain (links X hmap l) u) j
      exact (card_altsOf_le _ _).trans (by omega)
    | pr l σ j b =>
      have h1 := card_filter_pos_le (pChain (links X hmap l) (hmap l) σ) j
      exact (card_altsOf_le _ _).trans (by omega)
    | tm l σ b =>
      simp only [candidates]
      refine (card_union_le _ _).trans ?_
      refine (Nat.add_le_add (card_union_le _ _) (card_altsOf_le _ _)).trans ?_
      have h1 := card_altsOf_le l ((pChain (links X hmap l) (hmap l) σ).filter
        fun π => pos (pChain (links X hmap l) (hmap l) σ) π + 1 =
          (pChain (links X hmap l) (hmap l) σ).card)
      have h2 := card_filter_last_le (pChain (links X hmap l) (hmap l) σ)
      simp only [card_singleton] at h1 h2 ⊢
      omega
    | md k c b => simp [candidates]
    | adj k b => simp [candidates]
  · exact (card_altsOf_le _ _).trans (by simp)

theorem mem_parLib {X : Finset (Sym2 V)} {hmap : ℕ → V → V} {L : ℕ} {i : LibIdx V} :
    i ∈ parLib X hmap L ↔ ∃ l < L, i ∈ levelLib (links X hmap l) (hmap l) l := by
  simp [parLib]

theorem mem_levelLib {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ} {i : LibIdx V} :
    i ∈ levelLib Λ h l ↔ (∃ π ∈ Λ, ∃ x ca cb cs : Bool, i = LibIdx.alt l π x ca cb cs) ∨
      (∃ σ ∈ nextLinks Λ h, i = LibIdx.cyc l σ) := by
  simp only [levelLib, mem_union, mem_image, mem_product, mem_univ, and_true, Prod.exists]
  constructor
  · rintro (⟨π, x, ca, cb, cs, hπ, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · exact Or.inl ⟨π, hπ, x, ca, cb, cs, rfl⟩
    · exact Or.inr ⟨σ, hσ, rfl⟩
  · rintro (⟨π, hπ, x, ca, cb, cs, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · exact Or.inl ⟨π, x, ca, cb, cs, hπ, rfl⟩
    · exact Or.inr ⟨σ, hσ, rfl⟩

theorem mem_adjLib {a : ℕ} {i : LibIdx V} : i ∈ adjLib a ↔ ∃ k < a, i = LibIdx.adj k := by
  simp [adjLib, eq_comm]

/-- **Multiplicity.** Every atom lies in at most `33` pieces of the library. -/
theorem mem_candidates (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a' : ℕ) {i : LibIdx V}
    (hi : i ∈ parLib X hmap L ∪ adjLib a') {a : Atom V} (ha : a ∈ piece X hmap i) :
    i ∈ candidates X hmap a := by
  rcases mem_union.mp hi with hi | hi
  · obtain ⟨l, -, hl⟩ := mem_parLib.mp hi
    rcases mem_levelLib.mp hl with ⟨π, hπ, x, ca, cb, cs, rfl⟩ | ⟨σ, hσ, rfl⟩
    · change a ∈ altAtoms (links X hmap l) (hmap l) l π x ca cb cs at ha
      rcases a with r | e
      · cases r with
        | ep l' u j b =>
          obtain ⟨rfl, h1, h2, -⟩ := ep_of_mem_altAtoms hπ ha
          exact mem_altsOf (mem_filter.mpr ⟨h1, h2⟩)
        | pr l' σ j b =>
          obtain ⟨rfl, -, h1, h2, -⟩ := pr_of_mem_altAtoms hπ ha
          exact mem_altsOf (mem_filter.mpr ⟨h1, h2⟩)
        | tm l' σ b =>
          rcases tm_of_mem_altAtoms hπ ha with ⟨hl0, rfl, rfl, -⟩ | ⟨rfl, -, h1, h2, -⟩
          · simp only [candidates]
            refine mem_union_right _ ?_
            have : l - 1 + 1 = l := by omega
            rw [this]
            exact mem_altsOf (mem_singleton_self _)
          · simp only [candidates]
            exact mem_union_left _ (mem_union_left _ (mem_altsOf (mem_filter.mpr ⟨h1, h2⟩)))
        | md k c b => exact absurd ha md_not_mem_altAtoms
        | adj k b => exact absurd ha adj_not_mem_altAtoms
      · obtain ⟨rfl, rfl⟩ := inr_of_mem_altAtoms ha
        exact mem_altsOf (mem_singleton_self _)
    · change a ∈ cycAtoms l σ at ha
      simp only [cycAtoms, mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [candidates]
  · obtain ⟨k, -, rfl⟩ := mem_adjLib.mp hi
    change a ∈ adjAtoms k at ha
    simp only [adjAtoms, mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [candidates]

theorem card_mult_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a' : ℕ) (a : Atom V) :
    ((parLib X hmap L ∪ adjLib a').filter fun i => a ∈ piece X hmap i).card ≤ 33 :=
  (card_le_card fun _ hi => mem_candidates X hmap L a' (mem_filter.mp hi).1
    (mem_filter.mp hi).2).trans (card_candidates_le X hmap a)

/-- Summing a weight over all pieces costs at most `33` times its total. -/
theorem sum_pieces_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a' : ℕ)
    (U : Finset (Atom V))
    (hU : ∀ i ∈ parLib X hmap L ∪ adjLib a', piece X hmap i ⊆ U) (g : Atom V → ℕ) :
    ∑ i ∈ parLib X hmap L ∪ adjLib a', ∑ a ∈ piece X hmap i, g a ≤ 33 * ∑ a ∈ U, g a := by
  have h1 : ∀ i ∈ parLib X hmap L ∪ adjLib a', ∑ a ∈ piece X hmap i, g a =
      ∑ a ∈ U, if a ∈ piece X hmap i then g a else 0 := by
    intro i hi
    rw [← sum_filter]
    congr 1
    ext a
    simp only [mem_filter]
    exact ⟨fun h => ⟨hU i hi h, h⟩, fun h => h.2⟩
  rw [sum_congr rfl h1, sum_comm, mul_sum]
  refine sum_le_sum fun a _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_mult_le X hmap L a' a)

/-! ### Requests of the hierarchy -/

section Reqs

variable [Fintype V]

/-- The requests of the first `L` levels. -/
def parReqs (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) : Finset (Req V) :=
  (range L).biUnion fun l => levelReqs (links X hmap l) (hmap l) l

omit [Fintype V] in
/-- The requests of the adjustment cycles. -/
def adjReqs (a : ℕ) : Finset (Req V) :=
  (range a).biUnion fun k => {Req.adj k false, Req.adj k true}

theorem parRem_eq (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) :
    parRem X hmap L = (parReqs X hmap L).image Sum.inl := by
  rw [parRem, parReqs, biUnion_image]
  exact biUnion_congr rfl fun l _ => levelAtoms_eq

omit [Fintype V] in
theorem adjRem_eq (a : ℕ) : adjRem a = (adjReqs a : Finset (Req V)).image Sum.inl := by
  rw [adjRem, adjReqs, biUnion_image]
  exact biUnion_congr rfl fun k _ => by simp [adjAtoms]

omit [Fintype V] in
theorem card_adjReqs (a : ℕ) : (adjReqs a : Finset (Req V)).card = 2 * a := by
  rw [adjReqs, card_biUnion]
  · simp [mul_comm]
  · intro k _ k' _ hkk'
    simp only [disjoint_insert_left, mem_insert, mem_singleton, Req.adj.injEq, hkk', false_and,
      or_self, not_false_eq_true, disjoint_singleton_left, and_self]

theorem card_parReqs_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) :
    (parReqs X hmap L).card ≤ 8 * ∑ l ∈ range L, (links X hmap l).card := by
  rw [mul_sum]
  exact card_biUnion_le.trans (sum_le_sum fun l _ => card_levelReqs_le)

omit [Fintype V] in
theorem card_parLib_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) :
    (parLib X hmap L).card ≤ 17 * ∑ l ∈ range L, (links X hmap l).card := by
  rw [mul_sum]
  refine card_biUnion_le.trans (sum_le_sum fun l _ => card_levelLib_le.trans ?_)
  have := card_nextLinks_le (Λ := links X hmap l) (h := hmap l)
  omega

omit [Fintype V] in
theorem card_adjLib_le (a : ℕ) : (adjLib a : Finset (LibIdx V)).card ≤ a :=
  card_image_le.trans (by simp)

omit [Fintype V] in
theorem rootLoad_biUnion_le {I κ : Type*} [DecidableEq I] (s : Finset κ) (A : κ → Finset I)
    (u v : I → V) (x : V) :
    rootLoad (s.biUnion A) u v x ≤ ∑ k ∈ s, rootLoad (A k) u v x := by
  unfold rootLoad
  rw [sum_add_distrib, filter_biUnion, filter_biUnion]
  exact Nat.add_le_add card_biUnion_le card_biUnion_le

/-- **Root load of the hierarchy.** -/
theorem parRootLoad_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ)
    (mdr : ℕ → V × V) (adr : V × V) (x : V) :
    rootLoad (parReqs X hmap L) (fun r => (rootPair hmap mdr adr r).1)
      (fun r => (rootPair hmap mdr adr r).2) x ≤
      ∑ l ∈ range L, (2 * (vChain (links X hmap l) x).card +
        10 * hubWeight (links X hmap l) (hmap l) x) :=
  (rootLoad_biUnion_le _ _ _ _ x).trans (sum_le_sum fun _ _ =>
    levelRootLoad_le _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) x)

/-- Every library piece consists of created atoms and of reserve edges. -/
theorem piece_subset (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L a' : ℕ) {i : LibIdx V}
    (hi : i ∈ parLib X hmap L ∪ adjLib a') :
    piece X hmap i ⊆ parRem X hmap L ∪ adjRem a' ∪ X.image Sum.inr := by
  intro a ha
  rcases mem_union.mp hi with hi | hi
  · obtain ⟨l, hl, hll⟩ := mem_parLib.mp hi
    have hlev : levelAtoms (links X hmap l) (hmap l) l ⊆ parRem X hmap L :=
      subset_biUnion_of_mem (fun l => levelAtoms (links X hmap l) (hmap l) l) (mem_range.mpr hl)
    rcases mem_levelLib.mp hll with ⟨π, hπ, x, ca, cb, cs, rfl⟩ | ⟨σ, hσ, rfl⟩
    · change a ∈ altAtoms (links X hmap l) (hmap l) l π x ca cb cs at ha
      rcases a with r | e
      · cases r with
        | ep l' u j b =>
          obtain ⟨rfl, h1, -, h2⟩ := ep_of_mem_altAtoms hπ ha
          exact mem_union_left _ (mem_union_left _ (hlev (ep_mem_levelAtoms.mpr ⟨rfl, h2⟩)))
        | pr l' σ j b =>
          obtain ⟨rfl, h0, -, -, h2⟩ := pr_of_mem_altAtoms hπ ha
          exact mem_union_left _ (mem_union_left _ (hlev (pr_mem_levelAtoms.mpr ⟨rfl, h0, h2⟩)))
        | tm l' σ b =>
          rcases tm_of_mem_altAtoms hπ ha with ⟨hl0, rfl, rfl, -⟩ | ⟨rfl, h0, -⟩
          · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
            have hlev' : levelAtoms (links X hmap m) (hmap m) m ⊆ parRem X hmap L :=
              subset_biUnion_of_mem (fun l => levelAtoms (links X hmap l) (hmap l) l)
                (mem_range.mpr (by omega))
            refine mem_union_left _ (mem_union_left _ (hlev' ?_))
            simp only [Nat.add_sub_cancel]
            exact tm_mem_levelAtoms.mpr ⟨rfl, hπ⟩
          · exact mem_union_left _ (mem_union_left _ (hlev (tm_mem_levelAtoms.mpr ⟨rfl, h0⟩)))
        | md k c b => exact absurd ha md_not_mem_altAtoms
        | adj k b => exact absurd ha adj_not_mem_altAtoms
      · obtain ⟨rfl, rfl⟩ := inr_of_mem_altAtoms ha
        exact mem_union_right _ (mem_image.mpr ⟨e, hπ, rfl⟩)
    · change a ∈ cycAtoms l σ at ha
      simp only [cycAtoms, mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;>
        exact mem_union_left _ (mem_union_left _ (hlev (tm_mem_levelAtoms.mpr ⟨rfl, hσ⟩)))
  · obtain ⟨k, hk, rfl⟩ := mem_adjLib.mp hi
    refine mem_union_left _ (mem_union_right _ ?_)
    exact subset_biUnion_of_mem adjAtoms (mem_range.mpr hk) ha

end Reqs

end PartitionedTriangleAbsorption.UniversalRefiner
