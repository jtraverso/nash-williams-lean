/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Hierarchy

/-!
# Counting for one level: atoms of an alternative, requests, library size, root loads

* `ep_of_mem_altAtoms`, `pr_of_mem_altAtoms`, `tm_of_mem_altAtoms`, `inr_of_mem_altAtoms`:
  which atoms an arbitrary alternative (not only the active one) can contain;
* `card_altAtoms_le`: an alternative has at most `11` atoms;
* `levelReqs`: the requests of one level, with `levelAtoms_eq`;
* `card_levelReqs_le`: at most `8 |Λ|` requests per level;
* `card_levelLib_le`: at most `17 |Λ|` library indices per level;
* `levelRootLoad_le`: the root load of a vertex `x` at one level is at most
  `2 deg x + 10 hubWeight x`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

section AltAtoms

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ}

theorem mem_altAtoms {a : Atom V} {π : Sym2 V} {x ca cb cs : Bool} :
    a ∈ altAtoms Λ h l π x ca cb cs ↔
      (x = true ∧ a = linkAtom l π) ∨ a ∈ vRecv Λ l (endA π) π ca (xor ca x) ∨
        a ∈ vRecv Λ l (endB π) π cb (xor cb x) ∨
        (¬ (Sym2.map h π).IsDiag ∧ a ∈ pRecv Λ h l π cs (xor cs x)) := by
  simp only [altAtoms, mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton]
  tauto

theorem pos_of_mem_recvLoc {N j p : ℕ} {cp cur : Bool} {b : Bool}
    (hq : (j, b) ∈ recvLoc N p cp cur) : p = j ∨ p = j + 1 := by
  rcases mem_recvLoc.mp hq with ⟨h0, -, he⟩ | ⟨-, he | ⟨-, he⟩⟩ <;>
    simp only [Prod.mk.injEq] at he <;> omega

theorem ep_of_mem_altAtoms {π : Sym2 V} {x ca cb cs : Bool} (hπ : π ∈ Λ) {l' : ℕ} {u : V}
    {j : ℕ} {b : Bool} (ha : (Sum.inl (Req.ep l' u j b) : Atom V) ∈ altAtoms Λ h l π x ca cb cs) :
    l' = l ∧ π ∈ vChain Λ u ∧ (pos (vChain Λ u) π = j ∨ pos (vChain Λ u) π = j + 1) ∧
      j + 1 < (vChain Λ u).card := by
  rw [mem_altAtoms] at ha
  simp only [vRecv, pRecv, ep_ne_linkAtom, and_false, ep_mem_epAtoms, mem_union,
    ep_mem_prAtoms, mem_ite_empty, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false,
    false_or] at ha
  rcases ha with ⟨h1, rfl, h3⟩ | ⟨h1, rfl, h3⟩
  · have hm : π ∈ vChain Λ (endA π) := mem_vChain.mpr ⟨hπ, endA_mem π⟩
    exact ⟨h1, hm, pos_of_mem_recvLoc h3, recvLoc_wire_lt (pos_lt hm) h3⟩
  · have hm : π ∈ vChain Λ (endB π) := mem_vChain.mpr ⟨hπ, endB_mem π⟩
    exact ⟨h1, hm, pos_of_mem_recvLoc h3, recvLoc_wire_lt (pos_lt hm) h3⟩

theorem pr_of_mem_altAtoms {π : Sym2 V} {x ca cb cs : Bool} (hπ : π ∈ Λ) {l' : ℕ} {σ : Sym2 V}
    {j : ℕ} {b : Bool} (ha : (Sum.inl (Req.pr l' σ j b) : Atom V) ∈ altAtoms Λ h l π x ca cb cs) :
    l' = l ∧ σ ∈ nextLinks Λ h ∧ π ∈ pChain Λ h σ ∧
      (pos (pChain Λ h σ) π = j ∨ pos (pChain Λ h σ) π = j + 1) ∧
      j + 1 < (pChain Λ h σ).card := by
  rw [mem_altAtoms] at ha
  simp only [vRecv, pRecv, pr_ne_linkAtom, and_false, pr_mem_epAtoms, mem_union,
    pr_mem_prAtoms, mem_ite_empty, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false,
    false_or] at ha
  obtain ⟨hd, h1, rfl, h3⟩ := ha
  have hm : π ∈ pChain Λ h (Sym2.map h π) := mem_pChain.mpr ⟨hπ, rfl⟩
  exact ⟨h1, mem_nextLinks.mpr ⟨⟨π, hπ, rfl⟩, hd⟩, hm, pos_of_mem_recvLoc h3,
    recvLoc_wire_lt (pos_lt hm) h3⟩

theorem tm_of_mem_altAtoms {π : Sym2 V} {x ca cb cs : Bool} (hπ : π ∈ Λ) {l' : ℕ} {σ : Sym2 V}
    {b : Bool} (ha : (Sum.inl (Req.tm l' σ b) : Atom V) ∈ altAtoms Λ h l π x ca cb cs) :
    (l ≠ 0 ∧ l' = l - 1 ∧ σ = π ∧ b = true) ∨
      (l' = l ∧ σ ∈ nextLinks Λ h ∧ π ∈ pChain Λ h σ ∧
        pos (pChain Λ h σ) π + 1 = (pChain Λ h σ).card ∧ b = false) := by
  rw [mem_altAtoms] at ha
  simp only [vRecv, pRecv, tm_eq_linkAtom, tm_mem_epAtoms, mem_union, tm_mem_prAtoms,
    mem_ite_empty, mem_singleton, Sum.inl.injEq, Req.tm.injEq, false_or] at ha
  rcases ha with ⟨-, h1⟩ | ⟨hd, ⟨hpos, -⟩, h2, h3, h4⟩
  · exact Or.inl ⟨h1.1, h1.2.1, h1.2.2⟩
  · subst h3
    exact Or.inr ⟨h2, mem_nextLinks.mpr ⟨⟨π, hπ, rfl⟩, hd⟩, mem_pChain.mpr ⟨hπ, rfl⟩, by
      omega, h4⟩

theorem inr_of_mem_altAtoms {π : Sym2 V} {x ca cb cs : Bool} {e : Sym2 V}
    (ha : (Sum.inr e : Atom V) ∈ altAtoms Λ h l π x ca cb cs) : l = 0 ∧ e = π := by
  rw [mem_altAtoms] at ha
  simp only [vRecv, pRecv, inr_eq_linkAtom, inr_mem_epAtoms, mem_union, inr_mem_prAtoms,
    mem_ite_empty, mem_singleton, reduceCtorEq, and_false, or_false] at ha
  exact ha.2

theorem md_not_mem_altAtoms {π : Sym2 V} {x ca cb cs : Bool} {k : ℕ} {c : Fin 3} {b : Bool} :
    (Sum.inl (Req.md k c b) : Atom V) ∉ altAtoms Λ h l π x ca cb cs := by
  rw [mem_altAtoms]
  simp [vRecv, pRecv, mem_ite_empty]

theorem adj_not_mem_altAtoms {π : Sym2 V} {x ca cb cs : Bool} {k : ℕ} {b : Bool} :
    (Sum.inl (Req.adj k b) : Atom V) ∉ altAtoms Λ h l π x ca cb cs := by
  rw [mem_altAtoms]
  simp [vRecv, pRecv, mem_ite_empty]

theorem card_altAtoms_le (π : Sym2 V) (x ca cb cs : Bool) :
    (altAtoms Λ h l π x ca cb cs).card ≤ 11 := by
  have h1 : (if x then ({linkAtom l π} : Finset (Atom V)) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have hv : ∀ u cp cur, (vRecv Λ l u π cp cur).card ≤ 3 := by
    intro u cp cur
    unfold vRecv epAtoms
    exact card_image_le.trans (recvLoc_card_le _ _ _ _)
  have hp : ∀ cp cur, (pRecv Λ h l π cp cur).card ≤ 4 := by
    intro cp cur
    refine (card_union_le _ _).trans ?_
    have : (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
        cur = true then ({Sum.inl (Req.tm l (Sym2.map h π) false)} : Finset (Atom V))
        else ∅).card ≤ 1 := by split_ifs <;> simp
    have h2 : (prAtoms l (Sym2.map h π) (recvLoc (pChain Λ h (Sym2.map h π)).card
        (pos (pChain Λ h (Sym2.map h π)) π) cp cur)).card ≤ 3 := by
      unfold prAtoms
      exact card_image_le.trans (recvLoc_card_le _ _ _ _)
    omega
  have hp' : (if (Sym2.map h π).IsDiag then ∅ else pRecv Λ h l π cs (xor cs x)).card ≤ 4 := by
    split_ifs
    · simp
    · exact hp _ _
  unfold altAtoms
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _)) _).trans ?_
  have := hv (endA π) ca (xor ca x)
  have := hv (endB π) cb (xor cb x)
  omega

end AltAtoms

section Requests

variable [Fintype V] {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ}

/-- The hub weight of `x`: total degree of the vertices sent to `x`. -/
def hubWeight (Λ : Finset (Sym2 V)) (h : V → V) (x : V) : ℕ :=
  ∑ u ∈ univ.filter (fun u => h u = x), (vChain Λ u).card

variable (Λ h l) in
/-- The path requests created at one level. -/
def levelReqs : Finset (Req V) :=
  ((univ : Finset V).biUnion fun u => (range ((vChain Λ u).card - 1) ×ˢ (univ : Finset Bool)).image
      fun q => Req.ep l u q.1 q.2) ∪
    ((nextLinks Λ h).biUnion fun σ => (range ((pChain Λ h σ).card - 1) ×ˢ
      (univ : Finset Bool)).image fun q => Req.pr l σ q.1 q.2) ∪
    ((nextLinks Λ h).biUnion fun σ => {Req.tm l σ false, Req.tm l σ true})

theorem levelAtoms_eq : levelAtoms Λ h l = (levelReqs Λ h l).image Sum.inl := by
  simp only [levelAtoms, levelReqs, image_union]
  congr 1
  · congr 1
    · rw [biUnion_image]
      refine biUnion_congr rfl fun u _ => ?_
      rw [epAtoms, image_image]
      rfl
    · rw [biUnion_image]
      refine biUnion_congr rfl fun u _ => ?_
      rw [prAtoms, image_image]
      rfl
  · rw [biUnion_image]
    refine biUnion_congr rfl fun u _ => ?_
    simp [cycAtoms]

theorem sum_vChain_card_le : ∑ u, (vChain Λ u).card ≤ 2 * Λ.card := by
  have h1 : ∀ u, (vChain Λ u).card = ∑ π ∈ Λ, if u ∈ π then 1 else 0 := fun u => by
    rw [vChain, card_filter]
  simp only [h1]
  rw [sum_comm]
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun π _ => ?_
  rw [← card_filter]
  refine (card_le_card (t := {endA π, endB π}) fun u hu => ?_).trans card_le_two
  rcases mem_iff_endA_endB.mp (mem_filter.mp hu).2 with rfl | rfl <;> simp

omit [Fintype V] in
theorem sum_pChain_card_le (T : Finset (Sym2 V)) : ∑ σ ∈ T, (pChain Λ h σ).card ≤ Λ.card := by
  simp only [pChain]
  rw [sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

omit [Fintype V] in
theorem card_nextLinks_le : (nextLinks Λ h).card ≤ Λ.card :=
  (card_filter_le _ _).trans card_image_le

theorem card_levelReqs_le : (levelReqs Λ h l).card ≤ 8 * Λ.card := by
  have h1 : ((univ : Finset V).biUnion fun u => (range ((vChain Λ u).card - 1) ×ˢ
      (univ : Finset Bool)).image fun q => Req.ep l u q.1 q.2).card ≤ 4 * Λ.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ u, ((range ((vChain Λ u).card - 1) ×ˢ (univ : Finset Bool)).image
          fun q => Req.ep l u q.1 q.2).card ≤ ∑ u, 2 * (vChain Λ u).card := by
          refine sum_le_sum fun u _ => card_image_le.trans ?_
          simp only [card_product, card_range, card_univ, Fintype.card_bool]
          omega
      _ ≤ 4 * Λ.card := by rw [← mul_sum]; have := sum_vChain_card_le (Λ := Λ); omega
  have h2 : ((nextLinks Λ h).biUnion fun σ => (range ((pChain Λ h σ).card - 1) ×ˢ
      (univ : Finset Bool)).image fun q => Req.pr l σ q.1 q.2).card ≤ 2 * Λ.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ σ ∈ nextLinks Λ h, ((range ((pChain Λ h σ).card - 1) ×ˢ (univ : Finset Bool)).image
          fun q => Req.pr l σ q.1 q.2).card ≤ ∑ σ ∈ nextLinks Λ h, 2 * (pChain Λ h σ).card := by
          refine sum_le_sum fun u _ => card_image_le.trans ?_
          simp only [card_product, card_range, card_univ, Fintype.card_bool]
          omega
      _ ≤ 2 * Λ.card := by
          rw [← mul_sum]; have := sum_pChain_card_le (Λ := Λ) (h := h) (nextLinks Λ h); omega
  have h3 : ((nextLinks Λ h).biUnion fun σ =>
      ({Req.tm l σ false, Req.tm l σ true} : Finset (Req V))).card ≤ 2 * Λ.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ σ ∈ nextLinks Λ h, ({Req.tm l σ false, Req.tm l σ true} : Finset (Req V)).card
          ≤ ∑ _σ ∈ nextLinks Λ h, 2 := sum_le_sum fun _ _ => card_le_two
      _ ≤ 2 * Λ.card := by
          rw [sum_const, smul_eq_mul]; have := card_nextLinks_le (Λ := Λ) (h := h); omega
  unfold levelReqs
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  omega

omit [Fintype V] in
theorem card_levelLib_le : (levelLib Λ h l).card ≤ 16 * Λ.card + (nextLinks Λ h).card := by
  unfold levelLib
  refine (card_union_le _ _).trans (Nat.add_le_add (card_image_le.trans ?_) card_image_le)
  simp [card_product, mul_comm]

/-! ### Root loads -/

omit [Fintype V] in
theorem card_filter_mem_map_le' (x : V) (T : Finset (Sym2 V)) (hT : ∀ σ ∈ T, x ∈ σ) :
    ∑ σ ∈ T, (pChain Λ h σ).card ≤ (Λ.filter fun π => x ∈ Sym2.map h π).card := by
  simp only [pChain]
  rw [sum_card_fiberwise_eq_card_filter]
  refine card_le_card fun π hπ => ?_
  obtain ⟨h1, h2⟩ := mem_filter.mp hπ
  exact mem_filter.mpr ⟨h1, hT _ h2⟩

theorem card_filter_mem_map_le (x : V) :
    (Λ.filter fun π => x ∈ Sym2.map h π).card ≤ hubWeight Λ h x := by
  refine (card_le_card (t := (univ.filter fun u => h u = x).biUnion (vChain Λ)) ?_).trans
    card_biUnion_le
  intro π hπ
  obtain ⟨h1, h2⟩ := mem_filter.mp hπ
  obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp h2
  exact mem_biUnion.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, rfl⟩, mem_vChain.mpr ⟨h1, hu⟩⟩

theorem card_nextLinks_filter_le (x : V) :
    ((nextLinks Λ h).filter fun σ => x ∈ σ).card ≤ hubWeight Λ h x := by
  refine (card_le_card (t := (Λ.filter fun π => x ∈ Sym2.map h π).image (Sym2.map h)) ?_).trans
    (card_image_le.trans (card_filter_mem_map_le x))
  intro σ hσ
  obtain ⟨h1, h2⟩ := mem_filter.mp hσ
  obtain ⟨⟨π, hπ, rfl⟩, -⟩ := mem_nextLinks.mp h1
  exact mem_image.mpr ⟨π, mem_filter.mpr ⟨hπ, h2⟩, rfl⟩

omit [Fintype V] in
theorem rootLoad_union_le {I : Type*} [DecidableEq I] (A B : Finset I) (u v : I → V) (x : V) :
    rootLoad (A ∪ B) u v x ≤ rootLoad A u v x + rootLoad B u v x := by
  unfold rootLoad
  rw [filter_union, filter_union]
  have := card_union_le (A.filter fun i => u i = x) (B.filter fun i => u i = x)
  have := card_union_le (A.filter fun i => v i = x) (B.filter fun i => v i = x)
  omega

omit [Fintype V] in
theorem rootLoad_le_of_subset {I : Type*} (A A' : Finset I) (u v : I → V) (x : V)
    (hA : ∀ i ∈ A, (u i = x ∨ v i = x) → i ∈ A') : rootLoad A u v x ≤ 2 * A'.card := by
  unfold rootLoad
  have h1 : (A.filter fun i => u i = x).card ≤ A'.card :=
    card_le_card fun i hi => hA i (mem_filter.mp hi).1 (Or.inl (mem_filter.mp hi).2)
  have h2 : (A.filter fun i => v i = x).card ≤ A'.card :=
    card_le_card fun i hi => hA i (mem_filter.mp hi).1 (Or.inr (mem_filter.mp hi).2)
  omega

/-- **Root load of one level.** -/
theorem levelRootLoad_le (rt : Req V → V × V)
    (hep : ∀ u j b, rt (Req.ep l u j b) = (u, h u))
    (hpr : ∀ σ j b, rt (Req.pr l σ j b) = (endA σ, endB σ))
    (htm : ∀ σ b, rt (Req.tm l σ b) = (endA σ, endB σ)) (x : V) :
    rootLoad (levelReqs Λ h l) (fun r => (rt r).1) (fun r => (rt r).2) x ≤
      2 * (vChain Λ x).card + 10 * hubWeight Λ h x := by
  have hE : rootLoad ((univ : Finset V).biUnion fun u => (range ((vChain Λ u).card - 1) ×ˢ
      (univ : Finset Bool)).image fun q => Req.ep l u q.1 q.2) (fun r => (rt r).1)
      (fun r => (rt r).2) x ≤ 2 * (vChain Λ x).card + 2 * hubWeight Λ h x := by
    unfold rootLoad
    have h1 : (((univ : Finset V).biUnion fun u => (range ((vChain Λ u).card - 1) ×ˢ
        (univ : Finset Bool)).image fun q => Req.ep l u q.1 q.2).filter
        fun r => (rt r).1 = x).card ≤ 2 * (vChain Λ x).card := by
      refine (card_le_card (t := (range ((vChain Λ x).card - 1) ×ˢ (univ : Finset Bool)).image
        fun q => Req.ep l x q.1 q.2) ?_).trans (card_image_le.trans ?_)
      · intro r hr
        obtain ⟨hr, hx⟩ := mem_filter.mp hr
        obtain ⟨u, -, hr⟩ := mem_biUnion.mp hr
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
        simp only [hep] at hx
        subst hx
        exact mem_image.mpr ⟨q, hq, rfl⟩
      · simp only [card_product, card_range, card_univ, Fintype.card_bool]
        omega
    have h2 : (((univ : Finset V).biUnion fun u => (range ((vChain Λ u).card - 1) ×ˢ
        (univ : Finset Bool)).image fun q => Req.ep l u q.1 q.2).filter
        fun r => (rt r).2 = x).card ≤ 2 * hubWeight Λ h x := by
      refine (card_le_card (t := (univ.filter fun u => h u = x).biUnion fun u =>
        (range ((vChain Λ u).card - 1) ×ˢ (univ : Finset Bool)).image
          fun q => Req.ep l u q.1 q.2) ?_).trans (card_biUnion_le.trans ?_)
      · intro r hr
        obtain ⟨hr, hx⟩ := mem_filter.mp hr
        obtain ⟨u, -, hr'⟩ := mem_biUnion.mp hr
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hr'
        simp only [hep] at hx
        exact mem_biUnion.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, hx⟩, mem_image.mpr ⟨q, hq, rfl⟩⟩
      · unfold hubWeight
        rw [mul_sum]
        refine sum_le_sum fun u _ => card_image_le.trans ?_
        simp only [card_product, card_range, card_univ, Fintype.card_bool]
        omega
    exact Nat.add_le_add h1 h2
  have hP : rootLoad ((nextLinks Λ h).biUnion fun σ => (range ((pChain Λ h σ).card - 1) ×ˢ
      (univ : Finset Bool)).image fun q => Req.pr l σ q.1 q.2) (fun r => (rt r).1)
      (fun r => (rt r).2) x ≤ 4 * hubWeight Λ h x := by
    refine (rootLoad_le_of_subset _ (((nextLinks Λ h).filter fun σ => x ∈ σ).biUnion fun σ =>
      (range ((pChain Λ h σ).card - 1) ×ˢ (univ : Finset Bool)).image
        fun q => Req.pr l σ q.1 q.2) _ _ x ?_).trans ?_
    · intro r hr hx
      obtain ⟨σ, hσ, hr'⟩ := mem_biUnion.mp hr
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hr'
      simp only [hpr] at hx
      refine mem_biUnion.mpr ⟨σ, mem_filter.mpr ⟨hσ, ?_⟩, mem_image.mpr ⟨q, hq, rfl⟩⟩
      rcases hx with hx | hx <;> rw [← hx]
      · exact endA_mem σ
      · exact endB_mem σ
    · have : (((nextLinks Λ h).filter fun σ => x ∈ σ).biUnion fun σ =>
          (range ((pChain Λ h σ).card - 1) ×ˢ (univ : Finset Bool)).image
            fun q => Req.pr l σ q.1 q.2).card ≤ 2 * hubWeight Λ h x := by
        refine card_biUnion_le.trans ?_
        calc ∑ σ ∈ (nextLinks Λ h).filter (fun σ => x ∈ σ),
              ((range ((pChain Λ h σ).card - 1) ×ˢ (univ : Finset Bool)).image
                fun q => Req.pr l σ q.1 q.2).card
            ≤ ∑ σ ∈ (nextLinks Λ h).filter (fun σ => x ∈ σ), 2 * (pChain Λ h σ).card := by
              refine sum_le_sum fun σ _ => card_image_le.trans ?_
              simp only [card_product, card_range, card_univ, Fintype.card_bool]
              omega
          _ ≤ 2 * hubWeight Λ h x := by
              rw [← mul_sum]
              exact Nat.mul_le_mul_left 2 ((card_filter_mem_map_le' x _
                (fun σ hσ => (mem_filter.mp hσ).2)).trans (card_filter_mem_map_le x))
      omega
  have hT : rootLoad ((nextLinks Λ h).biUnion fun σ =>
      ({Req.tm l σ false, Req.tm l σ true} : Finset (Req V))) (fun r => (rt r).1)
      (fun r => (rt r).2) x ≤ 4 * hubWeight Λ h x := by
    refine (rootLoad_le_of_subset _ (((nextLinks Λ h).filter fun σ => x ∈ σ).biUnion fun σ =>
      ({Req.tm l σ false, Req.tm l σ true} : Finset (Req V))) _ _ x ?_).trans ?_
    · intro r hr hx
      obtain ⟨σ, hσ, hr'⟩ := mem_biUnion.mp hr
      have hmem : x ∈ σ := by
        simp only [mem_insert, mem_singleton] at hr'
        rcases hr' with rfl | rfl <;> simp only [htm] at hx <;>
          rcases hx with hx | hx <;> rw [← hx]
        all_goals first | exact endA_mem σ | exact endB_mem σ
      exact mem_biUnion.mpr ⟨σ, mem_filter.mpr ⟨hσ, hmem⟩, hr'⟩
    · have : (((nextLinks Λ h).filter fun σ => x ∈ σ).biUnion fun σ =>
          ({Req.tm l σ false, Req.tm l σ true} : Finset (Req V))).card ≤
          2 * hubWeight Λ h x := by
        refine card_biUnion_le.trans ?_
        refine (sum_le_sum fun _ _ => card_le_two).trans ?_
        rw [sum_const, smul_eq_mul]
        have := card_nextLinks_filter_le (Λ := Λ) (h := h) x
        omega
      omega
  unfold levelReqs
  refine (rootLoad_union_le _ _ _ _ x).trans ?_
  refine (Nat.add_le_add_right (rootLoad_union_le _ _ _ _ x) _).trans ?_
  omega

end Requests

end PartitionedTriangleAbsorption.UniversalRefiner
