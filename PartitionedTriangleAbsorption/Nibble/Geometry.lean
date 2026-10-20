/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.Model

/-! # Combinatorics of distinct physical triangles

Uniqueness facts (three vertices, or two distinct edges, determine a physical
triangle), the double counting of loads around a star, and the neighbourhood
structure used by the tail estimates.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

theorem eq_triple_of_mem {T : Finset V} (hT : T.card = 3) {x y z : V} (hx : x ∈ T) (hy : y ∈ T)
    (hz : z ∈ T) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : T = {x, y, z} := by
  symm
  apply eq_of_subset_of_card_le
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  · rw [hT, card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]

theorem triEdges_triple {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triEdges ({x, y, z} : Finset V) = {s(x, y), s(x, z), s(y, z)} := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  rw [mem_triEdges]
  simp only [mem_insert, mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨ha, hb, hab⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]

theorem card_triEdges {T : Finset V} (hT : T.card = 3) : (triEdges T).card = 3 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hT
  rw [triEdges_triple hxy hxz hyz]
  apply card_eq_three.mpr
  refine ⟨s(x, y), s(x, z), s(y, z), ?_, ?_, ?_, rfl⟩ <;>
    simp [hxy, hxz, hyz, Ne.symm hxy]

theorem edge_subset_of_mem_triEdges {T : Finset V} {x y : V} (h : s(x, y) ∈ triEdges T) :
    ({x, y} : Finset V) ⊆ T := by
  rw [mem_triEdges] at h
  intro a ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl
  exacts [h.1, h.2.1]

namespace TriSystem

variable (S : TriSystem V m)

/-- A set of at least three vertices lies in at most one triangle. -/
theorem eq_of_three_subset {X : Finset V} (hX : 3 ≤ X.card) {i j : Fin m}
    (hi : X ⊆ S.tri i) (hj : X ⊆ S.tri j) : i = j := by
  apply S.tri_inj
  have h1 := eq_of_subset_of_card_le hi (by rw [S.card_tri]; exact hX)
  have h2 := eq_of_subset_of_card_le hj (by rw [S.card_tri]; exact hX)
  rw [← h1, ← h2]

/-- Triangles containing edge `e`. -/
def edgeTris (e : Sym2 V) : Finset (Fin m) := univ.filter (fun i => e ∈ triEdges (S.tri i))

/-- The load of edge `e`. -/
def load (w : Fin m → ℝ) (e : Sym2 V) : ℝ := ∑ i ∈ S.edgeTris e, w i

theorem mem_edgeTris {e : Sym2 V} {i : Fin m} : i ∈ S.edgeTris e ↔ e ∈ triEdges (S.tri i) := by
  simp [edgeTris]

/-- Two distinct edges lie in at most one common triangle. -/
theorem edgeTris_inter_card_le {e e' : Sym2 V} (hne : e ≠ e') :
    ((S.edgeTris e).filter (fun i => e' ∈ triEdges (S.tri i))).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  simp only [mem_filter, mem_edgeTris] at hi hj
  induction e using Sym2.ind with
  | _ x y =>
  induction e' using Sym2.ind with
  | _ p r =>
  have hX : 3 ≤ (({x, y} : Finset V) ∪ {p, r}).card := by
    have hxy : x ≠ y := (mem_triEdges.mp hi.1).2.2
    have hpr : p ≠ r := (mem_triEdges.mp hi.2).2.2
    have h2 : ({x, y} : Finset V).card = 2 := card_pair hxy
    have h2' : ({p, r} : Finset V).card = 2 := card_pair hpr
    by_contra hlt
    push Not at hlt
    have hsub : ({p, r} : Finset V) ⊆ {x, y} := by
      have hle : (({x, y} : Finset V) ∪ {p, r}).card ≤ ({x, y} : Finset V).card := by omega
      have heq := eq_of_subset_of_card_le subset_union_left hle
      rw [heq]; exact subset_union_right
    have heq : ({p, r} : Finset V) = {x, y} := eq_of_subset_of_card_le hsub (by rw [h2, h2'])
    apply hne
    have hp : p ∈ ({x, y} : Finset V) := heq ▸ mem_insert_self p {r}
    have hr : r ∈ ({x, y} : Finset V) := heq ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hp hr
    rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
    · exact absurd rfl hpr
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hpr
  exact S.eq_of_three_subset hX
    (union_subset (edge_subset_of_mem_triEdges hi.1) (edge_subset_of_mem_triEdges hi.2))
    (union_subset (edge_subset_of_mem_triEdges hj.1) (edge_subset_of_mem_triEdges hj.2))

/-- An edge avoiding `v` lies in at most one triangle through `v`. -/
theorem card_through_edge_le {v x y : V} (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v) :
    ((S.through v).filter (fun i => s(x, y) ∈ triEdges (S.tri i))).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  simp only [mem_filter, through, mem_univ, true_and] at hi hj
  have hX : ({v, x, y} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hxv.symm, hyv.symm]), card_pair hxy]
  have sub : ∀ k, v ∈ S.tri k → s(x, y) ∈ triEdges (S.tri k) → ({v, x, y} : Finset V) ⊆ S.tri k :=
    fun k hv he => insert_subset hv (edge_subset_of_mem_triEdges he)
  exact S.eq_of_three_subset hX.ge (sub i hi.1 hi.2) (sub j hj.1 hj.2)

/-- A triangle avoiding `v` shares an edge with at most three triangles through `v`. -/
theorem card_through_shares_le {v : V} {U : Fin m} (hvU : v ∉ S.tri U) :
    ((S.through v).filter (fun i => S.Shares i U)).card ≤ 3 := by
  have hsub : (S.through v).filter (fun i => S.Shares i U) ⊆
      (triEdges (S.tri U)).biUnion
        (fun e => (S.through v).filter (fun i => e ∈ triEdges (S.tri i))) := by
    intro i hi
    simp only [mem_filter] at hi
    obtain ⟨e, he1, he2⟩ := not_disjoint_iff.mp hi.2
    simp only [mem_biUnion, mem_filter]
    exact ⟨e, he2, hi.1, he1⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ e ∈ triEdges (S.tri U), ((S.through v).filter (fun i => e ∈ triEdges (S.tri i))).card
      ≤ ∑ _e ∈ triEdges (S.tri U), 1 := by
        apply sum_le_sum
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
        have h := mem_triEdges.mp he
        exact S.card_through_edge_le h.2.2 (ne_of_mem_of_not_mem h.1 hvU)
          (ne_of_mem_of_not_mem h.2.1 hvU)
    _ = (triEdges (S.tri U)).card := by simp
    _ = 3 := card_triEdges (S.card_tri U)

/-- A triangle not containing `e` shares an edge with at most three triangles through `e`. -/
theorem card_edgeTris_shares_le {e : Sym2 V} {U : Fin m} (hU : U ∉ S.edgeTris e) :
    ((S.edgeTris e).filter (fun i => S.Shares i U)).card ≤ 3 := by
  have hsub : (S.edgeTris e).filter (fun i => S.Shares i U) ⊆
      (triEdges (S.tri U)).biUnion
        (fun e' => (S.edgeTris e).filter (fun i => e' ∈ triEdges (S.tri i))) := by
    intro i hi
    simp only [mem_filter] at hi
    obtain ⟨e', he1, he2⟩ := not_disjoint_iff.mp hi.2
    simp only [mem_biUnion, mem_filter]
    exact ⟨e', he2, hi.1, he1⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ e' ∈ triEdges (S.tri U), ((S.edgeTris e).filter (fun i => e' ∈ triEdges (S.tri i))).card
      ≤ ∑ _e ∈ triEdges (S.tri U), 1 := by
        apply sum_le_sum
        intro e' he'
        have hne : e ≠ e' := by
          rintro rfl
          exact hU ((S.mem_edgeTris).mpr he')
        exact S.edgeTris_inter_card_le hne
    _ = (triEdges (S.tri U)).card := by simp
    _ = 3 := card_triEdges (S.card_tri U)

/-! ## Double counting -/

/-- Summing the loads around a star counts each triangle through `v` twice. -/
theorem sum_star_load (B : Finset (Sym2 V)) (hB : ∀ i, triEdges (S.tri i) ⊆ B)
    (w : Fin m → ℝ) (v : V) :
    ∑ e ∈ star B v, S.load w e = 2 * ∑ i ∈ S.through v, w i := by
  unfold load edgeTris
  simp only [sum_filter]
  rw [sum_comm]
  rw [mul_sum]
  unfold through
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  have hfilt : (star B v).filter (fun e => e ∈ triEdges (S.tri i)) =
      star (triEdges (S.tri i)) v := by
    ext e
    simp only [star, mem_filter]
    constructor
    · rintro ⟨⟨_, hv⟩, he⟩; exact ⟨he, hv⟩
    · rintro ⟨he, hv⟩; exact ⟨⟨hB i he, hv⟩, he⟩
  rw [sum_const, hfilt, nsmul_eq_mul]
  split_ifs with hv
  · rw [S.card_star_triEdges hv]; push_cast; ring
  · rw [S.star_triEdges_eq_empty hv]; simp

/-- Triangles through `v` and `a ≠ v` are exactly the triangles containing `va`. -/
theorem through_filter_eq_edgeTris {v a : V} (hav : a ≠ v) :
    (S.through v).filter (fun i => a ∈ S.tri i) = S.edgeTris s(v, a) := by
  ext i
  simp only [through, mem_filter, mem_univ, true_and, mem_edgeTris, mem_triEdges]
  constructor
  · rintro ⟨hv, ha⟩; exact ⟨hv, ha, hav.symm⟩
  · rintro ⟨hv, ha, _⟩; exact ⟨hv, ha⟩

/-- Summing link-weights over the other vertices counts each triangle through `v` twice. -/
theorem sum_link_weights [Fintype V] (w : Fin m → ℝ) (v : V) :
    ∑ a ∈ univ.erase v, ∑ i ∈ (S.through v).filter (fun i => a ∈ S.tri i), w i =
      2 * ∑ i ∈ S.through v, w i := by
  simp only [sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have : (univ.erase v).filter (fun a => a ∈ S.tri i) = (S.tri i).erase v := by
    ext a; simp [and_comm]
  rw [this, card_erase_of_mem (by simpa [through] using hi), S.card_tri]
  push_cast; ring

/-! ## The outside neighbourhood of a triangle through a fixed edge -/

/-- Triangles not containing `e` that share an edge with triangle `i`. -/
def outsideNbrs (e : Sym2 V) (i : Fin m) : Finset (Fin m) :=
  univ.filter (fun j => j ∉ S.edgeTris e ∧ S.Shares i j)

theorem outsideNbrs_eq {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) :
    S.outsideNbrs e i = ((triEdges (S.tri i)).erase e).biUnion
      (fun e' => (S.edgeTris e').erase i) := by
  ext j
  simp only [outsideNbrs, mem_filter, mem_univ, true_and, mem_biUnion, mem_erase, mem_edgeTris,
    Shares]
  constructor
  · rintro ⟨hje, hsh⟩
    obtain ⟨e', h1, h2⟩ := not_disjoint_iff.mp hsh
    refine ⟨e', ⟨?_, h1⟩, ?_, h2⟩
    · rintro rfl; exact hje h2
    · rintro rfl; exact hje ((S.mem_edgeTris).mp hi)
  · rintro ⟨e', ⟨hne, he'⟩, hji, hj⟩
    refine ⟨?_, not_disjoint_iff.mpr ⟨e', he', hj⟩⟩
    intro hje
    have h1 := S.edgeTris_inter_card_le (e := e) (e' := e') (Ne.symm hne)
    have hmem_i : i ∈ (S.edgeTris e).filter (fun k => e' ∈ triEdges (S.tri k)) :=
      mem_filter.mpr ⟨hi, he'⟩
    have hmem_j : j ∈ (S.edgeTris e).filter (fun k => e' ∈ triEdges (S.tri k)) :=
      mem_filter.mpr ⟨(S.mem_edgeTris).mpr hje, hj⟩
    exact hji (card_le_one.mp h1 j hmem_j i hmem_i)

theorem sum_outsideNbrs {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) (w : Fin m → ℝ) :
    ∑ j ∈ S.outsideNbrs e i, w j = ∑ e' ∈ (triEdges (S.tri i)).erase e, (S.load w e' - w i) := by
  rw [S.outsideNbrs_eq hi, sum_biUnion]
  · apply sum_congr rfl
    intro e' he'
    rw [load, ← add_sum_erase _ _ ((S.mem_edgeTris).mpr (mem_erase.mp he').2)]
    ring
  · intro e1 h1 e2 h2 hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hc := S.edgeTris_inter_card_le (e := e1) (e' := e2) hne
    have hmi : i ∈ (S.edgeTris e1).filter (fun k => e2 ∈ triEdges (S.tri k)) :=
      mem_filter.mpr ⟨(S.mem_edgeTris).mpr (mem_erase.mp h1).2, (mem_erase.mp h2).2⟩
    have hmj : j ∈ (S.edgeTris e1).filter (fun k => e2 ∈ triEdges (S.tri k)) :=
      mem_filter.mpr ⟨(mem_erase.mp hj1).2, (S.mem_edgeTris).mp (mem_erase.mp hj2).2⟩
    exact (mem_erase.mp hj1).1 (card_le_one.mp hc j hmj i hmi)

theorem card_triEdges_erase {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) :
    ((triEdges (S.tri i)).erase e).card = 2 := by
  rw [card_erase_of_mem ((S.mem_edgeTris).mp hi), card_triEdges (S.card_tri i)]

/-- A triangle through `v` has at most one edge avoiding `v`; any triangle avoiding
`v` and sharing an edge with it contains that edge. -/
theorem sum_outside_shares_le (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) {v : V} {i : Fin m}
    (hvi : v ∈ S.tri i) (Lmax : ℝ) (hL : ∀ e ∈ triEdges (S.tri i), S.load w e ≤ Lmax)
    (hL0 : 0 ≤ Lmax) :
    ∑ U ∈ univ.filter (fun U => v ∉ S.tri U ∧ S.Shares i U), w U ≤ Lmax := by
  by_cases hemp : univ.filter (fun U => v ∉ S.tri U ∧ S.Shares i U) = ∅
  · rw [hemp, sum_empty]; exact hL0
  obtain ⟨U0, hU0⟩ := nonempty_iff_ne_empty.mpr hemp
  simp only [mem_filter, mem_univ, true_and] at hU0
  obtain ⟨e0, he0i, he0U⟩ := not_disjoint_iff.mp hU0.2
  have key : ∀ U, v ∉ S.tri U → ∀ e, e ∈ triEdges (S.tri i) → e ∈ triEdges (S.tri U) →
      e = e0 := by
    intro U hvU e hei heU
    induction e using Sym2.ind with
    | _ x y =>
    induction e0 using Sym2.ind with
    | _ x' y' =>
    have h1 := mem_triEdges.mp hei
    have h2 := mem_triEdges.mp heU
    have h3 := mem_triEdges.mp he0i
    have h4 := mem_triEdges.mp he0U
    have hxv : x ≠ v := ne_of_mem_of_not_mem h2.1 hvU
    have hyv : y ≠ v := ne_of_mem_of_not_mem h2.2.1 hvU
    have hx'v : x' ≠ v := ne_of_mem_of_not_mem h4.1 hU0.1
    have hy'v : y' ≠ v := ne_of_mem_of_not_mem h4.2.1 hU0.1
    have hT := eq_triple_of_mem (S.card_tri i) hvi h1.1 h1.2.1 hxv.symm hyv.symm h1.2.2
    have hx' := h3.1; have hy' := h3.2.1
    rw [hT] at hx' hy'
    simp only [mem_insert, mem_singleton] at hx' hy'
    rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
      (first
        | exact absurd rfl hx'v
        | exact absurd rfl hy'v
        | exact absurd rfl h3.2.2
        | rfl
        | exact Sym2.eq_swap)
  have hsub : univ.filter (fun U => v ∉ S.tri U ∧ S.Shares i U) ⊆ S.edgeTris e0 := by
    intro U hU
    simp only [mem_filter, mem_univ, true_and] at hU
    obtain ⟨e, hei, heU⟩ := not_disjoint_iff.mp hU.2
    rw [S.mem_edgeTris, ← key U hU.1 e hei heU]
    exact heU
  calc _ ≤ ∑ U ∈ S.edgeTris e0, w U := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    _ = S.load w e0 := rfl
    _ ≤ Lmax := hL e0 he0i

end TriSystem

end PartitionedTriangleAbsorption.Nibble
