/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128Reduction
public import RequestProject.NW18.Case125.Surplus

@[expose] public section

/-!
# Lemma 15.17: greedy covering of a sparse set of interior edges

Let `H` be a graph with a 2-partition `q`, and `O` a set of *interior* edges of `H` (both ends in
the same part) with maximum degree at most `d`, such that the two ends of every `O`-edge have at
least `m` common neighbours in the other part.  If `|O| + 4K(d + K) < K m` for some `K > 0`, then
there is a family of edge-disjoint triangles of `H`, each consisting of one `O`-edge and an apex in
the other part, covering `O`, and whose edges meet every vertex at most `2(d + K)` times.

The proof is the greedy one: the edges of `O` are processed one at a time, and the apex is
chosen among the common neighbours that are apex of fewer than `K` triangles so far and for which
neither of the two new edges has been used before.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex set of a triple `(x, y, z)`. -/
def triOf (s : V × V × V) : Finset V := {s.1, s.2.1, s.2.2}

/-- The invariant of the greedy procedure: `S` is a family of triples `(x, y, z)` (an `O'`-edge
`xy` and an apex `z` in the other part) in bijection with `O'`, whose triangles are edge-disjoint
and in which every vertex is apex at most `K` times. -/
structure GreedyInv (H : SimpleGraph V) (q : V → Fin 2) (O' : Finset (Sym2 V)) (K : ℕ)
    (S : Finset (V × V × V)) : Prop where
  edge : ∀ s ∈ S, s(s.1, s.2.1) ∈ O'
  cover : ∀ e ∈ O', ∃ s ∈ S, s(s.1, s.2.1) = e
  inj : ∀ s ∈ S, ∀ s' ∈ S, s(s.1, s.2.1) = s(s'.1, s'.2.1) → s = s'
  card : S.card = O'.card
  apexq : ∀ s ∈ S, q s.2.2 ≠ q s.1
  adj1 : ∀ s ∈ S, H.Adj s.1 s.2.2
  adj2 : ∀ s ∈ S, H.Adj s.2.1 s.2.2
  disj : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → Disjoint (triEdges (triOf s)) (triEdges (triOf s'))
  apex : ∀ z, (S.filter (fun s => s.2.2 = z)).card ≤ K

section

variable {H : SimpleGraph V} {q : V → Fin 2} {O : Finset (Sym2 V)}

omit [Fintype V] in
lemma triOf_ne {S : Finset (V × V × V)} {O' : Finset (Sym2 V)} {K : ℕ}
    (hinv : GreedyInv H q O' K S) (hO'O : O' ⊆ O)
    (hOH : ∀ x y, s(x, y) ∈ O → H.Adj x y) (hOint : ∀ x y, s(x, y) ∈ O → q x = q y)
    {s : V × V × V} (hs : s ∈ S) :
    s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2 ∧ q s.1 = q s.2.1 := by
  have he := hO'O (hinv.edge s hs)
  refine ⟨(hOH _ _ he).ne, (hinv.adj1 s hs).ne, (hinv.adj2 s hs).ne, hOint _ _ he⟩

omit [Fintype V] in
lemma triOf_injOn {S : Finset (V × V × V)} {O' : Finset (Sym2 V)} {K : ℕ}
    (hinv : GreedyInv H q O' K S) (hO'O : O' ⊆ O)
    (hOH : ∀ x y, s(x, y) ∈ O → H.Adj x y) (hOint : ∀ x y, s(x, y) ∈ O → q x = q y) :
    Set.InjOn triOf (S : Set (V × V × V)) := by
  intro s hs s' hs' heq
  by_contra hne
  have hd := hinv.disj s hs s' hs' hne
  have h1 := triOf_ne hinv hO'O hOH hOint hs
  have hmem : s(s.1, s.2.1) ∈ triEdges (triOf s) :=
    mk_mem_triEdges.mpr ⟨by simp [triOf], by simp [triOf], h1.1⟩
  exact (disjoint_left.mp hd) hmem (heq ▸ hmem)

omit [Fintype V] in
lemma greedy_card3 {S : Finset (V × V × V)} {O' : Finset (Sym2 V)} {K : ℕ}
    (hinv : GreedyInv H q O' K S) (hO'O : O' ⊆ O)
    (hOH : ∀ x y, s(x, y) ∈ O → H.Adj x y) (hOint : ∀ x y, s(x, y) ∈ O → q x = q y) :
    ∀ t ∈ S.image triOf, t.card = 3 := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  obtain ⟨h1, h2, h3, -⟩ := triOf_ne hinv hO'O hOH hOint hs
  rw [triOf, card_insert_of_notMem (by simp [h1, h2]), card_pair h3]

omit [Fintype V] in
lemma greedy_pairwiseDisjoint {S : Finset (V × V × V)} {O' : Finset (Sym2 V)} {K : ℕ}
    (hinv : GreedyInv H q O' K S) :
    ((S.image triOf : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint triEdges := by
  intro t ht t' ht' hne
  obtain ⟨s, hs, rfl⟩ := mem_image.mp (mem_coe.mp ht)
  obtain ⟨s', hs', rfl⟩ := mem_image.mp (mem_coe.mp ht')
  exact hinv.disj s hs s' hs' (fun h => hne (h ▸ rfl))

omit [Fintype V] in
/-- Edges of the greedy family at a vertex: at most `2(d + K)`. -/
lemma greedy_deg_bound {S : Finset (V × V × V)} {O' : Finset (Sym2 V)} {K d : ℕ}
    (hinv : GreedyInv H q O' K S) (hO'O : O' ⊆ O)
    (hOH : ∀ x y, s(x, y) ∈ O → H.Adj x y) (hOint : ∀ x y, s(x, y) ∈ O → q x = q y)
    (hOdeg : ∀ v, (O.filter (fun e => v ∈ e)).card ≤ d) (v : V) :
    (((S.image triOf).biUnion triEdges).filter (fun e => v ∈ e)).card ≤ 2 * (d + K) := by
  rw [covered_incident_card _ (greedy_card3 hinv hO'O hOH hOint)
    (greedy_pairwiseDisjoint hinv) v]
  have hsplit : ((S.image triOf).filter (fun t => v ∈ t)).card ≤
      (S.filter (fun s => s.1 = v ∨ s.2.1 = v)).card + (S.filter (fun s => s.2.2 = v)).card := by
    calc _ ≤ (S.filter (fun s => v ∈ triOf s)).card := by
          rw [filter_image]; exact card_image_le
      _ ≤ _ := by
          refine (card_le_card ?_).trans (card_union_le _ _)
          intro s hs
          simp only [mem_filter, triOf, mem_insert, mem_singleton, mem_union] at hs ⊢
          rcases hs with ⟨hs, h | h | h⟩
          · exact Or.inl ⟨hs, Or.inl h.symm⟩
          · exact Or.inl ⟨hs, Or.inr h.symm⟩
          · exact Or.inr ⟨hs, h.symm⟩
  have h1 : (S.filter (fun s => s.1 = v ∨ s.2.1 = v)).card ≤ d := by
    refine le_trans ?_ (hOdeg v)
    refine card_le_card_of_injOn (fun s => s(s.1, s.2.1)) ?_ ?_
    · intro s hs
      obtain ⟨hs, hv⟩ := mem_filter.mp hs
      refine mem_filter.mpr ⟨hO'O (hinv.edge s hs), ?_⟩
      rcases hv with h | h <;> simp [h]
    · intro s hs s' hs' h
      exact hinv.inj s (mem_filter.mp hs).1 s' (mem_filter.mp hs').1 h
  have h2 := hinv.apex v
  omega

end

/-- One step of the greedy procedure: the invariant extends to one more `O`-edge. -/
lemma greedy_step (H : SimpleGraph V) [DecidableRel H.Adj] (q : V → Fin 2)
    (O : Finset (Sym2 V)) (d m K : ℕ)
    (hOH : ∀ x y, s(x, y) ∈ O → H.Adj x y) (hOint : ∀ x y, s(x, y) ∈ O → q x = q y)
    (hOdeg : ∀ v, (O.filter (fun e => v ∈ e)).card ≤ d)
    (hcom : ∀ x y, s(x, y) ∈ O →
      m ≤ (univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z)).card)
    (hcond : O.card + K * (4 * (d + K)) < K * m)
    {O' : Finset (Sym2 V)} {S : Finset (V × V × V)} (hinv : GreedyInv H q O' K S)
    (hO'O : O' ⊆ O) {x y : V} (heO : s(x, y) ∈ O) (heO' : s(x, y) ∉ O') :
    ∃ S', GreedyInv H q (insert s(x, y) O') K S' := by
  set U := (S.image triOf).biUnion triEdges with hU
  set C := univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z) with hC
  set B1 := univ.filter (fun z => K ≤ (S.filter (fun s => s.2.2 = z)).card) with hB1def
  set B2 := C.filter (fun z => s(x, z) ∈ U) with hB2def
  set B3 := C.filter (fun z => s(y, z) ∈ U) with hB3def
  have hB1 : K * B1.card ≤ O.card := by
    calc K * B1.card = ∑ z ∈ B1, K := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ z ∈ B1, (S.filter (fun s => s.2.2 = z)).card :=
          sum_le_sum fun z hz => (mem_filter.mp hz).2
      _ ≤ ∑ z, (S.filter (fun s => s.2.2 = z)).card := sum_le_sum_of_subset (subset_univ _)
      _ = S.card := (card_eq_sum_card_fiberwise (fun s _ => mem_univ s.2.2)).symm
      _ = O'.card := hinv.card
      _ ≤ O.card := card_le_card hO'O
  have hB2 : B2.card ≤ 2 * (d + K) := by
    refine le_trans (card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_)
      (greedy_deg_bound hinv hO'O hOH hOint hOdeg x)
    · intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).2, Sym2.mem_mk_left x z⟩
    · intro a _ b _ h
      exact Sym2.congr_right.mp h
  have hB3 : B3.card ≤ 2 * (d + K) := by
    refine le_trans (card_le_card_of_injOn (fun z => s(y, z)) ?_ ?_)
      (greedy_deg_bound hinv hO'O hOH hOint hOdeg y)
    · intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).2, Sym2.mem_mk_left y z⟩
    · intro a _ b _ h
      exact Sym2.congr_right.mp h
  have hex : ∃ z ∈ C, z ∉ B1 ∧ z ∉ B2 ∧ z ∉ B3 := by
    by_contra hno
    push_neg at hno
    have hsub : C ⊆ B1 ∪ B2 ∪ B3 := by
      intro z hz
      simp only [mem_union]
      by_cases h1 : z ∈ B1
      · exact Or.inl (Or.inl h1)
      by_cases h2 : z ∈ B2
      · exact Or.inl (Or.inr h2)
      exact Or.inr (hno z hz h1 h2)
    have hCc := (card_le_card hsub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have hm := hcom x y heO
    have : K * m ≤ K * (B1.card + B2.card + B3.card) :=
      Nat.mul_le_mul_left _ (hm.trans hCc)
    nlinarith
  obtain ⟨z, hzC, hz1, hz2, hz3⟩ := hex
  obtain ⟨-, hqz, hxz, hyz⟩ := mem_filter.mp hzC
  have hapz : (S.filter (fun s => s.2.2 = z)).card < K := by
    by_contra h
    exact hz1 (mem_filter.mpr ⟨mem_univ _, not_lt.mp h⟩)
  have hxzU : s(x, z) ∉ U := fun h => hz2 (mem_filter.mpr ⟨hzC, h⟩)
  have hyzU : s(y, z) ∉ U := fun h => hz3 (mem_filter.mpr ⟨hzC, h⟩)
  have hxy : x ≠ y := (hOH x y heO).ne
  have hqxy : q x = q y := hOint x y heO
  have hnew : ∀ s ∈ S, Disjoint (triEdges (triOf (x, y, z))) (triEdges (triOf s)) := by
    intro s hs
    rw [disjoint_left]
    intro e he he'
    have heU : e ∈ U := mem_biUnion.mpr ⟨triOf s, mem_image_of_mem _ hs, he'⟩
    have htri : triOf (x, y, z) = {x, y, z} := rfl
    rw [htri, triEdges_three hxy hxz.ne hyz.ne] at he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · obtain ⟨a, b, c⟩ := s
      obtain ⟨hxm, hym, -⟩ := mk_mem_triEdges.mp he'
      have hqc := hinv.apexq _ hs
      have hab := (triOf_ne hinv hO'O hOH hOint hs).2.2.2
      have hedge := hinv.edge _ hs
      simp only [triOf, mem_insert, mem_singleton] at hxm hym hqc hab hedge
      rcases hxm with rfl | rfl | rfl <;> rcases hym with rfl | rfl | rfl
      · exact hxy rfl
      · exact heO' hedge
      · exact hqc hqxy.symm
      · exact heO' (Sym2.eq_swap ▸ hedge)
      · exact hxy rfl
      · exact hqc (hqxy.symm.trans hab.symm)
      · exact hqc hqxy
      · exact hqc (hqxy.trans hab.symm)
      · exact hxy rfl
    · exact hxzU heU
    · exact hyzU heU
  have hnotS : ((x, y, z) : V × V × V) ∉ S := fun h => heO' (hinv.edge _ h)
  refine ⟨insert (x, y, z) S, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (hinv.edge s hs)
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact ⟨(x, y, z), mem_insert_self _ _, rfl⟩
    · obtain ⟨s, hs, hse⟩ := hinv.cover e he
      exact ⟨s, mem_insert_of_mem hs, hse⟩
  · intro s hs s' hs' h
    rcases mem_insert.mp hs with rfl | hs <;> rcases mem_insert.mp hs' with rfl | hs'
    · rfl
    · exact absurd (h ▸ hinv.edge _ hs') heO'
    · exact absurd (h.symm ▸ hinv.edge _ hs) heO'
    · exact hinv.inj s hs s' hs' h
  · rw [card_insert_of_notMem hnotS, card_insert_of_notMem heO', hinv.card]
  · intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact hqz
    · exact hinv.apexq s hs
  · intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact hxz
    · exact hinv.adj1 s hs
  · intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact hyz
    · exact hinv.adj2 s hs
  · intro s hs s' hs' hne
    rcases mem_insert.mp hs with rfl | hs <;> rcases mem_insert.mp hs' with rfl | hs'
    · exact absurd rfl hne
    · exact hnew s' hs'
    · exact (hnew s hs).symm
    · exact hinv.disj s hs s' hs' hne
  · intro w
    rw [filter_insert]
    split_ifs with h
    · simp (config := { failIfUnchanged := false }) only at h
      subst h
      exact (card_insert_le _ _).trans hapz
    · exact hinv.apex w

/-- **Lemma 15.17** (greedy cover of sparse interior edges).  `O` is a set of interior edges
of `H` (with respect to the 2-partition `q`) of maximum degree at most `d`, whose ends have at
least `m` common neighbours in the other part; if `|O| + 4K(d + K) < K m`, then `O` is covered by
an edge-disjoint family of triangles of `H`, each made of an `O`-edge and an apex in the other
part, whose edges meet every vertex at most `2(d + K)` times. -/
theorem lemma_15_17 (H : SimpleGraph V) [DecidableRel H.Adj] (q : V → Fin 2)
    (O : Finset (Sym2 V)) (d m K : ℕ)
    (hOH : ∀ x y, s(x, y) ∈ O → H.Adj x y) (hOint : ∀ x y, s(x, y) ∈ O → q x = q y)
    (hOdeg : ∀ v, (O.filter (fun e => v ∈ e)).card ≤ d)
    (hcom : ∀ x y, s(x, y) ∈ O →
      m ≤ (univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z)).card)
    (hcond : O.card + K * (4 * (d + K)) < K * m) :
    ∃ T : Finset (Finset V), IsTrianglePacking H T ∧ O ⊆ T.biUnion triEdges ∧
      (∀ t ∈ T, ∃ x y z, t = {x, y, z} ∧ s(x, y) ∈ O ∧ q z ≠ q x ∧ q x = q y) ∧
      ∀ v, ((T.biUnion triEdges).filter (fun e => v ∈ e)).card ≤ 2 * (d + K) := by
  suffices hmain : ∀ O' ⊆ O, ∃ S, GreedyInv H q O' K S by
    obtain ⟨S, hinv⟩ := hmain O subset_rfl
    refine ⟨S.image triOf, ⟨?_, greedy_pairwiseDisjoint hinv⟩, ?_, ?_,
      greedy_deg_bound hinv subset_rfl hOH hOint hOdeg⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      rw [triOf, SimpleGraph.is3Clique_triple_iff]
      exact ⟨hOH _ _ (hinv.edge s hs), hinv.adj1 s hs, hinv.adj2 s hs⟩
    · intro e he
      obtain ⟨s, hs, rfl⟩ := hinv.cover e he
      exact mem_biUnion.mpr ⟨triOf s, mem_image_of_mem _ hs, mk_mem_triEdges.mpr
        ⟨by simp [triOf], by simp [triOf], (triOf_ne hinv subset_rfl hOH hOint hs).1⟩⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      exact ⟨s.1, s.2.1, s.2.2, rfl, hinv.edge s hs, hinv.apexq s hs,
        (triOf_ne hinv subset_rfl hOH hOint hs).2.2.2⟩
  intro O' hO'
  induction O' using Finset.induction_on with
  | empty =>
    exact ⟨∅, ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp⟩⟩
  | insert e O' heO' ih =>
    obtain ⟨S, hinv⟩ := ih ((subset_insert _ _).trans hO')
    have heO : e ∈ O := hO' (mem_insert_self _ _)
    induction e using Sym2.ind with
    | _ x y =>
      exact greedy_step H q O d m K hOH hOint hOdeg hcom hcond hinv
        ((subset_insert _ _).trans hO') heO heO'

end NashWilliams18
