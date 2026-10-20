/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PartitionedTriangleAbsorption.ReturnedBasic

@[expose] public section

/-!
# Greedy apex cover of a sparse leftover through a prechosen reserve (branch 12.4)

`greedy_apex_cover`: let `L` (leftover) and `X` (reserve) be disjoint sets of non-loop edges.
Suppose every vertex lies in at most `D` edges of `L`, and every `xy ∈ L` has at least `M`
*apexes* `z` with `xz, yz ∈ X`.  If `3|L| + 6K(K+D) < K M` for some threshold `K`, then there
is a family of edge-disjoint triangles, each consisting of one edge of `L` and two edges of `X`,
covering all of `L`.  Unused edges of `X` are simply left uncovered.

The proof is a greedy induction.  Its invariant is that each vertex `v` lies in at most
`K + d_{L'}(v)` chosen triangles (`L'` the edges processed so far): a new apex is only chosen
among vertices lying in fewer than `K` triangles, so the saturated set has size at most
`3|L|/K` by double counting.
-/

namespace NashWilliams18.Case124.ReserveCover

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma mk_mem_triEdges_iff {s : Finset V} {a b : V} :
    s(a, b) ∈ triEdges s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp [triEdges, Finset.mem_filter, and_assoc]

lemma sum_card_filter_mem (T : Finset (Finset V)) :
    ∑ v, (T.filter (fun t => v ∈ t)).card = ∑ t ∈ T, t.card := by
  simp_rw [card_filter]
  rw [Finset.sum_comm]
  simp

/-- The greedy invariant, for every prefix `L'` of the leftover. -/
lemma greedy_apex_cover_aux (L X : Finset (Sym2 V)) (hLX : Disjoint L X)
    (hLd : ∀ e ∈ L, ¬ e.IsDiag) (hXd : ∀ e ∈ X, ¬ e.IsDiag)
    (D K M : ℕ) (hD : ∀ v, (L.filter (fun e => v ∈ e)).card ≤ D)
    (hM : ∀ x y, s(x, y) ∈ L → M ≤ (univ.filter fun z => s(x, z) ∈ X ∧ s(y, z) ∈ X).card)
    (hK : 3 * L.card + 6 * K * (K + D) < K * M) :
    ∀ L' ⊆ L, ∃ T : Finset (Finset V), (∀ t ∈ T, t.card = 3) ∧
      (T : Set (Finset V)).PairwiseDisjoint triEdges ∧
      L' ⊆ T.biUnion triEdges ∧ T.biUnion triEdges ⊆ L' ∪ X ∧ T.card ≤ L'.card ∧
      ∀ v, (T.filter (fun t => v ∈ t)).card ≤ K + (L'.filter (fun e => v ∈ e)).card := by
  intro L'
  induction L' using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | @insert e L' heL' ih =>
    intro hsub
    obtain ⟨T, hT3, hTdisj, hTcov, hTsub, hTcard, hTdeg⟩ :=
      ih ((subset_insert e L').trans hsub)
    have heL : e ∈ L := hsub (mem_insert_self e L')
    have heX : e ∉ X := fun h => disjoint_left.mp hLX heL h
    induction e using Sym2.ind with
    | h x y =>
    have hxy : x ≠ y := fun h => hLd _ heL (by simp [h])
    -- the saturated set
    set c : V → ℕ := fun v => (T.filter (fun t => v ∈ t)).card with hc
    set Z := univ.filter (fun v => K ≤ c v) with hZ
    have hKpos : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h; simp at hK
      · exact h
    have hZcard : K * Z.card ≤ 3 * L.card := by
      have h1 : K * Z.card ≤ ∑ v ∈ Z, c v := by
        rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun v hv => (mem_filter.mp hv).2
      have h2 : ∑ v ∈ Z, c v ≤ ∑ v, c v :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      have h3 : ∑ v, c v = 3 * T.card := by
        rw [hc, sum_card_filter_mem, Finset.sum_congr rfl hT3]
        simp [mul_comm]
      have h4 : T.card ≤ L.card := hTcard.trans (card_le_card ((subset_insert _ _).trans hsub))
      omega
    have hcx : c x ≤ K + D := (hTdeg x).trans (by
      have := card_le_card (filter_subset_filter (fun e => x ∈ e)
        ((subset_insert _ L').trans hsub))
      have := hD x; omega)
    have hcy : c y ≤ K + D := (hTdeg y).trans (by
      have := card_le_card (filter_subset_filter (fun e => y ∈ e)
        ((subset_insert _ L').trans hsub))
      have := hD y; omega)
    set B := Z ∪ (T.filter (fun t => x ∈ t)).biUnion id ∪
      (T.filter (fun t => y ∈ t)).biUnion id with hB
    have hBcard : B.card ≤ Z.card + 3 * c x + 3 * c y := by
      have hb : ∀ w : V, ((T.filter (fun t => w ∈ t)).biUnion id).card ≤ 3 * c w := by
        intro w
        refine (card_biUnion_le).trans ?_
        rw [hc]
        simp only [id]
        rw [Finset.sum_congr rfl fun t ht => hT3 t (mem_filter.mp ht).1]
        simp [mul_comm]
      refine (card_union_le _ _).trans ?_
      have := card_union_le Z ((T.filter (fun t => x ∈ t)).biUnion id)
      have := hb x; have := hb y
      omega
    set Ap := univ.filter fun z => s(x, z) ∈ X ∧ s(y, z) ∈ X with hAp
    have hApcard : M ≤ Ap.card := hM x y heL
    have hlt : B.card < Ap.card := by
      have hZM : Z.card + 6 * (K + D) < M := by
        by_contra hcon
        push_neg at hcon
        have : K * M ≤ K * (Z.card + 6 * (K + D)) := Nat.mul_le_mul_left K hcon
        nlinarith
      omega
    obtain ⟨z, hzAp, hzB⟩ : ∃ z ∈ Ap, z ∉ B := by
      by_contra hcon
      push_neg at hcon
      exact absurd (card_le_card hcon) (not_le.mpr hlt)
    have hzX : s(x, z) ∈ X ∧ s(y, z) ∈ X := (mem_filter.mp hzAp).2
    have hxz : x ≠ z := fun h => hXd _ hzX.1 (by simp [h])
    have hyz : y ≠ z := fun h => hXd _ hzX.2 (by simp [h])
    have hzZ : z ∉ Z := fun h => hzB (mem_union_left _ (mem_union_left _ h))
    have hzx : ∀ t ∈ T, x ∈ t → z ∉ t := fun t ht hxt hzt =>
      hzB (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨t, mem_filter.mpr ⟨ht, hxt⟩, hzt⟩)))
    have hzy : ∀ t ∈ T, y ∈ t → z ∉ t := fun t ht hyt hzt =>
      hzB (mem_union_right _ (mem_biUnion.mpr ⟨t, mem_filter.mpr ⟨ht, hyt⟩, hzt⟩))
    have heT : s(x, y) ∉ T.biUnion triEdges := by
      intro h
      rcases mem_union.mp (hTsub h) with h | h
      · exact heL' h
      · exact heX h
    set t₀ : Finset V := {x, y, z} with ht₀
    -- edges of `t₀`
    have hedge : ∀ f ∈ triEdges t₀, f = s(x, y) ∨ f = s(x, z) ∨ f = s(y, z) := by
      intro f hf
      induction f using Sym2.ind with
      | h a b =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_triEdges_iff.mp hf
      simp only [ht₀, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hab
        | simp [Sym2.eq_swap]
    refine ⟨insert t₀ T, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · rw [card_insert_of_notMem (by simp [hxy, hxz]), card_insert_of_notMem (by simp [hyz]),
          card_singleton]
      · exact hT3 t ht
    · rw [coe_insert]
      refine hTdisj.insert fun t ht hne => ?_
      show Disjoint _ _
      rw [disjoint_left]
      intro f hf0 hft
      rcases hedge f hf0 with rfl | rfl | rfl
      · exact heT (mem_biUnion.mpr ⟨t, ht, hft⟩)
      · obtain ⟨hx, hz, -⟩ := mk_mem_triEdges_iff.mp hft
        exact hzx t ht hx hz
      · obtain ⟨hy, hz, -⟩ := mk_mem_triEdges_iff.mp hft
        exact hzy t ht hy hz
    · intro f hf
      rcases mem_insert.mp hf with rfl | hf
      · exact mem_biUnion.mpr ⟨t₀, mem_insert_self _ _,
          mk_mem_triEdges_iff.mpr ⟨by simp [ht₀], by simp [ht₀], hxy⟩⟩
      · exact biUnion_subset_biUnion_of_subset_left _ (subset_insert _ _) (hTcov hf)
    · intro f hf
      rw [biUnion_insert] at hf
      rcases mem_union.mp hf with hf | hf
      · rcases hedge f hf with rfl | rfl | rfl
        · exact mem_union_left _ (mem_insert_self _ _)
        · exact mem_union_right _ hzX.1
        · exact mem_union_right _ hzX.2
      · rcases mem_union.mp (hTsub hf) with h | h
        · exact mem_union_left _ (mem_insert_of_mem h)
        · exact mem_union_right _ h
    · rw [card_insert_of_notMem heL']
      have := card_insert_le t₀ T
      omega
    · intro v
      have hLv : ((insert s(x, y) L').filter (fun e => v ∈ e)).card =
          (L'.filter (fun e => v ∈ e)).card + if v ∈ s(x, y) then 1 else 0 := by
        rw [filter_insert]
        split_ifs with h
        · rw [card_insert_of_notMem (fun h' => heL' (mem_filter.mp h').1)]
        · simp
      have hTv : ((insert t₀ T).filter (fun t => v ∈ t)).card ≤
          c v + if v ∈ t₀ then 1 else 0 := by
        rw [filter_insert]
        split_ifs with h
        · exact card_insert_le _ _
        · simp [hc]
      rw [hLv]
      have hdv := hTdeg v
      have hcv : c v = (T.filter (fun t => v ∈ t)).card := rfl
      have hif : (if v ∈ t₀ then 1 else 0) ≤ 1 := by split_ifs <;> omega
      by_cases hve : v ∈ s(x, y)
      · rw [if_pos hve]; omega
      · rw [if_neg hve]
        have hvx : v ≠ x := fun h => hve (h ▸ Sym2.mem_mk_left _ _)
        have hvy : v ≠ y := fun h => hve (h ▸ Sym2.mem_mk_right _ _)
        by_cases hvz : v = z
        · have : c v < K := by
            by_contra h
            exact hzZ (hvz ▸ mem_filter.mpr ⟨mem_univ _, not_lt.mp h⟩)
          omega
        · have : v ∉ t₀ := by simp [ht₀, hvx, hvy, hvz]
          rw [if_neg this] at hTv
          omega

/-- **Greedy apex cover.**  A sparse leftover `L` is covered by edge-disjoint triangles, each
made of one edge of `L` and two edges of the reserve `X`. -/
theorem greedy_apex_cover (L X : Finset (Sym2 V)) (hLX : Disjoint L X)
    (hLd : ∀ e ∈ L, ¬ e.IsDiag) (hXd : ∀ e ∈ X, ¬ e.IsDiag)
    (D K M : ℕ) (hD : ∀ v, (L.filter (fun e => v ∈ e)).card ≤ D)
    (hM : ∀ x y, s(x, y) ∈ L → M ≤ (univ.filter fun z => s(x, z) ∈ X ∧ s(y, z) ∈ X).card)
    (hK : 3 * L.card + 6 * K * (K + D) < K * M) :
    ∃ T : Finset (Finset V), (∀ t ∈ T, t.card = 3) ∧
      (T : Set (Finset V)).PairwiseDisjoint triEdges ∧
      L ⊆ T.biUnion triEdges ∧ T.biUnion triEdges ⊆ L ∪ X := by
  obtain ⟨T, h1, h2, h3, h4, -⟩ :=
    greedy_apex_cover_aux L X hLX hLd hXd D K M hD hM hK L subset_rfl
  exact ⟨T, h1, h2, h3, h4⟩

end NashWilliams18.Case124.ReserveCover
