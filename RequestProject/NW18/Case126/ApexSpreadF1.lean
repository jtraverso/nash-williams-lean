/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.CrossingCoverF1
import RequestProject.NW18.Case126.SpreadMatchingGen

/-!
# Theorem 14.7 for `F₁`, vortex route: greedy apex cover of the outer leftover with apex LOAD CAP

**Attribution.**  Adapted from the L3 F0 project (`L3_F0_reference/L3F0/ApexCover.lean`,
`exists_apexes`, `apex_cover`).  The only change is the triangle-type condition: instead of the
`F0` condition "the three labels are not all equal" we require the `F₁` condition
`{p x, p y, p z} ∈ F₁` on the apex `z`.  Everything else (greedy choice, freshness, load cap) is
the F0 argument verbatim.

Leftover edges `x_i y_i` (`i < k`) with both ends outside `U` are covered by triangles
`x_i y_i z_i` with an apex `z_i ∈ U` and both apex edges in the cross reserve `Rc`.  An apex is
blocked if one of its two edges was already used (`≤ 2γ` apexes) or if it is already the apex of
`β` earlier edges (`≤ k / β` apexes), so `2γ + k/β < s` suffices and the apex load is `≤ β`.
In contrast with `CrossingCover.F1_inner_cover` (which needs `2|X|+1` common neighbours, i.e. the
peeling regime), the requirement here is `k / β < s`: the number of leftover edges divided by the
apex cap, which is small for a sparse leftover even when `|W \ U| ≫ |U|`.
-/

namespace NashWilliams18.ApexF1

open Finset PartitionedTriangleAbsorption SpreadGen
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [DecidableEq V]

/-- The apex edges chosen for the first `m` leftover edges. -/
def apexEdges (m : ℕ) (x y z : ℕ → V) : Finset (Sym2 V) :=
  (range m).biUnion (fun i => {s(x i, z i), s(y i, z i)})

theorem mem_apexEdges {m : ℕ} {x y z : ℕ → V} {f : Sym2 V} :
    f ∈ apexEdges m x y z ↔ ∃ i < m, f = s(x i, z i) ∨ f = s(y i, z i) := by
  simp [apexEdges]

/-- **Greedy apex selection.** -/
theorem F1_exists_apexes (p : V → Fin 4) (Rc : Finset (Sym2 V)) (U : Finset V) (k : ℕ)
    (x y : ℕ → V) (s γ β : ℕ)
    (hxU : ∀ i < k, x i ∉ U) (hyU : ∀ i < k, y i ∉ U)
    (hdegx : ∀ i < k, ((range k).filter (fun j => x i = x j ∨ x i = y j)).card ≤ γ)
    (hdegy : ∀ i < k, ((range k).filter (fun j => y i = x j ∨ y i = y j)).card ≤ γ)
    (hsup : ∀ i < k, s ≤ (U.filter (fun z => s(x i, z) ∈ Rc ∧ s(y i, z) ∈ Rc ∧
      ({p (x i), p (y i), p z} : Multiset (Fin 4)) ∈ F1)).card)
    (hβ : 0 < β) (hs : 2 * γ + k / β < s) :
    ∃ z : ℕ → V, (∀ i < k, z i ∈ U ∧ s(x i, z i) ∈ Rc ∧ s(y i, z i) ∈ Rc ∧
        ({p (x i), p (y i), p (z i)} : Multiset (Fin 4)) ∈ F1) ∧
      (∀ i < k, ∀ j < k, i ≠ j → s(x i, z i) ∉ ({s(x j, z j), s(y j, z j)} : Finset _) ∧
        s(y i, z i) ∉ ({s(x j, z j), s(y j, z j)} : Finset _)) ∧
      (∀ w, ((range k).filter (fun i => z i = w)).card ≤ β) := by
  classical
  suffices H : ∀ m ≤ k, ∃ z : ℕ → V, (∀ i < m, z i ∈ U ∧ s(x i, z i) ∈ Rc ∧ s(y i, z i) ∈ Rc ∧
        ({p (x i), p (y i), p (z i)} : Multiset (Fin 4)) ∈ F1) ∧
      (∀ i < m, ∀ j < m, i ≠ j → s(x i, z i) ∉ ({s(x j, z j), s(y j, z j)} : Finset _) ∧
        s(y i, z i) ∉ ({s(x j, z j), s(y j, z j)} : Finset _)) ∧
      (∀ w, ((range m).filter (fun i => z i = w)).card ≤ β) from H k le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun _ => x 0, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _), fun w => by simp⟩
  | succ m ih =>
    intro hm
    have hmk : m < k := hm
    obtain ⟨z, hz, hdis, hload⟩ := ih (Nat.le_of_succ_le hm)
    -- blocked apexes
    set Blk : Finset V := ((range m).filter (fun j => x m = x j ∨ x m = y j ∨
      y m = x j ∨ y m = y j)).image z with hBlk
    set Sat : Finset V := (U.filter (fun w => β ≤ ((range m).filter (fun i => z i = w)).card))
      with hSat
    set Cand : Finset V := U.filter (fun w => s(x m, w) ∈ Rc ∧ s(y m, w) ∈ Rc ∧
      ({p (x m), p (y m), p w} : Multiset (Fin 4)) ∈ F1) with hCand
    have hBlkc : Blk.card ≤ 2 * γ := by
      refine Finset.card_image_le.trans ?_
      have h1 : (range m).filter (fun j => x m = x j ∨ x m = y j ∨ y m = x j ∨ y m = y j) ⊆
          (range k).filter (fun j => x m = x j ∨ x m = y j) ∪
          (range k).filter (fun j => y m = x j ∨ y m = y j) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hj ⊢
        rcases hj with ⟨hj, h | h | h | h⟩
        · exact Or.inl ⟨by omega, Or.inl h⟩
        · exact Or.inl ⟨by omega, Or.inr h⟩
        · exact Or.inr ⟨by omega, Or.inl h⟩
        · exact Or.inr ⟨by omega, Or.inr h⟩
      have := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      have := hdegx m hmk
      have := hdegy m hmk
      omega
    have hSatc : Sat.card ≤ k / β := by
      have hsum : β * Sat.card ≤ m := by
        calc β * Sat.card = ∑ _w ∈ Sat, β := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ w ∈ Sat, ((range m).filter (fun i => z i = w)).card :=
            Finset.sum_le_sum (fun w hw => (Finset.mem_filter.mp hw).2)
          _ = ((range m).filter (fun i => z i ∈ Sat)).card := by
            rw [Finset.card_eq_sum_card_fiberwise (s := (range m).filter (fun i => z i ∈ Sat))
              (f := z) (t := Sat)
              (fun i hi => (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2)]
            apply Finset.sum_congr rfl
            intro w hw
            congr 1
            ext i
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hi, rfl⟩; exact ⟨⟨hi, hw⟩, rfl⟩
            · rintro ⟨⟨hi, -⟩, h⟩; exact ⟨hi, h⟩
          _ ≤ (range m).card := Finset.card_filter_le _ _
          _ = m := Finset.card_range m
      have : Sat.card ≤ m / β := (Nat.le_div_iff_mul_le hβ).mpr (by linarith)
      exact this.trans (Nat.div_le_div_right (le_of_lt hmk))
    have hCandc : s ≤ Cand.card := hsup m hmk
    obtain ⟨w, hwC, hwB⟩ : ∃ w ∈ Cand, w ∉ Blk ∪ Sat := by
      by_contra hcon
      push_neg at hcon
      have : Cand ⊆ Blk ∪ Sat := hcon
      have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
      omega
    simp only [hCand, Finset.mem_filter] at hwC
    simp only [Finset.mem_union, not_or] at hwB
    obtain ⟨hwBlk, hwSat⟩ := hwB
    let z' : ℕ → V := fun i => if i = m then w else z i
    have hz'm : z' m = w := by simp [z']
    have hz'i : ∀ i < m, z' i = z i := fun i hi => by simp [z', Nat.ne_of_lt hi]
    -- freshness of the new apex edges
    have hfresh : ∀ j < m, s(x m, w) ∉ ({s(x j, z j), s(y j, z j)} : Finset _) ∧
        s(y m, w) ∉ ({s(x j, z j), s(y j, z j)} : Finset _) := by
      intro j hj
      have hzjU := (hz j hj).1
      have hblk : ¬ (x m = x j ∨ x m = y j ∨ y m = x j ∨ y m = y j) ∨ w ≠ z j := by
        by_contra hc
        push_neg at hc
        exact hwBlk (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj, hc.1⟩, hc.2.symm⟩)
      have hxm := hxU m hmk
      have hym := hyU m hmk
      have hne1 : ∀ a b : V, a ∉ U → b ∉ U → s(a, w) = s(b, z j) → a = b ∧ w = z j := by
        intro a b ha hb h
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact ⟨h1, h2⟩
        · exact absurd (h1 ▸ hzjU) ha
      have hxj := hxU j (lt_trans hj hmk)
      have hyj := hyU j (lt_trans hj hmk)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
      · obtain ⟨h1, h2⟩ := hne1 _ _ hxm hxj h
        rcases hblk with hb | hb
        · exact hb (Or.inl h1)
        · exact hb h2
      · obtain ⟨h1, h2⟩ := hne1 _ _ hxm hyj h
        rcases hblk with hb | hb
        · exact hb (Or.inr (Or.inl h1))
        · exact hb h2
      · obtain ⟨h1, h2⟩ := hne1 _ _ hym hxj h
        rcases hblk with hb | hb
        · exact hb (Or.inr (Or.inr (Or.inl h1)))
        · exact hb h2
      · obtain ⟨h1, h2⟩ := hne1 _ _ hym hyj h
        rcases hblk with hb | hb
        · exact hb (Or.inr (Or.inr (Or.inr h1)))
        · exact hb h2
    -- the old apex edges avoid the new ones (symmetric form)
    have hfresh' : ∀ j < m, s(x j, z j) ∉ ({s(x m, w), s(y m, w)} : Finset _) ∧
        s(y j, z j) ∉ ({s(x m, w), s(y m, w)} : Finset _) := by
      intro j hj
      obtain ⟨h1, h2⟩ := hfresh j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2 ⊢
      exact ⟨⟨fun h => h1.1 h.symm, fun h => h2.1 h.symm⟩,
        ⟨fun h => h1.2 h.symm, fun h => h2.2 h.symm⟩⟩
    refine ⟨z', fun i hi => ?_, fun i hi j hj hij => ?_, fun v => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hz'i i hi]; exact hz i hi
      · rw [hz'm]; exact hwC
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hz'i i hi, hz'i j hj]; exact hdis i hi j hj hij
      · rw [hz'i i hi, hz'm]; exact hfresh' i hi
      · rw [hz'i j hj, hz'm]; exact hfresh j hj
      · exact absurd rfl hij
    · rw [Finset.range_add_one, Finset.filter_insert]
      have hold : (range m).filter (fun i => z' i = v) = (range m).filter (fun i => z i = v) :=
        Finset.filter_congr (fun i hi => by rw [hz'i i (Finset.mem_range.mp hi)])
      split_ifs with hv
      · rw [hold, Finset.card_insert_of_notMem (by simp)]
        rw [hz'm] at hv
        subst hv
        have : ¬ β ≤ ((range m).filter (fun i => z i = w)).card := by
          intro hb; exact hwSat (Finset.mem_filter.mpr ⟨hwC.1, hb⟩)
        omega
      · rw [hold]; exact hload v

theorem deg_pair_le (a b z v : V) (hab : a ≠ b) :
    (({s(a, z), s(b, z)} : Finset (Sym2 V)).filter (fun e => v ∈ e)).card ≤
      (if v = a ∨ v = b then 1 else 0) + (if z = v then 2 else 0) := by
  by_cases hz : z = v
  · simp only [hz, ↓reduceIte]
    exact (Finset.card_filter_le _ _).trans (Finset.card_insert_le _ _ |>.trans (by simp))
  · simp only [hz, ↓reduceIte, add_zero]
    by_cases hva : v = a
    · subst hva
      simp only [true_or, ↓reduceIte]
      apply Finset.card_le_one.mpr
      intro e he e' he'
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at he he'
      have hb : ¬ v ∈ s(b, z) := by
        simp only [Sym2.mem_iff, not_or]; exact ⟨hab, fun h => hz h.symm⟩
      rcases he with ⟨rfl | rfl, h⟩ <;> rcases he' with ⟨rfl | rfl, h'⟩
      all_goals first | rfl | exact absurd h hb | exact absurd h' hb
    · by_cases hvb : v = b
      · subst hvb
        simp only [or_true, ↓reduceIte]
        apply Finset.card_le_one.mpr
        intro e he e' he'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at he he'
        have ha : ¬ v ∈ s(a, z) := by
          simp only [Sym2.mem_iff, not_or]; exact ⟨hva, fun h => hz h.symm⟩
        rcases he with ⟨rfl | rfl, h⟩ <;> rcases he' with ⟨rfl | rfl, h'⟩
        all_goals first | rfl | exact absurd h ha | exact absurd h' ha
      · have hn : ¬ (v = a ∨ v = b) := by tauto
        simp only [hn, ↓reduceIte]
        rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl <;> simp only [Sym2.mem_iff] at hv <;> tauto

/-- **Apex cover.** The outer leftover edges together with the chosen apex edges have an
actual `F₁`-decomposition; the apex edges lie in `Rc`, avoid the leftover, and have degree at
most `#{i : v ∈ {x i, y i}} + 2 · #{i : z i = v}` at every vertex (so the apex load is `≤ 2β`
on `U` and equals the leftover deg outside `U`). -/
theorem F1_apex_cover_spread (p : V → Fin 4) (Rc : Finset (Sym2 V)) (U : Finset V) (k : ℕ)
    (x y : ℕ → V) (s γ β : ℕ)
    (hxy : ∀ i < k, x i ≠ y i)
    (hinj : ∀ i < k, ∀ j < k, s(x i, y i) = s(x j, y j) → i = j)
    (hxU : ∀ i < k, x i ∉ U) (hyU : ∀ i < k, y i ∉ U)
    (hdegx : ∀ i < k, ((range k).filter (fun j => x i = x j ∨ x i = y j)).card ≤ γ)
    (hdegy : ∀ i < k, ((range k).filter (fun j => y i = x j ∨ y i = y j)).card ≤ γ)
    (hsup : ∀ i < k, s ≤ (U.filter (fun z => s(x i, z) ∈ Rc ∧ s(y i, z) ∈ Rc ∧
      ({p (x i), p (y i), p z} : Multiset (Fin 4)) ∈ F1)).card)
    (hβ : 0 < β) (hs : 2 * γ + k / β < s) :
    ∃ z : ℕ → V, (∀ i < k, z i ∈ U) ∧ apexEdges k x y z ⊆ Rc ∧
      Disjoint ((range k).image (fun i => s(x i, y i))) (apexEdges k x y z) ∧
      (∀ w, ((range k).filter (fun i => z i = w)).card ≤ β) ∧
      (∀ v, deg (apexEdges k x y z) v ≤
        ((range k).filter (fun i => v = x i ∨ v = y i)).card +
          2 * ((range k).filter (fun i => z i = v)).card) ∧
      HasDecomp p F1 ((range k).image (fun i => s(x i, y i)) ∪ apexEdges k x y z) := by
  classical
  obtain ⟨z, hz, hdis, hload⟩ :=
    F1_exists_apexes p Rc U k x y s γ β hxU hyU hdegx hdegy hsup hβ hs
  have hzU : ∀ i < k, z i ∈ U := fun i hi => (hz i hi).1
  have hdist : ∀ i < k, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i := fun i hi =>
    ⟨hxy i hi, fun h => hxU i hi (h ▸ hzU i hi), fun h => hyU i hi (h ▸ hzU i hi)⟩
  -- leftover edges contain no vertex of `U`; apex edges contain one
  have hHnoU : ∀ i < k, ∀ v ∈ s(x i, y i), v ∉ U := by
    intro i hi v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    exacts [hxU i hi, hyU i hi]
  have hHA : ∀ i < k, ∀ j < k, s(x i, y i) ≠ s(x j, z j) ∧ s(x i, y i) ≠ s(y j, z j) := by
    intro i hi j hj
    constructor <;> intro h
    · exact hHnoU i hi (z j) (h ▸ Sym2.mem_mk_right _ _) (hzU j hj)
    · exact hHnoU i hi (z j) (h ▸ Sym2.mem_mk_right _ _) (hzU j hj)
  let tri : ℕ → Finset V := fun i => {x i, y i, z i}
  have htriE : ∀ i < k, triEdges (tri i) = {s(x i, y i), s(x i, z i), s(y i, z i)} := by
    intro i hi
    obtain ⟨a, b, c⟩ := hdist i hi
    exact PartitionedTriangleAbsorption.triEdges_three a b c
  refine ⟨z, hzU, ?_, ?_, hload, ?_, (range k).image tri, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, hi, h | h⟩ := mem_apexEdges.mp hf <;> rw [h]
    exacts [(hz i hi).2.1, (hz i hi).2.2.1]
  · rw [Finset.disjoint_left]
    intro f hf hf'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨j, hj, h | h⟩ := mem_apexEdges.mp hf'
    · exact (hHA i (Finset.mem_range.mp hi) j hj).1 h
    · exact (hHA i (Finset.mem_range.mp hi) j hj).2 h
  · intro v
    unfold deg apexEdges
    rw [Finset.filter_biUnion]
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ i ∈ range k, (({s(x i, z i), s(y i, z i)} : Finset (Sym2 V)).filter
          (fun e => v ∈ e)).card
        ≤ ∑ i ∈ range k, ((if v = x i ∨ v = y i then 1 else 0) + (if z i = v then 2 else 0)) :=
          Finset.sum_le_sum (fun i hi =>
            deg_pair_le (x i) (y i) (z i) v (hxy i (Finset.mem_range.mp hi)))
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl; intro i _; split_ifs <;> rfl
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hi' := Finset.mem_range.mp hi
    obtain ⟨a, b, c⟩ := hdist i hi'
    refine ⟨?_, ?_⟩
    · simp only [tri]
      rw [Finset.card_insert_of_notMem (by simp [a, b]),
        Finset.card_insert_of_notMem (by simp [c]), Finset.card_singleton]
    · simp only [tri]
      have hm : ({x i, y i, z i} : Finset V).val.map p = {p (x i), p (y i), p (z i)} := by
        simp [Finset.insert_val, Multiset.ndinsert_of_notMem, a, b, c]
      rw [hm]
      exact (hz i hi').2.2.2
  · intro t ht t' ht' htt
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at ht ht'
    obtain ⟨i, hi, rfl⟩ := ht
    obtain ⟨j, hj, rfl⟩ := ht'
    have hij : i ≠ j := fun h => htt (h ▸ rfl)
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf hf'
    rw [htriE i hi] at hf
    rw [htriE j hj] at hf'
    obtain ⟨hd1, hd2⟩ := hdis i hi j hj hij
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd1 hd2 hf hf'
    rcases hf with rfl | rfl | rfl <;> rcases hf' with h | h | h
    · exact hij (hinj i hi j hj h)
    · exact (hHA i hi j hj).1 h
    · exact (hHA i hi j hj).2 h
    · exact (hHA j hj i hi).1 h.symm
    · exact hd1.1 h
    · exact hd1.2 h
    · exact (hHA j hj i hi).2 h.symm
    · exact hd2.1 h
    · exact hd2.2 h
  · ext f
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Finset.mem_union]
    constructor
    · rintro ⟨t, ⟨i, hi, rfl⟩, hf⟩
      rw [htriE i hi] at hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr (mem_apexEdges.mpr ⟨i, hi, Or.inl rfl⟩)
      · exact Or.inr (mem_apexEdges.mpr ⟨i, hi, Or.inr rfl⟩)
    · rintro (⟨i, hi, rfl⟩ | hf)
      · exact ⟨tri i, ⟨i, hi, rfl⟩, by rw [htriE i hi]; simp⟩
      · obtain ⟨i, hi, h | h⟩ := mem_apexEdges.mp hf
        · exact ⟨tri i, ⟨i, hi, rfl⟩, by rw [htriE i hi, h]; simp⟩
        · exact ⟨tri i, ⟨i, hi, rfl⟩, by rw [htriE i hi, h]; simp⟩

end NashWilliams18.ApexF1
