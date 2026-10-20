/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.HubHeap

/-! # Root load of the heap hierarchy at an auxiliary hub

At a hub, the root load of the whole hierarchy is at most `10 Δ + 22 · 2^(p+1)`, where `Δ`
bounds the reserve degrees. This is `O(Δ + |V|)`: hub congestion is **not** bounded by
`O(Δ + 1)` in this construction (see `TYPED_REFINER_F0_STAGE38.md`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection UniversalRefiner

variable {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ} (Xo : Finset (Sym2 V))

/-- Hubs of level `l`. -/
def levelHubs (p l : ℕ) : Finset (Fin (2 ^ (p + 1))) :=
  univ.filter fun i => 2 ^ (p + 1 - l) ≤ i.val ∧ i.val < 2 ^ (p + 2 - l)

omit [Fintype V] [DecidableEq V] in
theorem card_levelHubs_le {l : ℕ} (hlp : l ≤ p + 1) : (levelHubs p l).card ≤ 2 ^ (p + 1 - l) := by
  have h : (levelHubs p l).card ≤ (Ico (2 ^ (p + 1 - l)) (2 ^ (p + 2 - l))).card := by
    refine card_le_card_of_injOn (fun i => i.val) (fun i hi => ?_) (fun i _ j _ h => Fin.ext h)
    obtain ⟨h1, h2⟩ := (mem_filter.mp (mem_coe.mp hi)).2
    exact mem_coe.mpr (mem_Ico.mpr ⟨h1, h2⟩)
  rw [Nat.card_Ico, show p + 2 - l = (p + 1 - l) + 1 by omega, pow_succ 2 (p + 1 - l)] at h
  omega

theorem vChain_hub_subset (hp : Fintype.card V < 2 ^ p) {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p + 1)
    (x : HU V p) : vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l) x ⊆
      (levelHubs p l).image fun i => s(x, Sum.inr i) := by
  intro π hπ
  obtain ⟨hπ, hx⟩ := mem_vChain.mp hπ
  have hin : ∀ w ∈ π, ∃ i ∈ levelHubs p l, w = Sum.inr i := by
    intro w hw
    obtain ⟨i, rfl, h1, h2⟩ := links_hlevel Xo hp l hl1 hlp π hπ w hw
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, h1, h2⟩, rfl⟩
  rcases mem_iff_endA_endB.mp hx with h | h
  · obtain ⟨i, hi, he⟩ := hin _ (endB_mem π)
    refine mem_image.mpr ⟨i, hi, ?_⟩
    rw [← he, h, mk_endA_endB π]
  · obtain ⟨i, hi, he⟩ := hin _ (endA_mem π)
    refine mem_image.mpr ⟨i, hi, ?_⟩
    rw [← he, h, Sym2.eq_swap, mk_endA_endB π]

theorem card_vChain_hub_le (hp : Fintype.card V < 2 ^ p) {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p + 1)
    (x : HU V p) :
    (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l) x).card ≤ 2 ^ (p + 1 - l) :=
  (card_le_card (vChain_hub_subset Xo hp hl1 hlp x)).trans
    (card_image_le.trans (card_levelHubs_le hlp))

theorem hubWeight_hub_le (hp : Fintype.card V < 2 ^ p) {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p)
    (i : Fin (2 ^ (p + 1))) :
    hubWeight (links (mapE Sum.inl Xo) (heapH (V := V) p) l) (heapH p l) (Sum.inr i) ≤
      2 * 2 ^ (p + 1 - l) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  unfold hubWeight
  have hfib : (univ.filter fun w : HU V p => heapH p (m + 1) w = Sum.inr i).card ≤ 2 := by
    refine (card_le_card_of_injOn (fun w => match w with | Sum.inl _ => 0 | Sum.inr j => j.val)
      (t := {2 * i.val, 2 * i.val + 1}) ?_ ?_).trans card_le_two
    · intro w hw
      have hw := (mem_filter.mp (mem_coe.mp hw)).2
      rcases w with u | j
      · simp [heapH] at hw
      · have hlt : j.val / 2 < 2 ^ (p + 1) := lt_of_le_of_lt (Nat.div_le_self _ _) j.isLt
        simp only [heapH, hubOf_eq hlt, Sum.inr.injEq, Fin.ext_iff] at hw
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
    · intro w hw w' hw' h
      have hw := (mem_filter.mp (mem_coe.mp hw)).2
      have hw' := (mem_filter.mp (mem_coe.mp hw')).2
      rcases w with u | j <;> rcases w' with u' | j'
      · simp [heapH] at hw
      · simp [heapH] at hw
      · simp [heapH] at hw'
      · simp only at h
        rw [Fin.ext h]
  calc ∑ w ∈ univ.filter (fun w : HU V p => heapH p (m + 1) w = Sum.inr i),
        (vChain (links (mapE Sum.inl Xo) (heapH p) (m + 1)) w).card
      ≤ ∑ _w ∈ univ.filter (fun w : HU V p => heapH p (m + 1) w = Sum.inr i),
          2 ^ (p + 1 - (m + 1)) :=
        sum_le_sum fun w _ => card_vChain_hub_le Xo hp (by omega) (by omega) w
    _ ≤ 2 * 2 ^ (p + 1 - (m + 1)) := by
        rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hfib

omit [Fintype V] in
theorem vChain_level0_hub (i : Fin (2 ^ (p + 1))) :
    vChain (mapE Sum.inl Xo : Finset (Sym2 (HU V p))) (Sum.inr i) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro π hπ
  obtain ⟨hπ, hx⟩ := mem_vChain.mp hπ
  obtain ⟨u, hu⟩ := mem_mapE_inl_vertex Xo hπ hx
  exact Sum.inr_ne_inl hu

theorem hubWeight_level0_hub (hp : Fintype.card V < 2 ^ p) (D : ℕ)
    (hD : ∀ v, incidentLoad Xo v ≤ D) (i : Fin (2 ^ (p + 1))) :
    hubWeight (mapE Sum.inl Xo : Finset (Sym2 (HU V p))) (heapH p 0) (Sum.inr i) ≤ D := by
  unfold hubWeight
  set S := univ.filter fun w : HU V p => heapH p 0 w = Sum.inr i
  rw [← sum_filter_of_ne (p := fun w : HU V p => w.isLeft) ?_]
  · have hcard : (S.filter fun w : HU V p => w.isLeft).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      obtain ⟨ha, hal⟩ := mem_filter.mp ha
      obtain ⟨hb, hbl⟩ := mem_filter.mp hb
      have ha := (mem_filter.mp ha).2
      have hb := (mem_filter.mp hb).2
      rcases a with u | j <;> rcases b with u' | j' <;> simp at hal hbl
      have hu := idx_lt u
      have hu' := idx_lt u'
      have h1 : 2 ^ p + idx u < 2 ^ (p + 1) := by rw [pow_succ]; omega
      have h2 : 2 ^ p + idx u' < 2 ^ (p + 1) := by rw [pow_succ]; omega
      simp only [heapH, hubOf_eq h1, hubOf_eq h2, Sum.inr.injEq] at ha hb
      rw [← hb] at ha
      have := congrArg Fin.val ha
      simp only at this
      rw [idx_inj (show idx u = idx u' by omega)]
    calc ∑ w ∈ S.filter (fun w : HU V p => w.isLeft), (vChain (mapE Sum.inl Xo) w).card
        ≤ ∑ _w ∈ S.filter (fun w : HU V p => w.isLeft), D := by
          refine sum_le_sum fun w _ => ?_
          rcases w with u | j
          · change incidentLoad (mapE Sum.inl Xo) (Sum.inl u) ≤ D
            rw [incidentLoad_mapE_apply Sum.inl_injective]
            exact hD u
          · rw [vChain_level0_hub]; simp
      _ ≤ D := by
          rw [sum_const, smul_eq_mul]
          calc _ ≤ 1 * D := Nat.mul_le_mul_right _ hcard
            _ = D := one_mul D
  · intro w _ hw
    rcases w with u | j
    · rfl
    · exact absurd (by rw [vChain_level0_hub]; rfl) hw

theorem sum_two_pow_sub_le : ∀ p : ℕ, ∑ l ∈ range p, 2 ^ (p - l) ≤ 2 ^ (p + 1)
  | 0 => by simp
  | p + 1 => by
    rw [sum_range_succ']
    have ih := sum_two_pow_sub_le p
    have h : ∑ l ∈ range p, 2 ^ (p + 1 - (l + 1)) = ∑ l ∈ range p, 2 ^ (p - l) :=
      sum_congr rfl fun l _ => by rw [show p + 1 - (l + 1) = p - l by omega]
    rw [h, show p + 1 - 0 = p + 1 by omega, pow_succ 2 (p + 1)]
    omega

/-- **Root load of the heap hierarchy at a hub.** -/
theorem heap_root_hub (hp : Fintype.card V < 2 ^ p) (D : ℕ) (hD : ∀ v, incidentLoad Xo v ≤ D)
    (i : Fin (2 ^ (p + 1))) :
    ∑ l ∈ range (p + 1), (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l)
        (Sum.inr i)).card + 10 * hubWeight (links (mapE Sum.inl Xo) (heapH p) l) (heapH p l)
        (Sum.inr i)) ≤ 10 * D + 22 * 2 ^ (p + 1) := by
  rw [sum_range_succ']
  have h0 := hubWeight_level0_hub Xo hp D hD i
  have hv0 : (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) 0) (Sum.inr i)).card = 0 := by
    change (vChain (mapE Sum.inl Xo) (Sum.inr i)).card = 0
    rw [vChain_level0_hub]; rfl
  have hrest : ∑ l ∈ range p, (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) (l + 1))
      (Sum.inr i)).card + 10 * hubWeight (links (mapE Sum.inl Xo) (heapH p) (l + 1))
      (heapH p (l + 1)) (Sum.inr i)) ≤ ∑ l ∈ range p, 22 * 2 ^ (p - l) := by
    refine sum_le_sum fun l hl => ?_
    have hl' := mem_range.mp hl
    have h1 := card_vChain_hub_le Xo hp (l := l + 1) (by omega) (by omega) (Sum.inr i)
    have h2 := hubWeight_hub_le Xo hp (l := l + 1) (by omega) (by omega) i
    rw [show p + 1 - (l + 1) = p - l by omega] at h1 h2
    omega
  have hgeo : ∑ l ∈ range p, 22 * 2 ^ (p - l) ≤ 22 * 2 ^ (p + 1) := by
    rw [← mul_sum]; exact Nat.mul_le_mul_left 22 (sum_two_pow_sub_le p)
  change _ + (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) 0) (Sum.inr i)).card +
    10 * hubWeight (mapE Sum.inl Xo) (heapH p 0) (Sum.inr i)) ≤ _
  omega

end PartitionedTriangleAbsorption.TypedRefinerF0
