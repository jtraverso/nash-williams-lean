/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHubHeap

/-! # Root load of the compressed hierarchy at an auxiliary hub

At a hub, the whole-hierarchy root load is at most
`10 (|V| / 2^p + 1) Δ + 44 · 2^p`. The first hub count is a free parameter.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub

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

theorem vChain_hub_subset {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p + 1)
    (x : HU V p) : vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l) x ⊆
      (levelHubs p l).image fun i => s(x, Sum.inr i) := by
  intro π hπ
  obtain ⟨hπ, hx⟩ := mem_vChain.mp hπ
  have hin : ∀ w ∈ π, ∃ i ∈ levelHubs p l, w = Sum.inr i := by
    intro w hw
    obtain ⟨i, rfl, h1, h2⟩ := links_hlevel Xo l hl1 hlp π hπ w hw
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, h1, h2⟩, rfl⟩
  rcases mem_iff_endA_endB.mp hx with h | h
  · obtain ⟨i, hi, he⟩ := hin _ (endB_mem π)
    refine mem_image.mpr ⟨i, hi, ?_⟩
    rw [← he, h, mk_endA_endB π]
  · obtain ⟨i, hi, he⟩ := hin _ (endA_mem π)
    refine mem_image.mpr ⟨i, hi, ?_⟩
    rw [← he, h, Sym2.eq_swap, mk_endA_endB π]

theorem card_vChain_hub_le {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p + 1)
    (x : HU V p) :
    (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l) x).card ≤ 2 ^ (p + 1 - l) :=
  (card_le_card (vChain_hub_subset Xo hl1 hlp x)).trans
    (card_image_le.trans (card_levelHubs_le hlp))

theorem hubWeight_hub_le {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p)
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
        sum_le_sum fun w _ => card_vChain_hub_le Xo (by omega) (by omega) w
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

theorem hubWeight_level0_hub (D : ℕ)
    (hD : ∀ v, incidentLoad Xo v ≤ D) (i : Fin (2 ^ (p + 1))) :
    hubWeight (mapE Sum.inl Xo : Finset (Sym2 (HU V p))) (heapH p 0) (Sum.inr i) ≤
      (Fintype.card V / 2 ^ p + 1) * D := by
  unfold hubWeight
  set S := univ.filter fun w : HU V p => heapH p 0 w = Sum.inr i
  rw [← sum_filter_of_ne (p := fun w : HU V p => w.isLeft) ?_]
  · have hcard : (S.filter fun w : HU V p => w.isLeft).card ≤
        Fintype.card V / 2 ^ p + 1 := by
      refine (card_le_card_of_injOn
        (fun w : HU V p => match w with | Sum.inl u => idx u / 2 ^ p | Sum.inr _ => 0)
        (t := range (Fintype.card V / 2 ^ p + 1)) ?_ ?_).trans (by simp)
      · intro w hw
        obtain ⟨_, hwleft⟩ := mem_filter.mp hw
        rcases w with u | j
        · simp only [coe_range, Set.mem_Iio]
          have hdiv := Nat.div_le_div_right (c := 2 ^ p) (Nat.le_of_lt (idx_lt u))
          omega
        · simp at hwleft
      · intro w hw w' hw' h
        obtain ⟨hw, hwleft⟩ := mem_filter.mp hw
        obtain ⟨hw', hwleft'⟩ := mem_filter.mp hw'
        have hw := (mem_filter.mp hw).2
        have hw' := (mem_filter.mp hw').2
        rcases w with u | j <;> rcases w' with u' | j'
        · have hu := Nat.mod_lt (idx u) (Nat.two_pow_pos p)
          have hu' := Nat.mod_lt (idx u') (Nat.two_pow_pos p)
          have h1 : 2 ^ p + idx u % 2 ^ p < 2 ^ (p + 1) := by rw [pow_succ]; omega
          have h2 : 2 ^ p + idx u' % 2 ^ p < 2 ^ (p + 1) := by rw [pow_succ]; omega
          simp only [heapH, hubOf_eq h1, hubOf_eq h2, Sum.inr.injEq] at hw hw'
          have hmod : idx u % 2 ^ p = idx u' % 2 ^ p := by
            have heq := congrArg Fin.val (hw.trans hw'.symm)
            change 2 ^ p + idx u % 2 ^ p = 2 ^ p + idx u' % 2 ^ p at heq
            omega
          have e1 := Nat.div_add_mod (idx u) (2 ^ p)
          have e2 := Nat.div_add_mod (idx u') (2 ^ p)
          change idx u / 2 ^ p = idx u' / 2 ^ p at h
          rw [h, hmod] at e1
          have heq : idx u = idx u' := by omega
          exact congrArg Sum.inl (idx_inj heq)
        · simp at hwleft'
        · simp at hwleft
        · simp at hwleft
    calc ∑ w ∈ S.filter (fun w : HU V p => w.isLeft), (vChain (mapE Sum.inl Xo) w).card
        ≤ ∑ _w ∈ S.filter (fun w : HU V p => w.isLeft), D := by
          refine sum_le_sum fun w _ => ?_
          rcases w with u | j
          · change incidentLoad (mapE Sum.inl Xo) (Sum.inl u) ≤ D
            rw [incidentLoad_mapE_apply Sum.inl_injective]
            exact hD u
          · rw [vChain_level0_hub]; simp
      _ ≤ (Fintype.card V / 2 ^ p + 1) * D := by
          rw [sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hcard
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
theorem heap_root_hub (D : ℕ) (hD : ∀ v, incidentLoad Xo v ≤ D)
    (i : Fin (2 ^ (p + 1))) :
    ∑ l ∈ range (p + 1), (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l)
        (Sum.inr i)).card + 10 * hubWeight (links (mapE Sum.inl Xo) (heapH p) l) (heapH p l)
        (Sum.inr i)) ≤ 10 * ((Fintype.card V / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) := by
  rw [sum_range_succ']
  have h0 := hubWeight_level0_hub Xo D hD i
  have hv0 : (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) 0) (Sum.inr i)).card = 0 := by
    change (vChain (mapE Sum.inl Xo) (Sum.inr i)).card = 0
    rw [vChain_level0_hub]; rfl
  have hrest : ∑ l ∈ range p, (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) (l + 1))
      (Sum.inr i)).card + 10 * hubWeight (links (mapE Sum.inl Xo) (heapH p) (l + 1))
      (heapH p (l + 1)) (Sum.inr i)) ≤ ∑ l ∈ range p, 22 * 2 ^ (p - l) := by
    refine sum_le_sum fun l hl => ?_
    have hl' := mem_range.mp hl
    have h1 := card_vChain_hub_le Xo (l := l + 1) (by omega) (by omega) (Sum.inr i)
    have h2 := hubWeight_hub_le Xo (l := l + 1) (by omega) (by omega) i
    rw [show p + 1 - (l + 1) = p - l by omega] at h1 h2
    omega
  have hgeo : ∑ l ∈ range p, 22 * 2 ^ (p - l) ≤ 22 * 2 ^ (p + 1) := by
    rw [← mul_sum]; exact Nat.mul_le_mul_left 22 (sum_two_pow_sub_le p)
  change _ + (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) 0) (Sum.inr i)).card +
    10 * hubWeight (mapE Sum.inl Xo) (heapH p 0) (Sum.inr i)) ≤ _
  omega

/-- Positive levels use only their shrinking hub layer. -/
theorem card_links_le_level {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p + 1) :
    (links (mapE Sum.inl Xo) (heapH (V := V) p) l).card ≤
      (levelHubs p l).card * 2 ^ p := by
  have hsub : links (mapE Sum.inl Xo) (heapH (V := V) p) l ⊆
      (levelHubs p l ×ˢ levelHubs p l).image
        (fun q => s(Sum.inr q.1, Sum.inr q.2) : Fin _ × Fin _ → Sym2 (HU V p)) := by
    intro π hπ
    have hin : ∀ w ∈ π, ∃ i ∈ levelHubs p l, w = Sum.inr i := by
      intro w hw
      obtain ⟨i, rfl, h1, h2⟩ := links_hlevel Xo l hl1 hlp π hπ w hw
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, h1, h2⟩, rfl⟩
    obtain ⟨i, hi, ei⟩ := hin _ (endA_mem π)
    obtain ⟨j, hj, ej⟩ := hin _ (endB_mem π)
    exact mem_image.mpr ⟨(i, j), mem_product.mpr ⟨hi, hj⟩,
      by rw [← ei, ← ej, mk_endA_endB π]⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_product]
  apply Nat.mul_le_mul_left
  exact (card_levelHubs_le hlp).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Total link mass has no logarithmic factor. -/
theorem heap_sum_links_compressed :
    ∑ l ∈ range (p + 1), (links (mapE Sum.inl Xo) (heapH (V := V) p) l).card ≤
      Xo.card + 2 * (2 ^ p) ^ 2 := by
  rw [sum_range_succ']
  have hrest : ∑ l ∈ range p,
      (links (mapE Sum.inl Xo) (heapH (V := V) p) (l + 1)).card ≤
      2 ^ (p + 1) * 2 ^ p := by
    calc _ ≤ ∑ l ∈ range p, (levelHubs p (l + 1)).card * 2 ^ p :=
        sum_le_sum fun l hl => card_links_le_level Xo (by omega) (by
          have := mem_range.mp hl; omega)
      _ = (∑ l ∈ range p, (levelHubs p (l + 1)).card) * 2 ^ p := by rw [sum_mul]
      _ ≤ 2 ^ (p + 1) * 2 ^ p := by
        apply Nat.mul_le_mul_right
        calc _ ≤ ∑ l ∈ range p, 2 ^ (p - l) := by
              refine sum_le_sum fun l hl => ?_
              have := mem_range.mp hl
              simpa only [show p + 1 - (l + 1) = p - l by omega] using
                (card_levelHubs_le (p := p) (l := l + 1) (by omega))
          _ ≤ _ := sum_two_pow_sub_le p
  have hzero : (links (mapE Sum.inl Xo) (heapH (V := V) p) 0).card = Xo.card :=
    card_mapE Sum.inl_injective Xo
  rw [hzero]
  have hp2 : 2 ^ (p + 1) * 2 ^ p = 2 * (2 ^ p) ^ 2 := by rw [pow_succ]; ring
  have hrest' := hrest.trans_eq hp2
  nlinarith

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub

