/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.RobustRandom

/-! # Robust matching with an arbitrary number of flexible slots

`exists_robust z s` (for `s ≤ z`): there are `m ≤ 3z` fixed minus vertices and a bipartite
graph `H` from the plus side `[0, m+s)` to `[0,m) ⊔ [0,z)`, with plus degrees at most `24` and
minus degrees at most `18`, such that for **every** `Z ⊆ [0,z)` with `|Z| = s` the plus side
has a perfect matching onto `[0,m) ⊔ Z`.

It is obtained from the balanced graph of `RobustRandom` with `k = max (z-s) s`: surplus
flexible slots are turned into fixed minus vertices (padding), missing ones are never present
(ghosts) and their edges are discarded.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset

/-- Relabelling of the balanced minus side. -/
def slotMap (z k : ℕ) : ℕ ⊕ ℕ → ℕ ⊕ ℕ
  | Sum.inl y => Sum.inl y
  | Sum.inr j => if j < z then Sum.inr j else Sum.inl (2 * k + (j - z))

/-- Slots that are kept (not ghosts). -/
def keep (z pad : ℕ) : ℕ ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < z + pad

instance (z pad : ℕ) : DecidablePred (keep z pad) := fun y => by
  cases y <;> unfold keep <;> infer_instance

theorem slotMap_injOn {z k pad : ℕ} {a b : ℕ ⊕ ℕ}
    (ha : a ∈ minusSide k) (hb : b ∈ minusSide k) (hka : keep z pad a) (hkb : keep z pad b)
    (h : slotMap z k a = slotMap z k b) : a = b := by
  simp only [minusSide, mem_disjSum, mem_range] at ha hb
  rcases a with a | a <;> rcases b with b | b <;> simp only [keep] at hka hkb <;>
    simp only [slotMap] at h
  · simpa using h
  · rcases ha with ⟨a', ha', h'⟩ | ⟨a', -, h'⟩ <;>
      simp only [Sum.inl.injEq, reduceCtorEq] at h'
    subst h'
    split_ifs at h
    simp at h
    omega
  · rcases hb with ⟨b', hb', h'⟩ | ⟨b', -, h'⟩ <;>
      simp only [Sum.inl.injEq, reduceCtorEq] at h'
    subst h'
    split_ifs at h
    simp at h
    omega
  · split_ifs at h with ha' hb' hb' <;> simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    · rw [h]
    · congr 1; omega

/-- **Robust matching with `z` flexible slots of which exactly `s` are present.** -/
theorem exists_robust (z s : ℕ) (hs : s ≤ z) : ∃ m : ℕ, ∃ H : Finset (ℕ × (ℕ ⊕ ℕ)),
    m ≤ 3 * z ∧ (∀ h ∈ H, h.1 < m + s) ∧ (∀ h ∈ H, h.2 ∈ (range m).disjSum (range z)) ∧
    (∀ x, (H.filter fun h => h.1 = x).card ≤ 24) ∧
    (∀ y, (H.filter fun h => h.2 = y).card ≤ 18) ∧
    ∀ Z ⊆ range z, Z.card = s →
      ∃ f : ℕ → ℕ ⊕ ℕ, Set.InjOn f (range (m + s)) ∧ (∀ x < m + s, (x, f x) ∈ H) ∧
        (range (m + s)).image f = (range m).disjSum Z := by
  set k := max (z - s) s with hk
  set pad := z - 2 * s with hpad
  have hcase : (2 * s ≤ z ∧ k = z - s) ∨ (z < 2 * s ∧ k = s) := by
    rcases Nat.lt_or_ge z (2 * s) with h | h
    · right; exact ⟨h, by rw [hk]; omega⟩
    · left; exact ⟨h, by rw [hk]; omega⟩
  have hzk : z + pad ≤ 2 * k := by omega
  have h3k : 2 * k + pad + s = 3 * k := by omega
  obtain ⟨H0, h0fst, h0snd, h0dx, h0dy, h0match⟩ := exists_rmbg k
  set m := 2 * k + pad
  let φ : ℕ × (ℕ ⊕ ℕ) → ℕ × (ℕ ⊕ ℕ) := fun h => (h.1, slotMap z k h.2)
  set H := (H0.filter fun h => keep z pad h.2).image φ with hH
  have hmemH : ∀ h ∈ H, ∃ h0 ∈ H0, keep z pad h0.2 ∧ h = φ h0 := by
    intro h hh
    obtain ⟨h0, hh0, rfl⟩ := mem_image.mp hh
    exact ⟨h0, (mem_filter.mp hh0).1, (mem_filter.mp hh0).2, rfl⟩
  refine ⟨m, H, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨h0, hh0, -, rfl⟩ := hmemH h hh
    have := h0fst h0 hh0
    simp only [φ]; omega
  · intro h hh
    obtain ⟨h0, hh0, hkeep, rfl⟩ := hmemH h hh
    have h2 := h0snd h0 hh0
    simp only [minusSide, mem_disjSum, mem_range] at h2
    simp only [φ, mem_disjSum, mem_range]
    rcases h0 with ⟨x, y | j⟩
    · rcases h2 with ⟨a, ha, h'⟩ | ⟨a, -, h'⟩ <;>
        simp only [Sum.inl.injEq, reduceCtorEq] at h'
      subst h'
      exact Or.inl ⟨a, by omega, rfl⟩
    · simp only [keep] at hkeep
      simp only [slotMap]
      split_ifs with hj
      · exact Or.inr ⟨j, hj, rfl⟩
      · exact Or.inl ⟨_, by omega, rfl⟩
  · intro x
    have hsub : (H.filter fun h => h.1 = x) ⊆ (H0.filter fun h => h.1 = x).image φ := by
      intro h hh
      obtain ⟨hh, hx⟩ := mem_filter.mp hh
      obtain ⟨h0, hh0, -, rfl⟩ := hmemH h hh
      exact mem_image.mpr ⟨h0, mem_filter.mpr ⟨hh0, hx⟩, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (h0dx x))
  · intro y
    by_cases hne : (H.filter fun h => h.2 = y).Nonempty
    · obtain ⟨h1, hh1⟩ := hne
      obtain ⟨hh1, hy1⟩ := mem_filter.mp hh1
      obtain ⟨g1, hg1, hk1, rfl⟩ := hmemH h1 hh1
      have hsub : (H.filter fun h => h.2 = y) ⊆ (H0.filter fun h => h.2 = g1.2).image φ := by
        intro h hh
        obtain ⟨hh, hy⟩ := mem_filter.mp hh
        obtain ⟨h0, hh0, hk0, rfl⟩ := hmemH h hh
        refine mem_image.mpr ⟨h0, mem_filter.mpr ⟨hh0, ?_⟩, rfl⟩
        refine slotMap_injOn (h0snd h0 hh0) (h0snd g1 hg1) hk0 hk1 ?_
        simp only [φ] at hy hy1
        rw [hy, hy1]
      exact (card_le_card hsub).trans (card_image_le.trans (h0dy _))
    · rw [not_nonempty_iff_eq_empty.mp hne]; simp
  · intro Z hZ hZc
    set Zs := Z ∪ Ico z (z + pad) with hZs
    have hZsub : Zs ⊆ range (2 * k) := by
      intro j hj
      rcases mem_union.mp hj with hj | hj
      · have := mem_range.mp (hZ hj); exact mem_range.mpr (by omega)
      · have := mem_Ico.mp hj; exact mem_range.mpr (by omega)
    have hdisj : Disjoint Z (Ico z (z + pad)) := by
      rw [disjoint_left]
      intro j hj hj'
      have := mem_range.mp (hZ hj); have := mem_Ico.mp hj'; omega
    have hZsc : Zs.card = k := by
      rw [hZs, card_union_of_disjoint hdisj, hZc, Nat.card_Ico]; omega
    obtain ⟨f0, hinj0, hedge0, himg0⟩ := h0match Zs hZsub hZsc
    have hf0mem : ∀ x < 3 * k, f0 x ∈ (range (2 * k)).disjSum Zs := by
      intro x hx
      rw [← himg0]
      exact mem_image_of_mem f0 (mem_range.mpr hx)
    have hpresent_minus : ∀ y ∈ (range (2 * k)).disjSum Zs, y ∈ minusSide k ∧ keep z pad y := by
      intro y hy
      rw [mem_disjSum] at hy
      rcases hy with ⟨a, ha, rfl⟩ | ⟨j, hj, rfl⟩
      · refine ⟨?_, trivial⟩
        rw [minusSide, mem_disjSum]; exact Or.inl ⟨a, ha, rfl⟩
      · refine ⟨?_, ?_⟩
        · rw [minusSide, mem_disjSum]; exact Or.inr ⟨j, hZsub hj, rfl⟩
        · simp only [keep]
          rcases mem_union.mp hj with hj | hj
          · have := mem_range.mp (hZ hj); omega
          · exact (mem_Ico.mp hj).2
    refine ⟨fun x => slotMap z k (f0 x), ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      have hx' : x < 3 * k := by have := mem_range.mp hx; omega
      have hy' : y < 3 * k := by have := mem_range.mp hy; omega
      obtain ⟨ma, ka⟩ := hpresent_minus _ (hf0mem x hx')
      obtain ⟨mb, kb⟩ := hpresent_minus _ (hf0mem y hy')
      exact hinj0 (mem_range.mpr hx') (mem_range.mpr hy') (slotMap_injOn ma mb ka kb hxy)
    · intro x hx
      have hx' : x < 3 * k := by omega
      refine mem_image.mpr ⟨(x, f0 x), mem_filter.mpr ⟨hedge0 x hx', ?_⟩, rfl⟩
      exact (hpresent_minus _ (hf0mem x hx')).2
    · have hm3 : m + s = 3 * k := h3k
      rw [hm3]
      have himg : (range (3 * k)).image (fun x => slotMap z k (f0 x)) =
          ((range (2 * k)).disjSum Zs).image (slotMap z k) := by
        rw [← himg0, image_image]; rfl
      rw [himg]
      ext y
      simp only [mem_image, mem_disjSum, mem_range]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases hw with ⟨a, ha, rfl⟩ | ⟨j, hj, rfl⟩
        · exact Or.inl ⟨a, by omega, rfl⟩
        · simp only [slotMap]
          split_ifs with hjz
          · rcases mem_union.mp hj with hj | hj
            · exact Or.inr ⟨j, hj, rfl⟩
            · have := mem_Ico.mp hj; omega
          · rcases mem_union.mp hj with hj | hj
            · have := mem_range.mp (hZ hj); omega
            · have := mem_Ico.mp hj; exact Or.inl ⟨_, by omega, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, rfl⟩)
        · rcases Nat.lt_or_ge a (2 * k) with h1 | h1
          · exact ⟨Sum.inl a, Or.inl ⟨a, h1, rfl⟩, rfl⟩
          · refine ⟨Sum.inr (z + (a - 2 * k)), Or.inr ⟨_, mem_union_right _
              (mem_Ico.mpr ⟨by omega, by omega⟩), rfl⟩, ?_⟩
            simp only [slotMap]
            rw [ite_eq_right (by omega)]
            congr 1; omega
        · refine ⟨Sum.inr j, Or.inr ⟨j, mem_union_left _ hj, rfl⟩, ?_⟩
          simp only [slotMap]
          rw [ite_eq_left (mem_range.mp (hZ hj))]

end PartitionedTriangleAbsorption.TypedRefinerF0
