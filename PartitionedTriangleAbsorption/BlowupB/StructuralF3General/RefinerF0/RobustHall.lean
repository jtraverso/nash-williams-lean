/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Robust matchability from two expansion properties

A bipartite graph `H` between a plus side `[0,3k)` and a minus side
`[0,2k) ⊔ [0,2k)` (the fixed part `Y` and the flexible part `Z`) is *robustly matchable* if,
for every `Z' ⊆ Z` of size `k`, the plus side has a perfect matching onto `Y ⊔ Z'`.

`matching_of_good` derives this from
* `Good1`: every plus set `A` with `1 ≤ |A| ≤ k` has more than `|A|` neighbours in `Y`;
* `Good2`: every minus set `B` with `1 ≤ |B| ≤ 2k` has more than `|B|` neighbours,
by Hall's theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.RefinerF0

open Finset

/-- Minus-side neighbours of a set of plus vertices. -/
def nbr (H : Finset (ℕ × (ℕ ⊕ ℕ))) (A : Finset ℕ) : Finset (ℕ ⊕ ℕ) :=
  (H.filter fun h => h.1 ∈ A).image Prod.snd

/-- Plus-side neighbours of a set of minus vertices. -/
def nbrX (H : Finset (ℕ × (ℕ ⊕ ℕ))) (B : Finset (ℕ ⊕ ℕ)) : Finset ℕ :=
  (H.filter fun h => h.2 ∈ B).image Prod.fst

/-- The minus side `Y ⊔ Z`. -/
def minusSide (k : ℕ) : Finset (ℕ ⊕ ℕ) := (range (2 * k)).disjSum (range (2 * k))

/-- Small plus sets expand into the fixed side. -/
def Good1 (k : ℕ) (H : Finset (ℕ × (ℕ ⊕ ℕ))) : Prop :=
  ∀ A ⊆ range (3 * k), 1 ≤ A.card → A.card ≤ k → A.card < (nbr H A).toLeft.card

/-- Small minus sets expand. -/
def Good2 (k : ℕ) (H : Finset (ℕ × (ℕ ⊕ ℕ))) : Prop :=
  ∀ B ⊆ minusSide k, 1 ≤ B.card → B.card ≤ 2 * k → B.card < (nbrX H B).card

theorem mem_nbr {H : Finset (ℕ × (ℕ ⊕ ℕ))} {A : Finset ℕ} {y : ℕ ⊕ ℕ} :
    y ∈ nbr H A ↔ ∃ x ∈ A, (x, y) ∈ H := by
  simp only [nbr, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨x, y'⟩, ⟨hh, hx⟩, rfl⟩; exact ⟨x, hx, hh⟩
  · rintro ⟨x, hx, hh⟩; exact ⟨(x, y), ⟨hh, hx⟩, rfl⟩

theorem mem_nbrX {H : Finset (ℕ × (ℕ ⊕ ℕ))} {B : Finset (ℕ ⊕ ℕ)} {x : ℕ} :
    x ∈ nbrX H B ↔ ∃ y ∈ B, (x, y) ∈ H := by
  simp only [nbrX, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨x', y⟩, ⟨hh, hy⟩, rfl⟩; exact ⟨y, hy, hh⟩
  · rintro ⟨y, hy, hh⟩; exact ⟨(x, y), ⟨hh, hy⟩, rfl⟩

theorem card_present (k : ℕ) {Z : Finset ℕ} (hZ : Z.card = k) :
    ((range (2 * k)).disjSum Z).card = 3 * k := by
  rw [card_disjSum, card_range, hZ]; ring

/-- **Hall's condition from expansion.** -/
theorem hall_of_good {k : ℕ} {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hfst : ∀ h ∈ H, h.1 < 3 * k) (hsnd : ∀ h ∈ H, h.2 ∈ minusSide k)
    (g1 : Good1 k H) (g2 : Good2 k H) {Z : Finset ℕ} (hZs : Z ⊆ range (2 * k))
    (hZ : Z.card = k) {A : Finset ℕ} (hA : A ⊆ range (3 * k)) :
    A.card ≤ (nbr H A ∩ (range (2 * k)).disjSum Z).card := by
  set P := (range (2 * k)).disjSum Z with hP
  have hPM : P ⊆ minusSide k := by
    intro y hy
    rw [hP, mem_disjSum] at hy
    rw [minusSide, mem_disjSum]
    rcases hy with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨b, hZs hb, rfl⟩
  have hPc : P.card = 3 * k := card_present k hZ
  have hAc : A.card ≤ 3 * k := by simpa using card_le_card hA
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · omega
  rcases Nat.lt_or_ge k A.card with hbig | hsmall
  · by_contra hlt
    push Not at hlt
    set B := P \ nbr H A with hB
    have hBc : B.card + (P ∩ nbr H A).card = 3 * k := by
      rw [hB, card_sdiff_add_card_inter, hPc]
    have hcomm : (P ∩ nbr H A).card = (nbr H A ∩ P).card := by rw [inter_comm]
    have hBX : nbrX H B ⊆ range (3 * k) \ A := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_nbrX.mp hx
      refine mem_sdiff.mpr ⟨mem_range.mpr (hfst _ hxy), fun hxA => ?_⟩
      exact (mem_sdiff.mp hy).2 (mem_nbr.mpr ⟨x, hxA, hxy⟩)
    have hXc : (nbrX H B).card ≤ 3 * k - A.card := by
      have := card_le_card hBX
      rwa [card_sdiff_of_subset hA, card_range] at this
    have hBM : B ⊆ minusSide k := fun y hy => hPM (mem_sdiff.mp hy).1
    rcases Nat.lt_or_ge (2 * k) B.card with hB2 | hB2
    · obtain ⟨B', hB'B, hB'c⟩ := exists_subset_card_eq hB2.le
      have hmono : nbrX H B' ⊆ nbrX H B := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := mem_nbrX.mp hx
        exact mem_nbrX.mpr ⟨y, hB'B hy, hxy⟩
      have := g2 B' (hB'B.trans hBM) (by omega) (by omega)
      have := card_le_card hmono
      omega
    · have := g2 B hBM (by omega) hB2
      omega
  · have h1 := g1 A hA hpos hsmall
    refine h1.le.trans ?_
    refine card_le_card_of_injOn Sum.inl ?_ (fun _ _ _ _ h => Sum.inl_injective h)
    intro y hy
    rw [mem_coe, mem_toLeft] at hy
    refine mem_inter.mpr ⟨hy, ?_⟩
    obtain ⟨x, -, hxy⟩ := mem_nbr.mp hy
    have := hsnd _ hxy
    simp only [minusSide, mem_disjSum, Sum.inl.injEq, reduceCtorEq, and_false,
      exists_false, or_false] at this
    obtain ⟨a, ha, rfl⟩ := this
    rw [hP, mem_disjSum]
    exact Or.inl ⟨a, ha, rfl⟩

/-- **Robust matchability.** -/
theorem matching_of_good {k : ℕ} {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hfst : ∀ h ∈ H, h.1 < 3 * k) (hsnd : ∀ h ∈ H, h.2 ∈ minusSide k)
    (g1 : Good1 k H) (g2 : Good2 k H) {Z : Finset ℕ} (hZs : Z ⊆ range (2 * k))
    (hZ : Z.card = k) :
    ∃ f : ℕ → ℕ ⊕ ℕ, Set.InjOn f (range (3 * k)) ∧ (∀ x < 3 * k, (x, f x) ∈ H) ∧
      (range (3 * k)).image f = (range (2 * k)).disjSum Z := by
  set P := (range (2 * k)).disjSum Z with hP
  let t : Fin (3 * k) → Finset (ℕ ⊕ ℕ) := fun x => nbr H {x.val} ∩ P
  have hhall : ∀ s : Finset (Fin (3 * k)), s.card ≤ (s.biUnion t).card := by
    intro s
    have hA : s.map Fin.valEmbedding ⊆ range (3 * k) := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := mem_map.mp hx
      exact mem_range.mpr y.isLt
    have heq : s.biUnion t = nbr H (s.map Fin.valEmbedding) ∩ P := by
      ext y
      simp only [t, mem_biUnion, mem_inter, mem_nbr, mem_map, mem_singleton,
        Fin.valEmbedding_apply]
      constructor
      · rintro ⟨x, hx, ⟨x', rfl, hxy⟩, hyP⟩
        exact ⟨⟨x, ⟨x, hx, rfl⟩, hxy⟩, hyP⟩
      · rintro ⟨⟨_, ⟨x, hx, rfl⟩, hxy⟩, hyP⟩
        exact ⟨x, hx, ⟨x, rfl, hxy⟩, hyP⟩
    rw [heq]
    have := hall_of_good hfst hsnd g1 g2 hZs hZ hA
    rwa [card_map] at this
  obtain ⟨f0, hinj, hf0⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  let f : ℕ → ℕ ⊕ ℕ := fun x => if h : x < 3 * k then f0 ⟨x, h⟩ else Sum.inl 0
  have hfval : ∀ x (h : x < 3 * k), f x = f0 ⟨x, h⟩ := fun x h => by simp [f, h]
  have hinjOn : Set.InjOn f (range (3 * k)) := by
    intro x hx y hy hxy
    have hx' := mem_range.mp hx
    have hy' := mem_range.mp hy
    rw [hfval x hx', hfval y hy'] at hxy
    have := hinj hxy
    simpa using this
  refine ⟨f, hinjOn, ?_, ?_⟩
  · intro x hx
    rw [hfval x hx]
    have := (mem_inter.mp (hf0 ⟨x, hx⟩)).1
    obtain ⟨x', hx', hxy⟩ := mem_nbr.mp this
    rw [mem_singleton] at hx'
    rw [hx'] at hxy
    exact hxy
  · have hsub : (range (3 * k)).image f ⊆ P := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      rw [hfval x (mem_range.mp hx)]
      exact (mem_inter.mp (hf0 _)).2
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_image_of_injOn hinjOn, card_range, card_present k hZ]

end PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
