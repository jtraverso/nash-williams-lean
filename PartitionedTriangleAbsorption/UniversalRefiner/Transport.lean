/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Basic

/-!
# Abstract parity transport and its telescoping composition

Everything here is about finite sets of abstract atoms `α`, a library of pieces
`A : κ → Finset α`, and a boundary map `rb : α → M` into an additive group (later
`V → ZMod 2`).  A *link family* is a finite set `Λ` of link indices with link atoms `la`.

* `Refiner A rb Λ la lib R`: every zero-boundary selection `S ⊆ Λ` is covered, together with
  the remainder `R`, by pairwise disjoint zero-boundary library pieces.
* `Transport A rb Λ la Λ' la' lib R`: every zero-boundary selection `S ⊆ Λ` is covered,
  together with `R`, by disjoint zero-boundary library pieces and a zero-boundary selection
  `S' ⊆ Λ'` of next-level links, which are *not* consumed at this level.

`refiner_of_transport` is the telescoping step; `refiner_of_levels` iterates it over finitely
many levels, with an empty last link family.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset

variable {α κ β : Type*} [DecidableEq α] {M : Type*} [AddCommMonoid M]

/-- A library refining every zero-boundary selection of links, with remainder `R`. -/
def Refiner (A : κ → Finset α) (rb : α → M) (Λ : Finset β) (la : β → α)
    (lib : Finset κ) (R : Finset α) : Prop :=
  ∀ S ⊆ Λ, ∑ π ∈ S, rb (la π) = 0 → ∃ T ⊆ lib, (T : Set κ).PairwiseDisjoint A ∧
    (∀ i ∈ T, ∑ a ∈ A i, rb a = 0) ∧ T.biUnion A = R ∪ S.image la

/-- One level of transport: selected links are refined except for a zero-boundary selection
of next-level links, which is left over (and is disjoint from the pieces used). -/
def Transport (A : κ → Finset α) (rb : α → M) (Λ : Finset β) (la : β → α)
    (Λ' : Finset β) (la' : β → α) (lib : Finset κ) (R : Finset α) : Prop :=
  ∀ S ⊆ Λ, ∑ π ∈ S, rb (la π) = 0 → ∃ S' ⊆ Λ', ∑ σ ∈ S', rb (la' σ) = 0 ∧
    ∃ T ⊆ lib, (T : Set κ).PairwiseDisjoint A ∧ (∀ i ∈ T, ∑ a ∈ A i, rb a = 0) ∧
      Disjoint (T.biUnion A) (S'.image la') ∧ T.biUnion A ∪ S'.image la' = R ∪ S.image la

/-- The empty link family is refined by the empty library with empty remainder. -/
theorem refiner_empty (A : κ → Finset α) (rb : α → M) (la : β → α) :
    Refiner A rb (∅ : Finset β) la ∅ ∅ := by
  intro S hS _
  have : S = ∅ := subset_empty.mp hS
  subst this
  exact ⟨∅, subset_refl _, by simp, by simp, by simp⟩

/-- **Telescoping step.** A transport level followed by a refiner of the next-level links is a
refiner, provided the later remainder avoids this level's remainder and links. -/
theorem refiner_of_transport [DecidableEq κ] {A : κ → Finset α} {rb : α → M}
    {Λ Λ' : Finset β} {la la' : β → α} {lib₀ lib₁ : Finset κ} {R₀ R₁ : Finset α}
    (h₀ : Transport A rb Λ la Λ' la' lib₀ R₀) (h₁ : Refiner A rb Λ' la' lib₁ R₁)
    (hdisj : Disjoint R₁ (R₀ ∪ Λ.image la)) :
    Refiner A rb Λ la (lib₀ ∪ lib₁) (R₀ ∪ R₁) := by
  intro S hS hS0
  obtain ⟨S', hS', hS'0, T₀, hT₀, hdis₀, hev₀, hsep, hU₀⟩ := h₀ S hS hS0
  obtain ⟨T₁, hT₁, hdis₁, hev₁, hU₁⟩ := h₁ S' hS' hS'0
  have hsub₀ : ∀ i ∈ T₀, A i ⊆ R₀ ∪ S.image la := fun i hi =>
    (subset_biUnion_of_mem A hi).trans (hU₀ ▸ subset_union_left)
  have hsub₁ : ∀ i ∈ T₁, A i ⊆ R₁ ∪ S'.image la' := fun i hi =>
    hU₁ ▸ subset_biUnion_of_mem A hi
  have hSla : S.image la ⊆ Λ.image la := image_subset_image hS
  have hcross : ∀ i ∈ T₀, ∀ j ∈ T₁, Disjoint (A i) (A j) := by
    intro i hi j hj
    refine disjoint_of_subset_right (hsub₁ j hj) (disjoint_union_right.mpr ⟨?_, ?_⟩)
    · exact disjoint_of_subset_left (hsub₀ i hi)
        (disjoint_of_subset_left (union_subset_union subset_rfl hSla) hdisj.symm)
    · exact disjoint_of_subset_left (subset_biUnion_of_mem A hi) hsep
  refine ⟨T₀ ∪ T₁, union_subset_union hT₀ hT₁, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    rcases mem_union.mp (mem_coe.mp hi) with hi | hi <;>
      rcases mem_union.mp (mem_coe.mp hj) with hj | hj
    · exact hdis₀ hi hj hij
    · exact hcross i hi j hj
    · exact (hcross j hj i hi).symm
    · exact hdis₁ hi hj hij
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact hev₀ i hi
    · exact hev₁ i hi
  · rw [union_biUnion, hU₁]
    ext a
    have := congrArg (a ∈ ·) hU₀
    simp only [mem_union, eq_iff_iff] at this ⊢
    tauto

/-- **Telescoping over finitely many levels.** -/
theorem refiner_of_levels [DecidableEq κ] {A : κ → Finset α} {rb : α → M}
    (Λ : ℕ → Finset β) (la : ℕ → β → α) (lib : ℕ → Finset κ) (R : ℕ → Finset α) (L : ℕ)
    (htr : ∀ l < L, Transport A rb (Λ l) (la l) (Λ (l + 1)) (la (l + 1)) (lib l) (R l))
    (hlast : Λ L = ∅)
    (hdisj : ∀ l < L, ∀ m, l < m → m < L → Disjoint (R m) (R l ∪ (Λ l).image (la l))) :
    Refiner A rb (Λ 0) (la 0) ((range L).biUnion lib) ((range L).biUnion R) := by
  suffices key : ∀ k, k ≤ L → Refiner A rb (Λ (L - k)) (la (L - k))
      ((Ico (L - k) L).biUnion lib) ((Ico (L - k) L).biUnion R) by
    have := key L le_rfl
    rw [Nat.sub_self] at this
    rwa [range_eq_Ico]
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.sub_zero, Ico_self, biUnion_empty, hlast]
    exact refiner_empty A rb (la L)
  | succ k ih =>
    intro hk
    have hl : L - (k + 1) + 1 = L - k := by omega
    have hIco : Ico (L - (k + 1)) L = insert (L - (k + 1)) (Ico (L - k) L) := by
      rw [← hl, insert_Ico_add_one_left_eq_Ico (by omega)]
    rw [hIco, biUnion_insert, biUnion_insert]
    have h₁ := ih (by omega)
    have htr' := htr (L - (k + 1)) (by omega)
    rw [hl] at htr'
    refine refiner_of_transport htr' h₁ ?_
    rw [disjoint_biUnion_left]
    intro m hm
    rw [mem_Ico] at hm
    exact hdisj _ (by omega) m (by omega) hm.2

/-- Always-active pieces (here: the adjustment cycles) can be added to a refiner. -/
theorem refiner_add_always [DecidableEq κ] {A : κ → Finset α} {rb : α → M}
    {Λ : Finset β} {la : β → α} {lib : Finset κ} {R : Finset α} (C : Finset κ)
    (href : Refiner A rb Λ la lib R)
    (hCdisj : (C : Set κ).PairwiseDisjoint A)
    (hCsep : ∀ i ∈ C, Disjoint (A i) (R ∪ Λ.image la))
    (hCeven : ∀ i ∈ C, ∑ a ∈ A i, rb a = 0) :
    Refiner A rb Λ la (lib ∪ C) (R ∪ C.biUnion A) := by
  intro S hS hS0
  obtain ⟨T, hT, hdis, hev, hU⟩ := href S hS hS0
  have hSla : S.image la ⊆ Λ.image la := image_subset_image hS
  have hcross : ∀ i ∈ T, ∀ j ∈ C, Disjoint (A i) (A j) := by
    intro i hi j hj
    have hsub : A i ⊆ R ∪ Λ.image la :=
      (subset_biUnion_of_mem A hi).trans (hU ▸ union_subset_union subset_rfl hSla)
    exact disjoint_of_subset_left hsub (hCsep j hj).symm
  refine ⟨T ∪ C, union_subset_union hT subset_rfl, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    rcases mem_union.mp (mem_coe.mp hi) with hi | hi <;>
      rcases mem_union.mp (mem_coe.mp hj) with hj | hj
    · exact hdis hi hj hij
    · exact hcross i hi j hj
    · exact (hcross j hj i hi).symm
    · exact hCdisj hi hj hij
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact hev i hi
    · exact hCeven i hi
  · rw [union_biUnion, hU]
    ext a; simp only [mem_union]; tauto

end PartitionedTriangleAbsorption.UniversalRefiner
