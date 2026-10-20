/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownPairingStage105

/-! # Stage105 pairing step: an unused, unblocked reserve triple exists

The count is exactly the budget `m + 4λ ≤ 2 a2`: at most `(m-2)/2` triples at `x`
are already used, and at most `λ` are blocked by NEW internal edges at each of
`y₁, y₂`; static blocking is already excluded from the richness count.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

theorem blocked_load_le {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m lam a2 : ℕ}
    (hD : PairingData p E U T2 B0 M0 m lam a2) {M : Finset (Sym2 V)} {A : Finset (V × V × V)}
    {I : Finset (Sym2 V)} (hI : PairingInv E U T2 B0 M0 M A I) {y : V} (hy : y ∈ U) :
    incidentLoad I y ≤ lam := by
  have h2 := hI.load y
  have h3 := incidentLoad_mono (spokesOf_subset_resEdges hI.resA) y
  have h4 := hD.loadB y hy
  omega

theorem exists_good_reserve {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m lam a2 : ℕ}
    (hD : PairingData p E U T2 B0 M0 m lam a2) {M : Finset (Sym2 V)} {A : Finset (V × V × V)}
    {I : Finset (Sym2 V)} (hI : PairingInv E U T2 B0 M0 M A I) {x y₁ y₂ : V} (hx : x ∉ U)
    (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ U) (hne : y₁ ≠ y₂) (he₁ : s(x, y₁) ∈ M) (he₂ : s(x, y₂) ∈ M) :
    ∃ r ∈ T2, r.1 = x ∧ s(y₁, r.2.1) ∈ E ∧ s(r.2.2, y₂) ∈ E ∧ r ∉ A ∧
      s(y₁, r.2.1) ∉ B0 ∪ I ∧ s(r.2.2, y₂) ∉ B0 ∪ I := by
  by_contra hno
  push Not at hno
  have hsub : (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ E ∧ s(r.2.2, y₂) ∈ E ∧
        s(y₁, r.2.1) ∉ B0 ∧ s(r.2.2, y₂) ∉ B0) ⊆
      ((A.filter fun r => r.1 = x) ∪
        (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ I)) ∪
        (T2.filter fun r => r.1 = x ∧ s(r.2.2, y₂) ∈ I) := by
    intro r hr
    obtain ⟨hrT, hrx, h1, h2, hB1, hB2⟩ := mem_filter.mp hr
    by_cases hA : r ∈ A
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hA, hrx⟩))
    by_cases hb : s(y₁, r.2.1) ∈ I
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hrT, hrx, hb⟩))
    have hb' : s(y₁, r.2.1) ∉ B0 ∪ I := by simp [hB1, hb]
    have := hno r hrT hrx h1 h2 hA hb'
    have hI2 : s(r.2.2, y₂) ∈ I := by
      rcases mem_union.mp this with h | h
      · exact absurd h hB2
      · exact h
    exact mem_union_right _ (mem_filter.mpr ⟨hrT, hrx, hI2⟩)
  have hc := card_le_card hsub
  have hu1 := card_union_le ((A.filter fun r => r.1 = x) ∪
        (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ I))
        (T2.filter fun r => r.1 = x ∧ s(r.2.2, y₂) ∈ I)
  have hu2 := card_union_le (A.filter fun r => r.1 = x)
        (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ I)
  have hb1 := card_bad₁_le hD.res_disj I x y₁
  have hb2 := card_bad₂_le hD.res_disj I x y₂
  have hl1 := blocked_load_le hD hI hy₁
  have hl2 := blocked_load_le hD hI hy₂
  have hrich := hD.rich x hx y₁ y₂ hne (hI.sub he₁) (hI.sub he₂)
  have hcount := hI.count x hx
  have hdeg := hD.degM x hx
  have hpair : 2 ≤ incidentLoad M x := by
    have hne' : s(x, y₁) ≠ s(x, y₂) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, h2⟩
      · exact hne h
      · exact hne (h2.trans h1)
    have := incidentLoad_mono (show ({s(x, y₁), s(x, y₂)} : Finset (Sym2 V)) ⊆ M by
      intro f hf
      simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl
      exacts [he₁, he₂]) x
    rw [incidentLoad_pair hne' x] at this
    simpa using this
  have hbud := hD.budget
  omega

end PartitionedTriangleAbsorption.CoverDownStage105

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

theorem ne_of_M0_res {T2 : Finset (V × V × V)} {M0 : Finset (Sym2 V)}
    (hdisj : Disjoint M0 (resEdges T2)) {x y z z' : V} (hM : s(x, y) ∈ M0)
    (hr : (x, z, z') ∈ T2) : y ≠ z ∧ y ≠ z' := by
  constructor
  · rintro rfl
    exact disjoint_left.mp hdisj hM (mem_biUnion.mpr ⟨_, hr, mem_resTri_self₁ (x, y, z')⟩)
  · rintro rfl
    exact disjoint_left.mp hdisj hM (mem_biUnion.mpr ⟨_, hr, mem_resTri_self₂ (x, z, y)⟩)

theorem pair_load_outer {U : Finset V} {x y₁ y₂ x₀ : V} (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ U)
    (hne : s(x, y₁) ≠ s(x, y₂)) (hx₀ : x₀ ∉ U) :
    incidentLoad {s(x, y₁), s(x, y₂)} x₀ = if x₀ = x then 2 else 0 := by
  rw [incidentLoad_pair hne]
  have h1 : x₀ ≠ y₁ := fun h => hx₀ (h ▸ hy₁)
  have h2 : x₀ ≠ y₂ := fun h => hx₀ (h ▸ hy₂)
  by_cases h : x₀ = x <;> simp [Sym2.mem_iff, h, h1, h2]

/-- The invariant is restored after one pairing. -/
theorem pairing_inv_step {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m lam a2 : ℕ}
    (hD : PairingData p E U T2 B0 M0 m lam a2) {M : Finset (Sym2 V)} {A : Finset (V × V × V)}
    {I : Finset (Sym2 V)} (hI : PairingInv E U T2 B0 M0 M A I) {x y₁ y₂ z z' : V}
    (hx : x ∉ U) (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ U) (hne : y₁ ≠ y₂)
    (he₁ : s(x, y₁) ∈ M) (he₂ : s(x, y₂) ∈ M) (hrT : (x, z, z') ∈ T2)
    (hf₁E : s(y₁, z) ∈ E) (hf₂E : s(z', y₂) ∈ E) (hrA : (x, z, z') ∉ A)
    (hf₁ : s(y₁, z) ∉ B0 ∪ I) (hf₂ : s(z', y₂) ∉ B0 ∪ I) :
    PairingInv E U T2 B0 M0 (M \ {s(x, y₁), s(x, y₂)}) (insert (x, z, z') A)
      (insert s(y₁, z) (insert s(z', y₂) I)) := by
  obtain ⟨-, hz, hz', hrE⟩ := hD.res _ hrT
  have hzz' : z ≠ z' := by
    have := hD.cross z z' (hrE (mem_resTri_self₃ (x, z, z')))
    exact fun h => this (h ▸ rfl)
  obtain ⟨n1z, n1z'⟩ := ne_of_M0_res hD.disj (hI.sub he₁) hrT
  obtain ⟨n2z, n2z'⟩ := ne_of_M0_res hD.disj (hI.sub he₂) hrT
  have hee : s(x, y₁) ≠ s(x, y₂) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact hne h
    · exact hne (h2.trans h1)
  have hff : s(y₁, z) ≠ s(z', y₂) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact n1z' h1
    · exact hne h1
  have hf₂I : s(z', y₂) ∉ I := fun h => hf₂ (mem_union_right _ h)
  have hf₁I : s(y₁, z) ∉ insert s(z', y₂) I := by
    simp only [mem_insert, not_or]
    exact ⟨hff, fun h => hf₁ (mem_union_right _ h)⟩
  have hpairM : ({s(x, y₁), s(x, y₂)} : Finset (Sym2 V)) ⊆ M := by
    intro f hf
    simp only [mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl
    exacts [he₁, he₂]
  have hMsplit := fun w => incidentLoad_sdiff_add hpairM w
  refine ⟨sdiff_subset.trans hI.sub, insert_subset hrT hI.resA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x₀ hx₀
    have h1 := hMsplit x₀
    rw [pair_load_outer hy₁ hy₂ hee hx₀] at h1
    have h2 := hI.even x₀ hx₀
    rw [Nat.even_iff] at h2 ⊢
    split_ifs at h1 <;> omega
  · intro x₀ hx₀
    have h1 := hMsplit x₀
    rw [pair_load_outer hy₁ hy₂ hee hx₀] at h1
    have h2 := hI.count x₀ hx₀
    rw [incidentLoad_filter_A A hrA x₀]
    by_cases h : x₀ = x
    · subst h; simp only [↓reduceIte] at h1 ⊢; omega
    · have h' : ¬ x = x₀ := fun h'' => h h''.symm
      simp only [h, h', ↓reduceIte] at h1 ⊢; omega
  · intro w
    have h1 := hMsplit w
    rw [incidentLoad_pair hee] at h1
    rw [incidentLoad_insert hf₁I, incidentLoad_insert hf₂I, spokesOf_insert,
      OnePart.incidentLoad_union ?_]
    · have hsp : incidentLoad (resSpokes (x, z, z')) w =
          (if w ∈ s(x, z) then 1 else 0) + if w ∈ s(x, z') then 1 else 0 := by
        have hg : s(x, z) ≠ s(x, z') := by
          intro h
          rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, -⟩
          · exact hzz' h
          · exact hx (h1 ▸ hz')
        exact incidentLoad_pair hg w
      rw [hsp]
      have i1 := ind_le_two y₁ z x w
      have i2 := ind_le_two z' y₂ x w
      have h2 := hI.load w
      omega
    · rw [disjoint_left]
      intro f hf hfA
      obtain ⟨r', hr'A, hf'⟩ := mem_biUnion.mp hfA
      have hne' : (x, z, z') ≠ r' := fun h => hrA (h ▸ hr'A)
      exact disjoint_left.mp (hD.res_disj hrT (hI.resA hr'A) hne')
        (resSpokes_subset_resTri _ hf) (resSpokes_subset_resTri _ hf')
  · exact insert_subset hf₁E (insert_subset hf₂E hI.inE)
  · intro f hf
    simp only [mem_insert] at hf
    rcases hf with rfl | rfl | hf
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      exacts [hy₁, hz]
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      exacts [hz', hy₂]
    · exact hI.inner f hf
  · rw [disjoint_left]
    intro f hf hfB
    simp only [mem_insert] at hf
    rcases hf with rfl | rfl | hf
    · exact hf₁ (mem_union_left _ hfB)
    · exact hf₂ (mem_union_left _ hfB)
    · exact disjoint_left.mp hI.avoid hf hfB

end PartitionedTriangleAbsorption.CoverDownStage105
