/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownPairingStepStage105

/-! # Selected-load cover-down: geometry and the load invariant

The numerical hypotheses charge only used reserve spokes, not the full reserve.
Accepted Stage105 files are unchanged.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SelectedCoverDownStage122

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105

variable {V : Type*} [DecidableEq V]

structure Data (p : V → Fin 4) (E : Finset (Sym2 V)) (U : Finset V)
    (T2 : Finset (V × V × V)) (B0 M0 : Finset (Sym2 V)) (m b a q : ℕ) : Prop where
  cross : ∀ u v, s(u, v) ∈ E → p u ≠ p v
  res : ∀ r ∈ T2, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E
  res_disj : (T2 : Set (V × V × V)).PairwiseDisjoint resTri
  sub : M0 ⊆ E
  spoke : ∀ e ∈ M0, IsSpoke U e
  disj : Disjoint M0 (resEdges T2)
  forb : resEdges T2 ⊆ B0
  rich : ∀ x, x ∉ U → ∀ y₁ y₂, y₁ ≠ y₂ → s(x, y₁) ∈ M0 → s(x, y₂) ∈ M0 →
    a ≤ (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ E ∧ s(r.2.2, y₂) ∈ E ∧
      s(y₁, r.2.1) ∉ B0 ∧ s(r.2.2, y₂) ∉ B0).card
  degM : ∀ x, x ∉ U → incidentLoad M0 x ≤ m
  loadM : ∀ y ∈ U, incidentLoad M0 y ≤ b
  positive : 0 < q
  budget : m + 4 * (b + q) + 2 * (M0.card / q) ≤ 2 * a

/-- A saturated vertex blocks at most one triple at a fixed root, regardless
of which inner position it occupies. -/
theorem card_meeting_le {T : Finset (V × V × V)}
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) (x : V) (Z : Finset V) :
    (T.filter fun r => r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)).card ≤ Z.card := by
  classical
  let f : V × V × V → V := fun r => if r.2.1 ∈ Z then r.2.1 else r.2.2
  have hf : ∀ r ∈ T.filter (fun r => r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)),
      f r ∈ Z ∧ s(x, f r) ∈ resTri r := by
    intro r hr
    obtain ⟨_, hrx, hz⟩ := mem_filter.mp hr
    dsimp [f]
    split_ifs with h
    · exact ⟨h, hrx ▸ mem_resTri_self₁ r⟩
    · exact ⟨hz.resolve_left h, hrx ▸ mem_resTri_self₂ r⟩
  apply card_le_card_of_injOn f
  · intro r hr; exact (hf r hr).1
  · intro r hr r' hr' heq
    by_contra hne
    have hdis := hd (mem_filter.mp hr).1 (mem_filter.mp hr').1 hne
    exact disjoint_left.mp hdis (hf r hr).2 (heq ▸ (hf r' hr').2)

theorem physical_inv_step {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m b a q : ℕ}
    (hD : Data p E U T2 B0 M0 m b a q) {M : Finset (Sym2 V)} {A : Finset (V × V × V)}
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


variable [Fintype V]

structure Inv (E : Finset (Sym2 V)) (U : Finset V) (T2 : Finset (V × V × V))
    (B0 M0 M : Finset (Sym2 V)) (A : Finset (V × V × V)) (I : Finset (Sym2 V))
    (q : ℕ) (f : V → ℕ) : Prop extends PairingInv E U T2 B0 M0 M A I where
  selected : ∀ y ∈ U, incidentLoad (spokesOf A) y ≤ f y
  cap : ∀ y, f y ≤ q
  total : (∑ y, f y) + M.card ≤ M0.card

theorem inv_step {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m b a q : ℕ}
    (hD : Data p E U T2 B0 M0 m b a q)
    {M I : Finset (Sym2 V)} {A : Finset (V × V × V)} {f : V → ℕ}
    (hI : Inv E U T2 B0 M0 M A I q f) {x y₁ y₂ z z' : V}
    (hx : x ∉ U) (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ U) (hne : y₁ ≠ y₂)
    (he₁ : s(x, y₁) ∈ M) (he₂ : s(x, y₂) ∈ M) (hrT : (x, z, z') ∈ T2)
    (hf₁E : s(y₁, z) ∈ E) (hf₂E : s(z', y₂) ∈ E) (hrA : (x, z, z') ∉ A)
    (hf₁ : s(y₁, z) ∉ B0 ∪ I) (hf₂ : s(z', y₂) ∉ B0 ∪ I)
    (hzq : f z < q) (hz'q : f z' < q) :
    Inv E U T2 B0 M0 (M \ {s(x, y₁), s(x, y₂)}) (insert (x, z, z') A)
      (insert s(y₁, z) (insert s(z', y₂) I)) q
      (fun w => f w + (if w = z then 1 else 0) + if w = z' then 1 else 0) := by
  obtain ⟨_, hz, hz', hrE⟩ := hD.res _ hrT
  have hzz' : z ≠ z' := fun h => hD.cross z z' (hrE (mem_resTri_self₃ _)) (h ▸ rfl)
  have hee : s(x, y₁) ≠ s(x, y₂) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact hne h
    · exact hne (h2.trans h1)
  refine ⟨physical_inv_step hD hI.toPairingInv hx hy₁ hy₂ hne he₁ he₂ hrT
    hf₁E hf₂E hrA hf₁ hf₂, ?_, ?_, ?_⟩
  · intro w hw
    rw [spokesOf_insert]
    have hu := incidentLoad_union_le (resSpokes (x, z, z')) (spokesOf A) w
    have hsp : incidentLoad (resSpokes (x, z, z')) w =
        (if w = z then 1 else 0) + if w = z' then 1 else 0 := by
      have hneq : s(x, z) ≠ s(x, z') := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, _⟩
        · exact hzz' h
        · exact hx (h1 ▸ hz')
      rw [resSpokes, incidentLoad_pair hneq]
      have hwx : w ≠ x := fun h => hx (h ▸ hw)
      simp [Sym2.mem_iff, hwx]
    rw [hsp] at hu
    have hh := hI.selected w hw
    omega
  · intro w
    have hh := hI.cap w
    by_cases h : w = z
    · subst w; simp [hzz']; omega
    by_cases h' : w = z'
    · subst w; simp [Ne.symm hzz']; omega
    simp [h, h', hh]
  · have hp : ({s(x, y₁), s(x, y₂)} : Finset (Sym2 V)) ⊆ M := by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    have hc := card_sdiff_add_card_eq_card hp
    have hpc : ({s(x, y₁), s(x, y₂)} : Finset (Sym2 V)).card = 2 := by simp [hee]
    rw [hpc] at hc
    have hs : (∑ w, (f w + (if w = z then 1 else 0) + if w = z' then 1 else 0)) =
        (∑ w, f w) + 2 := by simp [sum_add_distrib]
    rw [hs]
    have ht := hI.total
    omega

end PartitionedTriangleAbsorption.SelectedCoverDownStage122

