/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownPairingStepStage105

/-! # Stage105 pairing induction

All spokes of `M0` are covered by actual triangles. Used reserve spokes are
covered too; the new internal edges stay inside `U`, avoid `B0`, and are charged
vertex by vertex.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

theorem pairing_aux {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m lam a2 : ℕ}
    (hD : PairingData p E U T2 B0 M0 m lam a2) (k : ℕ) :
    ∀ (M : Finset (Sym2 V)) (A : Finset (V × V × V)) (I : Finset (Sym2 V)), M.card = k →
      PairingInv E U T2 B0 M0 M A I →
      ∃ A' I', A ⊆ A' ∧ I ⊆ I' ∧ PairingInv E U T2 B0 M0 ∅ A' I' ∧
        HasDecomp p F3 (M ∪ spokesOf (A' \ A) ∪ (I' \ I)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M A I hk hI
  rcases M.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · refine ⟨A, I, subset_rfl, subset_rfl, hI, ?_⟩
    simpa [spokesOf] using hasDecomp_empty
  obtain ⟨x, y₁, hx, hy₁, rfl⟩ := hD.spoke _ (hI.sub he)
  have hev := hI.even x hx
  have hone : 1 < (M.filter fun f => x ∈ f).card := by
    have h1 : 1 ≤ incidentLoad M x :=
      card_pos.mpr ⟨_, mem_filter.mpr ⟨he, Sym2.mem_mk_left _ _⟩⟩
    rw [Nat.even_iff] at hev
    unfold incidentLoad at h1 hev
    omega
  obtain ⟨e₂, he₂f, he₂ne⟩ := exists_mem_ne hone s(x, y₁)
  obtain ⟨he₂, hxe₂⟩ := mem_filter.mp he₂f
  obtain ⟨y₂, hy₂, rfl⟩ := spoke_eq_of_mem hx (hD.spoke _ (hI.sub he₂)) hxe₂
  have hne : y₁ ≠ y₂ := fun h => he₂ne (h ▸ rfl)
  obtain ⟨⟨x', z, z'⟩, hrT, hrx, hf₁E, hf₂E, hrA, hf₁, hf₂⟩ :=
    exists_good_reserve hD hI hx hy₁ hy₂ hne he he₂
  simp only at hrx hf₁E hf₂E hf₁ hf₂
  subst hrx
  have hI' := pairing_inv_step hD hI hx hy₁ hy₂ hne he he₂ hrT hf₁E hf₂E hrA hf₁ hf₂
  have hlt : (M \ {s(x', y₁), s(x', y₂)}).card < k := by
    rw [← hk]
    apply card_lt_card
    refine ⟨sdiff_subset, fun h => ?_⟩
    have := h he
    simp at this
  obtain ⟨A'', I'', hA'', hI'', hinv, hdec⟩ := ih _ hlt _ _ _ rfl hI'
  refine ⟨A'', I'', (subset_insert _ _).trans hA'',
    ((subset_insert _ _).trans (subset_insert _ _)).trans hI'', hinv, ?_⟩
  -- the local facts
  obtain ⟨-, hz, hz', hrE⟩ := hD.res _ hrT
  have hzz' : z ≠ z' := by
    have := hD.cross z z' (hrE (mem_resTri_self₃ (x', z, z')))
    exact fun h => this (h ▸ rfl)
  obtain ⟨n1z, n1z'⟩ := ne_of_M0_res hD.disj (hI.sub he) hrT
  obtain ⟨n2z, n2z'⟩ := ne_of_M0_res hD.disj (hI.sub he₂) hrT
  have nxy₁ : x' ≠ y₁ := fun h => hx (h ▸ hy₁)
  have nxy₂ : x' ≠ y₂ := fun h => hx (h ▸ hy₂)
  have nxz : x' ≠ z := fun h => hx (h ▸ hz)
  have nxz' : x' ≠ z' := fun h => hx (h ▸ hz')
  have hrA'' : (x', z, z') ∈ A'' := hA'' (mem_insert_self _ _)
  have hf₁I'' : s(y₁, z) ∈ I'' := hI'' (mem_insert_self _ _)
  have hf₂I'' : s(z', y₂) ∈ I'' := hI'' (mem_insert_of_mem (mem_insert_self _ _))
  have hg₁ : s(x', z) ∈ resEdges T2 := mem_biUnion.mpr ⟨_, hrT, mem_resTri_self₁ _⟩
  have hg₂ : s(x', z') ∈ resEdges T2 := mem_biUnion.mpr ⟨_, hrT, mem_resTri_self₂ _⟩
  have hspA : spokesOf A'' ⊆ resEdges T2 := spokesOf_subset_resEdges hinv.resA
  have hnotinner : ∀ v, v ∉ U → ∀ w, ¬ IsInner U s(v, w) :=
    fun v hv w hin => hv (hin v (Sym2.mem_mk_left _ _))
  have t1 := hasDecomp_tri p E hD.cross (hD.sub (hI.sub he)) (hrE (mem_resTri_self₁ _)) hf₁E
  have t2 := hasDecomp_tri p E hD.cross (hrE (mem_resTri_self₂ _)) (hD.sub (hI.sub he₂)) hf₂E
  have d12 : Disjoint ({s(x', y₁), s(x', z), s(y₁, z)} : Finset (Sym2 V))
      {s(x', z'), s(x', y₂), s(z', y₂)} := by
    rw [disjoint_left]
    intro f hf hf'
    simp only [mem_insert, mem_singleton] at hf hf'
    rcases hf with rfl | rfl | rfl <;>
      simp only [Sym2.eq_iff] at hf' <;> aesop
  set Rest := (M \ {s(x', y₁), s(x', y₂)}) ∪ spokesOf (A'' \ insert (x', z, z') A) ∪
    (I'' \ insert s(y₁, z) (insert s(z', y₂) I)) with hRest
  have dR : Disjoint ({s(x', y₁), s(x', z), s(y₁, z)} ∪ {s(x', z'), s(x', y₂), s(z', y₂)})
      Rest := by
    rw [disjoint_left]
    intro f hf hfR
    simp only [mem_union, mem_insert, mem_singleton] at hf
    rw [hRest] at hfR
    simp only [mem_union, mem_sdiff] at hfR
    have hspoke_out : f ∈ spokesOf (A'' \ insert (x', z, z') A) →
        ∃ q ∈ A'', q ≠ (x', z, z') ∧ f ∈ resSpokes q := by
      intro hq
      obtain ⟨q, hq, hfq⟩ := mem_biUnion.mp hq
      obtain ⟨hqA, hqn⟩ := mem_sdiff.mp hq
      exact ⟨q, hqA, fun h => hqn (h ▸ mem_insert_self _ _), hfq⟩
    have hspoke_notinner : ∀ q ∈ A'', ∀ g ∈ resSpokes q, ¬ IsInner U g := by
      intro q hq g hg
      have hq1 := (hD.res q (hinv.resA hq)).1
      simp only [resSpokes, mem_insert, mem_singleton] at hg
      rcases hg with rfl | rfl <;> exact hnotinner _ hq1 _
    have hres_other : ∀ g ∈ resTri (x', z, z'), ∀ q ∈ A'', q ≠ (x', z, z') →
        g ∉ resSpokes q := by
      intro g hg q hq hqn hgq
      exact disjoint_left.mp (hD.res_disj hrT (hinv.resA hq) (Ne.symm hqn)) hg
        (resSpokes_subset_resTri q hgq)
    -- classify `f`
    rcases hf with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · rcases hfR with (⟨-, h⟩ | h) | ⟨h, -⟩
      · exact h (by simp)
      · obtain ⟨q, hq, -, hfq⟩ := hspoke_out h
        exact disjoint_left.mp hD.disj (hI.sub he) (hspA (mem_biUnion.mpr ⟨q, hq, hfq⟩))
      · exact hnotinner _ hx _ (hinv.inner _ h)
    · rcases hfR with (⟨h, -⟩ | h) | ⟨h, -⟩
      · exact disjoint_left.mp hD.disj (hI.sub h) hg₁
      · obtain ⟨q, hq, hqn, hfq⟩ := hspoke_out h
        exact hres_other _ (mem_resTri_self₁ _) q hq hqn hfq
      · exact disjoint_left.mp hinv.avoid h (hD.forb hg₁)
    · rcases hfR with (⟨h, -⟩ | h) | ⟨-, h⟩
      · exact spoke_not_inner (hD.spoke _ (hI.sub h))
          (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
      · obtain ⟨q, hq, -, hfq⟩ := hspoke_out h
        exact hspoke_notinner q hq _ hfq
          (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
      · exact h (mem_insert_self _ _)
    · rcases hfR with (⟨h, -⟩ | h) | ⟨h, -⟩
      · exact disjoint_left.mp hD.disj (hI.sub h) hg₂
      · obtain ⟨q, hq, hqn, hfq⟩ := hspoke_out h
        exact hres_other _ (mem_resTri_self₂ _) q hq hqn hfq
      · exact disjoint_left.mp hinv.avoid h (hD.forb hg₂)
    · rcases hfR with (⟨-, h⟩ | h) | ⟨h, -⟩
      · exact h (by simp)
      · obtain ⟨q, hq, -, hfq⟩ := hspoke_out h
        exact disjoint_left.mp hD.disj (hI.sub he₂) (hspA (mem_biUnion.mpr ⟨q, hq, hfq⟩))
      · exact hnotinner _ hx _ (hinv.inner _ h)
    · rcases hfR with (⟨h, -⟩ | h) | ⟨-, h⟩
      · exact spoke_not_inner (hD.spoke _ (hI.sub h))
          (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
      · obtain ⟨q, hq, -, hfq⟩ := hspoke_out h
        exact hspoke_notinner q hq _ hfq
          (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
      · exact h (mem_insert_of_mem (mem_insert_self _ _))
  have hall := (t1.union t2 d12).union hdec dR
  convert hall using 1
  ext f
  simp only [hRest, mem_union, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ((hfM | hfS) | ⟨hfI, hfnI⟩)
    · by_cases h1 : f = s(x', y₁)
      · exact Or.inl (Or.inl (Or.inl h1))
      by_cases h2 : f = s(x', y₂)
      · exact Or.inl (Or.inr (Or.inr (Or.inl h2)))
      exact Or.inr (Or.inl (Or.inl ⟨hfM, by simp [h1, h2]⟩))
    · obtain ⟨q, hq, hfq⟩ := mem_biUnion.mp hfS
      obtain ⟨hqA, hqnA⟩ := mem_sdiff.mp hq
      by_cases hqr : q = (x', z, z')
      · subst hqr
        simp only [resSpokes, mem_insert, mem_singleton] at hfq
        rcases hfq with rfl | rfl
        · exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
        · exact Or.inl (Or.inr (Or.inl rfl))
      · refine Or.inr (Or.inl (Or.inr (mem_biUnion.mpr ⟨q, mem_sdiff.mpr ⟨hqA, ?_⟩, hfq⟩)))
        simp [hqr, hqnA]
    · by_cases h1 : f = s(y₁, z)
      · exact Or.inl (Or.inl (Or.inr (Or.inr h1)))
      by_cases h2 : f = s(z', y₂)
      · exact Or.inl (Or.inr (Or.inr (Or.inr h2)))
      exact Or.inr (Or.inr ⟨hfI, by simp [h1, h2, hfnI]⟩)
  · rintro (((h | h | h) | (h | h | h)) | ((⟨hfM, -⟩ | hfS) | ⟨hfI, hfn⟩))
    · subst h; exact Or.inl (Or.inl he)
    · subst h
      refine Or.inl (Or.inr (mem_biUnion.mpr ⟨_, mem_sdiff.mpr ⟨hrA'', hrA⟩, ?_⟩))
      simp [resSpokes]
    · subst h
      exact Or.inr ⟨hf₁I'', fun h => hf₁ (mem_union_right _ h)⟩
    · subst h
      refine Or.inl (Or.inr (mem_biUnion.mpr ⟨_, mem_sdiff.mpr ⟨hrA'', hrA⟩, ?_⟩))
      simp [resSpokes]
    · subst h; exact Or.inl (Or.inl he₂)
    · subst h
      exact Or.inr ⟨hf₂I'', fun h => hf₂ (mem_union_right _ h)⟩
    · exact Or.inl (Or.inl hfM)
    · obtain ⟨q, hq, hfq⟩ := mem_biUnion.mp hfS
      obtain ⟨hqA, hqn⟩ := mem_sdiff.mp hq
      exact Or.inl (Or.inr (mem_biUnion.mpr
        ⟨q, mem_sdiff.mpr ⟨hqA, fun h => hqn (mem_insert_of_mem h)⟩, hfq⟩))
    · exact Or.inr ⟨hfI, fun h => hfn (Or.inr (Or.inr h))⟩

end PartitionedTriangleAbsorption.CoverDownStage105
