/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.RainbowAbsorber

/-! # BlowupB.RainbowTerminal — a terminal absorber for the rainbow type

For a bounded edge set `X` (`|X| ≤ K`) of a nearly complete rainbow blowup, one fixed edge set `A`
absorbs **every** integrally divisible `L ⊆ X` (`rainbow_terminal_absorber`): `A` decomposes and
`A ∪ L` decomposes for every such `L`. `A` is the union of private absorbers of the (at most
`2^K`) divisible subsets of `X`, chosen one after the other on fresh vertices; each private
absorber contains a fresh vertex in every edge, so they are pairwise edge-disjoint and avoid `X`.
No `ThreeStepLinks` is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_vertsOf_of {X : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ X) {v : V} (hv : v ∈ e) :
    v ∈ vertsOf X :=
  mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ _, hv⟩⟩

theorem vertsOf_mono {L X : Finset (Sym2 V)} (h : L ⊆ X) : vertsOf L ⊆ vertsOf X :=
  biUnion_subset_biUnion_of_subset_left _ h

end

/-- **Rainbow terminal absorber.** -/
theorem rainbow_terminal_absorber {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 3}
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ}
    (hsub : ∀ u v, G.Adj u v → p u ≠ p v) (hmiss : ∀ v, missDeg p R3 G v ≤ d)
    (X : Finset (Sym2 V)) (Z : Finset V) (hXG : X ⊆ G.edgeFinset) (hK : X.card ≤ K)
    (hcls : ∀ c, Z.card + 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) :
    ∃ A ⊆ G.edgeFinset, Disjoint A X ∧ HasDecomp p R3 A ∧
      (∀ L ⊆ X, IsIntDiv p R3 L → HasDecomp p R3 (A ∪ L)) ∧
      ∃ U : Finset V, Disjoint U (Z ∪ vertsOf X) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf X ∨ v ∈ U := by
  classical
  set D := X.powerset.filter (IsIntDiv p R3) with hD
  have hDc : D.card ≤ 2 ^ K := (card_filter_le _ _).trans
    (by rw [card_powerset]; exact Nat.pow_le_pow_right (by norm_num) hK)
  have hVX : (vertsOf X).card ≤ 2 * K := card_vertsOf_le.trans (by omega)
  have key : ∀ 𝓛 : Finset (Finset (Sym2 V)), 𝓛 ⊆ D → ∃ A ⊆ G.edgeFinset, Disjoint A X ∧
      HasDecomp p R3 A ∧ (∀ L ∈ 𝓛, HasDecomp p R3 (A ∪ L)) ∧
      ∃ U : Finset V, U.card ≤ 4 * K * 𝓛.card ∧ Disjoint U (Z ∪ vertsOf X) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf X ∨ v ∈ U := by
    intro 𝓛
    induction 𝓛 using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, empty_subset _, disjoint_empty_left _, hasDecomp_empty',
        fun L h => absurd h (notMem_empty _), ∅, by simp, disjoint_empty_left _,
        fun e he => absurd he (notMem_empty _)⟩
    | insert L 𝓛 hL ih =>
      intro h𝓛
      obtain ⟨A, hAG, hAX, hAdec, hAall, U, hUc, hUZ, hAv⟩ :=
        ih (subset_trans (subset_insert _ _) h𝓛)
      obtain ⟨hLX, hLdiv⟩ := mem_filter.mp (h𝓛 (mem_insert_self L 𝓛))
      have hLX' : L ⊆ X := mem_powerset.mp hLX
      have hLc : L.card ≤ K := (card_le_card hLX').trans hK
      have h𝓛c : 𝓛.card ≤ 2 ^ K := by
        have := card_le_card h𝓛
        rw [card_insert_of_notMem hL] at this
        omega
      have hZ' : (Z ∪ U ∪ vertsOf X).card ≤ Z.card + 4 * K * 2 ^ K + 2 * K := by
        have h1 := card_union_le (Z ∪ U) (vertsOf X)
        have h2 := card_union_le Z U
        have h3 : 4 * K * 𝓛.card ≤ 4 * K * 2 ^ K := Nat.mul_le_mul_left _ h𝓛c
        omega
      obtain ⟨B, hBG, hBL, hBdec, hBLdec, UL, hULc, hULZ, hBv, hBu⟩ :=
        rainbow_private_absorber hsub hmiss (Z ∪ U ∪ vertsOf X) (subset_trans hLX' hXG) hLdiv hLc
          (fun c => by have := hcls c; omega)
      have hUL_out : ∀ u ∈ UL, u ∉ U ∧ u ∉ vertsOf X := by
        intro u hu
        have := disjoint_left.mp hULZ hu
        simp only [mem_union, not_or] at this
        exact ⟨this.1.1.2, this.1.2⟩
      have hBA : Disjoint B A := by
        rw [disjoint_left]
        intro e heB heA
        obtain ⟨u, hu, huUL⟩ := hBu e heB
        obtain ⟨h1, h2⟩ := hUL_out u huUL
        rcases hAv e heA u hu with h | h
        · exact h2 h
        · exact h1 h
      have hBX : Disjoint B X := by
        rw [disjoint_left]
        intro e heB heX
        obtain ⟨u, hu, huUL⟩ := hBu e heB
        exact (hUL_out u huUL).2 (mem_vertsOf_of heX hu)
      refine ⟨A ∪ B, union_subset hAG hBG, disjoint_union_left.mpr ⟨hAX, hBX⟩,
        hasDecomp_union hAdec hBdec hBA.symm, ?_, U ∪ UL, ?_, ?_, ?_⟩
      · intro L' hL'
        rcases mem_insert.mp hL' with rfl | hL'
        · rw [union_assoc]
          refine hasDecomp_union hAdec hBLdec ?_
          exact disjoint_union_right.mpr ⟨hBA.symm, disjoint_of_subset_right hLX' hAX⟩
        · have hL'X : L' ⊆ X := mem_powerset.mp (mem_filter.mp (h𝓛 (mem_insert_of_mem hL'))).1
          have e : A ∪ B ∪ L' = (A ∪ L') ∪ B := by
            ext x; simp only [mem_union]; tauto
          rw [e]
          refine hasDecomp_union (hAall L' hL') hBdec ?_
          exact disjoint_union_left.mpr ⟨hBA.symm, (disjoint_of_subset_left hL'X hBX.symm)⟩
      · rw [card_insert_of_notMem hL]
        have := card_union_le U UL
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · rw [disjoint_union_left]
        refine ⟨hUZ, ?_⟩
        rw [disjoint_left]
        intro u hu hu'
        have := disjoint_left.mp hULZ hu
        simp only [mem_union, not_or] at this hu'
        rcases hu' with h | h
        · exact this.1.1.1 h
        · exact this.1.2 h
      · intro e he v hv
        rcases mem_union.mp he with he | he
        · rcases hAv e he v hv with h | h
          · exact Or.inl h
          · exact Or.inr (mem_union_left _ h)
        · rcases hBv e he v hv with h | h
          · exact Or.inl (vertsOf_mono hLX' h)
          · exact Or.inr (mem_union_right _ h)
  obtain ⟨A, hAG, hAX, hAdec, hAall, U, _, hUZ, hAv⟩ := key D (subset_refl _)
  refine ⟨A, hAG, hAX, hAdec, fun L hL hLdiv => hAall L ?_, U, hUZ, hAv⟩
  exact mem_filter.mpr ⟨mem_powerset.mpr hL, hLdiv⟩

end PartitionedTriangleAbsorption.BlowupB
