/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupStepStage100

/-! # Producing all catalytic closures by finite induction

The induction consumes the actual invariant-preserving physical step.
Already closed blocks are skipped; no terminal decomposition is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupStage100

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89
  TripleCutStage94 CatalyticCleanupStage99 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))}
  {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V}

/-- Close the listed blocks, preserving every block already closed. -/
theorem cleanup_list (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d) :
    ∀ (ys : List V) (pos : Tok V → Sym2 V) (U : Finset (Sym2 V)) (Z : Finset V),
      Phys p F G B S.tokens pos U Z → Bdry p F S pos ∅ →
      (∀ y ∈ ys, y ∈ S.A) →
      (Z.card : ℝ) + 110 * ys.length + 4 * (d + U.card) < a →
      ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V) (n : ℕ),
        Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' ∅ ∧
        (∀ y ∈ ys, Closed S pos' y) ∧
        (∀ y ∈ S.A, Closed S pos y → Closed S pos' y) ∧
        (∀ e, pos' (.inl e) = pos (.inl e)) ∧
        (∀ y, pos' (.inr (y, 2)) = pos (.inr (y, 2))) ∧
        U ⊆ U' ∧ U'.card ≤ U.card + 27 * ys.length ∧
        Z ⊆ Z' ∧ Z'.card ≤ Z.card + 2 * ys.length ∧ n ≤ 3 * ys.length ∧
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos') n ∧
        ∀ W k, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W k →
          PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (n + k) := by
  intro ys
  induction ys with
  | nil =>
    intro pos U Z ph bd _ _
    refine ⟨pos, U, Z, 0, ph, bd, by simp, fun _ _ hc => hc, fun _ => rfl,
      fun _ => rfl, Subset.refl _, by simp, Subset.refl _, by simp, by simp, .stop _ _, ?_⟩
    intro W k ht
    simpa using ht
  | cons y ys ih =>
    intro pos U Z ph bd hys hb
    have hy : y ∈ S.A := hys y (by simp)
    have htail : ∀ y' ∈ ys, y' ∈ S.A := fun y' hy' => hys y' (List.mem_cons_of_mem y hy')
    have hlen : ((y :: ys).length : ℝ) = ys.length + 1 := by simp
    have hnonneg : (0 : ℝ) ≤ ys.length := Nat.cast_nonneg _
    by_cases hc : Closed S pos y
    · obtain ⟨pos', U', Z', n, ph', bd', cs, persist, unO, un2, hUU, hUc, hZZ, hZc, hn,
        tr, cont⟩ := ih pos U Z ph bd htail (by rw [hlen] at hb; linarith)
      refine ⟨pos', U', Z', n, ph', bd', ?_, persist, unO, un2, hUU, ?_, hZZ, ?_, ?_, tr, cont⟩
      · intro y' hy'
        rcases List.mem_cons.mp hy' with rfl | hy'
        · exact persist y' hy hc
        · exact cs y' hy'
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
    · obtain ⟨pos₁, U₁, Z₁, ph₁, bd₁, cy, persist₁, unO₁, un2₁, hUU₁, hUc₁,
        hZZ₁, hZc₁, tr₁, cont₁⟩ :=
        close_step a d hF hs hB hd ph bd hy hc (by rw [hlen] at hb; linarith)
      have hUr : (U₁.card : ℝ) ≤ U.card + 27 := by exact_mod_cast hUc₁
      have hZr : (Z₁.card : ℝ) ≤ Z.card + 2 := by exact_mod_cast hZc₁
      obtain ⟨pos₂, U₂, Z₂, n, ph₂, bd₂, cs, persist₂, unO₂, un2₂,
        hUU₂, hUc₂, hZZ₂, hZc₂, hn, tr₂, cont₂⟩ :=
        ih pos₁ U₁ Z₁ ph₁ bd₁ htail (by rw [hlen] at hb; linarith)
      refine ⟨pos₂, U₂, Z₂, 3 + n, ph₂, bd₂, ?_, ?_, ?_, ?_,
        hUU₁.trans hUU₂, ?_, hZZ₁.trans hZZ₂, ?_, ?_, cont₁ _ _ tr₂, ?_⟩
      · intro y' hy'
        rcases List.mem_cons.mp hy' with rfl | hy'
        · exact persist₂ y' hy cy
        · exact cs y' hy'
      · intro y' hy' hc'
        exact persist₂ y' hy' (persist₁ y' hy' hc')
      · intro e; rw [unO₂, unO₁]
      · intro y'; rw [un2₂, un2₁]
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · intro W k ht
        have h := cont₁ W (n + k) (cont₂ W k ht)
        simpa only [Nat.add_assoc] using h

/-- Produce a fully decomposed current configuration. All catalytic closures
are obtained by the induction, not supplied to the assembly consumer. -/
theorem cleanup_all (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    {pos : Tok V → Sym2 V} {U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos ∅)
    (hl : ∀ y ∈ S.A, Link F (p y) (p (S.cs y)) (p (S.ct y)))
    (hb : (Z.card : ℝ) + 110 * S.A.card + 4 * (d + U.card) < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V) (n : ℕ),
      Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' ∅ ∧
      (∀ y ∈ S.A, Closed S pos' y) ∧ HasDecomp p F (S.tokens.image pos') ∧
      (∀ e, pos' (.inl e) = pos (.inl e)) ∧
      (∀ y, pos' (.inr (y, 2)) = pos (.inr (y, 2))) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 27 * S.A.card ∧
      Z ⊆ Z' ∧ Z'.card ≤ Z.card + 2 * S.A.card ∧ n ≤ 3 * S.A.card ∧
      PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos') n ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W k →
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (n + k) := by
  obtain ⟨pos', U', Z', n, ph', bd', cs, -, unO, un2, hUU, hUc, hZZ, hZc, hn, tr, cont⟩ :=
    cleanup_list a d hF hs hB hd S.A.toList pos U Z ph bd (by simp) (by simpa using hb)
  have hc : ∀ y ∈ S.A, Closed S pos' y := fun y hy => cs y (mem_toList.mpr hy)
  refine ⟨pos', U', Z', n, ph', bd', hc, full_decomp_of_closed ph' bd' hl hc,
    unO, un2, hUU, ?_, hZZ, ?_, ?_, tr, cont⟩
  · simpa using hUc
  · simpa using hZc
  · simpa using hn

end PartitionedTriangleAbsorption.CleanupStage100
