/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairMoveStage85

/-! # Backwards assembly of private absorbers from fresh pair moves

One step consumes an absorber of the next configuration and constructs an
absorber of the current configuration. Repeated steps still require an actual
fresh move sequence; its existence is not assumed to follow from divisibility.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairMoveAssemblyStage85

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Exact two-mode certificate for a private residue, with no universality claim. -/
def Absorbs (A X : Finset (Sym2 V)) : Prop :=
  Disjoint A X ∧ HasDecomp p F A ∧ HasDecomp p F (A ∪ X)

/-- If the final configuration decomposes, it needs no auxiliary edges. -/
theorem terminal {X : Finset (Sym2 V)} (hX : HasDecomp p F X) :
    Absorbs (p := p) (F := F) ∅ X := by
  refine ⟨by simp, ⟨∅, ?_⟩, ?_⟩
  · exact ⟨by simp, by simp, by simp⟩
  · simpa using hX

/-- Transport the two positive modes backwards across a fresh move.
`Q` is removed from `X` and replaced by `R`; the next absorber must avoid
the entire old configuration, not merely the part that survives the move. -/
theorem backwards_step {X Q R H A : Finset (Sym2 V)}
    (hQ : Q ⊆ X) (hRX : Disjoint R X)
    (hmove : IsTransformer (p := p) (F := F) H Q R)
    (hHX : Disjoint H X) (hHA : Disjoint H A) (hAX : Disjoint A X)
    (hnext : Absorbs (p := p) (F := F) A ((X \ Q) ∪ R)) :
    Absorbs (p := p) (F := F) (H ∪ R ∪ A) X := by
  have hHR := (disjoint_union_right.mp hmove.1).2
  have hAR := (disjoint_union_right.mp hnext.1).2
  have hQrest : Disjoint Q (X \ Q) := by
    rw [disjoint_left]
    intro e he he'
    exact (mem_sdiff.mp he').2 he
  have hQnext : Disjoint Q ((X \ Q) ∪ R) :=
    disjoint_union_right.mpr ⟨hQrest, (hRX.mono_right hQ).symm⟩
  have hHnext : Disjoint H ((X \ Q) ∪ R) :=
    disjoint_union_right.mpr ⟨hHX.mono_right sdiff_subset, hHR⟩
  have hleft : Disjoint (H ∪ Q) (A ∪ ((X \ Q) ∪ R)) :=
    disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hHA, hHnext⟩,
      disjoint_union_right.mpr ⟨(hAX.mono_right hQ).symm, hQnext⟩⟩
  have hright : Disjoint (H ∪ R) A :=
    disjoint_union_left.mpr ⟨hHA, hAR.symm⟩
  refine ⟨disjoint_union_left.mpr
    ⟨disjoint_union_left.mpr ⟨hHX, hRX⟩, hAX⟩,
    hmove.2.2.union hnext.2.1 hright, ?_⟩
  have hcover : (H ∪ Q) ∪ (A ∪ ((X \ Q) ∪ R)) = (H ∪ R ∪ A) ∪ X := by
    have hx : Q ∪ (X \ Q) = X := union_sdiff_of_subset hQ
    rw [← hx]
    ext e
    simp only [mem_union, mem_sdiff]
    tauto
  rw [← hcover]
  exact hmove.2.1.union hnext.2.2 hleft

/-- A seven-edge move adds at most nine edges to a backwards absorber. -/
theorem backwards_card_bound (H R A : Finset (Sym2 V))
    (hH : H.card ≤ 7) (hR : R.card ≤ 2) :
    (H ∪ R ∪ A).card ≤ A.card + 9 := by
  have hc := (card_union_le (H ∪ R) A).trans
    (Nat.add_le_add_right (card_union_le H R) A.card)
  omega

/-- Add initially supplied decomposable catalysts to the private absorber.
The catalysts may stay in the final configuration; they need not all be moved. -/
theorem discard_catalysts {P D A : Finset (Sym2 V)}
    (hPD : Disjoint P D) (hD : HasDecomp p F D)
    (h : Absorbs (p := p) (F := F) A (P ∪ D)) :
    Absorbs (p := p) (F := F) (A ∪ D) P := by
  have hAP := (disjoint_union_right.mp h.1).1
  have hAD := (disjoint_union_right.mp h.1).2
  refine ⟨disjoint_union_left.mpr ⟨hAP, hPD.symm⟩, h.2.1.union hD hAD, ?_⟩
  simpa only [union_assoc, union_comm, union_left_comm] using h.2.2

/-- A concrete fresh move trace. U is cumulative history, never just the current
configuration. The forbidden edge set is fixed throughout the trace. -/
inductive FreshMoves (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (B : Finset (Sym2 V)) :
    Finset (Sym2 V) → Finset (Sym2 V) → Finset (Sym2 V) → ℕ → Prop
  | stop (U X : Finset (Sym2 V)) : FreshMoves p F B U X X 0
  | step {U X Y Q R H : Finset (Sym2 V)} {n : ℕ}
      (history : X ⊆ U) (removed : Q ⊆ X)
      (fresh : Disjoint (H ∪ R) (B ∪ U))
      (move : IsTransformer (p := p) (F := F) H Q R)
      (sizeH : H.card ≤ 7) (sizeR : R.card ≤ 2)
      (tail : FreshMoves p F B (U ∪ H ∪ R) ((X \ Q) ∪ R) Y n) :
      FreshMoves p F B U X Y (n + 1)

/-- Induction on an actual fresh trace produces both positive modes and a
linear size bound. It does not presuppose any absorber for the source. -/
theorem FreshMoves.exists_absorber {B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : FreshMoves p F B U X Y n) (hY : HasDecomp p F Y) :
    ∃ A, Absorbs (p := p) (F := F) A X ∧
      Disjoint A (B ∪ U) ∧ A.card ≤ 9 * n := by
  induction h with
  | stop U X =>
    exact ⟨∅, terminal hY, by simp, by simp⟩
  | @step U X Y Q R H n hXU hQ hf hm hH hR ht ih =>
    obtain ⟨A, hA, havoid, hcard⟩ := ih hY
    have hHU : Disjoint H U :=
      (disjoint_union_right.mp (disjoint_union_left.mp hf).1).2
    have hRU : Disjoint R U :=
      (disjoint_union_right.mp (disjoint_union_left.mp hf).2).2
    have hAU : Disjoint A U := havoid.mono_right (by
      intro e he
      exact mem_union.mpr (Or.inr (mem_union.mpr
        (Or.inl (mem_union.mpr (Or.inl he))))))
    have hAH : Disjoint A H := havoid.mono_right (by
      intro e he
      exact mem_union.mpr (Or.inr (mem_union.mpr
        (Or.inl (mem_union.mpr (Or.inr he))))))
    have hsmall : B ∪ U ⊆ B ∪ (U ∪ H ∪ R) := by
      intro e he
      simp only [mem_union] at he ⊢
      tauto
    refine ⟨H ∪ R ∪ A,
      backwards_step hQ (hRU.mono_right hXU) hm (hHU.mono_right hXU)
        hAH.symm (hAU.mono_right hXU) hA,
      disjoint_union_left.mpr ⟨hf, havoid.mono_right hsmall⟩, ?_⟩
    have hc := backwards_card_bound H R A hH hR
    omega

/-- The public private-absorber consumer includes the initially decomposable
padding, preserves avoidance of B, and counts that padding only once. -/
theorem private_absorber_of_trace {B P D Y : Finset (Sym2 V)} {n : ℕ}
    (hPD : Disjoint P D) (hBD : Disjoint D B) (hD : HasDecomp p F D)
    (htrace : FreshMoves p F B (P ∪ D) (P ∪ D) Y n)
    (hY : HasDecomp p F Y) :
    ∃ A, Absorbs (p := p) (F := F) A P ∧ Disjoint A B ∧
      A.card ≤ 9 * n + D.card := by
  obtain ⟨A, hA, havoid, hcard⟩ := htrace.exists_absorber hY
  refine ⟨A ∪ D, discard_catalysts hPD hD hA,
    disjoint_union_left.mpr ⟨(disjoint_union_right.mp havoid).1, hBD⟩, ?_⟩
  exact (card_union_le A D).trans (Nat.add_le_add_right hcard D.card)

end PartitionedTriangleAbsorption.PairMoveAssemblyStage85
