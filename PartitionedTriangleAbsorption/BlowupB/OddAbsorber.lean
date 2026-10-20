/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.OddBridge

/-! # BlowupB.OddAbsorber — absorbers from odd transformers

If the trail system `Hx = P` is transformed by an odd transformer `T` into a trail system
`Hy = Q` which is itself decomposable, then `A = T ∪ Q` is an absorber for `P`: both `A` and
`A ∪ P` decompose. No link hypothesis beyond the odd walks of `OddTypes` is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {W : Type*} [DecidableEq W] {t : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
  {p : W → Fin t} {F : Finset (Multiset (Fin t))}
  {σ : Equiv.Perm I} {x y : I → W} {m : ℕ} {a : I → ℕ → W}

/-- **Absorber from an odd transformer and a decomposable target.** -/
theorem absorber_of_oddTransformer (h : OddTransformerData σ x y m a)
    (hT : OddTypes p F σ x y m a) (hQ : HasDecomp p F (srcE σ y))
    (hPQ : Disjoint (oddT σ x y m a ∪ srcE σ x) (srcE σ y)) :
    HasDecomp p F (oddT σ x y m a ∪ srcE σ y) ∧
      HasDecomp p F (oddT σ x y m a ∪ srcE σ y ∪ srcE σ x) := by
  refine ⟨oddTransformer_target h hT, ?_⟩
  have e : oddT σ x y m a ∪ srcE σ y ∪ srcE σ x = (oddT σ x y m a ∪ srcE σ x) ∪ srcE σ y := by
    ext e; simp only [mem_union]; tauto
  rw [e]
  exact hasDecomp_union (oddTransformer_source h hT) hQ hPQ

end PartitionedTriangleAbsorption.BlowupB
