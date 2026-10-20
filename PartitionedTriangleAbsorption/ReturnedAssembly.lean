/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/-
Port of Aristotle continuation 841854b3 (Assembly.lean).
Only imports and module visibility are adapted; the original is preserved.
This is a conditional deterministic assembly, not an existence theorem.
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-!
# Step L6: deterministic closing (assembly of the exact decomposition)

Given
* an integrally `F`-divisible edge set `E` (the edges of the host graph),
* an absorber `A ⊆ E` and a reserve `X ⊆ E`, disjoint, such that `A ∪ L` is
  `F`-decomposable for **every** integrally `F`-divisible `L ⊆ X`,
* an `F`-decomposable edge set `EQ ⊆ E \ A` covering all of `E \ (A ∪ X)`
  (the output of the nibble with reserves),

the whole of `E` is `F`-decomposable.  With `L := X \ EQ` we get
`E = EQ ⊔ A ⊔ L`; inherited divisibility (L0) applied twice shows that `L` is integrally
divisible, and the absorbing property finishes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- **L6 (assembly).** An absorber for a reserve, together with a decomposable cover of
everything outside absorber and reserve, yields an `F`-decomposition of `E`. -/
theorem hasDecomp_of_absorber_cover {E A X EQ : Finset (Sym2 V)} (hE : IsIntDiv p F E)
    (hA : A ⊆ E) (hX : X ⊆ E) (hAX : Disjoint A X)
    (habs : ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L))
    (hEQ : EQ ⊆ E \ A) (hcov : E \ (A ∪ X) ⊆ EQ) (hQ : HasDecomp p F EQ) :
    HasDecomp p F E := by
  have hAdec : HasDecomp p F A := by
    simpa using habs ∅ (empty_subset _) isIntDiv_empty
  have hEQE : EQ ⊆ E := hEQ.trans sdiff_subset
  have hR : IsIntDiv p F (E \ EQ) := isIntDiv_sdiff_of_hasDecomp hE hQ hEQE
  have hAR : A ⊆ E \ EQ := fun e he => by
    refine mem_sdiff.mpr ⟨hA he, fun h => ?_⟩
    exact (mem_sdiff.mp (hEQ h)).2 he
  have hL : (E \ EQ) \ A = X \ EQ := by
    ext e
    simp only [mem_sdiff]
    constructor
    · rintro ⟨⟨heE, heQ⟩, heA⟩
      refine ⟨?_, heQ⟩
      by_contra heX
      exact heQ (hcov (mem_sdiff.mpr ⟨heE, by simp [heA, heX]⟩))
    · rintro ⟨heX, heQ⟩
      exact ⟨⟨hX heX, heQ⟩, fun heA => disjoint_left.mp hAX heA heX⟩
  have hLdiv : IsIntDiv p F (X \ EQ) := by
    rw [← hL]; exact isIntDiv_sdiff_of_hasDecomp hR hAdec hAR
  have hAL : HasDecomp p F (A ∪ (X \ EQ)) := habs _ sdiff_subset hLdiv
  have hEq : EQ ∪ (A ∪ (X \ EQ)) = E := by
    ext e
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (h | h | ⟨h, -⟩)
      exacts [hEQE h, hA h, hX h]
    · intro heE
      by_cases heQ : e ∈ EQ
      · exact Or.inl heQ
      by_cases heA : e ∈ A
      · exact Or.inr (Or.inl heA)
      by_cases heX : e ∈ X
      · exact Or.inr (Or.inr ⟨heX, heQ⟩)
      exact absurd (hcov (mem_sdiff.mpr ⟨heE, by simp [heA, heX]⟩)) heQ
  have hdisj : Disjoint EQ (A ∪ (X \ EQ)) := by
    refine disjoint_union_right.mpr ⟨?_, disjoint_sdiff⟩
    exact disjoint_left.mpr fun e he heA => (mem_sdiff.mp (hEQ he)).2 heA
  rw [← hEq]
  exact hQ.union hAL hdisj

end PartitionedTriangleAbsorption


