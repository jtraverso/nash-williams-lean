/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHingeStage53

/-! # The signed absorber in the existing physical API

No new absorber representation is introduced. The returned edge sets are exposed
through `SignedCertificate.IsAbsorber`, `SignedCertificate.IsTwoMode`, and
`IsTransformer`. Physical containment, vertex freshness, size bounds and all
three part-pair counts remain explicit. `HingeSupply` is still a hypothesis.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedAbsorberAPIStage57

open Finset SignedCertificate SignedHinge TypedApplicationLinks

/-- Repackage the same physical modes; no edge set or decomposition is changed. -/
theorem modes_to_api {V : Type*} [DecidableEq V] {p : V → Fin 2}
    {P A Q : Finset (Sym2 V)} (hPA : Disjoint P A) (hPQ : Disjoint P Q)
    (hAQ : Disjoint A Q) (hQ : HasDecomp p F0 Q) (hA : HasDecomp p F0 A)
    (hAP : HasDecomp p F0 (A ∪ P)) (hAQdec : HasDecomp p F0 (A ∪ Q)) :
    IsAbsorber p P A ∧ IsTwoMode p P A Q ∧ IsTransformer (p := p) (F := F0) A P Q := by
  exact ⟨⟨hPA.symm, hA, hAP⟩, ⟨hPA, hPQ, hAQ, hQ, hAP, hAQdec⟩,
    ⟨disjoint_union_right.mpr ⟨hPA.symm, hAQ⟩, hAP, hAQdec⟩⟩

/-- Fixed-host consumer with the unchanged quantitative and physical contract. -/
theorem absorber_of_budget_api (α β : ℝ) (C0 K : ℕ) {V : Type*}
    [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hparts : ∀ j : Fin 2, ∃ v, p v = j)
    (hanti : AntiEdgeful p F0 G α) (hsup : HingeSupply p F0 G β C0)
    {ι : Type*} [Fintype ι] (P : Finset (Sym2 V)) (t : ι → Finset V)
    (c : ι → ℤ) (Z : Finset V) (hcert : IsSignedCert p G P t c)
    (hK : certWeight c ≤ K) (hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z)
    (hZ : Z.card ≤ 3 * K)
    (hαM : (absorberBudget C0 K : ℝ) < α * Fintype.card V)
    (hβM : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * absorberBudget C0 K < β * Fintype.card V) :
    ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
      IsAbsorber p P A ∧ IsTwoMode p P A Q ∧ IsTransformer (p := p) (F := F0) A P Q ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
      (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
      A.card ≤ absorberConst C0 * K ∧ Q.card ≤ absorberConst C0 * K ∧
      (vertSet (A ∪ Q)).card ≤ absorberConst C0 * K ∧
      pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
      pairCount p Q 0 1 = pairCount p P 0 1 := by
  obtain ⟨A, Q, hAG, hQG, hPA, hPQ, hAQ, hQZ, hQD, hA, hAP, hAQdec,
    hAc, hQc, hVc, h00, h11, h01⟩ :=
    absorber_of_budget α β C0 K p G hparts hanti hsup P t c Z hcert hK hPZ hZ hαM hβM
  have hapi := modes_to_api hPA hPQ hAQ ⟨hQD.choose, hQD.choose_spec.1⟩ hA hAP hAQdec
  exact ⟨A, Q, hAG, hQG, hapi.1, hapi.2.1, hapi.2.2, hQZ, hQD,
    hAc, hQc, hVc, h00, h11, h01⟩

end PartitionedTriangleAbsorption.SignedAbsorberAPIStage57
