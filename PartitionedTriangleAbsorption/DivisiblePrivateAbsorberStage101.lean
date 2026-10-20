/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateAbsorberProducerStage101
public import PartitionedTriangleAbsorption.PaddedDeploymentStage89

/-! # Private absorption from bounded integral divisibility

The uniform coefficient bound is chosen before the graph and residue.
Padding, deployment, insertion, cut and cleanup are all produced in the
same physical graph. Compatible supply is still an explicit hypothesis.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateAbsorberStage101

open Finset TypedTransformer TypedDivisibilityCollapse PairMoveAssemblyStage85
  AntiEdgeSelection PairMoveSelectionStage85

variable {t : ℕ}

/-- Account for both the physical padding and the complete cleanup. -/
theorem padded_private_budget {z zp x k q u up d a : ℝ}
    (hx : x ≤ k + 3 * q) (hz : zp ≤ z + 6 * q) (hu : up ≤ u + 3 * q)
    (hb : z + 382 * k + 1164 * q + 4 * (d + u) < a) :
    zp + 382 * x + 4 * (d + up) < a := by
  linarith

/-- An actual private absorber for each bounded divisible residue.
No positive coefficients, move trace or terminal decomposition are premises.
The bound q depends only on F and K; no linear Smith bound is claimed. -/
theorem private_absorber_from_divisible (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F) (K : ℕ) :
    ∃ q : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
      (a d : ℝ) (_hs : CompatibleSupply p F G a)
      (B P : Finset (Sym2 V)) (Z : Finset V) (_hB : DegBounded B d) (_hd : 0 ≤ d),
      P ⊆ G.edgeFinset → Disjoint P B →
      (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → P.card ≤ K → IsIntDiv p F P →
      (Z.card : ℝ) + 382 * K + 1164 * q + 4 * (d + P.card) < a →
      ∃ A, Absorbs (p := p) (F := F) A P ∧ Disjoint A B ∧
        A.card ≤ 93 * K + 282 * q ∧ A ⊆ G.edgeFinset := by
  obtain ⟨q, hq⟩ := PaddedDeploymentStage89.bounded_physical_padding F hcard K
  refine ⟨q, fun {V} _ _ G _ p a d hs B P Z hB hd hPG hPB hPZ hK hdiv hb => ?_⟩
  have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  obtain ⟨c, Q, hQG, havoid, hPQ, hdec, hQc, _, hvec⟩ :=
    hq G p a d hs B P P Z hB hd (Subset.refl _) hK hdiv.1 (by linarith)
  have hXG : P ∪ Q ⊆ G.edgeFinset := union_subset hPG hQG
  have hXB : Disjoint (P ∪ Q) B := disjoint_union_left.mpr
    ⟨hPB, (disjoint_union_right.mp havoid).1⟩
  have hdivX := hdiv.union (isIntDiv_of_hasDecomp hdec) hPQ
  have hact := active_of_isIntDiv hcard hdivX
  have heven := even_of_isIntDiv hcard
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))) hdivX
  have hZ : ∀ e ∈ P ∪ Q, ∀ v ∈ e, v ∈ Z ∪ vertSet Q := by
    intro e he v hv
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (hPZ e he v hv)
    · exact mem_union_right _ (SignedHinge.mem_vertSet.mpr ⟨e, he, hv⟩)
  have hXc : (P ∪ Q).card ≤ K + 3 * q :=
    (card_union_le P Q).trans (Nat.add_le_add hK hQc)
  have hZc : (Z ∪ vertSet Q).card ≤ Z.card + 6 * q := by
    have hv := SignedHinge.card_vertSet_le Q
    have hc := card_union_le Z (vertSet Q)
    omega
  have hxR : ((P ∪ Q).card : ℝ) ≤ K + 3 * q := by exact_mod_cast hXc
  have hzR : ((Z ∪ vertSet Q).card : ℝ) ≤ Z.card + 6 * q := by exact_mod_cast hZc
  have huR : ((P ∪ Q).card : ℝ) ≤ P.card + 3 * q := by
    exact_mod_cast (card_union_le P Q).trans (Nat.add_le_add_left hQc P.card)
  obtain ⟨A, habs, hAB, hAc, hAG⟩ :=
    private_absorber_of_nonnegative_coefficients G a d hF hcard hs B (P ∪ Q)
      (Z ∪ vertSet Q) hB hd hXG hXB hZ hact heven _
      (PositiveTargetBridgeStage96.natural_positive_vector p (P ∪ Q) F c hvec)
      (padded_private_budget hxR hzR huR hb)
  refine ⟨A ∪ Q, discard_catalysts hPQ hdec habs,
    disjoint_union_left.mpr ⟨hAB, (disjoint_union_right.mp havoid).1⟩,
    ?_, union_subset hAG hQG⟩
  have hu := card_union_le A Q
  omega

end PartitionedTriangleAbsorption.PrivateAbsorberStage101
