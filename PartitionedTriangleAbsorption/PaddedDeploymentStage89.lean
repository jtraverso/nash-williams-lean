/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalPaddingStage89
public import PartitionedTriangleAbsorption.MoveLedgerStage88
public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse
public import PartitionedTriangleAbsorption.SignedHinge.Wedge

/-! # Actual padded deployment from integral divisibility

The coefficient bound is fixed before the graph and the bounded input piece.
The padding is selected in the graph, and the deployment is produced, not
assumed. The output is not yet an absorber: its terminal configuration still
needs token-triple surgery and a positive decomposition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PaddedDeploymentStage89

open Finset PhysicalPaddingStage89 TypedBoundedCoefficients
  PairMoveSelectionStage85 TypedDivisibilityCollapse PhysicalMovesStage86

variable {t : ℕ}

/-- Uniform padding inside the same host for every bounded lattice piece.
The bound is existential in F,K, not asserted to be linear in K. -/
theorem bounded_physical_padding (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, τ.card = 3) (K : ℕ) :
    ∃ q : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
      (a d : ℝ) (_hs : CompatibleSupply p F G a)
      (B U P : Finset (Sym2 V)) (Z : Finset V) (_hB : DegBounded B d) (_hd : 0 ≤ d),
      P ⊆ U → P.card ≤ K →
      (∃ c : Multiset (Fin t) → ℤ, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ) →
      3 * (q : ℝ) + Z.card + 4 * (d + U.card) < a →
      ∃ (c : Multiset (Fin t) → ℤ), ∃ Q, Q ⊆ G.edgeFinset ∧ Disjoint Q (B ∪ U) ∧ Disjoint P Q ∧
        HasDecomp p F Q ∧ Q.card ≤ 3 * q ∧
        (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
        edgeVec p (P ∪ Q) = ∑ τ ∈ F, (max (c τ) 0) • typeEdgeVec τ := by
  obtain ⟨q, hq⟩ := bounded_coefficients F K
  refine ⟨q, fun {V} _ _ G _ p a d hs B U P Z hB hd hPU hK hlat hb => ?_⟩
  obtain ⟨c, hc, hmass⟩ := hq p P hK hlat
  have hm : (negativeMass F c : ℝ) ≤ q := by exact_mod_cast hmass
  obtain ⟨Q, hQG, havoid, hdec, hcard, hz, hvec⟩ :=
    physical_padding G p F hF c a d hs B U Z hB hd (by linarith)
  have hPQ : Disjoint P Q :=
    ((disjoint_union_right.mp havoid).2.mono_right hPU).symm
  refine ⟨c, Q, hQG, havoid, hPQ, hdec,
    hcard.le.trans (Nat.mul_le_mul_left 3 hmass), hz, ?_⟩
  rw [edgeVec_union p hPQ, hc, hvec, ← sum_add_distrib]
  apply sum_congr rfl
  intro τ _
  rw [← add_smul]
  congr 1
  omega

/-- The actual producer from integral divisibility to a physically deployed
configuration and a final ledger. No catalyst or terminal decomposition is
assumed. Nonnegative type coefficients are asserted for the padded input;
token tracking through deployment is a separate producer obligation. -/
theorem prepare_from_divisible (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, τ.card = 3) (hlinks : TypedTransformer.ThreeStepLinks F) (K : ℕ) :
    ∃ q : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
      (a d : ℝ) (_hs : CompatibleSupply p F G a)
      (B U P : Finset (Sym2 V)) (Z : Finset V) (_hB : DegBounded B d) (_hd : 0 ≤ d),
      P ⊆ U → P ⊆ G.edgeFinset → Disjoint P B →
      (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → P.card ≤ K → IsIntDiv p F P →
      (Z.card : ℝ) + 37 * K + 129 * q + 4 * (d + U.card) < a →
      ∃ (c : Multiset (Fin t) → ℤ), ∃ Q Y L r,
        Q ⊆ G.edgeFinset ∧ Disjoint Q (B ∪ U) ∧ Disjoint P Q ∧
        HasDecomp p F Q ∧ Q.card ≤ 3 * q ∧
        (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
        edgeVec p (P ∪ Q) = ∑ τ ∈ F, (max (c τ) 0) • typeEdgeVec τ ∧
        r ≤ K + 3 * q ∧ PhysicalMoves p F G.edgeFinset B (U ∪ Q) (P ∪ Q) Y r ∧
        (∀ v, AntiEdgeSelection.incidentLoad Y v = 0 ∨
          AntiEdgeSelection.incidentLoad Y v = 2) ∧
        Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = (P ∪ Q).card ∧
        U ∪ Q ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * K + 30 * q ∧
        (∀ D : Finset (Sym2 V), Disjoint D L →
          PhysicalMoves p F G.edgeFinset B ((U ∪ Q) ∪ D)
            ((P ∪ Q) ∪ D) (Y ∪ D) r) := by
  obtain ⟨q, hq⟩ := bounded_physical_padding F hF K
  refine ⟨q, fun {V} _ _ G _ p a d hs B U P Z hB hd hPU hPG hPB hPZ hK hdiv hb => ?_⟩
  have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  obtain ⟨c, Q, hQG, havoid, hPQ, hdec, hcard, hz, hvec⟩ :=
    hq G p a d hs B U P Z hB hd hPU hK hdiv.1 (by linarith)
  have hXG : P ∪ Q ⊆ G.edgeFinset := union_subset hPG hQG
  have hXU : P ∪ Q ⊆ U ∪ Q := union_subset_union hPU (Subset.refl _)
  have hXB : Disjoint (P ∪ Q) B := disjoint_union_left.mpr
    ⟨hPB, (disjoint_union_right.mp havoid).1⟩
  have hdivX := hdiv.union (isIntDiv_of_hasDecomp hdec) hPQ
  have hact := active_of_isIntDiv hF hdivX
  have heven := even_of_isIntDiv hF
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))) hdivX
  have hZ : ∀ e ∈ P ∪ Q, ∀ v ∈ e, v ∈ Z ∪ vertSet Q := by
    intro e he v hv
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (hPZ e he v hv)
    · exact mem_union_right _ (SignedHinge.mem_vertSet.mpr ⟨e, he, hv⟩)
  have hXcard : (P ∪ Q).card ≤ K + 3*q :=
    (card_union_le P Q).trans (Nat.add_le_add hK hcard)
  have hUcard : (U ∪ Q).card ≤ U.card + 3*q :=
    (card_union_le U Q).trans (Nat.add_le_add_left hcard _)
  have hZcard : (Z ∪ vertSet Q).card ≤ Z.card + 6*q := by
    have hv := SignedHinge.card_vertSet_le Q
    have hc := card_union_le Z (vertSet Q)
    omega
  have hxR : ((P ∪ Q).card : ℝ) ≤ K + 3*q := by exact_mod_cast hXcard
  have huR : ((U ∪ Q).card : ℝ) ≤ U.card + 3*q := by exact_mod_cast hUcard
  have hzR : ((Z ∪ vertSet Q).card : ℝ) ≤ Z.card + 6*q := by exact_mod_cast hZcard
  obtain ⟨Y,L,r,hr,ht,hdeg,hYG,hYB,hYcard,hUL,hYL,hLc,hframe⟩ :=
    MoveLedgerStage88.deploy_for_catalysts G a d hlinks hs B (U ∪ Q) (P ∪ Q)
      (Z ∪ vertSet Q) hB hd hXU hXG hXB hZ hact heven (by linarith)
  refine ⟨c,Q,Y,L,r,hQG,havoid,hPQ,hdec,hcard,hz,hvec,hr.trans hXcard,ht,
    hdeg,hYG,hYB,hYcard,hUL,hYL,?_,hframe⟩
  omega

end PartitionedTriangleAbsorption.PaddedDeploymentStage89
