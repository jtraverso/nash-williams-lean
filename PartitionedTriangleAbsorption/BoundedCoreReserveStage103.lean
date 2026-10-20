/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateFamilyProducerStage102

/-! # A fixed absorber for every divisible residual in a bounded core

The library is produced by enumerating the divisible subsets of X. It is not
a supplied refiner. Its exponential size is acceptable only when |X| is fixed
before the graph; no linear-size sparse universal absorber is claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BoundedCoreStage103

open Finset TypedTransformer PairMoveAssemblyStage85 PairMoveSelectionStage85
  AntiEdgeSelection RefinerAssembly PrivateFamilyStage102

variable {t : ℕ}

/-- Choose one common absorber before the future divisible subset of X.
The bound K and the coefficient bound q both precede the physical graph. -/
theorem exists_fixed_absorber (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F) (K : ℕ) :
    ∃ q : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
      (a d : ℝ) (_hs : CompatibleSupply p F G a)
      (B X : Finset (Sym2 V)) (_hB : DegBounded B d) (_hd : 0 ≤ d),
      X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
      388 * (K : ℝ) + 1164 * q +
        4 * (d + K + (2 ^ K : ℕ) * (93 * K + 282 * q)) < a →
      ∃ C, C ⊆ G.edgeFinset ∧ Disjoint C (B ∪ X) ∧ HasDecomp p F C ∧
        C.card ≤ 2 ^ K * (93 * K + 282 * q) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (C ∪ L) := by
  obtain ⟨q, prod⟩ := exists_private_family F hcard hF K
  refine ⟨q, fun {V} _ _ G _ p a d hs B X hB hd hXG hXB hK hb => ?_⟩
  classical
  let S := X.powerset.filter (IsIntDiv p F)
  have hSc : S.card ≤ 2 ^ K :=
    (card_filter_le _ _).trans (by rw [card_powerset]; exact Nat.pow_le_pow_right (by omega) hK)
  have hSr : (S.card : ℝ) ≤ (2 ^ K : ℕ) := by exact_mod_cast hSc
  have hXr : (X.card : ℝ) ≤ K := by exact_mod_cast hK
  have hM0 : (0 : ℝ) ≤ 93 * K + 282 * q := by positivity
  have hbudget : 388 * (K : ℝ) + 1164 * q +
      4 * (d + X.card + S.card * (93 * K + 282 * q)) < a := by
    have hm := mul_le_mul_of_nonneg_right hSr hM0
    linarith
  have hpieces : ∀ L ∈ S, L ⊆ X ∧ L ⊆ G.edgeFinset ∧ Disjoint L B ∧
      L.card ≤ K ∧ IsIntDiv p F L := by
    intro L hL
    obtain ⟨hsub, hdiv⟩ := mem_filter.mp hL
    have hLX : L ⊆ X := mem_powerset.mp hsub
    exact ⟨hLX, hLX.trans hXG, hXB.mono_left hLX,
      (card_le_card hLX).trans hK, hdiv⟩
  obtain ⟨A, fam⟩ := prod G p a d hs S id B X hB hd hpieces hbudget
  refine ⟨S.biUnion A, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨L, hL, he⟩ := mem_biUnion.mp he
    exact fam.physical L hL he
  · rw [disjoint_biUnion_left]
    exact fam.avoids
  · exact hasDecomp_biUnion S A (fun L hL => (fam.absorbs L hL).2.1) fam.disjoint
  · exact fam.total.trans (Nat.mul_le_mul_right _ hSc)
  · intro L hLX hdiv
    have hLS : L ∈ S := mem_filter.mpr ⟨mem_powerset.mpr hLX, hdiv⟩
    have hh := selected_assembly S {L} (by simp [hLS]) X A id
      (fun J hJ => (fam.absorbs J hJ).2.1)
      (fun J hJ => (fam.absorbs J hJ).2.2) fam.disjoint
      (fun J hJ => (fam.avoids J hJ).mono_right subset_union_right)
      (fun J hJ => (hpieces J hJ).1) (by simp)
    simpa using hh

end PartitionedTriangleAbsorption.BoundedCoreStage103
