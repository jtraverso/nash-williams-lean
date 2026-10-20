/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FractionalPreparationStage71
public import PartitionedTriangleAbsorption.TypedCoverDownConsumer
public import PartitionedTriangleAbsorption.SparseDeletionDegree

/-! # Coupling the same reserve, absorber and repaired fractional seed

This integrates the formal nibble and cover-down, without invoking EGJ. A
physical signed correction is still an explicit input; its production from
the F3 host geometry is not asserted by this conditional consumer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FractionalConsumerStage72

open Finset TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- Fractional correction needs neutral edge charges, not even reserve degrees.
In particular a randomly selected neutral reserve need not be integrally
divisible. No integral divisibility of the main graph is concluded here. -/
theorem seed_after_neutral_reserve (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset (Sym2 V)) (hAG : A ⊆ G.edgeFinset) (hXG : X ⊆ G.edgeFinset)
    (hAX : Disjoint A X) (hG : IsIntDiv p F G.edgeFinset)
    (hA : HasDecomp p F A)
    (hX : ∀ l : Fin t → Fin t → ℤ, Annihilates F l →
      ∑ e ∈ X, (pairFun l (pairVec p e) : ℝ) = 0)
    (C eps a x : ℝ) (hC : 0 < C) (hn : 0 < Fintype.card V)
    (hAd : DegBounded A (a * Fintype.card V))
    (hXd : DegBounded X (x * Fintype.card V))
    (phi : Finset V → ℝ) (hseed : IsRegularAlmostPacking p F G C eps phi) :
    let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
    IsRegularAlmostPacking p F J C (eps + 2 * C * (a + x)) phi ∧
      ∀ l : Fin t → Fin t → ℤ, Annihilates F l →
        ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
          (1 - edgeLoad p F J phi e) = 0 := by
  classical
  dsimp only
  let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hd : DegBounded (A ∪ X) ((a + x) * Fintype.card V) := by
    convert SparseDeletionDegree.degBounded_union hAd hXd using 1
    ring
  have hs := PackingRestriction.regularAlmostPacking_deleteEdges (A ∪ X) hC hn hd hseed
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : eps + 2 * C * ((a + x) * Fintype.card V) / Fintype.card V =
      eps + 2 * C * (a + x) := by field_simp
  rw [heq] at hs
  refine ⟨hs, ?_⟩
  intro l hl
  have hGzero := annihilator_of_isIntDiv hG hl
  have hAzero := annihilator_of_isIntDiv (isIntDiv_of_hasDecomp hA) hl
  rw [pairFun_edgeVec] at hGzero hAzero
  have hGR : (∑ e ∈ G.edgeFinset, (pairFun l (pairVec p e) : ℝ)) = 0 := by
    exact_mod_cast hGzero
  have hAR : (∑ e ∈ A, (pairFun l (pairVec p e) : ℝ)) = 0 := by
    exact_mod_cast hAzero
  have hB : (∑ e ∈ A ∪ X, (pairFun l (pairVec p e) : ℝ)) = 0 := by
    rw [sum_union hAX, hAR, hX l hl, add_zero]
  have hmain : (∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ)) = 0 := by
    rw [SimpleGraph.edgeFinset_deleteEdges,
      sum_sdiff_eq_sub (union_subset hAG hXG), hGR, hB, sub_self]
  have hload := annihilator_load_identity p F J phi hl
  simp only [mul_sub, mul_one, sum_sub_distrib]
  rw [hload, sub_zero, hmain]

/-- Deleting a neutral reserve as well as the decomposable absorber preserves
the balance needed by a physical inverse, on precisely the main graph. -/
theorem seed_after_absorber_and_reserve (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset (Sym2 V)) (hAG : A ⊆ G.edgeFinset) (hXG : X ⊆ G.edgeFinset)
    (hAX : Disjoint A X) (hG : IsIntDiv p F G.edgeFinset)
    (hA : HasDecomp p F A) (hX : IsIntDiv p F X)
    (C eps a x : ℝ) (hC : 0 < C) (hn : 0 < Fintype.card V)
    (hAd : DegBounded A (a * Fintype.card V))
    (hXd : DegBounded X (x * Fintype.card V))
    (phi : Finset V → ℝ) (hseed : IsRegularAlmostPacking p F G C eps phi) :
    let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
    IsIntDiv p F J.edgeFinset ∧
      IsRegularAlmostPacking p F J C (eps + 2 * C * (a + x)) phi ∧
      ∀ l : Fin t → Fin t → ℤ, Annihilates F l →
        ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
          (1 - edgeLoad p F J phi e) = 0 := by
  classical
  dsimp only
  let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hJ : IsIntDiv p F J.edgeFinset := by
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact hG.sdiff ((isIntDiv_of_hasDecomp hA).union hX hAX) (union_subset hAG hXG)
  have hd : DegBounded (A ∪ X) ((a + x) * Fintype.card V) := by
    convert SparseDeletionDegree.degBounded_union hAd hXd using 1
    ring
  have hs := PackingRestriction.regularAlmostPacking_deleteEdges (A ∪ X) hC hn hd hseed
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : eps + 2 * C * ((a + x) * Fintype.card V) / Fintype.card V =
      eps + 2 * C * (a + x) := by field_simp
  rw [heq] at hs
  refine ⟨hJ, hs, ?_⟩
  intro l hl
  have hbalance := annihilator_of_isIntDiv hJ hl
  have hload := annihilator_load_identity p F J phi hl
  rw [pairFun_edgeVec] at hbalance
  simp only [mul_sub, mul_one, sum_sub_distrib]
  rw [hload, sub_zero]
  exact_mod_cast hbalance

/-- Pointwise physical correction, with all loads evaluated on the same J.
Only a half-seed correction is needed for the upper cap 2C/n. -/
theorem repaired_seed (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (C : ℝ) (hC : 1 ≤ C)
    (hn : 0 < Fintype.card V) (phi chi : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F J s →
      1 / (C * Fintype.card V) ≤ phi s ∧ phi s ≤ C / Fintype.card V)
    (hc : ∀ s, IsCopy p F J s → |chi s| ≤ 1 / (2 * C * Fintype.card V))
    (hload : ∀ e ∈ J.edgeFinset, edgeLoad p F J chi e = 1 - edgeLoad p F J phi e) :
    (∀ s, IsCopy p F J s → 0 ≤ (phi s + chi s) ∧
      phi s + chi s ≤ (2 * C) / Fintype.card V) ∧
    ∀ e ∈ J.edgeFinset, edgeLoad p F J (fun s => phi s + chi s) e = 1 := by
  have hCpos : 0 < C := by linarith
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hsmall : 1 / (2 * C * Fintype.card V) ≤ C / Fintype.card V := by
    rw [div_le_div_iff₀ (by positivity) hnR]
    have hC2 : 1 ≤ 2 * C ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hC2 hnR.le
    nlinarith only [hh]
  have hhalf : 1 / (2 * C * Fintype.card V) ≤ 1 / (C * Fintype.card V) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  constructor
  · intro s hs
    obtain ⟨hlo, hhi⟩ := hw s hs
    obtain ⟨hclo, hchi⟩ := abs_le.mp (hc s hs)
    constructor
    · linarith
    · rw [show (2 * C) / Fintype.card V = 2 * (C / Fintype.card V) by ring]
      linarith
  · intro e he
    unfold edgeLoad
    rw [sum_add_distrib]
    change edgeLoad p F J phi e + edgeLoad p F J chi e = 1
    rw [hload e he]
    ring

/-- EGJ-free exact assembly. The threshold precedes every graph and weight.
The unresolved signed correction is displayed as an input, never hidden as
an axiom or as an already-constructed object. -/
theorem decomposition_of_physical_correction (C alpha : ℝ) (hC : 1 ≤ C)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
        (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset (Sym2 V))
        [DecidableRel (ReserveCoverDown.reserveGraph X).Adj] (phi chi : Finset V → ℝ),
        A ⊆ G.edgeFinset → X ⊆ G.edgeFinset → Disjoint A X →
        IsIntDiv p F G.edgeFinset →
        (∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)) →
        AntiEdgeful p F (ReserveCoverDown.reserveGraph X) alpha →
        (∀ s, IsCopy p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) s →
          1 / (C * Fintype.card V) ≤ phi s ∧ phi s ≤ C / Fintype.card V) →
        (∀ s, IsCopy p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) s →
          |chi s| ≤ 1 / (2 * C * Fintype.card V)) →
        (∀ e ∈ G.edgeFinset \ (A ∪ X),
          edgeLoad p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) chi e =
            1 - edgeLoad p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) phi e) →
        HasDecomp p F G.edgeFinset := by
  have hCp : 0 < 2 * C := by linarith
  obtain ⟨N, hN⟩ := TypedCoverDown.typed_cover_down_absorption (2 * C) alpha hCp ha ha1
  refine ⟨max N 1, ?_⟩
  intro V _ _ hV t p F G _ A X _ phi chi hAG hXG hAX hG habs hres hw hc hload
  classical
  let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hJ : J.edgeFinset = G.edgeFinset \ (A ∪ X) := SimpleGraph.edgeFinset_deleteEdges _
  have hn : 0 < Fintype.card V := by have := le_of_max_le_right hV; omega
  obtain ⟨hweights, hexact⟩ := repaired_seed p F J C hC hn phi chi hw hc
    (fun e he => hload e (hJ ▸ he))
  exact hN V (le_of_max_le_left hV) t p F G A X (fun s => phi s + chi s)
    hAG hXG hAX hG habs hres hweights (fun e he => hexact e (hJ.symm ▸ he))

end PartitionedTriangleAbsorption.FractionalConsumerStage72
