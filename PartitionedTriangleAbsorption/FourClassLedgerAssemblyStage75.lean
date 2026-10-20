/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassChargeBridgeStage75
public import PartitionedTriangleAbsorption.FourClassSeedRepairStage74

/-! # EGJ-free assembly from one neutral reserve and one absorber

The signed corrector and the coordinate balance are constructed, not inputs.
The neutral reserve and the universal absorber remain explicit hypotheses.
All original deletions, absorber edges and reserve edges share one ledger.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassLedgerAssemblyStage75

open Finset TypedLoadNecessity FourClassCopyAdapterStage74 FourClassChargeBridgeStage75

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem annihilates_chi3a : Annihilates TypedApplicationLinks.F3
    TypedRefinerCharge.chi3a := TypedRefinerCharge.kills_chi3a

theorem annihilates_chi3b : Annihilates TypedApplicationLinks.F3
    TypedRefinerCharge.chi3b := TypedRefinerCharge.kills_chi3b

theorem seed_from_neutral_ledger (p : V → Fin 4) (G0 : SimpleGraph V)
    [DecidableRel G0.Adj] (hG0 : ∀ u v, G0.Adj u v ↔ p u ≠ p v)
    (F A X : Finset (Sym2 V))
    (hAG : A ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset)
    (hXG : X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset) (hAX : Disjoint A X)
    (hdiv : IsIntDiv p TypedApplicationLinks.F3
      (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset)
    (hA : HasDecomp p TypedApplicationLinks.F3 A)
    (hX : ∀ l : Fin 4 → Fin 4 → ℤ, Annihilates TypedApplicationLinks.F3 l →
      ∑ e ∈ X, (pairFun l (pairVec p e) : ℝ) = 0)
    (gamma C eps f a x : ℝ) (hg : 0 < gamma) (hC : 1 ≤ C)
    (heps : 0 ≤ eps) (hf : 0 ≤ f) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hFd : DegBounded F (f * Fintype.card V))
    (hAd : DegBounded A (a * Fintype.card V))
    (hXd : DegBounded X (x * Fintype.card V))
    (hsmall : 72 * (f + a + x) ≤ gamma ^ 3)
    (hbudget : 72 * C * (eps + 2 * C * (a + x)) ≤ gamma ^ 3)
    (phi : Finset V → ℝ)
    (hseed : IsRegularAlmostPacking p TypedApplicationLinks.F3
      (G0.deleteEdges (F : Set (Sym2 V))) C eps phi) :
    let J := (G0.deleteEdges (F : Set (Sym2 V))).deleteEdges
      ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
    ∃ psi : Finset V → ℝ,
      (∀ s, IsCopy p TypedApplicationLinks.F3 J s →
        0 ≤ psi s ∧ psi s ≤ (2 * C) / Fintype.card V) ∧
      ∀ e ∈ J.edgeFinset, edgeLoad p TypedApplicationLinks.F3 J psi e = 1 := by
  classical
  dsimp only
  let G := G0.deleteEdges (F : Set (Sym2 V))
  let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hJG : J ≤ G0 := (SimpleGraph.deleteEdges_le _).trans
    (SimpleGraph.deleteEdges_le _)
  have hCpos : 0 < C := by linarith
  obtain ⟨hs, hc⟩ := FractionalConsumerStage72.seed_after_neutral_reserve
    p TypedApplicationLinks.F3 G A X hAG hXG hAX hdiv hA hX
    C eps a x hCpos hn hAd hXd phi hseed
  change IsRegularAlmostPacking p TypedApplicationLinks.F3 J C
    (eps + 2 * C * (a + x)) phi at hs
  change ∀ l : Fin 4 → Fin 4 → ℤ, Annihilates TypedApplicationLinks.F3 l →
    ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
      (1 - edgeLoad p TypedApplicationLinks.F3 J phi e) = 0 at hc
  let d : Sym2 V → ℝ := fun e =>
    if e ∈ J.edgeFinset then 1 - edgeLoad p TypedApplicationLinks.F3 J phi e else 0
  have hd : FourClassInverseStage73.RawBalanced (demandCoordinates p d) := by
    apply rawBalanced_of_supported_charges p G0 J hG0 hJG d
    · intro e he
      exact ite_eq_right he
    · convert hc _ annihilates_chi3a using 1
      apply sum_congr rfl
      intro e he
      simp only [d, ite_eq_left he]
    · convert hc _ annihilates_chi3b using 1
      apply sum_congr rfl
      intro e he
      simp only [d, ite_eq_left he]
  have hJ : J = G0.deleteEdges ((F ∪ (A ∪ X) : Finset (Sym2 V)) : Set (Sym2 V)) := by
    simp only [J, G, SimpleGraph.deleteEdges_deleteEdges, coe_union]
  have hJE : J.edgeFinset =
      (G0.deleteEdges ((F ∪ (A ∪ X) : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset := by
    simp only [J, G, SimpleGraph.edgeFinset_deleteEdges, sdiff_sdiff_left]
    rfl
  have hb : DegBounded (F ∪ (A ∪ X)) ((f + a + x) * Fintype.card V) := by
    have h := SparseDeletionDegree.degBounded_union hFd
      (SparseDeletionDegree.degBounded_union hAd hXd)
    convert h using 1
    ring
  change FourClassInverseStage73.RawBalanced (demandCoordinates p (fun e =>
    if e ∈ J.edgeFinset then 1 - edgeLoad p TypedApplicationLinks.F3 J phi e else 0)) at hd
  change ∃ psi : Finset V → ℝ,
    (∀ s, IsCopy p TypedApplicationLinks.F3 J s →
      0 ≤ psi s ∧ psi s ≤ (2 * C) / Fintype.card V) ∧
    ∀ e ∈ J.edgeFinset, edgeLoad p TypedApplicationLinks.F3 J psi e = 1
  simp only [hJ] at hs hd ⊢
  simp only [hJE] at hd ⊢
  exact positive_seed_of_balanced_deficit p G0 hG0 (F ∪ (A ∪ X)) gamma C
    (eps + 2 * C * (a + x)) (f + a + x) hg hC (by positivity) (by positivity)
    hsmall hbudget hn hsize hb phi hs hd

/-- The uniform threshold is fixed before the graph, reserve, absorber and
weights. No correction or balance of the main deficit is supplied. -/
theorem decomposition_from_neutral_ledger (C alpha : ℝ) (hC : 1 ≤ C)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
        (F A X : Finset (Sym2 V))
        [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
        (gamma eps f a x : ℝ) (phi : Finset V → ℝ),
        (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
        0 < gamma → 0 ≤ eps → 0 ≤ f → 0 ≤ a → 0 ≤ x →
        (∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ)) →
        A ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset →
        X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset → Disjoint A X →
        IsIntDiv p TypedApplicationLinks.F3 (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset →
        (∀ L ⊆ X, IsIntDiv p TypedApplicationLinks.F3 L →
          HasDecomp p TypedApplicationLinks.F3 (A ∪ L)) →
        (∀ l : Fin 4 → Fin 4 → ℤ, Annihilates TypedApplicationLinks.F3 l →
          ∑ e ∈ X, (pairFun l (pairVec p e) : ℝ) = 0) →
        AntiEdgeful p TypedApplicationLinks.F3 (ReserveCoverDown.reserveGraph X) alpha →
        DegBounded F (f * Fintype.card V) →
        DegBounded A (a * Fintype.card V) → DegBounded X (x * Fintype.card V) →
        72 * (f + a + x) ≤ gamma ^ 3 →
        72 * C * (eps + 2 * C * (a + x)) ≤ gamma ^ 3 →
        IsRegularAlmostPacking p TypedApplicationLinks.F3
          (G0.deleteEdges (F : Set (Sym2 V))) C eps phi →
        HasDecomp p TypedApplicationLinks.F3 (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset := by
  obtain ⟨N,hN⟩ := TypedCoverDown.typed_cover_down_absorption (2 * C) alpha
    (by linarith) halpha halpha1
  refine ⟨max N 1, ?_⟩
  intro V _ _ hV p G0 _ F A X _ gamma eps f a x phi hG0 hg heps hf ha hx
    hsize hAG hXG hAX hdiv habs hX hres hFd hAd hXd hsmall hbudget hseed
  classical
  have hn : 0 < Fintype.card V := by have := le_of_max_le_right hV; omega
  have hA : HasDecomp p TypedApplicationLinks.F3 A := by
    simpa using habs ∅ (empty_subset _) isIntDiv_empty
  obtain ⟨psi,hw,hl⟩ := seed_from_neutral_ledger p G0 hG0 F A X hAG hXG hAX
    hdiv hA hX gamma C eps f a x hg hC heps hf ha hx hn hsize
    hFd hAd hXd hsmall hbudget phi hseed
  apply hN V (le_of_max_le_left hV) 4 p TypedApplicationLinks.F3
    (G0.deleteEdges (F : Set (Sym2 V))) A X psi hAG hXG hAX hdiv habs hres hw
  intro e he
  exact hl e (by rwa [SimpleGraph.edgeFinset_deleteEdges])

end PartitionedTriangleAbsorption.FourClassLedgerAssemblyStage75
