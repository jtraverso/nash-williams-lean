/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SeedMarginStage110
public import PartitionedTriangleAbsorption.F3ReserveTrimStage109
public import PartitionedTriangleAbsorption.NeutralChargeStage76

/-! # From the returned balance charges to a reusable exact seed

Balance of the physical host, rather than a supplied balanced deficit, is
enough to feed the existing deleted-host inverse. The complete four-class
ambient host and sparse deletion bounds remain explicit.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BalancedHostSeedStage110

open Finset TypedLoadNecessity TypedApplicationLinks CoverDownStage105
  NeutralChargeStage76 FourClassCopyAdapterStage74 FourClassChargeBridgeStage75

variable {V : Type*}

theorem aEdge_eq_bal (p : V → Fin 4) (e : Sym2 V) :
    aEdge p e = balEdge p 0 e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [aEdge_mk]
    simp only [balEdge, Sym2.lift_mk]
    have h : ∀ i j : Fin 4, TypedRefinerCharge.chi3a i j = balTab 0 i j := by decide
    exact h _ _

theorem bEdge_eq_bal (p : V → Fin 4) (e : Sym2 V) :
    bEdge p e = balEdge p 1 e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [bEdge_mk]
    simp only [balEdge, Sym2.lift_mk]
    have h : ∀ i j : Fin 4, TypedRefinerCharge.chi3b i j = balTab 1 i j := by decide
    exact h _ _

theorem neutral_of_bal (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (hbal : ∀ k : Fin 2, bal p k E = 0)
    (l : Fin 4 → Fin 4 → ℤ) (hl : Annihilates F3 l) :
    ∑ e ∈ E, pairFun l (pairVec p e) = 0 := by
  apply neutral_of_two_charges p E
    (fun e he u v heq => hcross u v (heq ▸ he))
  · simpa only [a, bal, aEdge_eq_bal] using hbal 0
  · simpa only [b, bal, bEdge_eq_bal] using hbal 1
  · exact hl

variable [Fintype V] [DecidableEq V]

theorem deficit_balanced (p : V → Fin 4) (G J : SimpleGraph V)
    [DecidableRel J.Adj]
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (hJG : J ≤ G)
    (hbal : ∀ k : Fin 2, bal p k J.edgeFinset = 0) (phi : Finset V → ℝ) :
    FourClassInverseStage73.RawBalanced (demandCoordinates p (fun e =>
      if e ∈ J.edgeFinset then 1 - edgeLoad p F3 J phi e else 0)) := by
  classical
  have hcross : ∀ u v, s(u, v) ∈ J.edgeFinset → p u ≠ p v := by
    intro u v he
    exact (hG u v).mp (hJG (J.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)))
  have hcharges (l : Fin 4 → Fin 4 → ℤ) (hl : Annihilates F3 l) :
      ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
        (if e ∈ J.edgeFinset then 1 - edgeLoad p F3 J phi e else 0) = 0 := by
    have heq : (∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
        (if e ∈ J.edgeFinset then 1 - edgeLoad p F3 J phi e else 0)) =
        ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
          (1 - edgeLoad p F3 J phi e) :=
      sum_congr rfl (fun e he => by rw [ite_eq_left he])
    rw [heq]
    simp only [mul_sub, mul_one, sum_sub_distrib]
    rw [annihilator_load_identity p F3 J phi hl, sub_zero]
    exact_mod_cast neutral_of_bal p J.edgeFinset hcross hbal l hl
  exact rawBalanced_of_supported_charges p G J hG hJG _
    (fun e he => ite_eq_right he)
    (hcharges _ TypedRefinerCharge.kills_chi3a)
    (hcharges _ TypedRefinerCharge.kills_chi3b)

/-- No signed corrector, balanced deficit or repaired seed is supplied. -/
theorem exact_seed_from_balanced_host (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (gamma C eps delta : ℝ)
    (hg : 0 < gamma) (hC : 1 ≤ C) (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hsmall : 72 * delta ≤ gamma ^ 3) (hbudget : 72 * C * eps ≤ gamma ^ 3)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hB : DegBounded B (delta * Fintype.card V)) (phi : Finset V → ℝ)
    (hseed : IsRegularAlmostPacking p F3 (G.deleteEdges (B : Set (Sym2 V))) C eps phi)
    (hbal : ∀ k : Fin 2, bal p k (G.deleteEdges (B : Set (Sym2 V))).edgeFinset = 0) :
    ∃ psi : Finset V → ℝ,
      IsRegularAlmostPacking p F3 (G.deleteEdges (B : Set (Sym2 V))) (2 * C) 0 psi := by
  exact SeedMarginStage110.exact_seed_with_margin p G hG B gamma C eps delta hg hC
    heps hdelta hsmall hbudget hn hsize hB phi hseed
    (deficit_balanced p G _ hG (SimpleGraph.deleteEdges_le _) hbal phi)

end PartitionedTriangleAbsorption.BalancedHostSeedStage110
