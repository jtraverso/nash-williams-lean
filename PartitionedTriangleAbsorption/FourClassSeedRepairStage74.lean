/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassDeletedInverseStage74
public import PartitionedTriangleAbsorption.FractionalConsumerStage72

/-! # Construct a positive exact seed from a balanced physical deficit

Balance is an explicit pair-total condition on the deficit, not a supplied
correction. The deleted-host inverse constructs that correction here.
Deriving this condition from the neutral-reserve charge ledger remains an
independent bridge; the reserve itself is not constructed by this theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem positive_seed_of_balanced_deficit (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (gamma C eps delta : ℝ)
    (hg : 0 < gamma) (hC : 1 ≤ C) (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hsmall : 72 * delta ≤ gamma ^ 3) (hbudget : 72 * C * eps ≤ gamma ^ 3)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hB : DegBounded B (delta * Fintype.card V)) (phi : Finset V → ℝ)
    (hseed : IsRegularAlmostPacking p TypedApplicationLinks.F3
      (G.deleteEdges (B : Set (Sym2 V))) C eps phi)
    (hbalance : RawBalanced (demandCoordinates p (fun e =>
      if e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset then
        1 - edgeLoad p TypedApplicationLinks.F3 (G.deleteEdges (B : Set (Sym2 V))) phi e
      else 0))) :
    ∃ psi : Finset V → ℝ,
      (∀ s, IsCopy p TypedApplicationLinks.F3 (G.deleteEdges (B : Set (Sym2 V))) s →
        0 ≤ psi s ∧ psi s ≤ (2 * C) / Fintype.card V) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        edgeLoad p TypedApplicationLinks.F3 (G.deleteEdges (B : Set (Sym2 V))) psi e = 1 := by
  classical
  let J := G.deleteEdges (B : Set (Sym2 V))
  let d := fun e => if e ∈ J.edgeFinset then
    1 - edgeLoad p TypedApplicationLinks.F3 J phi e else 0
  have hd : ∀ e ∈ G.edgeFinset, |d e| ≤ eps := by
    intro e _
    by_cases he : e ∈ J.edgeFinset
    · obtain ⟨hlo,hhi⟩ := hseed.2 e he
      change 1 - eps ≤ edgeLoad p TypedApplicationLinks.F3 J phi e at hlo
      change edgeLoad p TypedApplicationLinks.F3 J phi e ≤ 1 at hhi
      dsimp [d]
      rw [ite_eq_left he, abs_of_nonneg (by linarith)]
      linarith
    · simpa only [d, ite_eq_right he, abs_zero] using heps
  have hz : ∀ e ∉ J.edgeFinset, d e = 0 := by
    intro e he
    exact ite_eq_right he
  obtain ⟨chi,hload,hcap⟩ := deleted_physical_inverse p G hG B d hbalance
    gamma eps delta hg heps hdelta hsmall hn hsize hd hz hB
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hCpos : 0 < C := by linarith
  have hc : ∀ s, IsCopy p TypedApplicationLinks.F3 J s →
      |chi s| ≤ 1 / (2 * C * Fintype.card V) := by
    intro s _
    apply (hcap s).trans
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_right hbudget hnR.le
    convert hh using 1 <;> ring
  have hl : ∀ e ∈ J.edgeFinset, edgeLoad p TypedApplicationLinks.F3 J chi e =
      1 - edgeLoad p TypedApplicationLinks.F3 J phi e := by
    intro e he
    simpa only [d, ite_eq_left he] using hload e he
  exact ⟨fun s => phi s + chi s,
    FractionalConsumerStage72.repaired_seed p TypedApplicationLinks.F3 J C hC hn
      phi chi hseed.1 hc hl⟩

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
