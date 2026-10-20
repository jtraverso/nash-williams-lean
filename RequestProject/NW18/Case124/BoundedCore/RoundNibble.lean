/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.RegularThinning
public import RequestProject.NW18.Case124.BoundedCore.NibbleBridge

@[expose] public section

/-! The protected nibble leaves a maximum-degree-small physical leftover.
The estimate covers ALL stars, including stars below the EGJ monitor threshold.
All constants are chosen before the graph and the protected edge sets. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption

theorem protected_nibble_max_degree :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ →
      ∃ θ : ℝ, 0 < θ ∧ ∀ a : ℝ, 0 < a → ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (F Res : Finset (Sym2 V)) (W : Finset V) (dF dRes : ℕ),
        N ≤ Fintype.card V →
        (3 / 4 - θ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal β G →
        (∀ v, (F.filter (fun e => v ∈ e)).card ≤ dF) →
        (∀ v, (Res.filter (fun e => v ∈ e)).card ≤ dRes) →
        ((dF + dRes + W.card : ℕ) : ℝ) ≤ θ * Fintype.card V →
        ∃ Ep : Finset (Sym2 V),
          Ep ⊆ (del G (F ∪ Res ∪ W.sym2)).edgeFinset ∧
          HasDecomp onePart K3fam Ep ∧
          ∀ v, ((((del G (F ∪ Res ∪ W.sym2)).edgeFinset \ Ep).filter
            (fun e => v ∈ e)).card : ℝ) ≤ a * Fintype.card V := by
  obtain ⟨β₀, hβ₀, hnibble⟩ := protected_nibble
  refine ⟨β₀, hβ₀, fun β hβ hβlim => ?_⟩
  obtain ⟨θ, hθ, hnibble⟩ := hnibble β hβ hβlim
  refine ⟨θ, hθ, fun a ha => ?_⟩
  obtain ⟨N₁, hpack⟩ := hnibble a ha 1
  obtain ⟨N₂, hcut⟩ := exists_quarter_cutoff a ha
  refine ⟨max N₁ N₂, fun V _ _ G _ F Res W dF dRes hN hdeg hnx hF hRes hbudget => ?_⟩
  classical
  let J := del G (F ∪ Res ∪ W.sym2)
  let S : V → Finset (Sym2 V) := fun v => J.edgeFinset.filter (fun e => v ∈ e)
  obtain ⟨P, hP, hdisj, hmon⟩ := hpack V G F Res ∅ W dF dRes 0
    (le_trans (le_max_left _ _) hN) hdeg hnx hF hRes (by simp) (by simpa using hbudget)
    V S (by simp) (fun v => by simp [J, S])
  simp only [union_empty] at hP hmon
  have hclique : ∀ t ∈ P, J.IsNClique 3 t := fun t ht =>
    SimpleGraph.mem_cliqueFinset_iff.mp (hP ht)
  have hphysical : (P : Set (Finset V)).PairwiseDisjoint triEdges := by
    intro t ht t' ht' hne
    change Disjoint (BKLOIface.triEdges t) (BKLOIface.triEdges t')
    exact hdisj t ht t' ht' hne
  have hstars : ∀ v, 6 * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤
      ((J.edgeFinset.filter (fun e => v ∈ e)).card : ℝ) →
      (((J.edgeFinset.filter (fun e => v ∈ e)) \ P.biUnion triEdges).card : ℝ) ≤
        a * (J.edgeFinset.filter (fun e => v ∈ e)).card := by
    intro v hv
    change (((S v) \ P.biUnion BKLOIface.triEdges).card : ℝ) ≤ a * (S v).card
    exact hmon v hv
  change ∃ Ep ⊆ J.edgeFinset,
    HasDecomp (fun _ : V => (0 : Fin 1)) ({{0, 0, 0}} : Finset (Multiset (Fin 1))) Ep ∧
    ∀ v, (((J.edgeFinset \ Ep).filter (fun e => v ∈ e)).card : ℝ) ≤ a * Fintype.card V
  exact physical_nibble_bridge J P a ha hclique hphysical
    (hcut (Fintype.card V) (le_trans (le_max_right _ _) hN)) hstars

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.protected_nibble_max_degree
