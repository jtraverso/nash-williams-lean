/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassPhysicalInverseStage74
public import PartitionedTriangleAbsorption.SignedRestrictionStage73
public import PartitionedTriangleAbsorption.FourClassBalanceStage74

/-! # Construct the first physical correction in the deleted host

The complete inverse is constructed from the balanced demand. Its restriction
has a certified error 36 delta M / gamma^3 on every surviving physical edge.
No inverse for the deleted graph is supplied as a hypothesis.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deleted_correction_step (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (d : Sym2 V → ℝ)
    (hd : RawBalanced (demandCoordinates p d))
    (gamma M delta : ℝ) (hg : 0 < gamma) (hM : 0 ≤ M)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ M)
    (hB : DegBounded B (delta * Fintype.card V)) :
    ∃ psi : Finset V → ℝ,
      (∀ s, |psi s| ≤ 18 * M / (gamma ^ 3 * Fintype.card V)) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        |d e - edgeLoad p TypedApplicationLinks.F3
          (G.deleteEdges (B : Set (Sym2 V))) psi e| ≤ 36 / gamma ^ 3 * delta * M := by
  obtain ⟨psi,hload,hbound⟩ := physical_inverse p G hG d hd gamma M hg hM hn hsize hcap
  refine ⟨psi,hbound,?_⟩
  have hK : 0 ≤ 18 / gamma ^ 3 := by positivity
  have hpsi : ∀ s, IsCopy p TypedApplicationLinks.F3 G s →
      |psi s| ≤ (18 / gamma ^ 3) * M / Fintype.card V := by
    intro s _
    convert hbound s using 1
    ring
  have he := SignedRestrictionStage73.sparse_deleted_load_error p TypedApplicationLinks.F3
    G B (18 / gamma ^ 3) M delta hK hM hn hB psi hpsi
  intro e heJ
  have heG : e ∈ G.edgeFinset :=
    SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _) heJ
  have hh := he e heJ
  rw [hload e heG] at hh
  convert hh using 1
  ring

theorem load_zero_off_edges {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : SimpleGraph V) [DecidableRel J.Adj]
    (psi : Finset V → ℝ) (e : Sym2 V) (he : e ∉ J.edgeFinset) :
    edgeLoad p F J psi e = 0 := by
  unfold edgeLoad
  apply sum_eq_zero
  intro s hs
  obtain ⟨hs,heS⟩ := mem_filter.mp hs
  exact False.elim (he (TypedNibble.triEdges_subset_of_isCopy
    (TypedNibble.mem_copies_iff.mp hs) heS))

/-- The new residual remains in the same balanced, surviving-edge space. -/
theorem supported_correction_step (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (d : Sym2 V → ℝ)
    (hd : RawBalanced (demandCoordinates p d))
    (gamma M delta : ℝ) (hg : 0 < gamma) (hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ M)
    (hzero : ∀ e ∉ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset, d e = 0)
    (hB : DegBounded B (delta * Fintype.card V)) :
    ∃ psi : Finset V → ℝ,
      (∀ s, |psi s| ≤ 18 * M / (gamma ^ 3 * Fintype.card V)) ∧
      RawBalanced (demandCoordinates p (fun e => d e - edgeLoad p TypedApplicationLinks.F3
        (G.deleteEdges (B : Set (Sym2 V))) psi e)) ∧
      (∀ e ∈ G.edgeFinset, |d e - edgeLoad p TypedApplicationLinks.F3
        (G.deleteEdges (B : Set (Sym2 V))) psi e| ≤ 36 / gamma ^ 3 * delta * M) ∧
      (∀ e ∉ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        d e - edgeLoad p TypedApplicationLinks.F3
          (G.deleteEdges (B : Set (Sym2 V))) psi e = 0) := by
  obtain ⟨w,hw,hbound⟩ := physical_inverse_data p G hG d hd gamma M hg hM hn hsize hcap
  let psi := physicalWeights p w
  let J := G.deleteEdges (B : Set (Sym2 V))
  have hload := load_eq_of_boundary p G hG w d hw
  have hpsi : ∀ s, |psi s| ≤ 18 * M / (gamma ^ 3 * Fintype.card V) :=
    physicalWeights_bound p w _ (by positivity) hbound
  have hrzero : ∀ e ∉ J.edgeFinset, d e - edgeLoad p TypedApplicationLinks.F3 J psi e = 0 := by
    intro e he
    rw [hzero e he, load_zero_off_edges p TypedApplicationLinks.F3 J psi e he, sub_self]
  refine ⟨psi,hpsi,residual_balanced p G J hG d hd w,?_,hrzero⟩
  have hK : 0 ≤ 18 / gamma ^ 3 := by positivity
  have hc : ∀ s, IsCopy p TypedApplicationLinks.F3 G s →
      |psi s| ≤ (18 / gamma ^ 3) * M / Fintype.card V := by
    intro s _
    convert hpsi s using 1
    ring
  have he := SignedRestrictionStage73.sparse_deleted_load_error p TypedApplicationLinks.F3
    G B (18 / gamma ^ 3) M delta hK hM hn hB psi hc
  intro e heG
  by_cases heJ : e ∈ J.edgeFinset
  · have hh := he e heJ
    rw [hload e heG] at hh
    convert hh using 1
    ring
  · rw [hrzero e heJ, abs_zero]
    positivity

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
