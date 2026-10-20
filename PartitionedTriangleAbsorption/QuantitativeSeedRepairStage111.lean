/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BalancedHostSeedStage110

/-! # Repair with an explicit, additive weight budget

The actual correction is constructed by the existing physical inverse. The
input permits loads on either side of one; no corrected seed is supplied.
The complete four-class ambient host and sparse deletion bound are essential.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.QuantitativeSeedRepairStage111

open Finset TypedLoadNecessity TypedApplicationLinks FourClassCopyAdapterStage74
  BalancedHostSeedStage110 CoverDownStage105

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem repair_with_explicit_error (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (gamma eps delta : ℝ)
    (hg : 0 < gamma) (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hsmall : 72 * delta ≤ gamma ^ 3) (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hB : DegBounded B (delta * Fintype.card V)) (phi : Finset V → ℝ)
    (herror : ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
      |1 - edgeLoad p F3 (G.deleteEdges (B : Set (Sym2 V))) phi e| ≤ eps)
    (hbal : ∀ k : Fin 2, bal p k (G.deleteEdges (B : Set (Sym2 V))).edgeFinset = 0) :
    ∃ psi : Finset V → ℝ,
      (∀ s, |psi s - phi s| ≤ 36 * eps / (gamma ^ 3 * Fintype.card V)) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        edgeLoad p F3 (G.deleteEdges (B : Set (Sym2 V))) psi e = 1 := by
  classical
  let J := G.deleteEdges (B : Set (Sym2 V))
  let d := fun e => if e ∈ J.edgeFinset then 1 - edgeLoad p F3 J phi e else 0
  have hd : FourClassInverseStage73.RawBalanced (demandCoordinates p d) :=
    deficit_balanced p G J hG (SimpleGraph.deleteEdges_le _) hbal phi
  have hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ eps := by
    intro e _
    by_cases he : e ∈ J.edgeFinset
    · simpa only [d, ite_eq_left he] using herror e he
    · simpa only [d, ite_eq_right he, abs_zero] using heps
  obtain ⟨chi, hload, hchi⟩ := deleted_physical_inverse p G hG B d hd
    gamma eps delta hg heps hdelta hsmall hn hsize hcap
    (fun e he => ite_eq_right he) hB
  refine ⟨fun s => phi s + chi s, ?_, ?_⟩
  · intro s
    simpa only [add_sub_cancel_left] using hchi s
  · intro e he
    have hl : edgeLoad p F3 J chi e = 1 - edgeLoad p F3 J phi e := by
      have hh := hload e he
      change edgeLoad p F3 J chi e = d e at hh
      dsimp only [d] at hh
      rw [ite_eq_left he] at hh
      exact hh
    unfold edgeLoad
    rw [sum_add_distrib]
    change edgeLoad p F3 J phi e + edgeLoad p F3 J chi e = 1
    rw [hl]
    ring

/-- A cumulative window implies the same regularity constant at every step.
This arithmetic lemma does not select a host, a reserve, or a vortex. -/
theorem regular_of_window (p : V → Fin 4) (J : SimpleGraph V)
    [DecidableRel J.Adj] (C E : ℝ) (hC : 1 ≤ C) (hn : 0 < Fintype.card V)
    (hE : E ≤ 1 / (2 * C)) (psi : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F3 J s →
      (1 / C - E) / Fintype.card V ≤ psi s ∧
        psi s ≤ (C + E) / Fintype.card V)
    (hl : ∀ e ∈ J.edgeFinset, edgeLoad p F3 J psi e = 1) :
    IsRegularAlmostPacking p F3 J (2 * C) 0 psi := by
  have hCp : 0 < C := by linarith
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hhalf : 1 / (2 * C) ≤ C := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
    nlinarith
  have heq : 1 / (2 * C * Fintype.card V) = (1 / (2 * C)) / Fintype.card V := by
    field_simp
  have hlo : 1 / (2 * C) ≤ 1 / C - E := by
    have hh : 1 / C = 2 * (1 / (2 * C)) := by field_simp
    linarith
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨hslo, hshi⟩ := hw s hs
    constructor
    · rw [heq]
      exact (div_le_div_of_nonneg_right hlo hnR.le).trans hslo
    · exact hshi.trans (div_le_div_of_nonneg_right (by linarith) hnR.le)
  · intro e he
    change 1 - 0 ≤ edgeLoad p F3 J psi e ∧ edgeLoad p F3 J psi e ≤ 1
    rw [hl e he]
    norm_num

end PartitionedTriangleAbsorption.QuantitativeSeedRepairStage111
