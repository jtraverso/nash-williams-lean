/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassIterationStage74
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FunProp

/-! # Exact physical inverse after sparse deletion

The finite correction induction produces uniformly bounded coefficients and
geometrically vanishing errors. Compactness of the finite coefficient space
gives an exact limit. No linear choice of corrections or external rounding
theorem is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem continuous_load {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) (e : Sym2 V) :
    Continuous (fun psi : Finset V → ℝ => edgeLoad p F J psi e) := by
  unfold edgeLoad
  fun_prop

/-- Produces the correction on the deleted physical graph, with exact loads. -/
theorem deleted_physical_inverse (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (d : Sym2 V → ℝ)
    (hd : RawBalanced (demandCoordinates p d))
    (gamma M delta : ℝ) (hg : 0 < gamma) (hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (hsmall : 72 * delta ≤ gamma ^ 3) (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ M)
    (hzero : ∀ e ∉ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset, d e = 0)
    (hB : DegBounded B (delta * Fintype.card V)) :
    ∃ psi : Finset V → ℝ,
      (∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        edgeLoad p TypedApplicationLinks.F3
          (G.deleteEdges (B : Set (Sym2 V))) psi e = d e) ∧
      (∀ s, |psi s| ≤ 36 * M / (gamma ^ 3 * Fintype.card V)) := by
  classical
  let J := G.deleteEdges (B : Set (Sym2 V))
  have hx := physical_correction_iterations p G hG B d hd gamma M delta hg hM
    hdelta hsmall hn hsize hcap hzero hB
  choose seq hseq using hx
  let cap := 36 * M / (gamma ^ 3 * Fintype.card V)
  have hcap0 : 0 ≤ cap := by dsimp [cap]; positivity
  have hbounded : ∀ k, seq k ∈ Metric.closedBall (0 : Finset V → ℝ) cap := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hcap0).mpr
    intro s
    rw [Real.norm_eq_abs]
    calc
      |seq k s| ≤ (18 * M / (gamma ^ 3 * Fintype.card V)) *
          ∑ i ∈ range k, (1 / (2 : ℝ)) ^ i := (hseq k).1 s
      _ ≤ (18 * M / (gamma ^ 3 * Fintype.card V)) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by positivity)
      _ = cap := by dsimp [cap]; ring
  obtain ⟨psi,hpsi,phi,hphi,hlim⟩ :=
    (isCompact_closedBall (0 : Finset V → ℝ) cap).tendsto_subseq hbounded
  refine ⟨psi,?_,?_⟩
  · intro e heJ
    have heG : e ∈ G.edgeFinset :=
      SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _) heJ
    have hpow : Tendsto (fun k : ℕ => M * (1 / (2 : ℝ)) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / (2 : ℝ)) < 1)).const_mul M
    have hres : Tendsto (fun k => d e - edgeLoad p TypedApplicationLinks.F3 J
        (seq k) e) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ hpow
      intro k
      rw [Real.norm_eq_abs]
      exact (hseq k).2.2.1 e heG
    have hresSub := hres.comp hphi.tendsto_atTop
    have hload : Tendsto (fun k => edgeLoad p TypedApplicationLinks.F3 J
        (seq (phi k)) e) atTop (𝓝 (edgeLoad p TypedApplicationLinks.F3 J psi e)) :=
      (continuous_load p TypedApplicationLinks.F3 J e).tendsto psi |>.comp hlim
    have hother : Tendsto (fun k => d e - edgeLoad p TypedApplicationLinks.F3 J
        (seq (phi k)) e) atTop (𝓝 (d e - edgeLoad p TypedApplicationLinks.F3 J psi e)) :=
      tendsto_const_nhds.sub hload
    have hz : (0 : ℝ) = d e - edgeLoad p TypedApplicationLinks.F3 J psi e :=
      tendsto_nhds_unique hresSub hother
    linarith
  · intro s
    have hnpsi : ‖psi‖ ≤ cap := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hpsi
    have hs : |psi s| ≤ ‖psi‖ := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm psi s)
    exact hs.trans hnpsi

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
