/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassDeletedStepStage74
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual physical corrections, iterated on the same deleted host

The residual is balanced and supported on the surviving edges at every step.
The corrections need not be chosen linearly: their uniform bound suffices.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem load_add {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) (psi chi : Finset V → ℝ) (e : Sym2 V) :
    edgeLoad p F J (fun s => psi s + chi s) e =
      edgeLoad p F J psi e + edgeLoad p F J chi e := by
  simp only [edgeLoad, sum_add_distrib]

theorem physical_correction_iterations (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B : Finset (Sym2 V)) (d : Sym2 V → ℝ)
    (hd : RawBalanced (demandCoordinates p d))
    (gamma M delta : ℝ) (hg : 0 < gamma) (hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (hsmall : 72 * delta ≤ gamma ^ 3) (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ M)
    (hzero : ∀ e ∉ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset, d e = 0)
    (hB : DegBounded B (delta * Fintype.card V)) (k : ℕ) :
    ∃ psi : Finset V → ℝ,
      (∀ s, |psi s| ≤ (18 * M / (gamma ^ 3 * Fintype.card V)) *
        ∑ i ∈ range k, (1 / (2 : ℝ)) ^ i) ∧
      RawBalanced (demandCoordinates p (fun e => d e - edgeLoad p TypedApplicationLinks.F3
        (G.deleteEdges (B : Set (Sym2 V))) psi e)) ∧
      (∀ e ∈ G.edgeFinset, |d e - edgeLoad p TypedApplicationLinks.F3
        (G.deleteEdges (B : Set (Sym2 V))) psi e| ≤ M * (1 / (2 : ℝ)) ^ k) ∧
      (∀ e ∉ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        d e - edgeLoad p TypedApplicationLinks.F3
          (G.deleteEdges (B : Set (Sym2 V))) psi e = 0) := by
  let J := G.deleteEdges (B : Set (Sym2 V))
  have hq : 36 / gamma ^ 3 * delta ≤ 1 / (2 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hg _)]
    linarith
  induction k with
  | zero =>
    refine ⟨fun _ => 0,?_,?_,?_,?_⟩
    · simp
    · simpa only [edgeLoad, sum_const_zero, sub_zero] using hd
    · simpa only [edgeLoad, sum_const_zero, sub_zero, pow_zero, mul_one] using hcap
    · simpa only [edgeLoad, sum_const_zero, sub_zero] using hzero
  | succ k ih =>
    obtain ⟨psi,hpsi,hr,hrcap,hrzero⟩ := ih
    let r := fun e => d e - edgeLoad p TypedApplicationLinks.F3 J psi e
    obtain ⟨chi,hchi,hs,hscap,hszero⟩ := supported_correction_step p G hG B r hr
      gamma (M * (1 / (2 : ℝ)) ^ k) delta hg (by positivity) hdelta hn hsize
      hrcap hrzero hB
    have heq : (fun e => r e - edgeLoad p TypedApplicationLinks.F3 J chi e) =
        (fun e => d e - edgeLoad p TypedApplicationLinks.F3 J
          (fun s => psi s + chi s) e) := by
      funext e
      rw [load_add]
      dsimp [r]
      ring
    rw [heq] at hs
    have hszero' : ∀ e ∉ J.edgeFinset,
        d e - edgeLoad p TypedApplicationLinks.F3 J (fun s => psi s + chi s) e = 0 := by
      intro e he
      rw [← congrFun heq e]
      exact hszero e he
    refine ⟨fun s => psi s + chi s,?_,hs,?_,hszero'⟩
    · intro s
      calc
        |psi s + chi s| ≤ |psi s| + |chi s| := abs_add_le _ _
        _ ≤ (18 * M / (gamma ^ 3 * Fintype.card V)) *
            (∑ i ∈ range k, (1 / (2 : ℝ)) ^ i) +
            18 * (M * (1 / (2 : ℝ)) ^ k) / (gamma ^ 3 * Fintype.card V) :=
          add_le_add (hpsi s) (hchi s)
        _ = (18 * M / (gamma ^ 3 * Fintype.card V)) *
            ∑ i ∈ range (k + 1), (1 / (2 : ℝ)) ^ i := by
          rw [sum_range_succ]
          ring
    · intro e he
      have hh := hscap e he
      change |(fun e => r e - edgeLoad p TypedApplicationLinks.F3 J chi e) e| ≤ _ at hh
      rw [heq] at hh
      calc
        |d e - edgeLoad p TypedApplicationLinks.F3 J (fun s => psi s + chi s) e| ≤
            36 / gamma ^ 3 * delta * (M * (1 / (2 : ℝ)) ^ k) := hh
        _ ≤ (1 / (2 : ℝ)) * (M * (1 / (2 : ℝ)) ^ k) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
        _ = M * (1 / (2 : ℝ)) ^ (k + 1) := by rw [pow_succ]; ring

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
