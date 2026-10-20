/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateAbsorberProducerStage101
public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse
public import Mathlib.Data.Real.Archimedean

/-! # Global F1 normality by rounding its one-dimensional kernel

This is only a global type-vector statement. It does not assert normality of
vertex-link semigroups or produce a decomposition of the whole host graph.
The final theorem constructs a physical absorber for a given residue.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1PositiveStage166

open Finset TypedApplicationLinks TypedDivisibilityCollapse TypedTransformer
  PairMoveSelectionStage85 PairMoveAssemblyStage85

def kernelSign (tau : Multiset (Fin 4)) : ℤ :=
  if tau ∈ ({{0, 0, 2}, {1, 1, 3}, {1, 2, 2}, {0, 3, 3}} : Finset _) then 1 else -1

private theorem signs :
    kernelSign {0, 0, 2} = 1 ∧ kernelSign {0, 0, 3} = -1 ∧
    kernelSign {1, 1, 2} = -1 ∧ kernelSign {1, 1, 3} = 1 ∧
    kernelSign {0, 2, 2} = -1 ∧ kernelSign {1, 2, 2} = 1 ∧
    kernelSign {0, 3, 3} = 1 ∧ kernelSign {1, 3, 3} = -1 := by decide

theorem F1_kernel_zero :
    (∑ tau ∈ F1, kernelSign tau • typeEdgeVec tau) = 0 := by
  simp only [F1]
  repeat rw [sum_insert (by decide)]
  rw [sum_singleton]
  rcases signs with ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩
  simp only [s0, s1, s2, s3, s4, s5, s6, s7]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeEdgeVec, Pi.add_apply]

/-- Every two real global representations differ along the displayed kernel. -/
theorem F1_global_coefficients_kernel (c d : Multiset (Fin 4) → ℝ)
    (h : (∑ tau ∈ F1, c tau • fun i j => (typeEdgeVec tau i j : ℝ)) =
      ∑ tau ∈ F1, d tau • fun i j => (typeEdgeVec tau i j : ℝ)) :
    ∃ t : ℝ, ∀ tau ∈ F1, d tau = c tau + t * kernelSign tau := by
  simp only [F1] at h
  repeat rw [sum_insert (by decide)] at h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h22 := congrFun (congrFun h 2) 2
  have h33 := congrFun (congrFun h 3) 3
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h12 := congrFun (congrFun h 1) 2
  simp [typeEdgeVec, sum_singleton, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Multiset.count_cons] at h00 h11 h22 h33 h02 h03 h12
  rcases signs with ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩
  simp only [Multiset.insert_eq_cons] at s0 s1 s2 s3 s4 s5 s6 s7
  refine ⟨d {0, 0, 2} - c {0, 0, 2}, ?_⟩
  intro tau htau
  simp only [F1, mem_insert, mem_singleton] at htau
  rcases htau with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num only [s0, s1, s2, s3, s4, s5, s6, s7, Multiset.insert_eq_cons,
      Int.cast_one, Int.cast_neg, mul_one, mul_neg]
    linarith only [h00, h11, h22, h33, h02, h03, h12]

variable {V : Type}

/-- Integral endpoints of the feasible interval permit rounding upward. -/
theorem F1_nonnegative_global_coefficients (p : V → Fin 4) (P : Finset (Sym2 V))
    (hI : ∃ c : Multiset (Fin 4) → ℤ,
      edgeVec p P = ∑ tau ∈ F1, c tau • typeEdgeVec tau)
    (hR : ∃ c : Multiset (Fin 4) → ℝ, (∀ tau, 0 ≤ c tau) ∧
      (fun i j => (edgeVec p P i j : ℝ)) =
        ∑ tau ∈ F1, c tau • fun i j => (typeEdgeVec tau i j : ℝ)) :
    ∃ c : Multiset (Fin 4) → ℕ,
      edgeVec p P = ∑ tau ∈ F1, (c tau : ℤ) • typeEdgeVec tau := by
  obtain ⟨cI, hcI⟩ := hI
  obtain ⟨cR, hnR, hcR⟩ := hR
  have heq : (∑ tau ∈ F1, (cI tau : ℝ) • fun i j => (typeEdgeVec tau i j : ℝ)) =
      ∑ tau ∈ F1, cR tau • fun i j => (typeEdgeVec tau i j : ℝ) := by
    rw [← hcR]
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h := congrFun (congrFun hcI i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact_mod_cast h.symm
  obtain ⟨t, ht⟩ := F1_global_coefficients_kernel (fun tau => (cI tau : ℝ)) cR heq
  let z : Multiset (Fin 4) → ℤ := fun tau => cI tau + Int.ceil t * kernelSign tau
  have hz : ∀ tau ∈ F1, 0 ≤ z tau := by
    intro tau htau
    have hr := hnR tau
    rw [ht tau htau] at hr
    by_cases hs : tau ∈ ({{0, 0, 2}, {1, 1, 3}, {1, 2, 2}, {0, 3, 3}} : Finset _)
    · simp only [kernelSign, if_pos hs, Int.cast_one, mul_one] at hr
      have hc : t ≤ (Int.ceil t : ℝ) := Int.le_ceil t
      have hzR : (0 : ℝ) ≤ (cI tau : ℝ) + (Int.ceil t : ℝ) := by linarith
      dsimp [z]
      simp only [kernelSign, if_pos hs, mul_one]
      exact_mod_cast hzR
    · simp only [kernelSign, if_neg hs, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at hr
      have hc : Int.ceil t ≤ cI tau := Int.ceil_le.mpr (by linarith)
      dsimp [z]
      simp only [kernelSign, if_neg hs, mul_neg, mul_one]
      omega
  have hrep : edgeVec p P = ∑ tau ∈ F1, z tau • typeEdgeVec tau := by
    rw [hcI]
    simp only [z, add_smul, mul_smul]
    rw [sum_add_distrib, ← smul_sum, F1_kernel_zero, smul_zero, add_zero]
  refine ⟨fun tau => (z tau).toNat, ?_⟩
  rw [hrep]
  apply sum_congr rfl
  intro tau htau
  rw [Int.toNat_of_nonneg (hz tau htau)]

variable [DecidableEq V]

theorem F1_coefficients_of_divisibility (p : V → Fin 4) (P : Finset (Sym2 V))
    (hI : IsIntDiv p F1 P) (hR : IsFracDiv p F1 P) :
    ∃ c : Multiset (Fin 4) → ℕ,
      edgeVec p P = ∑ tau ∈ F1, (c tau : ℤ) • typeEdgeVec tau :=
  F1_nonnegative_global_coefficients p P hI.1 hR.1

variable [Fintype V]

theorem F1_private_absorber (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (a d : ℝ) (hs : CompatibleSupply p F1 G a)
    (B P : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d) (hPG : P ⊆ G.edgeFinset)
    (hPB : Disjoint P B) (hZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z)
    (hI : IsIntDiv p F1 P)
    (hR : ∃ c : Multiset (Fin 4) → ℝ, (∀ tau, 0 ≤ c tau) ∧
      (fun i j => (edgeVec p P i j : ℝ)) =
        ∑ tau ∈ F1, c tau • fun i j => (typeEdgeVec tau i j : ℝ))
    (hb : (Z.card : ℝ) + 382 * P.card + 4 * (d + P.card) < a) :
    ∃ A, Absorbs (p := p) (F := F1) A P ∧ Disjoint A B ∧
      A.card ≤ 93 * P.card ∧ A ⊆ G.edgeFinset := by
  obtain ⟨c, hc⟩ := F1_nonnegative_global_coefficients p P hI.1 hR
  apply PrivateAbsorberStage101.private_absorber_of_nonnegative_coefficients
    G a d F1_three_step (by decide) hs B P Z hB hd hPG hPB hZ
    (active_of_isIntDiv (by decide) hI) _ c hc hb
  exact even_of_isIntDiv (by decide)
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hPG he))) hI

end PartitionedTriangleAbsorption.F1PositiveStage166

end

