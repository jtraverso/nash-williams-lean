/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.BalancedLinearRepair
import Mathlib.LinearAlgebra.Pi

/-!
# Linear transport of indexed weights to physical mixed copies

An injective family of actual copies gives a norm-preserving linear transport
from indexed weights to the project's weights on `Finset V`. The load formula
is a finite interchange of sums. No surjectivity onto all copies is required.
-/

namespace PartitionedTriangleAbsorption.F0Direct.PhysicalWeightTransport

open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def pushWeights (T : I → Finset V) : (I → ℝ) →ₗ[ℝ] (Finset V → ℝ) :=
  ∑ i : I, (LinearMap.proj i).smulRight (Pi.single (T i) 1)

theorem pushWeights_apply (T : I → Finset V) (w : I → ℝ) (s : Finset V) :
    pushWeights T w s = ∑ i : I, if T i = s then w i else 0 := by
  classical
  simp only [pushWeights, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  apply sum_congr rfl
  intro i _
  by_cases h : T i = s
  · simp [h]
  · simp [h, Ne.symm h]

theorem pushWeights_at (T : I → Finset V) (hT : Function.Injective T)
    (w : I → ℝ) (i : I) : pushWeights T w (T i) = w i := by
  classical
  rw [pushWeights_apply]
  simp only [hT.eq_iff]
  simp

theorem pushWeights_off (T : I → Finset V) (w : I → ℝ) (s : Finset V)
    (hs : s ∉ Set.range T) : pushWeights T w s = 0 := by
  classical
  rw [pushWeights_apply]
  apply sum_eq_zero
  intro i _
  have hi : T i ≠ s := fun h => hs ⟨i, h⟩
  simp [hi]

theorem pushWeights_abs_le (T : I → Finset V) (hT : Function.Injective T)
    (w : I → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ i, |w i| ≤ M)
    (s : Finset V) : |pushWeights T w s| ≤ M := by
  classical
  by_cases hs : s ∈ Set.range T
  · obtain ⟨i, rfl⟩ := hs
    rw [pushWeights_at T hT]
    exact hw i
  · rw [pushWeights_off T w s hs, abs_zero]
    exact hM

theorem edgeLoad_single (p : V → Fin 2) (J : SimpleGraph V)
    (s : Finset V) (hs : s ∈ copies p F0 J) (c : ℝ) (e : Sym2 V) :
    edgeLoad p F0 J (Pi.single s c) e = if e ∈ triEdges s then c else 0 := by
  classical
  simp only [edgeLoad, Pi.single_apply]
  by_cases he : e ∈ triEdges s
  · simp [hs, he]
  · simp [hs, he]

theorem edgeLoad_pushWeights (p : V → Fin 2) (J : SimpleGraph V)
    (T : I → Finset V) (hT : ∀ i, T i ∈ copies p F0 J)
    (w : I → ℝ) (e : Sym2 V) :
    edgeLoad p F0 J (pushWeights T w) e =
      ∑ i : I, if e ∈ triEdges (T i) then w i else 0 := by
  classical
  simp only [edgeLoad, pushWeights, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Finset.sum_apply]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  change edgeLoad p F0 J (w i • Pi.single (T i) 1) e = _
  have hfun : w i • Pi.single (T i) (1 : ℝ) = Pi.single (T i) (w i) := by
    ext s
    simp [Pi.single_apply, mul_ite]
  rw [hfun, edgeLoad_single p J (T i) (hT i)]

#print axioms pushWeights_abs_le
#print axioms edgeLoad_pushWeights

end PartitionedTriangleAbsorption.F0Direct.PhysicalWeightTransport
