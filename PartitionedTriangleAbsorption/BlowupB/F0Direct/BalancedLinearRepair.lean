/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.F0RigidBoost
import PartitionedTriangleAbsorption.BlowupB.F0Direct.LinearRepair
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The finite-dimensional repair lemma on the actual F0 demand space

The domain is the kernel of the F0 balance functional on functions on the
physical edges of the host. The boundary map of actual mixed copies lands
in that kernel by the previously proved annihilator identity.

The final theorem converts a linear approximate inverse with half-error into
the existing `F0RigidBoost.HasBoundedBalancedInverse` interface. Construction
of the approximate inverse from the geometric assumptions is a separate step.
-/

namespace PartitionedTriangleAbsorption.F0Direct.BalancedLinearRepair

open Finset TypedLoadNecessity TypedApplicationLinks F0RigidBoost
  TypedLoadFamilies F0ParallelObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev HostEdge (J : SimpleGraph V) [DecidableRel J.Adj] :=
  {e : Sym2 V // e ∈ J.edgeFinset}

noncomputable def balanceMap (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj] : (HostEdge J → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ e : HostEdge J, gFun p e.val * x e
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

noncomputable abbrev BalancedDemand (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj] := (balanceMap p J).ker

noncomputable def loadMap (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj] : (Finset V → ℝ) →ₗ[ℝ] (HostEdge J → ℝ) where
  toFun w e := edgeLoad p F0 J w e.val
  map_add' x y := by
    funext e
    exact F0RigidBoost.edgeLoad_add p J x y e.val
  map_smul' c x := by
    funext e
    simp only [edgeLoad, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

theorem loadMap_balanced (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj] (w : Finset V → ℝ) :
    loadMap p J w ∈ BalancedDemand p J := by
  change ∑ e : HostEdge J, gFun p e.val * edgeLoad p F0 J w e.val = 0
  rw [← Finset.sum_subtype J.edgeFinset (fun _ => Iff.rfl)
    (fun e => gFun p e * edgeLoad p F0 J w e)]
  exact annihilator_load_identity p F0 J w annihilates_F0

noncomputable def boundary (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj] : (Finset V → ℝ) →ₗ[ℝ] BalancedDemand p J :=
  (loadMap p J).codRestrict (BalancedDemand p J) (loadMap_balanced p J)

/-- A concrete half-error linear inverse on the balanced physical edge space
implies the existing bounded balanced inverse interface with constant `2K`.
Values of the input away from host edges are discarded at the start. -/
theorem hasBoundedBalancedInverse_of_half_error
    (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (K : ℝ) (hK : 0 ≤ K)
    (T : BalancedDemand p J →ₗ[ℝ] (Finset V → ℝ))
    (hbound : ∀ x : BalancedDemand p J,
      ‖T x‖ ≤ (K / Fintype.card V) * ‖x‖)
    (herror : ∀ x : BalancedDemand p J,
      ‖x - boundary p J (T x)‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    HasBoundedBalancedInverse p J (2 * K) := by
  intro x M hM hx hbalance
  let g : BalancedDemand p J :=
    ⟨fun e => x e.val, by
      change ∑ e : HostEdge J, gFun p e.val * x e.val = 0
      rw [← Finset.sum_subtype J.edgeFinset (fun _ => Iff.rfl)
        (fun e => gFun p e * x e)]
      exact hbalance⟩
  have hg : ‖g‖ ≤ M := by
    change ‖(fun e : HostEdge J => x e.val)‖ ≤ M
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro e
    simpa only [Real.norm_eq_abs] using hx e.val e.property
  have hC : 0 ≤ K / (Fintype.card V : ℝ) := div_nonneg hK (Nat.cast_nonneg _)
  obtain ⟨w, hw, hnorm⟩ := LinearRepair.exact_repair_of_half_error
    (boundary p J) T (K / Fintype.card V) hC hbound herror g
  refine ⟨w, ?_, ?_⟩
  · intro e he
    have h := congrArg (fun z : BalancedDemand p J => z.val ⟨e, he⟩) hw
    exact h
  · intro s _
    have hs : |w s| ≤ ‖w‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm w s
    calc
      |w s| ≤ ‖w‖ := hs
      _ ≤ (2 * (K / Fintype.card V)) * ‖g‖ := hnorm
      _ ≤ (2 * (K / Fintype.card V)) * M :=
        mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num) hC)
      _ = (2 * K) * M / Fintype.card V := by ring

#print axioms loadMap_balanced
#print axioms hasBoundedBalancedInverse_of_half_error

end PartitionedTriangleAbsorption.F0Direct.BalancedLinearRepair
