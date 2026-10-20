/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.BalancedLinearRepair
import PartitionedTriangleAbsorption.BlowupB.F0Direct.CrossCompletion
import PartitionedTriangleAbsorption.PackingRestriction

/-! # Restricting a balanced inverse after sparse edge deletions

The weights are evaluated by the actual copy system of the smaller graph.
The approximation error is precisely the load of discarded copies.  A uniform
bound on their number therefore gives the half-error input of the convergent
linear repair theorem.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.InverseRestriction

open Finset TypedApplicationLinks TypedLoadNecessity F0RigidBoost PackingRestriction
open PartitionedTriangleAbsorption.F0Direct.BalancedLinearRepair

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def extendValue (J : SimpleGraph V) [DecidableRel J.Adj]
    (x : HostEdge J → ℝ) (e : Sym2 V) : ℝ :=
  if he : e ∈ J.edgeFinset then x ⟨e,he⟩ else 0

@[simp] theorem extendValue_host (J : SimpleGraph V) [DecidableRel J.Adj]
    (x : HostEdge J → ℝ) (e : Sym2 V) (he : e ∈ J.edgeFinset) :
    extendValue J x e = x ⟨e,he⟩ := by simp [extendValue, he]

theorem extendValue_balance (p : V → Fin 2) (J H : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel H.Adj] (hJH : J ≤ H)
    (x : BalancedDemand p J) :
    (∑ e : HostEdge H, gFun p e.val * extendValue J x.val e.val) = 0 := by
  classical
  rw [← Finset.sum_subtype H.edgeFinset (fun _ => Iff.rfl)
    (fun e => gFun p e * extendValue J x.val e)]
  calc
    _ = ∑ e ∈ J.edgeFinset, gFun p e * extendValue J x.val e := by
      symm
      apply Finset.sum_subset (SimpleGraph.edgeFinset_mono hJH)
      intro e _ he
      simp [extendValue, he]
    _ = ∑ e : HostEdge J, gFun p e.val * x.val e := by
      rw [Finset.sum_subtype J.edgeFinset (fun _ => Iff.rfl)
        (fun e => gFun p e * extendValue J x.val e)]
      apply Finset.sum_congr rfl
      intro e _
      rw [extendValue_host J x.val e.val e.property]
    _ = 0 := x.property

noncomputable def extendDemand (p : V → Fin 2) (J H : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel H.Adj] (hJH : J ≤ H) :
    BalancedDemand p J →ₗ[ℝ] BalancedDemand p H where
  toFun x := ⟨fun e => extendValue J x.val e.val, extendValue_balance p J H hJH x⟩
  map_add' x y := by
    ext e
    change extendValue J (x.val + y.val) e.val =
      extendValue J x.val e.val + extendValue J y.val e.val
    unfold extendValue
    split_ifs <;> simp
  map_smul' c x := by
    ext e
    change extendValue J (c • x.val) e.val = c * extendValue J x.val e.val
    unfold extendValue
    split_ifs <;> simp

theorem extendDemand_norm_le (p : V → Fin 2) (J H : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel H.Adj] (hJH : J ≤ H)
    (x : BalancedDemand p J) : ‖extendDemand p J H hJH x‖ ≤ ‖x‖ := by
  change ‖(fun e : HostEdge H => extendValue J x.val e.val)‖ ≤ ‖x.val‖
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro e
  by_cases he : e.val ∈ J.edgeFinset
  · rw [extendValue_host J x.val e.val he]
    exact norm_le_pi_norm x.val ⟨e.val,he⟩
  · simp [extendValue, he]

theorem edgeLoad_subgraph_difference (p : V → Fin 2) (J H : SimpleGraph V)
    (hJH : J ≤ H) (w : Finset V → ℝ) (e : Sym2 V) :
    edgeLoad p F0 H w e - edgeLoad p F0 J w e =
      ∑ s ∈ edgeCopies p F0 H e \ edgeCopies p F0 J e, w s := by
  classical
  have h := Finset.sum_sdiff (f := w) (edgeCopies_mono (p := p) (F := F0) hJH e)
  change (∑ s ∈ edgeCopies p F0 H e, w s) -
    (∑ s ∈ edgeCopies p F0 J e, w s) = _
  linarith

theorem edgeLoad_subgraph_error (p : V → Fin 2) (J H : SimpleGraph V)
    (hJH : J ≤ H) (w : Finset V → ℝ) (e : Sym2 V) (C : ℝ) (hC : 0 ≤ C)
    (hCount : ((edgeCopies p F0 H e \ edgeCopies p F0 J e).card : ℝ) ≤ C) :
    |edgeLoad p F0 H w e - edgeLoad p F0 J w e| ≤ C * ‖w‖ := by
  classical
  rw [edgeLoad_subgraph_difference p J H hJH w e]
  calc
    _ ≤ ∑ s ∈ edgeCopies p F0 H e \ edgeCopies p F0 J e, |w s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ edgeCopies p F0 H e \ edgeCopies p F0 J e, ‖w‖ := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm w s
    _ = (edgeCopies p F0 H e \ edgeCopies p F0 J e).card * ‖w‖ := by simp
    _ ≤ C * ‖w‖ := mul_le_mul_of_nonneg_right hCount (norm_nonneg _)

/-- A supergraph inverse survives a sparse loss of copies.  The hypothesis on
the discarded count is pointwise for every physical edge of the smaller host. -/
theorem hasBoundedBalancedInverse_of_supergraph
    (p : V → Fin 2) (J H : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel H.Adj]
    (hJH : J ≤ H) (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hn : 0 < Fintype.card V)
    (S : BalancedDemand p H →ₗ[ℝ] (Finset V → ℝ))
    (hS : ∀ x, boundary p H (S x) = x)
    (hNorm : ∀ x, ‖S x‖ ≤ (K / Fintype.card V) * ‖x‖)
    (hCount : ∀ e ∈ J.edgeFinset,
      ((edgeCopies p F0 H e \ edgeCopies p F0 J e).card : ℝ) ≤ D * Fintype.card V)
    (hSmall : D * K ≤ 1 / 2) : HasBoundedBalancedInverse p J (2 * K) := by
  classical
  let T := S.comp (extendDemand p J H hJH)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hKn : 0 ≤ K / (Fintype.card V : ℝ) := div_nonneg hK hnR.le
  have hBound : ∀ x : BalancedDemand p J, ‖T x‖ ≤ (K / Fintype.card V) * ‖x‖ := by
    intro x
    exact (hNorm _).trans (mul_le_mul_of_nonneg_left (extendDemand_norm_le p J H hJH x) hKn)
  apply hasBoundedBalancedInverse_of_half_error p J K hK T hBound
  intro x
  change ‖(fun e : HostEdge J => x.val e - edgeLoad p F0 J (T x) e.val)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro e
  have heH := SimpleGraph.edgeFinset_mono hJH e.property
  have heq := congrArg (fun z : BalancedDemand p H => z.val ⟨e.val,heH⟩)
    (hS (extendDemand p J H hJH x))
  change edgeLoad p F0 H (T x) e.val = extendValue J x.val e.val at heq
  rw [extendValue_host J x.val e.val e.property] at heq
  simp only [Real.norm_eq_abs]
  rw [← heq]
  calc
    _ ≤ (D * Fintype.card V) * ‖T x‖ :=
      edgeLoad_subgraph_error p J H hJH (T x) e.val _ (mul_nonneg hD hnR.le)
        (hCount e.val e.property)
    _ ≤ (D * Fintype.card V) * ((K / Fintype.card V) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hBound x) (mul_nonneg hD hnR.le)
    _ = (D * K) * ‖x‖ := by field_simp
    _ ≤ (1 / 2 : ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hSmall (norm_nonneg _)

#print axioms extendDemand_norm_le
#print axioms hasBoundedBalancedInverse_of_supergraph

end PartitionedTriangleAbsorption.BlowupB.F0Direct.InverseRestriction
