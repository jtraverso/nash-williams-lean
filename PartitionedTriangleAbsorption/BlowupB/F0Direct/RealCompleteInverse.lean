/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteSumCoordinates

@[expose] public section

/-!
# The complete physical balanced inverse

The complete-crossing incidence table is combined with the explicit inverse
of the internal signless incidence matrix.  The resulting operator is linear
on all balanced real demands, has exactly the prescribed physical edge loads,
and has norm at most `(512 / tau) / card V`.

The coordinate table may be on a sum of the parts or transported to any
equivalent vertex type.  No geometry is assumed beyond the displayed size
and rooted internal triangle bounds.
-/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete

open Finset TypedApplicationLinks TypedLoadNecessity
open BalancedLinearRepair

variable {V A B : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph A) (H : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Elementary cardinal estimates supply every matrix norm hypothesis. -/
theorem sizeBounds_of_card_bounds (n : ℝ) (hn : 0 < n)
    (hAL : n / 3 ≤ Fintype.card A) (hBL : n / 3 ≤ Fintype.card B)
    (hAU : (Fintype.card A : ℝ) ≤ n) (hBU : (Fintype.card B : ℝ) ≤ n)
    (hEB : n ^ 2 / 40 ≤ Fintype.card (HostEdge H)) :
    SizeBounds (Internal.matrix G) (Internal.matrix H) n where
  npos := hn
  a_lower := hAL
  b_lower := hBL
  b_upper := hBU
  ia_row u := (Internal.matrix_row_bound G u).trans hAU
  ib_row v := (Internal.matrix_row_bound H v).trans hBU
  eb_lower := hEB

/-- The operator itself depends only on the graph and its physical coordinates. -/
noncomputable def completeOperator (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj]
    (C : Coordinates p J (Internal.matrix G) (Internal.matrix H)) :
    BalancedDemand p J →ₗ[ℝ] (Finset V → ℝ) :=
  fullOperator p J (Internal.matrix G) (Internal.matrix H) C (Internal.inverse G)

theorem completeOperator_exact (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj]
    (C : Coordinates p J (Internal.matrix G) (Internal.matrix H))
    (hsize : SizeBounds (Internal.matrix G) (Internal.matrix H) (Fintype.card V))
    (hcount : ∀ u, 0 < (SignlessTriangle.trianglePairs G u).card)
    (x : BalancedDemand p J) (e : HostEdge J) :
    edgeLoad p F0 J (completeOperator G H p J C x) e.val = x.val e := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by have := hsize.npos; positivity) hsize.a_lower)
  have hB : (Fintype.card B : ℝ) ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by have := hsize.npos; positivity) hsize.b_lower)
  have hEB : (Fintype.card (HostEdge H) : ℝ) ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by have := hsize.npos; positivity) hsize.eb_lower)
  exact fullOperator_exact p J (Internal.matrix G) (Internal.matrix H) C
    (Internal.inverse G) (Internal.matrix_column_sum G) (Internal.matrix_column_sum H)
    hA hB hEB (Internal.inverse_exact G hcount) x e

theorem completeOperator_boundary (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj]
    (C : Coordinates p J (Internal.matrix G) (Internal.matrix H))
    (hsize : SizeBounds (Internal.matrix G) (Internal.matrix H) (Fintype.card V))
    (hcount : ∀ u, 0 < (SignlessTriangle.trianglePairs G u).card)
    (x : BalancedDemand p J) :
    boundary p J (completeOperator G H p J C x) = x := by
  apply Subtype.ext
  funext e
  exact completeOperator_exact G H p J C hsize hcount x e

theorem completeOperator_bound (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj]
    (C : Coordinates p J (Internal.matrix G) (Internal.matrix H))
    (tau : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hsize : SizeBounds (Internal.matrix G) (Internal.matrix H) (Fintype.card V))
    (hAU : (Fintype.card A : ℝ) ≤ Fintype.card V)
    (hcount : ∀ u, 2 * tau * (Fintype.card V : ℝ) ^ 2 ≤
      ((SignlessTriangle.trianglePairs G u).card : ℝ))
    (x : BalancedDemand p J) :
    ‖completeOperator G H p J C x‖ ≤ ((512 / tau) / Fintype.card V) * ‖x‖ := by
  have hQ := Internal.inverse_bound_global G (Fintype.card V) tau
    hsize.npos htau hAU hcount
  have hb := fullOperator_bound p J (Internal.matrix G) (Internal.matrix H) C
    (3 / (2 * tau)) (by positivity) hsize (Internal.inverse G) hQ x
  exact hb.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (complete_constant_le tau htau htau1) hsize.npos.le)
    (norm_nonneg x))

/-- The exact contract needed for subsequent restriction to a sparse subgraph. -/
theorem exists_completeInverse (p : V → Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj]
    (C : Coordinates p J (Internal.matrix G) (Internal.matrix H))
    (tau : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hsize : SizeBounds (Internal.matrix G) (Internal.matrix H) (Fintype.card V))
    (hAU : (Fintype.card A : ℝ) ≤ Fintype.card V)
    (hcount : ∀ u, 2 * tau * (Fintype.card V : ℝ) ^ 2 ≤
      ((SignlessTriangle.trianglePairs G u).card : ℝ)) :
    ∃ S : BalancedDemand p J →ₗ[ℝ] (Finset V → ℝ),
      (∀ x, boundary p J (S x) = x) ∧
      (∀ x, ‖S x‖ ≤ ((512 / tau) / Fintype.card V) * ‖x‖) := by
  have hpositive (u : A) : 0 < (SignlessTriangle.trianglePairs G u).card := by
    have hR : (0 : ℝ) < (SignlessTriangle.trianglePairs G u).card :=
      lt_of_lt_of_le (by have := hsize.npos; positivity) (hcount u)
    exact_mod_cast hR
  exact ⟨completeOperator G H p J C,
    completeOperator_boundary G H p J C hsize hpositive,
    completeOperator_bound G H p J C tau htau htau1 hsize hAU hcount⟩

#print axioms sizeBounds_of_card_bounds
#print axioms completeOperator_exact
#print axioms completeOperator_boundary
#print axioms completeOperator_bound
#print axioms exists_completeInverse

end PartitionedTriangleAbsorption.F0Direct.RealComplete
