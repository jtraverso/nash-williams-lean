/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteBounds
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.PhysicalWeightTransport

@[expose] public section

/-!
# From complete-crossing coordinates to physical copy loads

The coordinate interface consists of a bijection of physical edges and the
incidence table of an injective family of actual mixed triangles. The theorem
below transports the explicit three-stage operator to the project's `copies`
and `edgeLoad` definitions.
-/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete

open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks F0RigidBoost
open BalancedLinearRepair PhysicalWeightTransport

variable {V A B EA EB : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype A] [Fintype B] [Fintype EA] [Fintype EB]
variable [DecidableEq A] [DecidableEq B]

noncomputable def edgeIndicator (e : Sym2 V) (s : Finset V) : ℝ :=
  if e ∈ triEdges s then 1 else 0

structure Coordinates (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) where
  edge : EA ⊕ (EB ⊕ (A × B)) ≃ HostEdge J
  tri : (EA × B) ⊕ (A × EB) → Finset V
  tri_mem : ∀ i, tri i ∈ copies p F0 J
  tri_injective : Function.Injective tri
  chargeA : ∀ f, gFun p (edge (Sum.inl f)).val = -4
  chargeB : ∀ f, gFun p (edge (Sum.inr (Sum.inl f))).val = -4
  chargeC : ∀ uv, gFun p (edge (Sum.inr (Sum.inr uv))).val = 2
  aa : ∀ f fv, (edge (Sum.inl f)).val ∈ triEdges (tri (Sum.inl fv)) ↔ f = fv.1
  ab : ∀ f uf, (edge (Sum.inl f)).val ∉ triEdges (tri (Sum.inr uf))
  ba : ∀ f fv, (edge (Sum.inr (Sum.inl f))).val ∉ triEdges (tri (Sum.inl fv))
  bb : ∀ f uf, (edge (Sum.inr (Sum.inl f))).val ∈ triEdges (tri (Sum.inr uf)) ↔ f = uf.2
  ca : ∀ uv fv, edgeIndicator (edge (Sum.inr (Sum.inr uv))).val (tri (Sum.inl fv)) =
    if uv.2 = fv.2 then IA uv.1 fv.1 else 0
  cb : ∀ uv uf, edgeIndicator (edge (Sum.inr (Sum.inr uv))).val (tri (Sum.inr uf)) =
    if uv.1 = uf.1 then IB uv.2 uf.2 else 0

noncomputable def pullDemand (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB) :
    (HostEdge J → ℝ) →ₗ[ℝ] Demand A B EA EB where
  toFun x := (fun f => x (C.edge (Sum.inl f)),
    fun f => x (C.edge (Sum.inr (Sum.inl f))),
    fun uv => x (C.edge (Sum.inr (Sum.inr uv))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def joinWeights : Weights A B EA EB →ₗ[ℝ] ((EA × B) ⊕ (A × EB) → ℝ) where
  toFun w := Sum.elim w.1 w.2
  map_add' _ _ := by ext i; cases i <;> rfl
  map_smul' _ _ := by ext i; cases i <;> rfl

theorem pullDemand_balanced (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (x : BalancedDemand p J) : Balanced (pullDemand p J IA IB C x.val) := by
  have hx := x.property
  change (∑ e : HostEdge J, gFun p e.val * x.val e) = 0 at hx
  rw [← C.edge.sum_comp (fun e : HostEdge J => gFun p e.val * x.val e)] at hx
  simp only [Fintype.sum_sum_type, C.chargeA, C.chargeB, C.chargeC,
    ← Finset.mul_sum] at hx
  change (∑ uv, x.val (C.edge (Sum.inr (Sum.inr uv)))) =
    2 * ((∑ f, x.val (C.edge (Sum.inl f))) + ∑ f, x.val (C.edge (Sum.inr (Sum.inl f))))
  linarith

theorem load_joinA (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (w : Weights A B EA EB) (f : EA) :
    edgeLoad p F0 J (pushWeights C.tri (joinWeights w)) (C.edge (Sum.inl f)).val =
      internalLoadA w f := by
  classical
  rw [edgeLoad_pushWeights p J C.tri C.tri_mem]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, joinWeights,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr,
    C.aa, C.ab, if_false, sum_const_zero, add_zero]
  rw [Finset.sum_comm]
  simp [internalLoadA]

theorem load_joinB (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (w : Weights A B EA EB) (f : EB) :
    edgeLoad p F0 J (pushWeights C.tri (joinWeights w))
      (C.edge (Sum.inr (Sum.inl f))).val = internalLoadB w f := by
  classical
  rw [edgeLoad_pushWeights p J C.tri C.tri_mem]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, joinWeights,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr,
    C.ba, C.bb, if_false, sum_const_zero, zero_add]
  simp [eq_comm, internalLoadB]

theorem load_joinC (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (w : Weights A B EA EB) (uv : A × B) :
    edgeLoad p F0 J (pushWeights C.tri (joinWeights w))
      (C.edge (Sum.inr (Sum.inr uv))).val = crossLoad IA IB w uv := by
  classical
  rw [edgeLoad_pushWeights p J C.tri C.tri_mem]
  have hi (e : Sym2 V) (s : Finset V) (c : ℝ) :
      (if e ∈ triEdges s then c else 0) = edgeIndicator e s * c := by
    unfold edgeIndicator
    split_ifs <;> ring
  simp only [hi, Fintype.sum_sum_type, Fintype.sum_prod_type, joinWeights,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, C.ca, C.cb,
    ite_mul, zero_mul]
  simp [eq_comm, crossLoad, inc]

noncomputable def fullOperator (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ)) :
    BalancedDemand p J →ₗ[ℝ] (Finset V → ℝ) :=
  (pushWeights C.tri).comp (joinWeights.comp ((completeWeights IA IB Q).comp
    ((pullDemand p J IA IB C).comp (BalancedDemand p J).subtype)))

theorem fullOperator_exact (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (hIA : ∀ f, (∑ u, IA u f) = 2) (hIB : ∀ f, (∑ v, IB v f) = 2)
    (hA : (Fintype.card A : ℝ) ≠ 0) (hB : (Fintype.card B : ℝ) ≠ 0)
    (heB : (Fintype.card EB : ℝ) ≠ 0) (hQ : ∀ x, inc IA (Q x) = x)
    (x : BalancedDemand p J) (e : HostEdge J) :
    edgeLoad p F0 J (fullOperator p J IA IB C Q x) e.val = x.val e := by
  obtain ⟨j, rfl⟩ := C.edge.surjective e
  change edgeLoad p F0 J
    (pushWeights C.tri (joinWeights (completeWeights IA IB Q
      (pullDemand p J IA IB C x.val)))) (C.edge j).val = _
  rcases j with f | f | uv
  · rw [load_joinA]
    exact completeWeights_internalA IA IB Q hIB hB heB _ f
  · rw [load_joinB]
    exact completeWeights_internalB IA IB Q hIA hIB hA hB _
      (pullDemand_balanced p J IA IB C x) f
  · rw [load_joinC]
    exact completeWeights_cross IA IB Q hQ _ uv

theorem fullOperator_bound (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates p J IA IB)
    (Cq : ℝ) (hCq : 0 ≤ Cq) (h : SizeBounds IA IB (Fintype.card V))
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (hQ : ∀ (y : A → ℝ) (L : ℝ), 0 ≤ L → (∀ u, |y u| ≤ L) →
      ∀ f, |Q y f| ≤ Cq * L / Fintype.card V)
    (x : BalancedDemand p J) :
    ‖fullOperator p J IA IB C Q x‖ ≤
      ((143 + 147 * Cq) / Fintype.card V) * ‖x‖ := by
  have hn : 0 < (Fintype.card V : ℝ) := h.npos
  let g := pullDemand p J IA IB C x.val
  have hg : DemandBound g ‖x‖ := by
    have hx (e : HostEdge J) : |x.val e| ≤ ‖x‖ := by
      change |x.val e| ≤ ‖x.val‖
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.val e
    exact ⟨fun f => hx _, fun f => hx _, fun uv => hx _⟩
  obtain ⟨ha, hb⟩ := completeWeights_abs_le IA IB (Fintype.card V) Cq h hCq Q hQ
    g ‖x‖ (norm_nonneg _) hg
  have hM : 0 ≤ (143 + 147 * Cq) * ‖x‖ / Fintype.card V := by positivity
  have hs (s : Finset V) : |fullOperator p J IA IB C Q x s| ≤
      (143 + 147 * Cq) * ‖x‖ / Fintype.card V := by
    apply pushWeights_abs_le C.tri C.tri_injective _ _ hM
    intro i
    cases i with
    | inl fv => exact ha fv
    | inr uf => exact hb uf
  have hnorm : ‖fullOperator p J IA IB C Q x‖ ≤
      (143 + 147 * Cq) * ‖x‖ / Fintype.card V := by
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro s
    simpa only [Real.norm_eq_abs] using hs s
  convert hnorm using 1 <;> ring

#print axioms fullOperator_exact
#print axioms fullOperator_bound

end PartitionedTriangleAbsorption.F0Direct.RealComplete
