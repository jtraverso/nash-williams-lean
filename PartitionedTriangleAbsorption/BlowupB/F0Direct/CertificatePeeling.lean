/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateAssembly
public import PartitionedTriangleAbsorption.IntegerCertificate.Divisibility

/-! # Peeling the internal edges of a divisible source

One physical mixed triangle is subtracted at each internal source edge.  The
remaining integer edge function is supported on crossing edges, has zero F0
charge and even degree at every vertex, and has coefficient norm at most
four times the number of source edges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsInternal (p : V → Fin 2) (e : Sym2 V) : Prop := (e.map p).IsDiag

instance (p : V → Fin 2) (e : Sym2 V) : Decidable (IsInternal p e) := by
  unfold IsInternal
  infer_instance

def triangleChainFunction (L : IntegralChain (Finset V)) (e : Sym2 V) : ℤ :=
  L.eval (fun t => ind (triEdges t) e)

def edgeFunctionCost (f : Sym2 V → ℤ) : ℤ := ∑ e, |f e|

def vertexDegree (p : V → Fin 2) (f : Sym2 V → ℤ) (v : V) : ℤ :=
  ∑ e, f e * ∑ i, degContrib p v e i

theorem edgeFunctionCost_ind (E : Finset (Sym2 V)) : edgeFunctionCost (ind E) = E.card := by
  simp [edgeFunctionCost, ind, apply_ite]

theorem edgeFunctionCost_add (f g : Sym2 V → ℤ) :
    edgeFunctionCost (fun e => f e + g e) ≤ edgeFunctionCost f + edgeFunctionCost g := by
  unfold edgeFunctionCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => abs_add_le _ _

theorem edgeFunctionCost_sub (f g : Sym2 V → ℤ) :
    edgeFunctionCost (fun e => f e - g e) ≤ edgeFunctionCost f + edgeFunctionCost g := by
  unfold edgeFunctionCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => by simpa using abs_sub_le (f e) 0 (g e)

theorem edgeFunctionCost_mul (c : ℤ) (f : Sym2 V → ℤ) :
    edgeFunctionCost (fun e => c * f e) = |c| * edgeFunctionCost f := by
  simp only [edgeFunctionCost, abs_mul, Finset.mul_sum]

theorem triangleChainFunction_cost (p : V → Fin 2) (G : SimpleGraph V)
    (L : IntegralChain (Finset V)) (hL : Valid (IsCopy p F0 G) L) :
    edgeFunctionCost (triangleChainFunction L) ≤ 3 * L.cost := by
  induction L with
  | nil => simp [triangleChainFunction, edgeFunctionCost]
  | cons z L ih =>
    have hz := hL z (by simp)
    have ht : Valid (IsCopy p F0 G) L := fun y hy => hL y (by simp [hy])
    have hCard : (triEdges z.2).card = 3 :=
      (SignedCertificate.tri_counts p hz.1.card_eq hz.2).2.2.2
    have h := edgeFunctionCost_add (fun e => z.1 * ind (triEdges z.2) e)
      (triangleChainFunction L)
    rw [edgeFunctionCost_mul, edgeFunctionCost_ind, hCard] at h
    change edgeFunctionCost (fun e => z.1 * ind (triEdges z.2) e + triangleChainFunction L e) ≤
      3 * (|z.1| + IntegralChain.cost L)
    have hi := ih ht
    push_cast at h
    nlinarith

theorem vertexDegree_ind (p : V → Fin 2) (E : Finset (Sym2 V)) (v : V) :
    vertexDegree p (ind E) v = ∑ i, degVec p E v i := by
  unfold vertexDegree
  simp only [ind, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_comm]
  simp only [degVec, Finset.sum_apply]

theorem vertexDegree_add (p : V → Fin 2) (f g : Sym2 V → ℤ) (v : V) :
    vertexDegree p (fun e => f e + g e) v = vertexDegree p f v + vertexDegree p g v := by
  simp only [vertexDegree, add_mul, Finset.sum_add_distrib]

theorem vertexDegree_sub (p : V → Fin 2) (f g : Sym2 V → ℤ) (v : V) :
    vertexDegree p (fun e => f e - g e) v = vertexDegree p f v - vertexDegree p g v := by
  simp only [vertexDegree, sub_mul, Finset.sum_sub_distrib]

theorem vertexDegree_mul (p : V → Fin 2) (c : ℤ) (f : Sym2 V → ℤ) (v : V) :
    vertexDegree p (fun e => c * f e) v = c * vertexDegree p f v := by
  simp only [vertexDegree, mul_assoc, Finset.mul_sum]

theorem vertexDegree_even_of_isIntDiv (p : V → Fin 2) (P : Finset (Sym2 V))
    (hP : IsIntDiv p F0 P) (v : V) : Even (vertexDegree p (ind P) v) := by
  obtain ⟨c, hc⟩ := hP.2 v
  rw [vertexDegree_ind, hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  have hEq :
      (∑ τ ∈ F0 with p v ∈ τ, ∑ i, c τ * typeDegVec τ (p v) i) =
        2 * ∑ τ ∈ F0 with p v ∈ τ, c τ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [← Finset.mul_sum, IntegerCertificate.typeDegVec_sum_F0 τ (mem_filter.mp hτ).1]
    ring
  rw [hEq]
  exact ⟨_, by ring⟩

theorem vertexDegree_triangle_even (p : V → Fin 2) (G : SimpleGraph V)
    (T : Finset V) (hT : IsCopy p F0 G T) (v : V) :
    Even (vertexDegree p (ind (triEdges T)) v) := by
  rw [vertexDegree_ind]
  simp only [degVec_triEdges p hT.1.card_eq]
  by_cases hv : v ∈ T
  · simp only [if_pos hv]
    rw [IntegerCertificate.typeDegVec_sum_F0 (triType p T) hT.2]
    decide
  · simp [hv]

theorem vertexDegree_chain_even (p : V → Fin 2) (G : SimpleGraph V)
    (L : IntegralChain (Finset V)) (hL : Valid (IsCopy p F0 G) L) (v : V) :
    Even (vertexDegree p (triangleChainFunction L) v) := by
  induction L with
  | nil => simp [triangleChainFunction, vertexDegree]
  | cons z L ih =>
    change Even (vertexDegree p
      (fun e => z.1 * ind (triEdges z.2) e + triangleChainFunction L e) v)
    rw [vertexDegree_add, vertexDegree_mul]
    exact ((vertexDegree_triangle_even p G z.2 (hL z (by simp)) v).mul_left z.1).add
      (ih (fun y hy => hL y (by simp [hy])))

theorem charge_triangleChainFunction (p : V → Fin 2) (G : SimpleGraph V)
    (L : IntegralChain (Finset V)) (hL : Valid (IsCopy p F0 G) L) :
    IntegerCertificate.charge p (triangleChainFunction L) = 0 := by
  induction L with
  | nil => simp [triangleChainFunction, IntegerCertificate.charge]
  | cons z L ih =>
    have hT := (IntegerCertificate.Realizes.tri (hL z (by simp))).charge_eq_zero
    have hI := ih (fun y hy => hL y (by simp [hy]))
    change IntegerCertificate.charge p
      (z.1 • ind (triEdges z.2) + triangleChainFunction L) = 0
    rw [IntegerCertificate.charge_add, IntegerCertificate.charge_smul, hT, hI]
    ring

/-- Data needed for peeling one internal edge. -/
def InternalCompletion (p : V → Fin 2) (G : SimpleGraph V) (e : Sym2 V)
    (T : Finset V) : Prop :=
  IsCopy p F0 G T ∧ ∀ d, IsInternal p d → ind (triEdges T) d = if d = e then 1 else 0

theorem internalCompletion_of_adj (p : V → Fin 2) (G : SimpleGraph V)
    (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (huvPart : p u = p v) (hwPart : p w ≠ p u) :
    InternalCompletion p G s(u,v) {u,v,w} := by
  refine ⟨IntegerCertificate.isCopy_of_adj huv huw hvw ?_, ?_⟩
  · intro h
    exact hwPart (h.2.symm.trans h.1.symm)
  · intro d hd
    have hduw : d ≠ s(u,w) := by
      intro h
      subst d
      have hp : p u = p w := by simpa [IsInternal] using hd
      exact hwPart hp.symm
    have hdvw : d ≠ s(v,w) := by
      intro h
      subst d
      have hp : p v = p w := by simpa [IsInternal] using hd
      exact hwPart (hp.symm.trans huvPart.symm)
    rw [ind_triangle huv.ne huw.ne hvw.ne]
    simp [physicalEdgeUnit, hduw, hdvw]

/-- Anti-edgefulness supplies a physical mixed completion of each internal
edge, without any requirement of internal common neighborhoods. -/
theorem internalCompletion_of_antiEdgeful (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (hAnti : AntiEdgeful p F0 G β)
    (hPos : 0 < β * Fintype.card V) (e : Sym2 V) (he : e ∈ G.edgeFinset)
    (hI : IsInternal p e) : ∃ T, InternalCompletion p G e T := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := by simpa using he
    have hp : p u = p v := by simpa [IsInternal] using hI
    have ho : other0 (p u) ≠ p u := by generalize p u = a; revert a; decide
    have hF : ({p u,p v,other0 (p u)} : Multiset (Fin 2)) ∈ F0 :=
      IntegerCertificate.f0_of_not_mono _ _ _ (fun h => ho (h.2.symm.trans h.1.symm))
    have hCount := hAnti _ hF (p u) (p v) (other0 (p u)) rfl u v huv.ne rfl rfl
    have hCountPos : 0 < (univ.filter
        (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = other0 (p u))).card := by
      exact_mod_cast hPos.trans_le hCount
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hCountPos
    obtain ⟨huw, hwv, hpw⟩ := (Finset.mem_filter.mp hw).2
    exact ⟨{u,v,w}, internalCompletion_of_adj p G u v w huv huw hwv.symm hp
      (fun h => ho (hpw.symm.trans h))⟩

/-- Peeling itself, with no choice of common matrix anchors yet. -/
theorem peel_internal_edges (p : V → Fin 2) (G : SimpleGraph V)
    (P : Finset (Sym2 V)) (hDiv : IsIntDiv p F0 P)
    (hT : ∀ e ∈ P, IsInternal p e → ∃ T, InternalCompletion p G e T) :
    ∃ L : IntegralChain (Finset V), ∃ f : Sym2 V → ℤ,
      Valid (IsCopy p F0 G) L ∧
      (∀ e, ind P e = triangleChainFunction L e + f e) ∧
      L.cost ≤ P.card ∧ edgeFunctionCost f ≤ 4 * P.card ∧
      (∀ e, IsInternal p e → f e = 0) ∧
      (∀ v, Even (vertexDegree p f v)) ∧ IntegerCertificate.charge p f = 0 := by
  classical
  let S : Finset (Sym2 V) := P.filter (IsInternal p)
  have hChoice : ∀ e : S, ∃ T, InternalCompletion p G e T := by
    intro e
    exact hT e (mem_filter.mp e.2).1 (mem_filter.mp e.2).2
  choose T hTV hTE using hChoice
  let L : IntegralChain (Finset V) := IntegralChain.sum (fun e : S => [(1,T e)])
  let f : Sym2 V → ℤ := fun e => ind P e - triangleChainFunction L e
  have hLV : Valid (IsCopy p F0 G) L := by
    apply valid_sum
    intro e z hz
    simp only [List.mem_singleton] at hz
    subst z
    exact hTV e
  have hLC : L.cost ≤ P.card := by
    simp only [L, cost_sum, cost_cons, cost_nil]
    norm_num
    exact_mod_cast Finset.card_filter_le P (IsInternal p)
  refine ⟨L, f, hLV, ?_, hLC, ?_, ?_, ?_, ?_⟩
  · intro e
    dsimp [f]
    ring

  · have h := edgeFunctionCost_sub (ind P) (triangleChainFunction L)
    rw [edgeFunctionCost_ind] at h
    have hC := triangleChainFunction_cost p G L hLV
    change edgeFunctionCost (fun e => ind P e - triangleChainFunction L e) ≤ _
    nlinarith
  · intro e he
    have h : triangleChainFunction L e = ind P e := by
      simp only [triangleChainFunction, L, eval_sum, eval_cons, eval_nil, one_mul, add_zero]
      simp_rw [hTE _ e he]
      rw [Finset.sum_coe_sort S (fun d => if e = d then (1 : ℤ) else 0)]
      simp [S, ind, he]
    simp [f, h]
  · intro v
    rw [show f = fun e => ind P e - triangleChainFunction L e from rfl, vertexDegree_sub]
    exact (vertexDegree_even_of_isIntDiv p P hDiv v).sub (vertexDegree_chain_even p G L hLV v)
  · change IntegerCertificate.charge p (ind P - triangleChainFunction L) = 0
    rw [IntegerCertificate.charge_sub, IntegerCertificate.charge_ind_of_isIntDiv hDiv,
      charge_triangleChainFunction p G L hLV]
    ring

theorem peel_of_antiEdgeful (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (hAnti : AntiEdgeful p F0 G β)
    (hPos : 0 < β * Fintype.card V) (P : Finset (Sym2 V))
    (hPG : P ⊆ G.edgeFinset) (hDiv : IsIntDiv p F0 P) :
    ∃ L : IntegralChain (Finset V), ∃ f : Sym2 V → ℤ,
      Valid (IsCopy p F0 G) L ∧
      (∀ e, ind P e = triangleChainFunction L e + f e) ∧
      L.cost ≤ P.card ∧ edgeFunctionCost f ≤ 4 * P.card ∧
      (∀ e, IsInternal p e → f e = 0) ∧
      (∀ v, Even (vertexDegree p f v)) ∧ IntegerCertificate.charge p f = 0 := by
  exact peel_internal_edges p G P hDiv (fun e he hI =>
    internalCompletion_of_antiEdgeful p G β hAnti hPos e (hPG he) hI)

#print axioms vertexDegree_chain_even
#print axioms peel_internal_edges
#print axioms peel_of_antiEdgeful

end PartitionedTriangleAbsorption.BlowupB.F0Direct
