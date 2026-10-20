/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateAlgebra

/-! # Integer incidence repair from four-edge walks

The only geometric input is an even walk of length four between each pair
of distinct vertices, and one neighbor of the anchor.  The conclusion is an
explicit integer combination of actual edges with coefficient cost at most
`13/2` times the input `l1` norm.  No division in the coefficient ring is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain

variable {V : Type*} [DecidableEq V]

def vertexUnit (a x : V) : ℤ := if x = a then 1 else 0

def edgeIncidence (e : V × V) (x : V) : ℤ := vertexUnit e.1 x + vertexUnit e.2 x

def fourWalkChain (f : Fin 5 → V) : IntegralChain (V × V) :=
  [(1,(f 0,f 1)), (-1,(f 1,f 2)), (1,(f 2,f 3)), (-1,(f 3,f 4))]

theorem fourWalkChain_eval (f : Fin 5 → V) (x : V) :
    (fourWalkChain f).eval (fun e => edgeIncidence e x) =
      vertexUnit (f 0) x - vertexUnit (f 4) x := by
  simp only [fourWalkChain, eval_cons, eval_nil, edgeIncidence]
  ring

theorem fourWalkChain_cost (f : Fin 5 → V) : (fourWalkChain f).cost = 4 := by
  norm_num [fourWalkChain]

theorem fourWalkChain_valid (H : SimpleGraph V) (f : Fin 5 → V)
    (hf : ∀ j : Fin 4, H.Adj (f j.castSucc) (f j.succ)) :
    Valid (fun e : V × V => H.Adj e.1 e.2) (fourWalkChain f) := by
  intro z hz
  simp only [fourWalkChain, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hf 0
  · exact hf 1
  · exact hf 2
  · exact hf 3

/-- The geometric walk interface.  Walks need not be injective. -/
def FourWalkSupply (H : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ f : Fin 5 → V,
    f 0 = u ∧ f 4 = v ∧ ∀ j : Fin 4, H.Adj (f j.castSucc) (f j.succ)

/-- A bounded integral presentation of every difference of vertex units and of
twice one anchor unit. -/
structure IncidenceBasis (H : SimpleGraph V) (a : V) where
  transfer : V → IntegralChain (V × V)
  transfer_valid : ∀ u, Valid (fun e : V × V => H.Adj e.1 e.2) (transfer u)
  transfer_eval : ∀ u x, (transfer u).eval (fun e => edgeIncidence e x) =
    vertexUnit u x - vertexUnit a x
  transfer_cost : ∀ u, (transfer u).cost ≤ 4
  double : IntegralChain (V × V)
  double_valid : Valid (fun e : V × V => H.Adj e.1 e.2) double
  double_eval : ∀ x, double.eval (fun e => edgeIncidence e x) = 2 * vertexUnit a x
  double_cost : double.cost ≤ 5

theorem incidenceBasis_of_fourWalkSupply (H : SimpleGraph V) (a : V)
    (hW : FourWalkSupply H) (hN : ∃ c, H.Adj a c) : Nonempty (IncidenceBasis H a) := by
  classical
  have hT : ∀ u : V, ∃ L : IntegralChain (V × V),
      Valid (fun e : V × V => H.Adj e.1 e.2) L ∧
      (∀ x, L.eval (fun e => edgeIncidence e x) = vertexUnit u x - vertexUnit a x) ∧
      L.cost ≤ 4 := by
    intro u
    by_cases h : u = a
    · subst u
      exact ⟨[], valid_nil _, by simp, by simp⟩
    · obtain ⟨f, h0, h4, hf⟩ := hW u a h
      exact ⟨fourWalkChain f, fourWalkChain_valid H f hf,
        by intro x; rw [fourWalkChain_eval, h0, h4],
        le_of_eq (fourWalkChain_cost f)⟩
  choose T hTV hTE hTC using hT
  obtain ⟨c, hc⟩ := hN
  let D : IntegralChain (V × V) := [(1,(a,c))] ++ scale (-1) (T c)
  refine ⟨⟨T, hTV, hTE, hTC, D, ?_, ?_, ?_⟩⟩
  · apply valid_append
    · intro z hz
      simp only [List.mem_singleton] at hz
      subst z
      exact hc
    · exact valid_scale _ (hTV c)
  · intro x
    simp only [D, eval_append, eval_cons, eval_nil, eval_scale, one_mul, add_zero]
    rw [hTE]
    simp only [edgeIncidence]
    ring
  · simp only [D, cost_append, cost_cons, cost_nil, cost_scale]
    norm_num
    linarith [hTC c]

variable [Fintype V]

def vectorCost (x : V → ℤ) : ℤ := ∑ u, |x u|

theorem vectorCost_nonneg (x : V → ℤ) : 0 ≤ vectorCost x :=
  Finset.sum_nonneg fun u _ => abs_nonneg (x u)

theorem sum_mul_vertexUnit (x : V → ℤ) (v : V) :
    (∑ u, x u * vertexUnit u v) = x v := by
  classical
  simp [vertexUnit]

theorem incidence_reweight (L : IntegralChain (V × V)) (x f : V → ℤ)
    (hL : ∀ v, L.eval (fun e => edgeIncidence e v) = x v) :
    L.eval (fun e => f e.1 + f e.2) = ∑ v, x v * f v := by
  classical
  have hEdge : ∀ e : V × V,
      f e.1 + f e.2 = ∑ v, edgeIncidence e v * f v := by
    intro e
    simp [edgeIncidence, vertexUnit, add_mul, Finset.sum_add_distrib]
  calc
    _ = L.eval (fun e => ∑ v, edgeIncidence e v * f v) :=
      IntegralChain.eval_congr L fun e _ => hEdge e.2
    _ = ∑ v, L.eval (fun e => edgeIncidence e v * f v) := eval_finite_sum L _
    _ = ∑ v, x v * f v := by simp only [eval_mul, hL]

/-- Quantified integer incidence repair.  Its output uses actual edges of `H`;
the bound is twice the coefficient norm, avoiding fractions. -/
theorem incidence_repair (H : SimpleGraph V) (a : V) (B : IncidenceBasis H a)
    (x : V → ℤ) (hx : Even (∑ u, x u)) :
    ∃ L : IntegralChain (V × V),
      Valid (fun e : V × V => H.Adj e.1 e.2) L ∧
      (∀ v, L.eval (fun e => edgeIncidence e v) = x v) ∧
      2 * L.cost ≤ 13 * vectorCost x := by
  classical
  obtain ⟨r, hr⟩ := hx
  let L : IntegralChain (V × V) :=
    IntegralChain.sum (fun u => scale (x u) (B.transfer u)) ++ scale r B.double
  refine ⟨L, ?_, ?_, ?_⟩
  · exact valid_append (valid_sum fun u => valid_scale _ (B.transfer_valid u))
      (valid_scale _ B.double_valid)
  · intro v
    simp only [L, eval_append, eval_sum, eval_scale, B.transfer_eval, B.double_eval]
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sum_mul_vertexUnit, hr]
    ring
  · have hS :
        (∑ u, |x u| * (B.transfer u).cost) ≤ 4 * vectorCost x := by
      calc
        _ ≤ ∑ u, |x u| * 4 := Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (B.transfer_cost u) (abs_nonneg (x u))
        _ = 4 * vectorCost x := by rw [← Finset.sum_mul]; unfold vectorCost; ring
    have hD := mul_le_mul_of_nonneg_left B.double_cost (abs_nonneg r)
    have hrBound : 2 * |r| ≤ vectorCost x := by
      have hAbs := Finset.abs_sum_le_sum_abs (f := x) Finset.univ
      rw [hr, ← two_mul, abs_mul] at hAbs
      norm_num at hAbs
      exact hAbs
    simp only [L, cost_append, cost_sum, cost_scale]
    nlinarith

#print axioms incidenceBasis_of_fourWalkSupply
#print axioms incidence_repair

end PartitionedTriangleAbsorption.BlowupB.F0Direct
