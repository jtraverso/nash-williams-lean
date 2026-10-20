/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateIncidence

/-! # From integer incidence repairs to physical triangle certificates

All triangles appearing below are actual copies in the supplied host.  List
positions become the finite occurrence indices of `IsSignedCert`, with exactly
the same coefficient cost.  The column lift is an exact identity on physical
edges, including the cancellation of the shared internal edge.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

def physicalEdgeUnit (u v : V) (e : Sym2 V) : ℤ := if e = s(u,v) then 1 else 0

theorem ind_triangle {u v b : V} (huv : u ≠ v) (hub : u ≠ b) (hvb : v ≠ b)
    (e : Sym2 V) :
    ind (triEdges ({u,v,b} : Finset V)) e =
      physicalEdgeUnit u v e + physicalEdgeUnit u b e + physicalEdgeUnit v b e := by
  have h := sum_triEdges_three (fun d : Sym2 V => if e = d then (1 : ℤ) else 0)
    huv hub hvb
  simpa [ind, physicalEdgeUnit] using h

def triangleDifference (u v b b0 : V) : IntegralChain (Finset V) :=
  [(1,{u,v,b}), (-1,{u,v,b0})]

theorem triangleDifference_cost (u v b b0 : V) : (triangleDifference u v b b0).cost = 2 := by
  norm_num [triangleDifference]

theorem triangleDifference_valid (p : V → Fin 2) (G : SimpleGraph V) (u v b b0 : V)
    (h : IsCopy p F0 G {u,v,b}) (h0 : IsCopy p F0 G {u,v,b0}) :
    Valid (IsCopy p F0 G) (triangleDifference u v b b0) := by
  intro z hz
  simp only [triangleDifference, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact h
  · exact h0

theorem triangleDifference_eval (p : V → Fin 2) (G : SimpleGraph V) (u v b b0 : V)
    (h : IsCopy p F0 G {u,v,b}) (h0 : IsCopy p F0 G {u,v,b0}) (e : Sym2 V) :
    (triangleDifference u v b b0).eval (fun t => ind (triEdges t) e) =
      (physicalEdgeUnit u b e - physicalEdgeUnit u b0 e) +
      (physicalEdgeUnit v b e - physicalEdgeUnit v b0 e) := by
  obtain ⟨huv, hub, hvb⟩ := SimpleGraph.is3Clique_triple_iff.mp h.1
  obtain ⟨_, hub0, hvb0⟩ := SimpleGraph.is3Clique_triple_iff.mp h0.1
  simp only [triangleDifference, eval_cons, eval_nil]
  rw [ind_triangle huv.ne hub.ne hvb.ne, ind_triangle huv.ne hub0.ne hvb0.ne]
  ring

/-- Convert every occurrence of a valid chain into a finite signed-certificate
index.  The cost is preserved exactly, including repeated physical triangles. -/
theorem signedCert_of_chain (p : V → Fin 2) (G : SimpleGraph V) (P : Finset (Sym2 V))
    (L : IntegralChain (Finset V)) (hL : Valid (IsCopy p F0 G) L)
    (hP : ∀ e, L.eval (fun t => ind (triEdges t) e) = ind P e) :
    ∃ n : ℕ, ∃ t : Fin n → Finset V, ∃ c : Fin n → ℤ,
      IsSignedCert p G P t c ∧ certWeight c = L.cost := by
  refine ⟨L.length, (fun i => (L.get i).2), (fun i => (L.get i).1), ?_, ?_⟩
  · constructor
    · intro i
      exact hL (L.get i) (List.get_mem L i)
    · intro e
      exact (hP e).symm.trans (eval_eq_sum_get L (fun t => ind (triEdges t) e))
  · exact (cost_eq_sum_get L).symm

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Replace a valid edge-incidence presentation with differences of physical
mixed triangles.  The only triangle requirement is stated for edges actually
used by the presentation. -/
theorem lift_incidence_column (p : V → Fin 2) (G : SimpleGraph V)
    (H : SimpleGraph U) (r : U → V) (b b0 : V) (x : U → ℤ)
    (L : IntegralChain (U × U))
    (hL : Valid (fun e : U × U => H.Adj e.1 e.2) L)
    (hX : ∀ u, L.eval (fun e => edgeIncidence e u) = x u)
    (hT : ∀ u v, H.Adj u v →
      IsCopy p F0 G {r u,r v,b} ∧ IsCopy p F0 G {r u,r v,b0}) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ u, x u * (physicalEdgeUnit (r u) b e - physicalEdgeUnit (r u) b0 e)) ∧
      T.cost ≤ 2 * L.cost := by
  let T := L.substitute (fun z => triangleDifference (r z.1) (r z.2) b b0)
  refine ⟨T, ?_, ?_, ?_⟩
  · exact valid_substitute hL (fun z hz =>
      triangleDifference_valid p G _ _ _ _ (hT z.1 z.2 hz).1 (hT z.1 z.2 hz).2)
  · intro e
    rw [show T = L.substitute (fun z => triangleDifference (r z.1) (r z.2) b b0) from rfl,
      eval_substitute]
    calc
      _ = L.eval (fun z =>
        (physicalEdgeUnit (r z.1) b e - physicalEdgeUnit (r z.1) b0 e) +
        (physicalEdgeUnit (r z.2) b e - physicalEdgeUnit (r z.2) b0 e)) := by
          apply IntegralChain.eval_congr L
          intro z hz
          have ht := hT z.2.1 z.2.2 (hL z hz)
          exact triangleDifference_eval p G _ _ _ _ ht.1 ht.2 e
      _ = _ := incidence_reweight L x (fun u => physicalEdgeUnit (r u) b e - physicalEdgeUnit (r u) b0 e) hX
  · exact cost_substitute_le fun z _ => le_of_eq (triangleDifference_cost _ _ _ _)

/-- The complete column-repair estimate: one even-sum vector is represented by
physical mixed triangles with coefficient cost at most thirteen times its norm. -/
theorem repair_physical_column (p : V → Fin 2) (G : SimpleGraph V)
    (H : SimpleGraph U) (a : U) (B : IncidenceBasis H a) (r : U → V)
    (b b0 : V) (x : U → ℤ) (hx : Even (∑ u, x u))
    (hT : ∀ u v, H.Adj u v →
      IsCopy p F0 G {r u,r v,b} ∧ IsCopy p F0 G {r u,r v,b0}) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ u, x u * (physicalEdgeUnit (r u) b e - physicalEdgeUnit (r u) b0 e)) ∧
      T.cost ≤ 13 * vectorCost x := by
  obtain ⟨L, hL, hX, hC⟩ := incidence_repair H a B x hx
  obtain ⟨T, hT, hE, hC'⟩ := lift_incidence_column p G H r b b0 x L hL hX hT
  exact ⟨T, hT, hE, hC'.trans hC⟩

theorem sum_subtype_eq_of_zero_outside (S : Finset U) (x : U → ℤ)
    (h : ∀ u, u ∉ S → x u = 0) : (∑ u : S, x u) = ∑ u, x u := by
  rw [Finset.sum_coe_sort S x]
  exact Finset.sum_subset (Finset.subset_univ S) (fun u _ hu => h u hu)

/-- Restrict an even column to a finite common-neighbor set.  This is the bridge
used when some physical vertices are not adjacent to the column apex. -/
theorem repair_physical_column_on (p : V → Fin 2) (G : SimpleGraph V)
    (S : Finset U) (H : SimpleGraph S) (a : S) (B : IncidenceBasis H a) (r : U → V)
    (b b0 : V) (x : U → ℤ) (hx : Even (∑ u, x u))
    (hS : ∀ u, u ∉ S → x u = 0)
    (hT : ∀ u v : S, H.Adj u v →
      IsCopy p F0 G {r u,r v,b} ∧ IsCopy p F0 G {r u,r v,b0}) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ u, x u * (physicalEdgeUnit (r u) b e - physicalEdgeUnit (r u) b0 e)) ∧
      T.cost ≤ 13 * vectorCost x := by
  have hxS : Even (∑ u : S, x u) := by
    rw [sum_subtype_eq_of_zero_outside S x hS]
    exact hx
  obtain ⟨T, hV, hE, hK⟩ := repair_physical_column p G H a B (fun u : S => r u)
    b b0 (fun u : S => x u) hxS hT
  refine ⟨T, hV, ?_, ?_⟩
  · intro e
    rw [hE]
    exact sum_subtype_eq_of_zero_outside S
      (fun u => x u * (physicalEdgeUnit (r u) b e - physicalEdgeUnit (r u) b0 e))
      (fun u hu => by rw [hS u hu, zero_mul])
  · have hNorm : vectorCost (fun u : S => x u) = vectorCost x :=
      sum_subtype_eq_of_zero_outside S (fun u => |x u|) (fun u hu => by rw [hS u hu, abs_zero])
    rw [hNorm] at hK
    exact hK

#print axioms signedCert_of_chain
#print axioms lift_incidence_column
#print axioms repair_physical_column
#print axioms repair_physical_column_on

end PartitionedTriangleAbsorption.BlowupB.F0Direct
