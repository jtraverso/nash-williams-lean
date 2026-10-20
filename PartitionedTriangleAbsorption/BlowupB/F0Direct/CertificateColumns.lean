/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateCrossMatrix
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateTransport
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkConsequences
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostWalkQueries

@[expose] public section

/-! # Bounded column repairs inside actual common-neighbour graphs -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks CloneSupply
  HostWalkQueries WalkSupply WalkConsequences

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε : ℝ}

def commonRows (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (b b0 : V) : Finset (PartVertex p i) :=
  univ.filter (fun u => G.Adj b u.val ∧ G.Adj b0 u.val)

@[simp] theorem mem_commonRows (i : Fin 2) (b b0 : V) (u : PartVertex p i) :
    u ∈ commonRows p G i b b0 ↔ G.Adj b u.val ∧ G.Adj b0 u.val := by
  simp only [commonRows, mem_filter, mem_univ, true_and]

def commonRowsEquiv (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (b b0 : V) :
    (commonRows p G i b b0 : Set (PartVertex p i)) ≃
      (commonPart p G i b b0 : Set V) where
  toFun u := ⟨u.val.val, mem_commonPart.mpr ⟨u.val.property,
    (mem_commonRows i b b0 u.val).mp u.property⟩⟩
  invFun u := ⟨⟨u.val, (mem_commonPart.mp u.property).1⟩,
    (mem_commonRows i b b0 _).mpr (mem_commonPart.mp u.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem column_repair_of_host (h : HostHyp p G α ε) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hεθ : 100 * ε ≤ θ) (hscale : 100 * θ ≤ α)
    (hn : 4096 ≤ θ * Fintype.card V) (i : Fin 2)
    (hext : Nonextreme G (partSet p i) α) (b b0 : V)
    (hb : p b = other0 i) (hb0 : p b0 = other0 i)
    (a0 : PartVertex p i) (ha : G.Adj b a0.val ∧ G.Adj b0 a0.val)
    (x : PartVertex p i → ℤ) (hx : Even (∑ a, x a))
    (hSupport : ∀ a, x a ≠ 0 → G.Adj b a.val ∧ G.Adj b0 a.val) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ a, x a * (physicalEdgeUnit a.val b e - physicalEdgeUnit a.val b0 e)) ∧
      T.cost ≤ 13 * ∑ a, |x a| := by
  classical
  let S := commonRows p G i b b0
  let D := commonPart p G i b b0
  let H : SimpleGraph (S : Set (PartVertex p i)) := G.comap (fun u => u.val.val)
  let K := G.induce (D : Set V)
  let E := commonRowsEquiv p G i b b0
  let a : (S : Set (PartVertex p i)) := ⟨a0, (mem_commonRows i b b0 a0).mpr ha⟩
  have hbi : p b ≠ i := by rw [hb]; exact other0_ne i
  have hb0i : p b0 ≠ i := by rw [hb0]; exact other0_ne i
  have hW := (common_walk_supply h hε0 hε θ hθ0 hθ1 hεθ hscale hn i hext b b0 hbi hb0i).2
  have hPos : ∀ u ∈ D, ∀ v ∈ D, 0 < arcs G (neighbors G D u) (neighbors G D v) := by
    intro u hu v hv
    exact lt_of_le_of_lt (by positivity) (hW u hu v hv)
  have hAdj : ∀ u v, H.Adj u v ↔ K.Adj (E u) (E v) := fun _ _ => Iff.rfl
  obtain ⟨B⟩ := incidenceBasis_of_equiv H K E hAdj a
    (fourWalkSupply_of_arcs_pos G D hPos)
    (neighbor_in_induced_of_arcs_pos G D (E a) (hPos _ (E a).property _ (E a).property))
  have hOutside : ∀ u ∉ S, x u = 0 := by
    intro u hu
    by_contra hx0
    exact hu ((mem_commonRows i b b0 u).mpr (hSupport u hx0))
  have hCopies : ∀ u v : (S : Set (PartVertex p i)), H.Adj u v →
      IsCopy p F0 G {u.val.val,v.val.val,b} ∧
      IsCopy p F0 G {u.val.val,v.val.val,b0} := by
    intro u v huv
    change G.Adj u.val.val v.val.val at huv
    have hu := (mem_commonRows i b b0 u.val).mp u.property
    have hv := (mem_commonRows i b b0 v.val).mp v.property
    constructor
    · apply IntegerCertificate.isCopy_of_adj huv hu.1.symm hv.1.symm
      rintro ⟨_, hm⟩
      have : i = other0 i := v.val.property.symm.trans (hm.trans hb)
      exact (other0_ne i) this.symm
    · apply IntegerCertificate.isCopy_of_adj huv hu.2.symm hv.2.symm
      rintro ⟨_, hm⟩
      have : i = other0 i := v.val.property.symm.trans (hm.trans hb0)
      exact (other0_ne i) this.symm
  exact repair_physical_column_on p G S H a B Subtype.val b b0 x hx hOutside hCopies

#print axioms column_repair_of_host

end PartitionedTriangleAbsorption.BlowupB.F0Direct
