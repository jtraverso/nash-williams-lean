/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateCrossMatrix
public import PartitionedTriangleAbsorption.SignedHinge.Wedge

/-! # Finite physical support of the peeled integer function -/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

def functionSupport (f : Sym2 V → ℤ) : Finset (Sym2 V) := univ.filter (fun e => f e ≠ 0)

def functionRoots (f : Sym2 V → ℤ) : Finset V := vertSet (functionSupport f)

theorem functionSupport_card (f : Sym2 V → ℤ) :
    ((functionSupport f).card : ℤ) ≤ edgeFunctionCost f := by
  have h : ∀ e ∈ functionSupport f, (1 : ℤ) ≤ |f e| := by
    intro e he
    have hp : 0 < |f e| := abs_pos.mpr (mem_filter.mp he).2
    omega
  calc
    _ = ∑ _e ∈ functionSupport f, (1 : ℤ) := by simp
    _ ≤ ∑ e ∈ functionSupport f, |f e| := Finset.sum_le_sum h
    _ ≤ ∑ e, |f e| := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun e _ _ => abs_nonneg (f e))

theorem functionRoots_card (f : Sym2 V → ℤ) :
    ((functionRoots f).card : ℤ) ≤ 2 * edgeFunctionCost f := by
  have h := SignedHinge.card_vertSet_le (functionSupport f)
  have h' : ((functionRoots f).card : ℤ) ≤ 2 * (functionSupport f).card := by
    exact_mod_cast h
  linarith [functionSupport_card f]

theorem mem_functionRoots_left (f : Sym2 V → ℤ) (u v : V) (h : f s(u,v) ≠ 0) :
    u ∈ functionRoots f := by
  apply SignedHinge.mem_vertSet.mpr
  exact ⟨s(u,v), mem_filter.mpr ⟨mem_univ _, h⟩, Sym2.mem_mk_left _ _⟩

theorem mem_functionRoots_right (f : Sym2 V → ℤ) (u v : V) (h : f s(u,v) ≠ 0) :
    v ∈ functionRoots f := by
  apply SignedHinge.mem_vertSet.mpr
  exact ⟨s(u,v), mem_filter.mpr ⟨mem_univ _, h⟩, Sym2.mem_mk_right _ _⟩

theorem triEdges_subset_host (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) (hT : IsCopy p F0 G T) :
    triEdges T ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨⟨hu, hv⟩, hne⟩ :=
      (show (u ∈ T ∧ v ∈ T) ∧ u ≠ v from by
        simpa only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] using he)
    have hAdj := hT.1.1 hu hv hne
    simpa using hAdj

theorem triangleChainFunction_off_host (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (L : IntegralChain (Finset V)) (hL : Valid (IsCopy p F0 G) L)
    (e : Sym2 V) (he : e ∉ G.edgeFinset) : triangleChainFunction L e = 0 := by
  calc
    _ = L.eval (fun _ => 0) := by
      apply IntegralChain.eval_congr L
      intro z hz
      have hn : e ∉ triEdges z.2 := fun h => he (triEdges_subset_host p G z.2 (hL z hz) h)
      simp [ind, hn]
    _ = 0 := by simp [IntegralChain.eval]

theorem peeled_off_host (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset)
    (L : IntegralChain (Finset V)) (hL : Valid (IsCopy p F0 G) L)
    (f : Sym2 V → ℤ) (hP : ∀ e, ind P e = triangleChainFunction L e + f e)
    (e : Sym2 V) (he : e ∉ G.edgeFinset) : f e = 0 := by
  have h := hP e
  have hp : e ∉ P := fun h => he (hPG h)
  rw [show ind P e = 0 from by simp [ind, hp],
    triangleChainFunction_off_host p G L hL e he, zero_add] at h
  exact h.symm

theorem crossingMatrix_adj (p : V → Fin 2) (i : Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤ)
    (hG : ∀ e, e ∉ G.edgeFinset → f e = 0)
    (a : PartVertex p i) (b : PartVertex p (other0 i))
    (h : crossingMatrix p i f a b ≠ 0) : G.Adj a.val b.val := by
  by_contra hn
  have he : s(a.val,b.val) ∉ G.edgeFinset := by simpa using hn
  exact h (hG _ he)

theorem halfRow_root (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (r : PartVertex p i → ℤ)
    (hr : ∀ a, (∑ b, crossingMatrix p i f a b) = 2 * r a)
    (a : PartVertex p i) (ha : r a ≠ 0) : a.val ∈ functionRoots f := by
  have hExists : ∃ b, crossingMatrix p i f a b ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (∑ b, crossingMatrix p i f a b) = 0 := by simp [h]
    rw [hr a] at hz
    exact ha (by omega)
  obtain ⟨b, hb⟩ := hExists
  exact mem_functionRoots_left f a.val b.val hb

#print axioms functionRoots_card
#print axioms peeled_off_host
#print axioms halfRow_root

end PartitionedTriangleAbsorption.BlowupB.F0Direct
