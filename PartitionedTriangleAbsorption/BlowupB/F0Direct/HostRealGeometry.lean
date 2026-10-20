/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateCrossMatrix
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkConsequences
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealInternalInverse

@[expose] public section

/-! # Geometric inputs for the complete-crossing real inverse

The vertex types are precisely the existing `PartVertex` subtypes.  The
triangle count is for ordered opposite pairs, so it includes the factor two
required by the real signless inverse with `tau = theta / 100`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealGeometry

open Finset CloneSupply TypedApplicationLinks WalkSupply HostWalkQueries HostHinges
open PartitionedTriangleAbsorption.F0Direct.BalancedLinearRepair
open PartitionedTriangleAbsorption.F0Direct.SignlessTriangle
open PartitionedTriangleAbsorption.F0Direct.RealComplete

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε θ : ℝ}

abbrev partGraph (p : V → Fin 2) (G : SimpleGraph V) (i : Fin 2) :
    SimpleGraph (PartVertex p i) := G.comap Subtype.val

theorem partVertex_card (p : V → Fin 2) (i : Fin 2) :
    Fintype.card (PartVertex p i) = (partSet p i).card := by
  exact Fintype.card_subtype (fun v => p v = i)

theorem partVertex_card_le (p : V → Fin 2) (i : Fin 2) :
    Fintype.card (PartVertex p i) ≤ Fintype.card V := by
  rw [partVertex_card]
  exact card_le_univ _

theorem partVertex_card_lower (h : HostHyp p G α ε) (he : ε ≤ 1/3) (i : Fin 2) :
    (Fintype.card V : ℝ) / 3 ≤ Fintype.card (PartVertex p i) := by
  rw [partVertex_card]
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right he hn
  have hs := h.part_size i
  nlinarith only [hm, hs]

theorem partGraph_degree (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (u : PartVertex p i) :
    (partGraph p G i).degree u = partDeg p G i u.val := by
  classical
  have hm : ((partGraph p G i).neighborFinset u).map (Function.Embedding.subtype _) =
      partNbrs p G i u.val := by
    ext v
    simp only [mem_map, SimpleGraph.mem_neighborFinset, mem_partNbrs]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · rintro ⟨hp, hg⟩
      exact ⟨⟨v, hp⟩, hg, rfl⟩
  have hc := congrArg Finset.card hm
  simpa only [card_map, SimpleGraph.card_neighborFinset_eq_degree, partDeg] using hc

theorem partGraph_edges_lower (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) :
    (Fintype.card V : ℝ)^2 / 40 ≤ Fintype.card (HostEdge (partGraph p G i)) := by
  classical
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hd : ∀ u : PartVertex p i, n / 5 ≤ ((partGraph p G i).degree u : ℝ) := by
    intro u
    rw [partGraph_degree]
    have hl := h.internal_lower u.val
    rw [u.property] at hl
    change (1/4-ε)*n ≤ _ at hl
    have hem := mul_le_mul_of_nonneg_right b.eps_le hn
    nlinarith only [hl, hem, hn]
  have hs := sum_le_sum (fun u (_hu : u ∈ (univ : Finset (PartVertex p i))) => hd u)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hs
  have hsum : (∑ u : PartVertex p i, ((partGraph p G i).degree u : ℝ)) =
      2 * ((partGraph p G i).edgeFinset.card : ℝ) := by
    exact_mod_cast (partGraph p G i).sum_degrees_eq_twice_card_edges
  rw [hsum] at hs
  have hpart := partVertex_card_lower h (by linarith only [b.eps_le]) i
  change n/3 ≤ (Fintype.card (PartVertex p i) : ℝ) at hpart
  have hmul := mul_le_mul_of_nonneg_right hpart (show (0 : ℝ) ≤ n/5 by positivity)
  have heq : Fintype.card (HostEdge (partGraph p G i)) = (partGraph p G i).edgeFinset.card :=
    Fintype.card_coe _
  rw [heq]
  change n^2/40 ≤ ((partGraph p G i).edgeFinset.card : ℝ)
  nlinarith only [hs, hmul, sq_nonneg n]

theorem arcs_diagonal_eq_partPairs (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (i : Fin 2) (u : PartVertex p i) :
    arcs G (neighbors G (partSet p i) u.val) (neighbors G (partSet p i) u.val) =
      ((trianglePairs (partGraph p G i) u).card : ℝ) := by
  classical
  have hs (f : V → ℝ) : (∑ a : PartVertex p i, f a.val) = ∑ a ∈ partSet p i, f a :=
    (Finset.sum_subtype (partSet p i) (fun _ => mem_partSet) f).symm
  calc
    _ = ∑ a ∈ partSet p i, ∑ c ∈ partSet p i,
        if G.Adj u.val a ∧ G.Adj u.val c ∧ G.Adj a c then (1 : ℝ) else 0 := by
      rw [arcs_eq_sum]
      simp only [neighbors, Finset.sum_filter, ite_and, Finset.sum_ite_irrel,
        Finset.sum_const_zero]
    _ = ∑ a : PartVertex p i, ∑ c : PartVertex p i,
        if G.Adj u.val a.val ∧ G.Adj u.val c.val ∧ G.Adj a.val c.val then (1 : ℝ) else 0 := by
      symm
      calc
        _ = ∑ a ∈ partSet p i, ∑ c : PartVertex p i,
            if G.Adj u.val a ∧ G.Adj u.val c.val ∧ G.Adj a c.val then (1 : ℝ) else 0 :=
          hs (fun a => ∑ c : PartVertex p i,
            if G.Adj u.val a ∧ G.Adj u.val c.val ∧ G.Adj a c.val then (1 : ℝ) else 0)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          exact hs (fun c =>
            if G.Adj u.val a ∧ G.Adj u.val c ∧ G.Adj a c then (1 : ℝ) else 0)
    _ = _ := by
      simp only [trianglePairs, card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type, SimpleGraph.comap_adj]

theorem good_part_pairs_lower (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) (hext : Nonextreme G (partSet p i) α)
    (u : PartVertex p i) :
    2 * (θ/100) * (Fintype.card V : ℝ)^2 ≤ ((trianglePairs (partGraph p G i) u).card : ℝ) := by
  have hm := (b.part_size h i).1
  have hreg := halfRegular_of_host h b.eps_nonneg (by linarith only [b.eps_le]) θ
    (by linarith only [b.eps_theta, b.eps_nonneg]) i
  have hw := arcs_neighbors_gt G (partSet p i) α θ b.theta_pos b.theta_le b.theta_alpha
    (by linarith only [hm]) hreg hext (mem_partSet.mpr u.property)
    (mem_partSet.mpr u.property)
  rw [arcs_diagonal_eq_partPairs p G i u] at hw
  have hp := partVertex_card_lower h (by linarith only [b.eps_le]) i
  rw [partVertex_card] at hp
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hsq : (Fintype.card V : ℝ)^2 ≤ 9 * ((partSet p i).card : ℝ)^2 := by
    have hm0 : (0 : ℝ) ≤ (partSet p i).card := Nat.cast_nonneg _
    nlinarith only [hp, hn, hm0, sq_nonneg ((partSet p i).card - (Fintype.card V : ℝ)/3)]
  have htm := mul_le_mul_of_nonneg_left hsq b.theta_pos.le
  have ht0 := mul_nonneg b.theta_pos.le (sq_nonneg (Fintype.card V : ℝ))
  nlinarith only [hw, htm, ht0]

theorem sizeBounds (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2) :
    SizeBounds (Internal.matrix (partGraph p G i))
      (Internal.matrix (partGraph p G (other0 i))) (Fintype.card V) := by
  have he : ε ≤ 1/3 := by linarith only [b.eps_le]
  refine ⟨by have := b.order_large; linarith,
    partVertex_card_lower h he i, partVertex_card_lower h he (other0 i),
    Nat.cast_le.mpr (partVertex_card_le p (other0 i)), ?_, ?_, partGraph_edges_lower b h (other0 i)⟩
  · intro u
    exact (Internal.matrix_row_bound _ u).trans (Nat.cast_le.mpr (partVertex_card_le p i))
  · intro u
    exact (Internal.matrix_row_bound _ u).trans
      (Nat.cast_le.mpr (partVertex_card_le p (other0 i)))

theorem exists_geometry (b : Budget α ε θ (Fintype.card V)) (h : HostHyp p G α ε) :
    ∃ i : Fin 2,
      SizeBounds (Internal.matrix (partGraph p G i))
        (Internal.matrix (partGraph p G (other0 i))) (Fintype.card V) ∧
      (Fintype.card (PartVertex p i) : ℝ) ≤ Fintype.card V ∧
      ∀ u : PartVertex p i, 2 * (θ/100) * (Fintype.card V : ℝ)^2 ≤
        ((trianglePairs (partGraph p G i) u).card : ℝ) := by
  obtain ⟨i, hi⟩ := h.good_part
  exact ⟨i, sizeBounds b h i, Nat.cast_le.mpr (partVertex_card_le p i),
    good_part_pairs_lower b h i hi⟩

#print axioms partGraph_edges_lower
#print axioms good_part_pairs_lower
#print axioms exists_geometry

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealGeometry
