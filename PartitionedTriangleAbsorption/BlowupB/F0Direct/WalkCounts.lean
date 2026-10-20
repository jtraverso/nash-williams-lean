/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.Geometry
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! # Counting short walks in the nonextreme part

All counts below concern ordered pairs of actual vertices.  In particular,
`arcs G S S` counts every physical edge twice.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkSupply

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (u : V) : Finset V :=
  D.filter (G.Adj u)

def arcs (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℝ :=
  ∑ u ∈ S, ((neighbors G T u).card : ℝ)

@[simp] theorem mem_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (u v : V) : v ∈ neighbors G D u ↔ v ∈ D ∧ G.Adj u v := by
  simp [neighbors]

theorem neighbors_subset (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (u : V) :
    neighbors G D u ⊆ D := filter_subset _ _

theorem arcs_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    arcs G S T = ∑ u ∈ S, ∑ v ∈ T, if G.Adj u v then (1 : ℝ) else 0 := by
  simp only [arcs, neighbors, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem arcs_eq_univ_sum (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    arcs G S T = ∑ u : V, ∑ v : V,
      if u ∈ S ∧ v ∈ T ∧ G.Adj u v then (1 : ℝ) else 0 := by
  simp only [ite_and]
  simp [arcs_eq_sum]

theorem arcs_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    0 ≤ arcs G S T := by
  exact sum_nonneg (fun u _ => Nat.cast_nonneg _)

theorem arcs_symm (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    arcs G S T = arcs G T S := by
  rw [arcs_eq_sum, arcs_eq_sum, sum_comm]
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro u hu
  simp only [G.adj_comm]

theorem arcs_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S S' T T' : Finset V} (hS : S ⊆ S') (hT : T ⊆ T') :
    arcs G S T ≤ arcs G S' T' := by
  apply le_trans (sum_le_sum fun u _ => Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hT)))
  apply sum_le_sum_of_subset_of_nonneg hS
  intro u hu hu'
  positivity

theorem arcs_le_mul (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    arcs G S T ≤ (S.card : ℝ) * T.card := by
  calc
    arcs G S T ≤ ∑ _u ∈ S, (T.card : ℝ) :=
      sum_le_sum fun u _ => Nat.cast_le.mpr (card_le_card (neighbors_subset G T u))
    _ = (S.card : ℝ) * T.card := by simp

theorem arcs_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {D S : Finset V} (hS : S ⊆ D) (d : ℝ)
    (hdeg : ∀ u ∈ D, d ≤ ((neighbors G D u).card : ℝ)) :
    (S.card : ℝ) * d ≤ arcs G S D := by
  calc
    (S.card : ℝ) * d = ∑ _u ∈ S, d := by simp
    _ ≤ arcs G S D := sum_le_sum fun u hu => hdeg u (hS hu)

theorem arcs_degree_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    {D S : Finset V} (hS : S ⊆ D) (d : ℝ)
    (hdeg : ∀ u ∈ D, ((neighbors G D u).card : ℝ) ≤ d) :
    arcs G S D ≤ (S.card : ℝ) * d := by
  calc
    arcs G S D ≤ ∑ _u ∈ S, d := sum_le_sum fun u hu => hdeg u (hS hu)
    _ = (S.card : ℝ) * d := by simp

theorem arcs_union_right_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T U : Finset V) : arcs G S (T ∪ U) ≤ arcs G S T + arcs G S U := by
  rw [arcs, arcs, arcs, ← sum_add_distrib]
  apply sum_le_sum
  intro v hv
  have heq : neighbors G (T ∪ U) v = neighbors G T v ∪ neighbors G U v := by
    ext w
    simp only [mem_neighbors, mem_union]
    tauto
  rw [heq]
  exact_mod_cast card_union_le (neighbors G T v) (neighbors G U v)

theorem arcs_union_left_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T U : Finset V) : arcs G (S ∪ T) U ≤ arcs G S U + arcs G T U := by
  rw [arcs_symm G (S ∪ T) U, arcs_symm G S U, arcs_symm G T U]
  exact arcs_union_right_le G U S T

theorem arcs_disjoint_union_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T U : Finset V) (h : Disjoint T U) :
    arcs G S (T ∪ U) = arcs G S T + arcs G S U := by
  simp only [arcs_eq_sum]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  exact sum_union h

theorem arcs_disjoint_union_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T U : Finset V) (h : Disjoint S T) :
    arcs G (S ∪ T) U = arcs G S U + arcs G T U := by
  rw [arcs_symm G (S ∪ T) U, arcs_symm G S U, arcs_symm G T U]
  exact arcs_disjoint_union_right G U S T h

theorem arcs_eq_card_pairs (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    arcs G S T = (((S ×ˢ T).filter fun uv => G.Adj uv.1 uv.2).card : ℝ) := by
  simp only [arcs_eq_sum, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_product]

private abbrev edgeGraph (E : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet E

private theorem edgeGraph_edges (E : Finset (Sym2 V)) [Fintype (edgeGraph E).edgeSet]
    (hE : ∀ e ∈ E, ¬ e.IsDiag) : (edgeGraph E).edgeFinset = E := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, edgeGraph, SimpleGraph.mem_edgeSet,
      SimpleGraph.fromEdgeSet_adj, mem_coe]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, fun huv => hE _ h (Sym2.mk_isDiag_iff.mpr huv)⟩

theorem two_mul_card_edges (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    (2 : ℝ) * E.card =
      ∑ u : V, ∑ v : V, if s(u, v) ∈ E then (1 : ℝ) else 0 := by
  have he : 2 * E.card =
      (univ.filter fun uv : V × V => (edgeGraph E).Adj uv.1 uv.2).card := by
    convert (edgeGraph E).two_mul_card_edgeFinset using 1
    congr 1
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset, edgeGraph, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, mem_coe]
    change e ∈ E ↔ e ∈ E ∧ ¬ e.IsDiag
    exact ⟨fun h => ⟨h, hE e h⟩, And.left⟩
  have hp : (univ.filter fun uv : V × V => (edgeGraph E).Adj uv.1 uv.2) =
      univ.filter (fun uv : V × V => s(uv.1, uv.2) ∈ E) := by
    ext uv
    simp only [mem_filter, mem_univ, true_and, edgeGraph, SimpleGraph.fromEdgeSet_adj, mem_coe]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, fun huv => hE _ h (Sym2.mk_isDiag_iff.mpr huv)⟩
  rw [hp] at he
  have hc := congrArg (fun k : ℕ => (k : ℝ)) he
  simpa only [Nat.cast_mul, Nat.cast_ofNat, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type] using hc

theorem arcs_self_eq_twice_induced (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    arcs G D D = 2 * (inducedEdges G D).card := by
  have hE : ∀ e ∈ inducedEdges G D, ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (mem_inter.mp he).1)
  rw [two_mul_card_edges _ hE, arcs_eq_sum]
  symm
  calc
    (∑ u : V, ∑ v : V, if s(u, v) ∈ inducedEdges G D then (1 : ℝ) else 0) =
        ∑ u : V, ∑ v : V, if u ∈ D ∧ v ∈ D ∧ G.Adj u v then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro u hu
      apply sum_congr rfl
      intro v hv
      congr 1
      simp only [inducedEdges, mem_inter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
      apply propext
      constructor
      · tauto
      · rintro ⟨huD, hvD, huv⟩
        exact ⟨huv, ⟨huD, hvD⟩, G.ne_of_adj huv⟩
    _ = ∑ u ∈ D, ∑ v ∈ D, if G.Adj u v then (1 : ℝ) else 0 := by
      simp only [ite_and]
      simp

theorem balanced_close {D U : Finset V} (hU : U ⊆ D) (r : ℝ)
    (hl : (D.card : ℝ) / 2 - r ≤ U.card)
    (hu : (U.card : ℝ) ≤ (D.card : ℝ) / 2 + r) :
    ∃ X ⊆ D, X.card = D.card / 2 ∧
      ((X \ U).card : ℝ) + (U \ X).card ≤ r + 1 := by
  have hklo : (D.card : ℝ) - 1 ≤ 2 * (D.card / 2 : ℕ) := by
    have : D.card ≤ 2 * (D.card / 2) + 1 := by omega
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    linarith
  have hkup : (2 : ℝ) * (D.card / 2 : ℕ) ≤ D.card := by
    exact_mod_cast Nat.mul_div_le D.card 2
  by_cases h : D.card / 2 ≤ U.card
  · obtain ⟨X, hXU, hXc⟩ := exists_subset_card_eq h
    refine ⟨X, hXU.trans hU, hXc, ?_⟩
    have hdiff := card_sdiff_add_card_eq_card hXU
    have hc := (congrArg (fun k : ℕ => (k : ℝ)) hdiff)
    push_cast at hc
    rw [hXc] at hc
    simp only [sdiff_eq_empty_iff_subset.mpr hXU, card_empty, Nat.cast_zero, zero_add]
    linarith
  · obtain ⟨X, hUX, hXD, hXc⟩ := exists_subsuperset_card_eq hU (by omega)
      (Nat.div_le_self D.card 2)
    refine ⟨X, hXD, hXc, ?_⟩
    have hdiff := card_sdiff_add_card_eq_card hUX
    have hc := (congrArg (fun k : ℕ => (k : ℝ)) hdiff)
    push_cast at hc
    rw [hXc] at hc
    simp only [sdiff_eq_empty_iff_subset.mpr hUX, card_empty, Nat.cast_zero, add_zero]
    linarith

theorem arcs_perturb (G : SimpleGraph V) [DecidableRel G.Adj]
    {D S T S' T' : Finset V} (hS : S ⊆ D) (hT : T ⊆ D)
    (hS' : S' ⊆ D) (hT' : T' ⊆ D) :
    arcs G S T ≤ arcs G S' T' +
      (((S \ S').card : ℝ) + (T \ T').card) * D.card := by
  have hleft : S ⊆ S' ∪ (S \ S') := by
    intro u hu
    by_cases h : u ∈ S' <;> simp [hu, h]
  have hright : T ⊆ T' ∪ (T \ T') := by
    intro u hu
    by_cases h : u ∈ T' <;> simp [hu, h]
  have h1 := arcs_mono G hleft (Subset.refl T)
  have h2 := arcs_union_left_le G S' (S \ S') T
  have h3 := arcs_mono G (Subset.refl S') hright
  have h4 := arcs_union_right_le G S' T' (T \ T')
  have h5 := arcs_le_mul G (S \ S') T
  have h6 := arcs_le_mul G S' (T \ T')
  have hTc : (T.card : ℝ) ≤ D.card := Nat.cast_le.mpr (card_le_card hT)
  have hSc : (S'.card : ℝ) ≤ D.card := Nat.cast_le.mpr (card_le_card hS')
  have h5' := mul_le_mul_of_nonneg_left hTc (show (0 : ℝ) ≤ (S \ S').card by positivity)
  have h6' := mul_le_mul_of_nonneg_right hSc (show (0 : ℝ) ≤ (T \ T').card by positivity)
  linarith

theorem two_mul_card_triEdges (S : Finset V) :
    (2 : ℝ) * (triEdges S).card = (S.card : ℝ) ^ 2 - S.card := by
  have hE : ∀ e ∈ triEdges S, ¬ e.IsDiag := by
    intro e he
    exact (mem_filter.mp he).2
  rw [two_mul_card_edges _ hE]
  have hpair : ∀ u v : V,
      (if s(u, v) ∈ triEdges S then (1 : ℝ) else 0) =
        (if u ∈ S ∧ v ∈ S then (1 : ℝ) else 0) -
        (if u ∈ S ∧ v = u then (1 : ℝ) else 0) := by
    intro u v
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases huv : u = v <;>
      simp_all [eq_comm]
  simp_rw [hpair, sum_sub_distrib]
  simp only [ite_and]
  simp [pow_two]

theorem editDistance_identity (E H : Finset (Sym2 V)) :
    (editDistance E H : ℝ) + 2 * (E ∩ H).card = E.card + H.card := by
  have h1 := card_sdiff_add_card_inter E H
  have h2 := card_sdiff_add_card_inter H E
  rw [inter_comm H E] at h2
  have h1' := congrArg (fun k : ℕ => (k : ℝ)) h1
  have h2' := congrArg (fun k : ℕ => (k : ℝ)) h2
  push_cast at h1' h2'
  simp only [editDistance, Nat.cast_add]
  linarith

theorem triEdges_mono {S T : Finset V} (h : S ⊆ T) : triEdges S ⊆ triEdges T := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he ⊢
    exact ⟨⟨h he.1.1, h he.1.2⟩, he.2⟩

theorem cliqueModel_subset {D X : Finset V} (hX : X ⊆ D) :
    cliqueModel D X ⊆ triEdges D := by
  exact union_subset (triEdges_mono hX) (triEdges_mono sdiff_subset)

theorem mk_mem_bipartiteModel {D X : Finset V} (hX : X ⊆ D) (u v : V) :
    s(u, v) ∈ bipartiteModel D X ↔
      (u ∈ X ∧ v ∈ D \ X) ∨ (u ∈ D \ X ∧ v ∈ X) := by
  simp only [bipartiteModel, cliqueModel, mem_sdiff, mem_union, triEdges,
    mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  have huXD : u ∈ X → u ∈ D := fun h => hX h
  have hvXD : v ∈ X → v ∈ D := fun h => hX h
  by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;>
    by_cases huD : u ∈ D <;> by_cases hvD : v ∈ D <;> by_cases heq : u = v <;>
    simp_all

theorem arcs_cut_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {D X : Finset V} (hX : X ⊆ D) :
    arcs G X (D \ X) = (inducedEdges G D ∩ bipartiteModel D X).card := by
  let E := inducedEdges G D ∩ bipartiteModel D X
  have hE : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeSet
      (SimpleGraph.mem_edgeFinset.mp (mem_inter.mp (mem_inter.mp he).1).1)
  have he := two_mul_card_edges E hE
  have hp : ∀ u v : V, (if s(u, v) ∈ E then (1 : ℝ) else 0) =
      (if u ∈ X ∧ v ∈ D \ X ∧ G.Adj u v then (1 : ℝ) else 0) +
      (if u ∈ D \ X ∧ v ∈ X ∧ G.Adj u v then (1 : ℝ) else 0) := by
    intro u v
    simp only [E, mem_inter, inducedEdges, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, mk_mem_bipartiteModel hX, triEdges, mem_filter,
      mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_sdiff]
    have huXD : u ∈ X → u ∈ D := fun h => hX h
    have hvXD : v ∈ X → v ∈ D := fun h => hX h
    by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;>
      by_cases huD : u ∈ D <;> by_cases hvD : v ∈ D <;> by_cases hadj : G.Adj u v <;>
      simp_all [G.ne_of_adj]
  simp_rw [hp, sum_add_distrib] at he
  rw [← arcs_eq_univ_sum, ← arcs_eq_univ_sum, arcs_symm G (D \ X) X] at he
  change arcs G X (D \ X) = (E.card : ℝ)
  linarith

theorem cliqueModel_card_identity {D X : Finset V} (hX : X ⊆ D) :
    (2 : ℝ) * (cliqueModel D X).card =
      (X.card : ℝ)^2 + ((D \ X).card : ℝ)^2 - D.card := by
  have hd : Disjoint (triEdges X) (triEdges (D \ X)) := by
    apply disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ u v =>
      simp only [triEdges, mem_filter, mk_mem_sym2_iff, mem_sdiff] at he hf
      exact hf.1.1.2 he.1.1
  have hc := card_sdiff_add_card_eq_card hX
  have hc' := congrArg (fun k : ℕ => (k : ℝ)) hc
  push_cast at hc'
  have ht1 := two_mul_card_triEdges X
  have ht2 := two_mul_card_triEdges (D \ X)
  simp only [cliqueModel, card_union_of_disjoint hd, Nat.cast_add]
  linarith

theorem model_card_bounds {D X : Finset V} (hX : X ⊆ D)
    (hbal : X.card = D.card / 2) (hm : (1 : ℝ) ≤ D.card) :
    (cliqueModel D X).card ≤ (D.card : ℝ)^2 / 4 ∧
      (bipartiteModel D X).card ≤ (D.card : ℝ)^2 / 4 := by
  have hc := card_sdiff_add_card_eq_card hX
  have hc' := congrArg (fun k : ℕ => (k : ℝ)) hc
  push_cast at hc'
  have hxy1 : (X.card : ℝ) ≤ (D \ X).card := by
    have : X.card ≤ (D \ X).card := by omega
    exact_mod_cast this
  have hxy2 : ((D \ X).card : ℝ) ≤ X.card + 1 := by
    have : (D \ X).card ≤ X.card + 1 := by omega
    exact_mod_cast this
  have hsq : (((D \ X).card : ℝ) - X.card)^2 ≤ 1 := by
    nlinarith
  have hclique := cliqueModel_card_identity hX
  have hk := two_mul_card_triEdges D
  have hb := card_sdiff_add_card_eq_card (cliqueModel_subset hX)
  have hb' := congrArg (fun k : ℕ => (k : ℝ)) hb
  push_cast at hb'
  change ((bipartiteModel D X).card : ℝ) + (cliqueModel D X).card = (triEdges D).card at hb'
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (((D \ X).card : ℝ) - X.card)]

theorem cut_distance_identities (G : SimpleGraph V) [DecidableRel G.Adj]
    {D X : Finset V} (hX : X ⊆ D) :
    (editDistance (inducedEdges G D) (cliqueModel D X) : ℝ) =
        (cliqueModel D X).card - (inducedEdges G D).card + 2 * arcs G X (D \ X) ∧
    (editDistance (inducedEdges G D) (bipartiteModel D X) : ℝ) =
        (bipartiteModel D X).card + (inducedEdges G D).card - 2 * arcs G X (D \ X) := by
  have hb := editDistance_identity (inducedEdges G D) (bipartiteModel D X)
  have hc := editDistance_identity (inducedEdges G D) (cliqueModel D X)
  have he : inducedEdges G D ∩ bipartiteModel D X =
      inducedEdges G D \ cliqueModel D X := by
    ext e
    have hh : e ∈ inducedEdges G D → e ∈ triEdges D := fun h => (mem_inter.mp h).2
    simp only [bipartiteModel, mem_inter, mem_sdiff]
    tauto
  have hp := card_sdiff_add_card_inter (inducedEdges G D) (cliqueModel D X)
  rw [← he] at hp
  have hp' := congrArg (fun k : ℕ => (k : ℝ)) hp
  push_cast at hp'
  have ha := arcs_cut_eq G hX
  constructor <;> linarith

end PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkSupply
