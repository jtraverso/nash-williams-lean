/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.GeometryKept
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.FiniteLibrary

@[expose] public section

/-!
# Nonextremality survives the deletions used by private placement

A balanced cut extends exactly after adding removed vertices.  Hence its
model incurs no cost on pairs whose two endpoints were kept.  The estimate
uses only the number of removed vertices and edges, never divisibility of
the new host.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply AntiEdgeSelection PhysicalHingeSupply TypedApplicationLinks
open StructuralF3General.FiniteLibrary

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable instance deleteGraph_decidable (G : SimpleGraph V) (B : Finset (Sym2 V)) :
    DecidableRel (G.deleteEdges (B : Set (Sym2 V))).Adj := Classical.decRel _

theorem inducedEdges_delete (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (D : Finset V) :
    inducedEdges (G.deleteEdges (B : Set (Sym2 V))) D = inducedEdges G D \ B := by
  classical
  ext e
  simp only [inducedEdges, SimpleGraph.edgeFinset_deleteEdges, mem_inter, mem_sdiff]
  tauto

theorem inducedEdges_restrict_delete (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) {D D' : Finset V} (hD : D' ⊆ D) :
    ((inducedEdges G D \ B) ∩ triEdges D') =
      inducedEdges (G.deleteEdges (B : Set (Sym2 V))) D' := by
  classical
  rw [inducedEdges_delete]
  have ht := WalkSupply.triEdges_mono hD
  ext e
  simp only [inducedEdges, mem_sdiff, mem_inter]
  constructor
  · rintro ⟨⟨⟨he,_⟩,hb⟩,hd⟩
    exact ⟨⟨he,hd⟩,hb⟩
  · rintro ⟨⟨he,hd⟩,hb⟩
    exact ⟨⟨⟨he,ht hd⟩,hb⟩,hd⟩

theorem Nonextreme.restrict_delete
    {G : SimpleGraph V} [DecidableRel G.Adj] {D D' : Finset V} {a : ℝ}
    (h : Nonextreme G D (2*a)) (ha : 0 ≤ a) (hD : D' ⊆ D)
    (B : Finset (Sym2 V))
    (hbudget : ((D \ D').card : ℝ)*D.card + B.card ≤ a*(D.card : ℝ)^2) :
    Nonextreme (G.deleteEdges (B : Set (Sym2 V))) D' a := by
  classical
  intro X' hX' hbal'
  obtain ⟨X,hX,hbal,hXX⟩ := balanced_extension hD hX' hbal'
  obtain ⟨hb,hc⟩ := h X hX hbal
  have hpair : ((triEdges D \ triEdges D').card : ℝ) ≤
      (D \ D').card * (D.card : ℝ) := by exact_mod_cast card_lost_pairs hD
  have hsq : a*(D'.card : ℝ)^2 ≤ a*(D.card : ℝ)^2 := by
    gcongr
  have hb' := editDistance_le_restrict_delete (inducedEdges G D) (bipartiteModel D X)
    (triEdges D) (triEdges D') B inter_subset_right sdiff_subset
  have hc' := editDistance_le_restrict_delete (inducedEdges G D) (cliqueModel D X)
    (triEdges D) (triEdges D') B inter_subset_right (WalkSupply.cliqueModel_subset hX)
  rw [inducedEdges_restrict_delete G B hD, bipartiteModel_inter hD hX hXX] at hb'
  rw [inducedEdges_restrict_delete G B hD, cliqueModel_inter hD hX hXX] at hc'
  have hbr : (editDistance (inducedEdges G D) (bipartiteModel D X) : ℝ) ≤
      editDistance (inducedEdges (G.deleteEdges (B : Set (Sym2 V))) D') (bipartiteModel D' X') +
      (triEdges D \ triEdges D').card + B.card := by exact_mod_cast hb'
  have hcr : (editDistance (inducedEdges G D) (cliqueModel D X) : ℝ) ≤
      editDistance (inducedEdges (G.deleteEdges (B : Set (Sym2 V))) D') (cliqueModel D' X') +
      (triEdges D \ triEdges D').card + B.card := by exact_mod_cast hc'
  constructor <;> nlinarith

theorem inducedEdges_kept_map (G : SimpleGraph V) [DecidableRel G.Adj]
    (Keep : Finset V) (B : Finset (Sym2 V)) (S : Finset {v : V // v ∈ Keep}) :
    (inducedEdges (keptGraph G Keep B) S).map (edgeEmb (Function.Embedding.subtype _)) =
      inducedEdges (G.deleteEdges (B : Set (Sym2 V))) (S.map (Function.Embedding.subtype _)) := by
  classical
  let f : {v : V // v ∈ Keep} ↪ V := Function.Embedding.subtype _
  rw [inducedEdges_delete]
  apply Subset.antisymm
  · intro e he
    obtain ⟨e',he',rfl⟩ := mem_map.mp he
    obtain ⟨hg,hs⟩ := mem_inter.mp he'
    have hsm : edgeEmb f e' ∈ triEdges (S.map f) := by
      rw [PhysicalHingeSupply.triEdges_map]
      exact mem_map_of_mem _ hs
    induction e' using Sym2.ind with
    | _ x y =>
      obtain ⟨hg,hb⟩ := (keptGraph_adj G Keep B x y).mp (SimpleGraph.mem_edgeFinset.mp hg)
      exact mem_sdiff.mpr ⟨mem_inter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hg,hsm⟩,hb⟩
  · intro e he
    obtain ⟨hE,hb⟩ := mem_sdiff.mp he
    obtain ⟨hg,hs⟩ := mem_inter.mp hE
    rw [PhysicalHingeSupply.triEdges_map] at hs
    obtain ⟨e',hs',rfl⟩ := mem_map.mp hs
    apply mem_map.mpr
    refine ⟨e',mem_inter.mpr ⟨?_,hs'⟩,rfl⟩
    induction e' using Sym2.ind with
    | _ x y =>
      exact SimpleGraph.mem_edgeFinset.mpr
        ((keptGraph_adj G Keep B x y).mpr ⟨SimpleGraph.mem_edgeFinset.mp hg,hb⟩)

theorem nonextreme_kept_of_restricted
    (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Keep : Finset V) (B : Finset (Sym2 V)) (i : Fin 2) (a : ℝ)
    (h : Nonextreme (G.deleteEdges (B : Set (Sym2 V))) (partSet p i ∩ Keep) a) :
    Nonextreme (keptGraph G Keep B)
      (partSet (fun v : {v : V // v ∈ Keep} => p v.val) i) a := by
  classical
  let f : {v : V // v ∈ Keep} ↪ V := Function.Embedding.subtype _
  let D := partSet (fun v : {v : V // v ∈ Keep} => p v.val) i
  intro X hX hbal
  have hDm : D.map f = partSet p i ∩ Keep := partSet_kept_map p Keep i
  have hXm : X.map f ⊆ partSet p i ∩ Keep := hDm ▸ map_subset_map.mpr hX
  have hbm : (X.map f).card = (partSet p i ∩ Keep).card / 2 := by
    rw [← hDm, card_map, card_map]
    exact hbal
  obtain ⟨hb,hc⟩ := h (X.map f) hXm hbm
  have he : inducedEdges (G.deleteEdges (B : Set (Sym2 V))) (partSet p i ∩ Keep) =
      (inducedEdges (keptGraph G Keep B) D).map (edgeEmb f) := by
    rw [← hDm, inducedEdges_kept_map]
  rw [he, ← hDm, card_map, bipartiteModel_map, editDistance_map] at hb
  rw [he, ← hDm, card_map, cliqueModel_map, editDistance_map] at hc
  exact ⟨hb,hc⟩

theorem HostHyp.kept
    {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {a ε η δ : ℝ} (h : HostHyp p G (2*a) ε)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/3)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hη1 : η ≤ 1)
    (hηa : η ≤ a/100) (hδa : δ ≤ a/100)
    (Keep : Finset V) (B : Finset (Sym2 V))
    (hmiss : ((univ \ Keep).card : ℝ) ≤ η * Fintype.card V / 2)
    (hB : DegBounded B (δ * Fintype.card V)) :
    HostHyp (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B)
      a (2*(ε+η+δ)) := by
  classical
  apply h.kept_of_nonextreme hε hη hδ hη1 Keep B hmiss hB
  obtain ⟨i,hi⟩ := h.good_part
  refine ⟨i,nonextreme_kept_of_restricted p G Keep B i a ?_⟩
  apply hi.restrict_delete ha inter_subset_left B
  let n : ℝ := Fintype.card V
  let d : ℝ := (partSet p i).card
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hdle : d ≤ n := by
    dsimp [d,n]
    exact_mod_cast card_le_univ (partSet p i)
  have hdge : n/3 ≤ d := by
    have hs := h.part_size i
    change (1-ε)*n/2 ≤ d at hs
    nlinarith [mul_le_mul_of_nonneg_right hε1 hn]
  have hr : ((partSet p i \ (partSet p i ∩ Keep)).card : ℝ) ≤
      ((univ \ Keep).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro v hv
    obtain ⟨hv,hn⟩ := mem_sdiff.mp hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hk => hn (mem_inter.mpr ⟨hv,hk⟩)⟩
  have hr' : ((partSet p i \ (partSet p i ∩ Keep)).card : ℝ) ≤ η*n/2 := hr.trans hmiss
  have hb : (B.card : ℝ) ≤ n*(δ*n) := card_le_order_mul_degree B (δ*n) hB
  have hprod : ((partSet p i \ (partSet p i ∩ Keep)).card : ℝ)*d ≤ (η*n/2)*n := by
    exact mul_le_mul hr' hdle hd (by positivity)
  have hsq : (n/3)^2 ≤ d^2 := by gcongr
  have hsqm := mul_le_mul_of_nonneg_left hsq ha
  have hcoef : η/2+δ ≤ a/9 := by linarith
  have hcoefm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg n)
  change ((partSet p i \ (partSet p i ∩ Keep)).card : ℝ)*d + B.card ≤ a*d^2
  nlinarith

#print axioms HostHyp.kept

#print axioms Nonextreme.restrict_delete
#print axioms inducedEdges_kept_map
#print axioms nonextreme_kept_of_restricted

end PartitionedTriangleAbsorption.BlowupB.F0Direct
