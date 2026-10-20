/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingRestriction
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply

@[expose] public section

/-!
# Deleting a sparse physical edge set

The two estimates used by fractional repair are deterministic. A query with
at most D roots loses at most D times the deleted maximum degree. A remaining
edge loses at most the sum of the deleted degrees of its two endpoints in
triangle weight. Both estimates apply to an arbitrary host.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset StructuralF3General RootedEmbeddingSelection AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem guardedSupply_deleteEdges (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (Allowed : Fin t → Fin t → Prop)
    (D : ℕ) (a d : ℝ) (hs : GuardedSupply p G Allowed D a)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d) :
    GuardedSupply p (G.deleteEdges (B : Set (Sym2 V))) Allowed D (a - D * d) := by
  classical
  intro S hS i hguard
  let W := guardedNeighbours p G S i
  have hsum : (∑ u ∈ S, (incidentLoad B u : ℝ)) ≤ (D : ℝ) * d := by
    calc
      _ ≤ (S.card : ℝ) * d := by
        simpa only [incidentLoad, sum_const, nsmul_eq_mul] using
          (sum_le_sum (s := S) fun u _ => hB u)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hd
  have hcountN := RootedEmbeddingSelection.available_card_budget W ∅ S B
  simp only [empty_union, card_empty, Nat.add_zero] at hcountN
  have hcount : (W.card : ℝ) ≤ ((W \ blockedMany B S).card : ℝ) +
      ∑ u ∈ S, (incidentLoad B u : ℝ) := by exact_mod_cast hcountN
  have hsub : W \ blockedMany B S ⊆
      guardedNeighbours p (G.deleteEdges (B : Set (Sym2 V))) S i := by
    intro w hw
    obtain ⟨hw, hbad⟩ := mem_sdiff.mp hw
    obtain ⟨_, hwi, hwa⟩ := mem_filter.mp hw
    refine mem_filter.mpr ⟨mem_univ _, hwi, ?_⟩
    intro u hu
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hwa u hu, ?_⟩
    intro he
    exact hbad (mem_biUnion.mpr ⟨u, hu, mem_filter.mpr ⟨mem_univ _, he⟩⟩)
  have hcard : ((W \ blockedMany B S).card : ℝ) ≤
      (guardedNeighbours p (G.deleteEdges (B : Set (Sym2 V))) S i).card :=
    by exact_mod_cast card_le_card hsub
  have hW : a ≤ (W.card : ℝ) := hs S hS i hguard
  linarith

theorem nearLoads_restrict (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (B : Finset (Sym2 V)) (hHG : H ≤ G)
    (hremoved : ∀ a b, G.Adj a b → ¬ H.Adj a b → s(a,b) ∈ B)
    (b ε d : ℝ) (hb : 0 < b) (hn : 0 < Fintype.card V) (hB : DegBounded B d)
    (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p F G T → 0 ≤ φ T ∧ φ T ≤ b / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) :
    ∀ e ∈ H.edgeFinset,
      |(∑ T ∈ copies p F H with e ∈ triEdges T, φ T) - 1| ≤
        ε + 2 * b * d / Fintype.card V := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have heH : H.Adj u v := H.mem_edgeFinset.mp he
    have heG : s(u,v) ∈ G.edgeFinset := G.mem_edgeFinset.mpr (hHG heH)
    let S := PackingRestriction.edgeCopies p F G s(u,v)
    let T := PackingRestriction.edgeCopies p F H s(u,v)
    have hTS : T ⊆ S := PackingRestriction.edgeCopies_mono hHG _
    have hcard : ((S \ T).card : ℝ) ≤ 2 * d :=
      (PackingRestriction.lost_copies_card B hremoved heH).trans (by
        have hu := hB u
        have hv := hB v
        linarith)
    have hloss : ∑ U ∈ S \ T, φ U ≤ 2 * d * (b / Fintype.card V) := by
      calc
        _ ≤ ∑ _U ∈ S \ T, b / Fintype.card V := by
          apply sum_le_sum
          intro U hU
          exact (hw U (PackingRestriction.mem_copies.mp
            (mem_filter.mp (mem_sdiff.mp hU).1).1)).2
        _ = ((S \ T).card : ℝ) * (b / Fintype.card V) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (div_pos hb hnR).le
    have hloss0 : 0 ≤ ∑ U ∈ S \ T, φ U := by
      apply sum_nonneg
      intro U hU
      exact (hw U (PackingRestriction.mem_copies.mp
        (mem_filter.mp (mem_sdiff.mp hU).1).1)).1
    have hsum : (∑ U ∈ S \ T, φ U) + (∑ U ∈ T, φ U) = ∑ U ∈ S, φ U :=
      sum_sdiff hTS
    have hmass : |(∑ U ∈ S, φ U) - 1| ≤ ε := hload _ heG
    have hlower := (abs_le.mp hmass).1
    have hupper := (abs_le.mp hmass).2
    change |(∑ U ∈ T, φ U) - 1| ≤ _
    have hfactor : 2 * d * (b / Fintype.card V) = 2 * b * d / Fintype.card V := by ring
    rw [hfactor] at hloss
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem nearLoads_deleteEdges (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (b ε d : ℝ) (hb : 0 < b) (hn : 0 < Fintype.card V) (hB : DegBounded B d)
    (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p F G T → 0 ≤ φ T ∧ φ T ≤ b / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) :
    ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
      |(∑ T ∈ copies p F (G.deleteEdges (B : Set (Sym2 V))) with e ∈ triEdges T, φ T) - 1| ≤
        ε + 2 * b * d / Fintype.card V := by
  apply nearLoads_restrict p F G _ B (SimpleGraph.deleteEdges_le _) _ b ε d hb hn hB φ hw hload
  intro a c hac hnot
  by_contra h
  exact hnot (SimpleGraph.deleteEdges_adj.mpr ⟨hac, h⟩)

#print axioms guardedSupply_deleteEdges
#print axioms nearLoads_restrict
#print axioms nearLoads_deleteEdges

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
