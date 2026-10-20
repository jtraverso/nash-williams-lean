/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.PrivateFamily
public import PartitionedTriangleAbsorption.PrivateTemplateStage69.LedgerStep

@[expose] public section

/-!
# From robust bounded terminals to placement against a global ledger

The terminal hypothesis below is explicitly an intermediate input.  It is
required in every induced host after a sparse edge deletion.  The conclusion
is the existing generic `PrivateStep` contract.  In particular the terminal
is applied on the kept vertex subtype, so its auxiliary vertices cannot be
heavy vertices of the ledger.

No condition of divisibility is imposed on the host after deletion.  Only the
small piece has to be integrally divisible.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks PhysicalHingeSupply AntiEdgeSelection
open PrivateTemplateStage69 StructuralF3General.PrivateFamily

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual host used for a local placement. -/
def keptGraph (G : SimpleGraph V) (Keep : Finset V) (B : Finset (Sym2 V)) :
    SimpleGraph {v : V // v ∈ Keep} :=
  (G.deleteEdges (B : Set (Sym2 V))).induce (Keep : Set V)

noncomputable instance keptGraph_decidable (G : SimpleGraph V) (Keep : Finset V)
    (B : Finset (Sym2 V)) : DecidableRel (keptGraph G Keep B).Adj := Classical.decRel _

theorem keptGraph_adj (G : SimpleGraph V) (Keep : Finset V) (B : Finset (Sym2 V))
    (x y : {v : V // v ∈ Keep}) :
    (keptGraph G Keep B).Adj x y ↔ G.Adj x.val y.val ∧ s(x.val,y.val) ∉ B := by
  simp [keptGraph]

/-- A bounded terminal theorem robust under deletion of vertices and edges.
This is a producer contract; this definition does not assert its existence. -/
def KeptTerminal (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m C : ℕ) (D a : ℝ) : Prop :=
  ∀ Keep : Finset V, (((univ \ Keep).card : ℕ) : ℝ) ≤ a / 2 →
    ∀ B : Finset (Sym2 V), DegBounded B D →
      ∀ P : Finset (Sym2 {v : V // v ∈ Keep}),
        P ⊆ (keptGraph G Keep B).edgeFinset → P.card ≤ m →
        IsIntDiv (fun v : {v : V // v ∈ Keep} => p v.val) F0 P →
      ∃ A : Finset (Sym2 {v : V // v ∈ Keep}),
        A ⊆ (keptGraph G Keep B).edgeFinset ∧ Disjoint A P ∧
        HasDecomp (fun v : {v : V // v ∈ Keep} => p v.val) F0 A ∧
        HasDecomp (fun v : {v : V // v ∈ Keep} => p v.val) F0 (A ∪ P) ∧ A.card ≤ C

theorem privateStep_of_keptTerminal (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (m C : ℕ) (T D a : ℝ) (hT : 0 < T)
    (hterm : KeptTerminal p G m C D a) :
    PrivateStep p F0 G m C T D a := by
  classical
  intro L hL hLc P hPG hm hdiv
  let Keep : Finset V := univ.filter fun v =>
    (incidentLoad L v : ℝ) ≤ T ∨ v ∈ vertSet P
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ a / 2 := by
    have hh := card_highLoad_le L T
    change (High.card : ℝ) * T ≤ 2 * L.card at hh
    nlinarith
  have hmiss : (((univ \ Keep).card : ℕ) : ℝ) ≤ a / 2 := by
    have hsub : univ \ Keep ⊆ High := by
      intro v hv
      have hn := (mem_sdiff.mp hv).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      by_contra h
      exact hn (mem_filter.mpr ⟨mem_univ _, Or.inl (not_lt.mp h)⟩)
    exact (show (((univ \ Keep).card : ℕ) : ℝ) ≤ High.card by
      exact_mod_cast card_le_card hsub).trans hHigh
  let U := {v : V // v ∈ Keep}
  let valE : U ↪ V := Function.Embedding.subtype _
  let pU : U → Fin 2 := p ∘ valE
  let B : Finset (Sym2 V) := L \ P
  have hB : DegBounded B D := by
    intro v
    exact (show (incidentLoad B v : ℝ) ≤ incidentLoad L v by
      exact_mod_cast StructuralF3General.PrivateFamily.incidentLoad_mono sdiff_subset v).trans
        (hL v)
  let PU : Finset (Sym2 U) := univ.filter fun e => edgeEmb valE e ∈ P
  have hPKeep : ∀ e ∈ P, ∀ v ∈ e, v ∈ Keep := fun e he v hv =>
    mem_filter.mpr ⟨mem_univ _, Or.inr (mem_filter.mpr ⟨mem_univ _, e, he, hv⟩)⟩
  have hPU : PU.map (edgeEmb valE) = P := map_comap_edges Keep P hPKeep
  have hPUm : PU.card ≤ m := by
    rw [← card_map (edgeEmb valE), hPU]
    exact hm
  have hdivU : IsIntDiv pU F0 PU := by
    apply isIntDiv_comap valE
    rw [hPU]
    exact hdiv
  have hPUG : PU ⊆ (keptGraph G Keep B).edgeFinset := by
    intro e he
    have hp := (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ x y =>
      have hg := SimpleGraph.mem_edgeFinset.mp (hPG hp)
      have hn : s(valE x, valE y) ∉ B := by
        intro hb
        exact (mem_sdiff.mp hb).2 hp
      exact SimpleGraph.mem_edgeFinset.mpr ((keptGraph_adj G Keep B x y).mpr ⟨hg, hn⟩)
  obtain ⟨AU, hAUG, hAUP, hdAU, hdAUP, hAUc⟩ :=
    hterm Keep hmiss B hB PU hPUG hPUm hdivU
  refine ⟨AU.map (edgeEmb valE), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    have hh := SimpleGraph.mem_edgeFinset.mp (hAUG he')
    induction e' using Sym2.ind with
    | _ x y =>
      exact SimpleGraph.mem_edgeFinset.mpr ((keptGraph_adj G Keep B x y).mp hh).1
  · apply disjoint_left.mpr
    intro e he heL
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    by_cases hp : edgeEmb valE e' ∈ P
    · exact disjoint_left.mp hAUP he' (mem_filter.mpr ⟨mem_univ _, hp⟩)
    · have hb : edgeEmb valE e' ∈ B := mem_sdiff.mpr ⟨heL, hp⟩
      have hh := SimpleGraph.mem_edgeFinset.mp (hAUG he')
      induction e' using Sym2.ind with
      | _ x y => exact ((keptGraph_adj G Keep B x y).mp hh).2 hb
  · exact hasDecomp_map valE (fun _ => rfl) hdAU
  · rw [← hPU, ← map_union]
    exact hasDecomp_map valE (fun _ => rfl) hdAUP
  · rw [card_map]
    exact hAUc
  · intro v hv
    obtain ⟨_, e, he, hve⟩ := mem_filter.mp hv
    obtain ⟨e', _, rfl⟩ := mem_map.mp he
    simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.mem_map] at hve
    obtain ⟨x, _, rfl⟩ := hve
    rcases (mem_filter.mp x.2).2 with h | h
    · exact Or.inr h
    · exact Or.inl h

#print axioms privateStep_of_keptTerminal

end PartitionedTriangleAbsorption.BlowupB.F0Direct
