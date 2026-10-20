/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalMovesFrameStage87
public import PartitionedTriangleAbsorption.PairSplitDeploymentStage87

/-! # Recovering the final move ledger and inserting later catalysts

A deployment theorem returns a configuration and a trace. Subsequent choices
must avoid every edge ever used, not just the last configuration. The theorem
below extracts that finite ledger from the trace, with its exact budget, and
restricts the trace's added edges to the ledger. Decomposable catalysts chosen
outside this ledger can then be inserted retrospectively without breaking any
earlier freshness condition. This does not select the catalysts or finish the
token-cut/cleanup producer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.MoveLedgerStage88

open Finset PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Extract a real terminal ledger. The supported trace can subsequently be
continued from precisely this ledger, and all its added edges lie in it. -/
theorem terminal_ledger {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) (hX : X ⊆ U) :
    ∃ L : Finset (Sym2 V), U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * n ∧
      PhysicalMoves p F (E ∩ L) B U X Y n ∧
      (∀ Z m, PhysicalMoves p F E B L Y Z m →
        PhysicalMoves p F E B U X Z (n + m)) := by
  induction h with
  | stop U X =>
    refine ⟨U, Subset.refl _, hX, by simp, .stop _ _, ?_⟩
    intro Z m hm
    simpa using hm
  | @step U X Y Q R H n hx hq hf hphys hm hH hR ht ih =>
    have hnext : (X \ Q) ∪ R ⊆ U ∪ H ∪ R := by
      intro e he
      simp only [mem_union, mem_sdiff] at he ⊢
      rcases he with ⟨he, _⟩ | he
      · exact Or.inl (Or.inl (hx he))
      · exact Or.inr he
    obtain ⟨L, hUL, hYL, hc, hsmall, hcont⟩ := ih hnext
    have hUL' : U ⊆ L := by
      intro e he
      exact hUL (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl he))))
    have hHRL : H ∪ R ⊆ L := by
      intro e he
      rcases mem_union.mp he with he | he
      · exact hUL (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr he))))
      · exact hUL (mem_union.mpr (Or.inr he))
    refine ⟨L, hUL', hYL, ?_, .step hx hq hf
      (fun e he => mem_inter.mpr ⟨hphys he, hHRL he⟩) hm hH hR hsmall, ?_⟩
    · have h1 := card_union_le (U ∪ H) R
      have h2 := card_union_le U H
      omega
    · intro Z m hz
      have htail := hcont Z m hz
      have hall := PhysicalMoves.step hx hq hf hphys hm hH hR htail
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Edges chosen outside the final ledger may be carried through all earlier
steps unchanged. The same ledger witnesses the continuation of the unpadded
trace; merely avoiding the last configuration would not suffice. -/
theorem ledger_with_catalysts {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) (hX : X ⊆ U) :
    ∃ L : Finset (Sym2 V), U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * n ∧
      (∀ D : Finset (Sym2 V), Disjoint D L →
        PhysicalMoves p F E B (U ∪ D) (X ∪ D) (Y ∪ D) n) := by
  obtain ⟨L, hUL, hYL, hc, ht, _⟩ := terminal_ledger h hX
  refine ⟨L, hUL, hYL, hc, ?_⟩
  intro D hDL
  have hXD : Disjoint X D := (hDL.mono_right (hX.trans hUL)).symm
  have hED : Disjoint (E ∩ L) (∅ ∪ D) := by
    simpa using (hDL.mono_right inter_subset_right).symm
  have hframe := ht.frame (E' := E) (B' := ∅) (U' := D) (W := D)
    inter_subset_left hED (Subset.refl _) hXD
  simpa using hframe

/-- Read the end ledger of deployment without assuming that its terminal
configuration already admits a decomposition. -/
theorem trace_with_final_ledger {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) (hX : X ⊆ U) (hcard : n ≤ X.card) :
    ∃ L : Finset (Sym2 V), U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      (∀ D : Finset (Sym2 V), Disjoint D L →
        PhysicalMoves p F E B (U ∪ D) (X ∪ D) (Y ∪ D) n) := by
  obtain ⟨L, hUL, hYL, hc, hd⟩ := ledger_with_catalysts h hX
  exact ⟨L, hUL, hYL, hc.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 9 hcard) U.card), hd⟩

/-- The actual deployment producer, with the ledger needed to choose catalysts
afterwards. No terminal decomposition or catalyst producer is assumed. -/
theorem deploy_for_catalysts [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (hF : TypedTransformer.ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, TypedTransformer.Link F (p u) (p v) k)
    (heven : ∀ v, Even (AntiEdgeSelection.incidentLoad X v))
    (hb : (Z.card : ℝ) + 37 * X.card + 4 * (d + U.card) < a) :
    ∃ Y L m, m ≤ X.card ∧
      PhysicalMoves p F G.edgeFinset B U X Y m ∧
      (∀ v, AntiEdgeSelection.incidentLoad Y v = 0 ∨
        AntiEdgeSelection.incidentLoad Y v = 2) ∧
      Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = X.card ∧
      U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      (∀ D : Finset (Sym2 V), Disjoint D L →
        PhysicalMoves p F G.edgeFinset B (U ∪ D) (X ∪ D) (Y ∪ D) m) := by
  obtain ⟨Y, m, hm, ht, hdeg, hYG, hYB, hYcard⟩ :=
    PairSplitDeploymentStage87.deploy p F hF G a d hs B U X Z hB hd
      hXU hXG hXB hZ hact heven hb
  obtain ⟨L, hUL, hYL, hc, hpad⟩ := trace_with_final_ledger ht hXU hm
  exact ⟨Y, L, m, hm, ht, hdeg, hYG, hYB, hYcard, hUL, hYL, hc, hpad⟩

/-- The deployment reserve pays one new carrier and at most nine used edges
per step. Thirty-seven is exactly 1 + 4 * 9. -/
theorem deployment_reserve_step (z u z' u' d a k : ℝ)
    (hz : z' ≤ z + 1) (hu : u' ≤ u + 9)
    (hb : z + 37 * (k + 1) + 4 * (d + u) < a) :
    z' + 37 * k + 4 * (d + u') < a := by
  linarith

end PartitionedTriangleAbsorption.MoveLedgerStage88
