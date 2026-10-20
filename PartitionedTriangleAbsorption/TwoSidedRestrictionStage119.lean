/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingRestriction
public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # Two-sided load error after deleting a sparse edge set

Vertex sampling permits loads above as well as below one. This version
therefore does not assume an almost packing with load at most one. It even
allows signed weights, provided their absolute values are bounded.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TwoSidedRestrictionStage119

open Finset PackingRestriction TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem error_restrict (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (B : Finset (Sym2 V)) (hHG : H ≤ G)
    (hremoved : ∀ a b, G.Adj a b → ¬ H.Adj a b → s(a, b) ∈ B)
    (φ : Finset V → ℝ) (ε d M : ℝ) (hM : 0 ≤ M) (hd : DegBounded B d)
    (hw : ∀ s, IsCopy p F G s → |φ s| ≤ M)
    (hl : ∀ e ∈ G.edgeFinset, |1 - edgeLoad p F G φ e| ≤ ε) :
    ∀ e ∈ H.edgeFinset, |1 - edgeLoad p F H φ e| ≤ ε + 2 * d * M := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have heH : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have heG : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hHG heH)
    let S := edgeCopies p F G s(u, v)
    let T := edgeCopies p F H s(u, v)
    have hTS : T ⊆ S := edgeCopies_mono hHG _
    have hcard : ((S \ T).card : ℝ) ≤ 2 * d :=
      (lost_copies_card B hremoved heH).trans (by have hu := hd u; have hv := hd v; linarith)
    have hloss : |∑ s ∈ S \ T, φ s| ≤ 2 * d * M := by
      calc
        |∑ s ∈ S \ T, φ s| ≤ ∑ s ∈ S \ T, |φ s| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _s ∈ S \ T, M := sum_le_sum (fun s hs =>
          hw s (PackingRestriction.mem_copies.mp (mem_filter.mp (mem_sdiff.mp hs).1).1))
        _ = ((S \ T).card : ℝ) * M := by simp
        _ ≤ 2 * d * M := mul_le_mul_of_nonneg_right hcard hM
    have hsum : (∑ s ∈ S \ T, φ s) + (∑ s ∈ T, φ s) = ∑ s ∈ S, φ s := sum_sdiff hTS
    have herr : |1 - ∑ s ∈ S, φ s| ≤ ε := hl _ heG
    change |1 - ∑ s ∈ T, φ s| ≤ ε + 2 * d * M
    have heq : 1 - ∑ s ∈ T, φ s = (1 - ∑ s ∈ S, φ s) + ∑ s ∈ S \ T, φ s := by
      linarith
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add herr hloss)

theorem error_deleteEdges (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (φ : Finset V → ℝ) (ε d M : ℝ) (hM : 0 ≤ M) (hd : DegBounded B d)
    (hw : ∀ s, IsCopy p F G s → |φ s| ≤ M)
    (hl : ∀ e ∈ G.edgeFinset, |1 - edgeLoad p F G φ e| ≤ ε) :
    ∀ e ∈ (G.deleteEdges B).edgeFinset,
      |1 - edgeLoad p F (G.deleteEdges B) φ e| ≤ ε + 2 * d * M := by
  apply error_restrict p F G (G.deleteEdges B) B (SimpleGraph.deleteEdges_le _) ?_
    φ ε d M hM hd hw hl
  intro a b hab hnot
  by_contra hb
  exact hnot (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hb⟩)

end PartitionedTriangleAbsorption.TwoSidedRestrictionStage119
