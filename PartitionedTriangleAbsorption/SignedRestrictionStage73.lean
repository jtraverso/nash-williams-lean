/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingRestriction
public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # Sparse deletion error for signed triangle corrections

Unlike the restriction of a positive seed, the correction may have either
sign. The lost-copy count still bounds the absolute load error on every
surviving physical edge. This proves the geometric error estimate, not an
inverse producer or a compatibility assertion for the reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedRestrictionStage73

open Finset PackingRestriction TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem signed_load_restrict {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G H : SimpleGraph V} [DecidableRel H.Adj]
    (B : Finset (Sym2 V)) (hHG : H ≤ G)
    (hremoved : ∀ a b, G.Adj a b → ¬ H.Adj a b → s(a, b) ∈ B)
    (d W : ℝ) (hW : 0 ≤ W) (hB : DegBounded B d) (psi : Finset V → ℝ)
    (hpsi : ∀ s, IsCopy p F G s → |psi s| ≤ W) :
    ∀ e ∈ H.edgeFinset, |edgeLoad p F G psi e - edgeLoad p F H psi e| ≤
      2 * d * W := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have heH : H.Adj u v :=
      H.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
    let S := edgeCopies p F G s(u, v)
    let T := edgeCopies p F H s(u, v)
    have hTS : T ⊆ S := edgeCopies_mono hHG _
    have hcard : ((S \ T).card : ℝ) ≤ 2 * d :=
      (lost_copies_card B hremoved heH).trans
        (by have hu := hB u; have hv := hB v; linarith)
    have hsum : (∑ s ∈ S \ T, psi s) + (∑ s ∈ T, psi s) =
        ∑ s ∈ S, psi s := sum_sdiff hTS
    change |(∑ s ∈ S, psi s) - ∑ s ∈ T, psi s| ≤ 2 * d * W
    rw [← hsum, add_sub_cancel_right]
    calc
      |∑ s ∈ S \ T, psi s| ≤ ∑ s ∈ S \ T, |psi s| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ S \ T, W := sum_le_sum (fun s hs =>
        hpsi s (mem_copies.mp (mem_filter.mp (mem_sdiff.mp hs).1).1))
      _ = ((S \ T).card : ℝ) * W := by simp
      _ ≤ 2 * d * W := mul_le_mul_of_nonneg_right hcard hW

theorem sparse_deleted_load_error (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (K M delta : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hn : 0 < Fintype.card V)
    (hB : DegBounded B (delta * Fintype.card V)) (psi : Finset V → ℝ)
    (hpsi : ∀ s, IsCopy p F G s → |psi s| ≤ K * M / Fintype.card V) :
    ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
      |edgeLoad p F G psi e -
        edgeLoad p F (G.deleteEdges (B : Set (Sym2 V))) psi e| ≤ 2 * K * delta * M := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hremove : ∀ a b, G.Adj a b →
      ¬ (G.deleteEdges (B : Set (Sym2 V))).Adj a b → s(a, b) ∈ B := by
    intro a b ha hb
    by_contra hh
    exact hb (SimpleGraph.deleteEdges_adj.mpr ⟨ha, hh⟩)
  have herror := signed_load_restrict B (SimpleGraph.deleteEdges_le _) hremove
    (delta * Fintype.card V) (K * M / Fintype.card V) (by positivity) hB psi hpsi
  intro e he
  have hh := herror e he
  convert hh using 1
  field_simp

end PartitionedTriangleAbsorption.SignedRestrictionStage73
