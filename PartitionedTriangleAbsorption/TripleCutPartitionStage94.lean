/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutBridgeStage94

/-! # Cutting a given partition of all remaining original tokens

If the given disjoint family of valid target triples covers exactly the
remaining original tokens, then after `cut_all` no original token remains:
all original tokens sit in isolated allowed triangles, their edges have an
actual decomposition, and every vertex carries nothing, exactly two catalytic
tokens, or exactly two original tokens of one finished triangle.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}

/-- **Cutting a given partition of the remaining original tokens.** -/
theorem cut_partition {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d) {S : Data V} (Ts : List (TargetTriple V t))
    {pos : Tok V → Sym2 V} {R U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos R)
    (hval : ∀ T ∈ Ts, T.Valid p F)
    (hpw : Ts.Pairwise (fun T T' => Disjoint T.toks T'.toks)) (hcover : allToks Ts = R)
    (hb : (Z.card : ℝ) + 4 * (d + U.card) + 330 * Ts.length < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V),
      Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' ∅ ∧
      HasDecomp p F (S.Y.image fun e => pos' (.inl e)) ∧
      (∀ v, tokAtP S pos' v = ∅ ∨
        (∃ κ κ' : V × Fin 3, κ ≠ κ' ∧ tokAtP S pos' v = {.inr κ, .inr κ'}) ∨
        (∃ e e', e ∈ S.Y ∧ e' ∈ S.Y ∧ e ≠ e' ∧ tokAtP S pos' v = {.inl e, .inl e'})) ∧
      (∀ T ∈ Ts, ∃ zA zB zC : V, TriangleCut p F S pos' T.e₁ T.e₂ T.e₃ T.i T.j T.k zA zB zC) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 81 * Ts.length ∧ Z ⊆ Z' ∧ Z'.card ≤ Z.card + 6 * Ts.length ∧
      PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos')
        (9 * Ts.length) ∧
      ∀ W m, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W m →
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (9 * Ts.length + m) := by
  obtain ⟨pos', U', Z', ph', bd', tris, -, -, -, hZZ, hZ, hUU, hU, htr, hcont⟩ :=
    cut_all a d hF hs hB hd Ts pos R U Z ph bd
      (fun T hT => ⟨hval T hT, hcover ▸ toks_subset_allToks hT⟩) hpw hb
  rw [hcover, sdiff_self] at bd'
  obtain ⟨hdec, hcls⟩ := bd'.all_done
  exact ⟨pos', U', Z', ph', bd', hdec, hcls, tris, hUU, hU, hZZ, hZ, htr, hcont⟩

end PartitionedTriangleAbsorption.TripleCutStage94
