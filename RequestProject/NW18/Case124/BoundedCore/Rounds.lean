/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.BoundedCore.Assembly

@[expose] public section

/-!
# The vortex cover-down from a single protected round (`RoundSpec124`)

`RoundSpec124` is the **one-round** cover-down of the bounded-core route: for a parent `U`, child
`W ⊆ U` and grandchild `Z ⊆ W` (possibly empty), and an old damage set `F` of edges inside `U`
with no edge inside `W`, it covers every remaining edge inside `U` but not inside `W` by a
triangle-decomposable `Q`, whose edges inside `W` avoid every edge inside the grandchild `Z`
and have maximum degree `≤ κ |W|`.

`vortexCoverSpec124_of_round` (**proved**) iterates the round along a clean vortex.  The
invariant is the exact support identity of the look-ahead (as in `TwoLevelDamage`): before
round `i` the uncovered edges inside `U i` are those of `G[U i]` minus
`F i = (Q_{<i} ∪ A) ∩ E(G[U i])`, and `F i` has no edge inside `U (i+1)`:

* `F 0 = A`, which avoids `E(G[U 1])`;
* for `i ≥ 1`, `A` has no edge inside `U i ⊆ U 1`, and `Q_{<i} ∩ E(G[U i])` is the inside part of
  the previous round only (older rounds have no edge inside `U i`), which avoids `E(G[U (i+1)])`
  because that round protected its grandchild.

Hence the damage passed to round `i` is the previous round's inside load `≤ κ |U i|`, with no
accumulation.  Parity at a root `x ∈ U i \ U (i+1)` follows from the divisibility of `G`, the even
degrees of `A` and of the triangle-decomposable `Q_{<i}`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **One protected cover-down round** (residual proposition of the bounded-core route). -/
def RoundSpec124 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∃ q₀ : ℝ, 0 < q₀ ∧
    ∀ q : ℝ, 0 < q → q ≤ q₀ → ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (U W Z : Finset V) (F : Finset (Sym2 V)),
        N₀ ≤ U.card → W ⊆ U → Z ⊆ W →
        7 * q / 8 * (U.card : ℝ) ≤ W.card → (W.card : ℝ) ≤ 9 * q / 8 * U.card →
        (Z.card : ℝ) ≤ 9 * q / 8 * W.card →
        (3 / 4 - θ) * (U.card : ℝ) ≤ ((G.induce (U : Set V)).minDegree : ℝ) →
        ¬ IsExtremal (β / 4) (G.induce (U : Set V)) →
        (∀ v ∈ U, (3 / 4 - θ) * (W.card : ℝ) ≤ ((W.filter (G.Adj v)).card : ℝ)) →
        F ⊆ insideEdges G U → Disjoint F (insideEdges G W) → DegBounded F (κ * U.card) →
        (∀ x ∈ U \ W, Even (((insideEdges G U \ F).filter fun e => x ∈ e).card)) →
        ∃ Q ⊆ insideEdges G U \ F, HasDecomp onePart K3fam Q ∧
          ((insideEdges G U \ F) \ insideEdges G W) ⊆ Q ∧ Disjoint Q (insideEdges G Z) ∧
          DegBounded (Q ∩ insideEdges G W) (κ * W.card)

omit [Fintype V] in
lemma degBounded_mono {E E' : Finset (Sym2 V)} (h : E ⊆ E') {d : ℝ} (h' : DegBounded E' d) :
    DegBounded E d := fun v =>
  le_trans (by exact_mod_cast card_le_card (filter_subset_filter _ h)) (h' v)

lemma insideEdges_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    insideEdges G univ = G.edgeFinset := by
  ext e
  rw [insideEdges, mem_inter, triEdges, mem_filter]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_, G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp h)⟩
    induction e using Sym2.ind with
    | _ x y => simp

lemma degree_eq_card_filter (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    G.degree x = (G.edgeFinset.filter fun e => x ∈ e).card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]

/-- **The vortex cover-down from one protected round** (proved). -/
theorem vortexCoverSpec124_of_round (hR : RoundSpec124) : VortexCoverSpec124 := by
  intro β hβ hβ1
  obtain ⟨θ, hθ0, hθ1, q₀, hq₀, hR'⟩ := hR β hβ hβ1
  refine ⟨θ, hθ0, hθ1, q₀, hq₀, fun q hq hqq₀ => ?_⟩
  obtain ⟨κ, hκ, N₀, hround⟩ := hR' q hq hqq₀
  refine ⟨κ, hκ, N₀, fun M hM => ⟨0, fun V _ _ G _ _ hdiv _ _ L U hV A hAG hAdisj hAdeg
    hAeven => ?_⟩⟩
  classical
  have hAG' : ∀ e ∈ A, e ∈ G.edgeFinset := fun e he => hAG he
  have hloop : ∀ {E : Finset (Sym2 V)}, E ⊆ G.edgeFinset → ∀ e ∈ E, ¬ e.IsDiag :=
    fun hE e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hE he))
  -- `A` has no edge inside any `U i` with `1 ≤ i ≤ L`
  have hA_in : ∀ i, 1 ≤ i → i ≤ L → Disjoint A (insideEdges G (U i)) := fun i h1 hiL =>
    hAdisj.mono_right (insideEdges_mono G (hV.antitone h1 hiL))
  have key : ∀ i ≤ L, ∃ Qc : Finset (Sym2 V), Qc ⊆ G.edgeFinset \ A ∧
      HasDecomp onePart K3fam Qc ∧ G.edgeFinset \ (A ∪ insideEdges G (U i)) ⊆ Qc ∧
      (i < L → Disjoint (Qc ∩ insideEdges G (U i)) (insideEdges G (U (i + 1)))) ∧
      DegBounded (Qc ∩ insideEdges G (U i)) (κ * (U i).card) ∧ (i = 0 → Qc = ∅) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨∅, empty_subset _, ⟨∅, by simp [IsDecomp]⟩, ?_, fun _ => by simp, ?_,
        fun _ => rfl⟩
      · rw [hV.1, insideEdges_univ]
        intro e he
        rw [mem_sdiff, mem_union] at he
        exact absurd (Or.inr he.1) he.2
      · intro v; simp only [empty_inter, filter_empty, card_empty, Nat.cast_zero]
        positivity
    | succ i ih =>
      intro hi1
      have hi : i < L := hi1
      obtain ⟨Qc, hQcA, hQcdec, hQccov, hQcdis, hQcdeg, hQc0⟩ := ih hi.le
      set F : Finset (Sym2 V) := (Qc ∪ A) ∩ insideEdges G (U i) with hF
      set Z : Finset V := if i + 2 ≤ L then U (i + 2) else ∅ with hZ
      have hstep := hV.2.1 i hi
      have hQcG : Qc ⊆ G.edgeFinset := fun e he => (mem_sdiff.mp (hQcA he)).1
      have hQcA' : Disjoint Qc A := by
        rw [disjoint_left]; intro e he heA; exact (mem_sdiff.mp (hQcA he)).2 heA
      -- hypotheses of the round
      have hN : N₀ ≤ (U i).card := hM.trans hstep.2.1
      have hZW : Z ⊆ U (i + 1) := by
        rw [hZ]; split_ifs with h
        · exact (hV.2.1 (i + 1) (by omega)).1
        · exact empty_subset _
      have hZcard : (Z.card : ℝ) ≤ 9 * q / 8 * (U (i + 1)).card := by
        rw [hZ]; split_ifs with h
        · exact (hV.2.1 (i + 1) (by omega)).2.2.2
        · simp only [card_empty, Nat.cast_zero]; positivity
      have hdeg := hV.2.2.2.2.2 i hi.le
      have hFsub : F ⊆ insideEdges G (U i) := inter_subset_right
      have hFdis : Disjoint F (insideEdges G (U (i + 1))) := by
        rw [disjoint_left]
        intro e heF heW
        rw [hF, mem_inter, mem_union] at heF
        rcases heF.1 with h | h
        · exact disjoint_left.mp (hQcdis hi) (mem_inter.mpr ⟨h, heF.2⟩) heW
        · exact disjoint_left.mp (hA_in (i + 1) (by omega) hi1) h heW
      have hFdeg : DegBounded F (κ * (U i).card) := by
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0
          have hQ0 := hQc0 rfl
          rw [hV.1, card_univ]
          refine degBounded_mono (fun e he => ?_) hAdeg
          rw [hF, mem_inter, hQ0, empty_union] at he
          exact he.1
        · refine degBounded_mono ?_ hQcdeg
          intro e he
          rw [hF, mem_inter, mem_union] at he
          rcases he.1 with h | h
          · exact mem_inter.mpr ⟨h, he.2⟩
          · exact absurd he.2 (disjoint_left.mp (hA_in i hpos hi.le) h)
      -- the remaining edges inside `U i` are exactly the uncovered edges of `G`
      have hrem : insideEdges G (U i) \ F = G.edgeFinset \ (Qc ∪ A) := by
        ext e
        simp only [hF, mem_sdiff, mem_inter, mem_union, not_and, not_or]
        constructor
        · rintro ⟨hin, hnot⟩
          refine ⟨insideEdges_subset G _ hin, fun h => hnot (Or.inl h) hin,
            fun h => hnot (Or.inr h) hin⟩
        · rintro ⟨heG, hnQ, hnA⟩
          have hin : e ∈ insideEdges G (U i) := by
            by_contra hc
            exact hnQ (hQccov (mem_sdiff.mpr ⟨heG, by rw [mem_union]; tauto⟩))
          exact ⟨hin, fun h _ => h.elim hnQ hnA⟩
      have hpar : ∀ x ∈ U i \ U (i + 1),
          Even (((insideEdges G (U i) \ F).filter fun e => x ∈ e).card) := by
        intro x _
        rw [hrem]
        have hSG : Qc ∪ A ⊆ G.edgeFinset := union_subset hQcG hAG
        have h1 : (G.edgeFinset.filter fun e => x ∈ e).card =
            ((G.edgeFinset \ (Qc ∪ A)).filter fun e => x ∈ e).card +
              ((Qc ∪ A).filter fun e => x ∈ e).card := by
          rw [← card_union_of_disjoint (disjoint_filter_filter sdiff_disjoint)]
          congr 1
          ext e
          simp only [mem_filter, mem_union, mem_sdiff]
          constructor
          · rintro ⟨he, hx⟩
            by_cases h : e ∈ Qc ∨ e ∈ A
            · exact Or.inr ⟨h, hx⟩
            · exact Or.inl ⟨⟨he, h⟩, hx⟩
          · rintro (⟨⟨he, _⟩, hx⟩ | ⟨h, hx⟩)
            · exact ⟨he, hx⟩
            · exact ⟨hSG (mem_union.mpr h), hx⟩
        have h2 : ((Qc ∪ A).filter fun e => x ∈ e).card =
            (Qc.filter fun e => x ∈ e).card + (A.filter fun e => x ∈ e).card := by
          rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hQcA')]
        have e1 := hdiv.2 x
        rw [degree_eq_card_filter] at e1
        have e2 := even_load_of_hasDecomp (hloop hQcG) hQcdec x
        have e3 := hAeven x
        rw [Nat.even_iff] at e1 e2 e3 ⊢
        omega
      obtain ⟨Q, hQsub, hQdec, hQcov, hQZ, hQdeg⟩ := hround V G (U i) (U (i + 1)) Z F hN
        hstep.1 hZW hstep.2.2.1 hstep.2.2.2 hZcard hdeg.1 hdeg.2 (hV.2.2.2.2.1 i hi)
        hFsub hFdis hFdeg hpar
      have hQin : ∀ e ∈ Q, e ∈ insideEdges G (U i) ∧ e ∉ F := fun e he => mem_sdiff.mp (hQsub he)
      have hQQc : Disjoint Qc Q := by
        rw [disjoint_left]
        intro e he heQ
        exact (hQin e heQ).2 (mem_inter.mpr ⟨mem_union_left _ he, (hQin e heQ).1⟩)
      have hQA : Disjoint Q A := by
        rw [disjoint_left]
        intro e heQ heA
        exact (hQin e heQ).2 (mem_inter.mpr ⟨mem_union_right _ heA, (hQin e heQ).1⟩)
      refine ⟨Qc ∪ Q, ?_, HasDecomp.union hQcdec hQdec hQQc, ?_, ?_, ?_, by omega⟩
      · intro e he
        rcases mem_union.mp he with h | h
        · exact hQcA h
        · exact mem_sdiff.mpr ⟨insideEdges_subset G _ (hQin e h).1,
            disjoint_left.mp hQA h⟩
      · intro e he
        rw [mem_sdiff, mem_union, not_or] at he
        by_cases hin : e ∈ insideEdges G (U i)
        · by_cases heF : e ∈ F
          · rw [hF, mem_inter, mem_union] at heF
            rcases heF.1 with h | h
            · exact mem_union_left _ h
            · exact absurd h he.2.1
          · exact mem_union_right _ (hQcov (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hin, heF⟩, he.2.2⟩))
        · exact mem_union_left _ (hQccov (mem_sdiff.mpr ⟨he.1, by rw [mem_union]; tauto⟩))
      · intro hi2
        have hZeq : Z = U (i + 2) := by rw [hZ, if_pos (by omega)]
        rw [disjoint_left]
        intro e he heZ
        rw [mem_inter, mem_union] at he
        rcases he.1 with h | h
        · have hsub := insideEdges_mono G (hV.antitone (Nat.le_succ i) hi1)
          exact disjoint_left.mp (hQcdis hi) (mem_inter.mpr ⟨h, hsub he.2⟩) he.2
        · exact disjoint_left.mp hQZ h (hZeq ▸ heZ)
      · refine degBounded_mono ?_ hQdeg
        intro e he
        rw [mem_inter, mem_union] at he
        rcases he.1 with h | h
        · have hsub := insideEdges_mono G (hV.antitone (Nat.le_succ i) hi1)
          exact absurd he.2 (disjoint_left.mp (hQcdis hi) (mem_inter.mpr ⟨h, hsub he.2⟩))
        · exact mem_inter.mpr ⟨h, he.2⟩
  obtain ⟨Qc, hQcA, hQcdec, hQccov, -, -, -⟩ := key L le_rfl
  exact ⟨Qc, hQcA, hQccov, hQcdec⟩

end NashWilliams18
