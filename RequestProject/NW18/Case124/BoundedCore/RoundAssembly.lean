/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.BoundedCore.K3RootCover
public import RequestProject.NW18.Case124.BoundedCore.Assembly

@[expose] public section

/-!
# Deterministic assembly of one protected round

`round_cover_assembly` (proved): on a whole vertex type with child `W ⊇ Z`, damage `F` and
available edges `EH = E(G) \ F`, suppose

* `Ep` is a triangle-decomposable packing using no reserve edge and no edge inside `W`;
* `Res` is a radial reserve of cross edges from the roots `x ∉ W` to `S = W \ Z`;
* `Ta` is a triangle-decomposable apex cover, using leftover edges and reserve edges, covering
  every leftover edge with both ends outside `W`;
* the remaining cross targets `T x = {z ∈ W : xz uncovered}` satisfy the hypotheses of the spread
  root cover-down for the internal reserve `R = E(G[W]) \ E(G[Z])`.

Then `Q = Ep ∪ Ta ∪ (root stars) ∪ M` is triangle-decomposable, covers every available edge not
inside `W`, uses no edge inside `Z`, and its edges inside `W` (exactly `M`) have degree `≤ L`.
The parity of every target is DERIVED from the parity hypothesis at the roots.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption SpreadGen SpreadF1

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem enum_finset (S : Finset V) (v0 : V) :
    ∃ r : ℕ → V, (∀ i < S.card, ∀ j < S.card, r i = r j → i = j) ∧
      (∀ j < S.card, r j ∈ S) ∧ (∀ x ∈ S, ∃ j < S.card, r j = x) := by
  let r : ℕ → V := fun i => if h : i < S.card then (S.equivFin.symm ⟨i, h⟩ : V) else v0
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [r, dif_pos hi, dif_pos hj] at hij
    have := S.equivFin.symm.injective (Subtype.ext hij)
    simpa using congrArg Fin.val this
  · intro j hj; simp only [r, dif_pos hj]; exact (S.equivFin.symm ⟨j, hj⟩).2
  · intro x hx
    refine ⟨(S.equivFin ⟨x, hx⟩ : ℕ), (S.equivFin ⟨x, hx⟩).2, ?_⟩
    simp [r]

/-- **Deterministic assembly of one protected round.** -/
theorem round_cover_assembly (G : SimpleGraph V) [DecidableRel G.Adj] (W Z : Finset V)
    (F Res Ep Ta : Finset (Sym2 V)) (γ₀ K B ω Lv : ℕ) (κW : ℝ)
    (hZW : Z ⊆ W) (hFW : Disjoint F (insideEdges G W))
    (hEp : HasDecomp onePart K3fam Ep)
    (hEpsub : Ep ⊆ (G.edgeFinset \ F) \ (Res ∪ insideEdges G W))
    (hRes : Res ⊆ G.edgeFinset \ F)
    (hRescross : ∀ e ∈ Res, ∃ x, x ∉ W ∧ ∃ z ∈ W \ Z, e = s(x, z))
    (hTa : HasDecomp onePart K3fam Ta)
    (hTasub : Ta ⊆ (((G.edgeFinset \ F) \ (Res ∪ insideEdges G W)) \ Ep) ∪ Res)
    (hTacov : ∀ e ∈ ((G.edgeFinset \ F) \ (Res ∪ insideEdges G W)) \ Ep,
      (∀ v ∈ e, v ∉ W) → e ∈ Ta)
    (hpar : ∀ x, x ∉ W → Even (((G.edgeFinset \ F).filter fun e => x ∈ e).card))
    (hK : 0 < K)
    (hdense : ∀ x, x ∉ W → ∀ y ∈ W.filter (fun z =>
        s(x, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta)),
      ((W.filter (fun z => s(x, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta))).filter
        fun z => ¬ (z ≠ y ∧ s(y, z) ∈ insideEdges G W \ insideEdges G Z)).card ≤ γ₀)
    (hmarg : ∀ x, x ∉ W →
      γ₀ + (B + K) + (W.filter (fun z =>
        s(x, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta))).card / 2 ≤
      (W.filter (fun z => s(x, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta))).card)
    (hover : ∀ x, x ∉ W → ∀ y, y ∉ W → x ≠ y →
      ((W.filter (fun z => s(x, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta))) ∩
        (W.filter (fun z => s(y, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta)))).card
        ≤ ω)
    (hload : ∀ v, ((univ \ W).filter (fun x =>
        s(x, v) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta) ∧ v ∈ W)).card ≤ Lv)
    (hB : (Real.exp 1 - 1) * ω * Lv / K +
      Real.log (∑ x ∈ univ \ W, ((W.filter (fun z =>
        s(x, z) ∈ ((G.edgeFinset \ F) \ insideEdges G W) \ (Ep ∪ Ta))).card : ℝ)) ≤ B)
    (hLκ : (Lv : ℝ) ≤ κW) :
    ∃ Q ⊆ G.edgeFinset \ F, HasDecomp onePart K3fam Q ∧
      ((G.edgeFinset \ F) \ insideEdges G W) ⊆ Q ∧ Disjoint Q (insideEdges G Z) ∧
      DegBounded (Q ∩ insideEdges G W) κW := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨∅, empty_subset _, ⟨∅, by simp [IsDecomp]⟩, fun e _ => ?_, disjoint_empty_left _,
      fun v => isEmptyElim v⟩
    induction e using Sym2.ind with
    | _ a b => exact isEmptyElim a
  set EH := G.edgeFinset \ F with hEH
  set Rem := (EH \ insideEdges G W) \ (Ep ∪ Ta) with hRem
  set T : V → Finset V := fun x => W.filter (fun z => s(x, z) ∈ Rem) with hT
  set R := insideEdges G W \ insideEdges G Z with hR
  set X := univ \ W with hX
  -- basic facts
  have hEpTa : Disjoint Ep Ta := by
    rw [disjoint_left]
    intro e he heT
    rcases mem_union.mp (hTasub heT) with h | h
    · exact (mem_sdiff.mp h).2 he
    · exact (mem_sdiff.mp (hEpsub he)).2 (mem_union_left _ h)
  have hResW : ∀ e ∈ Res, e ∉ insideEdges G W := by
    intro e he hin
    obtain ⟨x, hxW, z, -, rfl⟩ := hRescross e he
    exact hxW (mem_of_mem_insideEdges hin (Sym2.mem_mk_left _ _))
  have hEpW : ∀ e ∈ Ep, e ∉ insideEdges G W := fun e he hin =>
    (mem_sdiff.mp (hEpsub he)).2 (mem_union_right _ hin)
  have hTaW : ∀ e ∈ Ta, e ∉ insideEdges G W := by
    intro e he hin
    rcases mem_union.mp (hTasub he) with h | h
    · exact (mem_sdiff.mp (mem_sdiff.mp h).1).2 (mem_union_right _ hin)
    · exact hResW e h hin
  have hEpEH : Ep ⊆ EH := fun e he => (mem_sdiff.mp (hEpsub he)).1
  have hTaEH : Ta ⊆ EH := by
    intro e he
    rcases mem_union.mp (hTasub he) with h | h
    · exact (mem_sdiff.mp (mem_sdiff.mp h).1).1
    · exact hRes h
  have hRemEH : Rem ⊆ EH := fun e he => (mem_sdiff.mp (mem_sdiff.mp he).1).1
  -- the remaining edges are cross edges
  have hRemcross : ∀ e ∈ Rem, ∃ x, x ∉ W ∧ ∃ z ∈ W, e = s(x, z) := by
    intro e he
    have heEH := hRemEH he
    have hnin : e ∉ insideEdges G W := (mem_sdiff.mp (mem_sdiff.mp he).1).2
    have hnot : e ∉ Ep ∪ Ta := (mem_sdiff.mp he).2
    have hG : e ∈ G.edgeFinset := (mem_sdiff.mp heEH).1
    induction e using Sym2.ind with
    | _ a b =>
      by_cases ha : a ∈ W <;> by_cases hb : b ∈ W
      · exfalso; apply hnin
        rw [insideEdges, mem_inter, triEdges, mem_filter, Finset.mk_mem_sym2_iff]
        exact ⟨hG, ⟨ha, hb⟩, G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp hG)⟩
      · exact ⟨b, hb, a, ha, Sym2.eq_swap⟩
      · exact ⟨a, ha, b, hb, rfl⟩
      · exfalso
        have hnRes : s(a, b) ∉ Res := by
          intro hr
          obtain ⟨x, -, z, hz, he'⟩ := hRescross _ hr
          rcases Sym2.eq_iff.mp he' with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact hb (mem_sdiff.mp hz).1
          · exact ha (mem_sdiff.mp hz).1
        have hL : s(a, b) ∈ (EH \ (Res ∪ insideEdges G W)) \ Ep := by
          refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨heEH, ?_⟩, fun h => hnot (mem_union_left _ h)⟩
          rw [mem_union, not_or]; exact ⟨hnRes, hnin⟩
        refine hnot (mem_union_right _ (hTacov _ hL ?_))
        intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact ha
        · exact hb
  -- parity of the targets
  have hTcard : ∀ x, x ∉ W → (T x).card = (Rem.filter fun e => x ∈ e).card := by
    intro x hx
    refine card_bij (fun z _ => s(x, z)) ?_ ?_ ?_
    · intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).2, Sym2.mem_mk_left _ _⟩
    · intro z hz z' hz' h
      exact Sym2.congr_right.mp h
    · intro e he
      obtain ⟨heR, hxe⟩ := mem_filter.mp he
      obtain ⟨y, hyW, z, hzW, rfl⟩ := hRemcross e heR
      rcases Sym2.mem_iff.mp hxe with rfl | rfl
      · exact ⟨z, mem_filter.mpr ⟨hzW, heR⟩, rfl⟩
      · exact absurd hzW hx
  have heven : ∀ x, x ∉ W → Even (T x).card := by
    intro x hx
    rw [hTcard x hx]
    have hsplit : EH.filter (fun e => x ∈ e) =
        (Ep ∪ Ta).filter (fun e => x ∈ e) ∪ Rem.filter (fun e => x ∈ e) := by
      ext e
      simp only [mem_filter, mem_union, hRem, mem_sdiff]
      constructor
      · rintro ⟨he, hxe⟩
        by_cases h : e ∈ Ep ∨ e ∈ Ta
        · exact Or.inl ⟨h, hxe⟩
        · refine Or.inr ⟨⟨⟨he, fun hin => hx (mem_of_mem_insideEdges hin hxe)⟩, h⟩, hxe⟩
      · rintro (⟨h, hxe⟩ | ⟨⟨⟨he, -⟩, -⟩, hxe⟩)
        · rcases h with h | h
          · exact ⟨hEpEH h, hxe⟩
          · exact ⟨hTaEH h, hxe⟩
        · exact ⟨he, hxe⟩
    have hdisj : Disjoint ((Ep ∪ Ta).filter (fun e => x ∈ e)) (Rem.filter (fun e => x ∈ e)) :=
      disjoint_filter_filter (disjoint_left.mpr fun e he heR => (mem_sdiff.mp heR).2 he)
    have h1 := hpar x hx
    rw [hsplit, card_union_of_disjoint hdisj] at h1
    have hloop : ∀ e ∈ Ep ∪ Ta, ¬ e.IsDiag := fun e he =>
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp
        (mem_sdiff.mp ((union_subset hEpEH hTaEH) he)).1)
    have h2 := even_load_of_hasDecomp hloop (HasDecomp.union hEp hTa hEpTa) x
    rw [Nat.even_add] at h1
    exact h1.mp h2
  -- enumerate the roots
  obtain ⟨r, hrinj, hrX, hrsurj⟩ := enum_finset X (Classical.arbitrary V)
  set k := X.card with hk
  have hrW : ∀ i < k, r i ∉ W := fun i hi => (mem_sdiff.mp (hrX i hi)).2
  have hvisits : ∀ v, visits (fun i => T (r i)) k v ≤ Lv := by
    intro v
    refine le_trans ?_ (hload v)
    unfold visits
    refine card_le_card_of_injOn r ?_ ?_
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
      simp only [coe_filter, Set.mem_setOf_eq]
      have hvT := mem_filter.mp hi.2
      exact ⟨hrX i hi.1, hvT.2, hvT.1⟩
    · intro i hi j hj hij
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      exact hrinj i hi.1 j hj.1 hij
  have hsum : ∑ i ∈ range k, ((T (r i)).card : ℝ) = ∑ x ∈ X, ((T x).card : ℝ) := by
    refine sum_bij (fun i _ => r i) (fun i hi => hrX i (mem_range.mp hi))
      (fun i hi j hj h => hrinj i (mem_range.mp hi) j (mem_range.mp hj) h) ?_ (fun _ _ => rfl)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hrsurj x hx
    exact ⟨j, mem_range.mpr hj, rfl⟩
  obtain ⟨M, hMR, hMdeg, hstarM, hdec⟩ := SpreadK3.K3_spread_root_cover_down R k r
    (fun i => T (r i)) γ₀ K B ω Lv hK hrinj
    (fun i hi j _ hT' => hrW i hi (mem_filter.mp hT').1)
    (fun i hi => heven _ (hrW i hi))
    (fun i hi y hy => hdense _ (hrW i hi) y hy)
    (fun i hi => hmarg _ (hrW i hi))
    (fun i hi j hj hij => hover _ (hrW i hi) _ (hrW j hj) (fun h => hij (hrinj i hi j hj h)))
    hvisits (by rw [hsum]; exact hB)
  -- the root stars are exactly the remaining edges
  have hstar : rootStar k r (fun i => T (r i)) = Rem := by
    ext e
    simp only [rootStar, mem_biUnion, mem_range, mem_image]
    constructor
    · rintro ⟨i, -, z, hz, rfl⟩; exact (mem_filter.mp hz).2
    · intro he
      obtain ⟨x, hxW, z, hzW, rfl⟩ := hRemcross e he
      obtain ⟨j, hj, rfl⟩ := hrsurj x (mem_sdiff.mpr ⟨mem_univ _, hxW⟩)
      exact ⟨j, hj, z, mem_filter.mpr ⟨hzW, he⟩, rfl⟩
  rw [hstar] at hstarM hdec
  have hMW : M ⊆ insideEdges G W := fun e he => (mem_sdiff.mp (hMR he)).1
  have hMEH : M ⊆ EH := by
    intro e he
    refine mem_sdiff.mpr ⟨insideEdges_subset G W (hMW he), fun hF => ?_⟩
    exact disjoint_left.mp hFW hF (hMW he)
  have hdis2 : Disjoint (Ep ∪ Ta) (Rem ∪ M) := by
    rw [disjoint_union_right]
    refine ⟨disjoint_left.mpr fun e he heR => (mem_sdiff.mp heR).2 he, ?_⟩
    rw [disjoint_left]
    intro e he heM
    rcases mem_union.mp he with h | h
    · exact hEpW e h (hMW heM)
    · exact hTaW e h (hMW heM)
  refine ⟨Ep ∪ Ta ∪ (Rem ∪ M), union_subset (union_subset hEpEH hTaEH) (union_subset hRemEH hMEH),
    HasDecomp.union (HasDecomp.union hEp hTa hEpTa) hdec hdis2, ?_, ?_, ?_⟩
  · intro e he
    by_cases h : e ∈ Ep ∪ Ta
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨he, h⟩))
  · rw [disjoint_left]
    intro e he heZ
    have heW : e ∈ insideEdges G W := insideEdges_mono G hZW heZ
    rcases mem_union.mp he with h | h
    · rcases mem_union.mp h with h | h
      · exact hEpW e h heW
      · exact hTaW e h heW
    · rcases mem_union.mp h with h | h
      · exact (mem_sdiff.mp (mem_sdiff.mp h).1).2 heW
      · exact (mem_sdiff.mp (hMR h)).2 heZ
  · intro v
    have hsub : (Ep ∪ Ta ∪ (Rem ∪ M)) ∩ insideEdges G W ⊆ M := by
      intro e he
      obtain ⟨h1, h2⟩ := mem_inter.mp he
      rcases mem_union.mp h1 with h | h
      · rcases mem_union.mp h with h | h
        · exact absurd h2 (hEpW e h)
        · exact absurd h2 (hTaW e h)
      · rcases mem_union.mp h with h | h
        · exact absurd h2 (mem_sdiff.mp (mem_sdiff.mp h).1).2
        · exact h
    have h1 : (((Ep ∪ Ta ∪ (Rem ∪ M)) ∩ insideEdges G W).filter fun e => v ∈ e).card ≤
        deg M v := card_le_card (filter_subset_filter _ hsub)
    have h2 := hMdeg v
    have : ((((Ep ∪ Ta ∪ (Rem ∪ M)) ∩ insideEdges G W).filter fun e => v ∈ e).card : ℝ) ≤ Lv := by
      exact_mod_cast h1.trans h2
    linarith

end NashWilliams18
