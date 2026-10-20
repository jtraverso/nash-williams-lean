/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeFamily
public import PartitionedTriangleAbsorption.RefinerAssembly
public import PartitionedTriangleAbsorption.ReturnedAssembly

/-! # Exact typed cover-down with the sharper root-demand bound

The argument follows Aristotle's CoverDown return, but indexes requests by
actual leftover edges and reuses our Stage-5 family theorem. It records the
exact reserve cost and degree bound. No existence of a reserve, universal
absorber or approximate packing is assumed to have been established.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveCoverDown

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V] {t : ℕ}

abbrev reserveGraph (X : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (X : Set (Sym2 V))

theorem hasDecomp_triEdges {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {s : Finset V} (hs : IsTypedTri p F s) : HasDecomp p F (triEdges s) :=
  ⟨{s}, fun s' hs' => by rw [mem_singleton.mp hs']; exact hs, by simp, by simp⟩

/-- Exact cover of a supplied sparse, typeable leftover inside a supplied reserve. -/
theorem exists_reserve_cover [Fintype V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (X L : Finset (Sym2 V)) (α : ℝ)
    [DecidableRel (reserveGraph X).Adj]
    (hres : AntiEdgeful p F (reserveGraph X) α) (hLX : Disjoint L X)
    (hdiag : ∀ e ∈ L, ¬ e.IsDiag)
    (htype : ∀ a b : V, s(a, b) ∈ L →
      ∃ k : Fin t, ({p a, p b, k} : Multiset (Fin t)) ∈ F)
    (m r q : ℕ) (hq : 0 < q) (hcard : L.card ≤ m) (hdegree : DegBounded L r)
    (hbudget : (m : ℝ) / q + 2 * ((r : ℝ) + 2 * q) < α * Fintype.card V) :
    ∃ P ⊆ X, DegBounded P ((r : ℝ) + 2 * q) ∧ Disjoint L P ∧
      HasDecomp p F (L ∪ P) ∧ P.card = 2 * L.card := by
  classical
  let I := {e : Sym2 V // e ∈ L}
  let indices : Finset I := univ
  let u : I → V := fun e => (Quot.out e.val).1
  let v : I → V := fun e => (Quot.out e.val).2
  have huv : ∀ e : I, s(u e, v e) = e.val := fun e => Quot.out_eq e.val
  have hne : ∀ e : I, u e ≠ v e := by
    intro e heq
    apply hdiag e.val e.property
    rw [← huv e, heq]
    exact Sym2.mk_isDiag_iff.mpr rfl
  have hlabels : ∀ e : I, ∃ k : Fin t,
      ({p (u e), p (v e), k} : Multiset (Fin t)) ∈ F := by
    intro e
    exact htype (u e) (v e) (by rw [huv]; exact e.property)
  let k : I → Fin t := fun e => Classical.choose (hlabels e)
  have hk : ∀ e : I, ({p (u e), p (v e), k e} : Multiset (Fin t)) ∈ F :=
    fun e => Classical.choose_spec (hlabels e)
  have hroot : ∀ x, rootLoad indices u v x ≤ r := by
    intro x
    have hfilters : Disjoint (indices.filter (fun e => u e = x))
        (indices.filter (fun e => v e = x)) := by
      apply disjoint_left.mpr
      intro e he₁ he₂
      exact hne e ((mem_filter.mp he₁).2.trans (mem_filter.mp he₂).2.symm)
    have hcount : rootLoad indices u v x ≤ (L.filter (fun e => x ∈ e)).card := by
      unfold rootLoad
      rw [← card_union_of_disjoint hfilters]
      apply card_le_card_of_injOn (fun e : I => e.val)
      · intro e he
        refine mem_filter.mpr ⟨e.property, ?_⟩
        change x ∈ e.val
        rw [← huv e]
        rcases mem_union.mp he with he | he
        · simp [(mem_filter.mp he).2]
        · simp [(mem_filter.mp he).2]
      · intro e _ e' _ heq
        exact Subtype.ext heq
    have hreal : ((L.filter (fun e => x ∈ e)).card : ℝ) ≤ r := hdegree x
    exact hcount.trans (by exact_mod_cast hreal)
  have hindices : indices.card = L.card := by simp [indices, I]
  have hbudget' : (0 : ℝ) + (indices.card : ℝ) / q +
      2 * (0 + r + 2 * q) < α * (Fintype.card V : ℝ) := by
    have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
    have hm : (L.card : ℝ) / q ≤ (m : ℝ) / q :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hqReal.le
    rw [hindices]
    linarith
  obtain ⟨w, hw, hdis, haux⟩ := exists_compatible_family p F (reserveGraph X)
    α 0 hres ∅ (fun x => by simp) ∅ u v k indices
    (fun e _ => hne e) (fun e _ => hk e) r q hq hroot (by simpa using hbudget')
  have hadj : ∀ e : I, (reserveGraph X).Adj (u e) (w e) ∧
      (reserveGraph X).Adj (w e) (v e) ∧ p (w e) = k e := by
    intro e
    obtain ⟨ha, hb, hc, _, _, _⟩ := hw e (mem_univ e)
    exact ⟨ha, hb, hc⟩
  have hpaths : ∀ e : I, pathEdges (u e) (v e) (w e) ⊆ X := by
    intro e a ha
    obtain ⟨huw, hwv, _⟩ := hadj e
    rcases mem_insert.mp ha with rfl | ha
    · exact ((SimpleGraph.fromEdgeSet_adj _).mp huw).1
    · have heq := mem_singleton.mp ha
      subst a
      have h := ((SimpleGraph.fromEdgeSet_adj _).mp hwv).1
      change s(w e, v e) ∈ X at h
      simpa only [Sym2.eq_swap] using h
  let P := familyEdges indices u v w
  have hPX : P ⊆ X := by
    intro a ha
    obtain ⟨e, _, ha⟩ := mem_biUnion.mp ha
    exact hpaths e ha
  have hLP : Disjoint L P := hLX.mono_right hPX
  let S : I → Finset V := fun e => {u e, v e, w e}
  have hdist : ∀ e : I, u e ≠ v e ∧ u e ≠ w e ∧ v e ≠ w e := by
    intro e
    exact ⟨hne e, (hadj e).1.ne, (hadj e).2.1.ne.symm⟩
  have htri : ∀ e : I, triEdges (S e) = insert e.val (pathEdges (u e) (v e) (w e)) := by
    intro e
    obtain ⟨ha, hb, hc⟩ := hdist e
    rw [triEdges_three ha hb hc, huv]
    rfl
  have htyped : ∀ e : I, IsTypedTri p F (S e) := by
    intro e
    obtain ⟨ha, hb, hc⟩ := hdist e
    refine ⟨by simp [S, ha, hb, hc], ?_⟩
    rw [map_three p ha hb hc, (hadj e).2.2]
    exact hk e
  have htriDis : (indices : Set I).PairwiseDisjoint (fun e => triEdges (S e)) := by
    intro e he e' he' hne'
    change Disjoint (triEdges (S e)) (triEdges (S e'))
    rw [htri e, htri e', disjoint_insert_left, disjoint_insert_right, mem_insert, not_or]
    refine ⟨⟨fun h => hne' (Subtype.ext h), ?_⟩, ?_, hdis he he' hne'⟩
    · exact fun h => disjoint_left.mp hLX e.property (hpaths e' h)
    · exact fun h => disjoint_left.mp hLX e'.property (hpaths e h)
  have hunion : indices.biUnion (fun e => triEdges (S e)) = L ∪ P := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, ha⟩ := mem_biUnion.mp ha
      rw [htri e] at ha
      rcases mem_insert.mp ha with ha | ha
      · exact mem_union_left _ (ha ▸ e.property)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨e, he, ha⟩)
    · intro ha
      rcases mem_union.mp ha with ha | ha
      · let e : I := ⟨a, ha⟩
        exact mem_biUnion.mpr ⟨e, mem_univ e, by rw [htri e]; exact mem_insert_self _ _⟩
      · obtain ⟨e, he, ha⟩ := mem_biUnion.mp ha
        exact mem_biUnion.mpr ⟨e, he, by rw [htri e]; exact mem_insert_of_mem ha⟩
  refine ⟨P, hPX, ?_, hLP, ?_, ?_⟩
  · have h := family_degree_bound indices u v w ∅ 0 r q
      (fun x => by simp) hroot haux
    simpa only [empty_union, zero_add] using h
  · rw [← hunion]
    exact RefinerAssembly.hasDecomp_biUnion indices (fun e => triEdges (S e))
      (fun e _ => hasDecomp_triEdges (htyped e)) htriDis
  · rw [familyEdges_card indices u v w (fun e _ => hne e) hdis, hindices]

/-- Cover-down plus the supplied universal absorber closes the supplied packing.
The absorber receives `X \ P`, not the original main leftover. -/
theorem hasDecomp_of_sparse_main_packing [Fintype V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Q : Finset (Sym2 V)) (α : ℝ) [DecidableRel (reserveGraph X).Adj]
    (hE : IsIntDiv p F G.edgeFinset) (hA : A ⊆ G.edgeFinset) (hX : X ⊆ G.edgeFinset)
    (hAX : Disjoint A X)
    (habs : ∀ J ⊆ X, IsIntDiv p F J → HasDecomp p F (A ∪ J))
    (hres : AntiEdgeful p F (reserveGraph X) α)
    (hQ : Q ⊆ G.edgeFinset \ (A ∪ X)) (hQdec : HasDecomp p F Q)
    (htype : ∀ a b : V, s(a, b) ∈ (G.edgeFinset \ (A ∪ X)) \ Q →
      ∃ k : Fin t, ({p a, p b, k} : Multiset (Fin t)) ∈ F)
    (m r q : ℕ) (hq : 0 < q) (hcard : ((G.edgeFinset \ (A ∪ X)) \ Q).card ≤ m)
    (hdegree : DegBounded ((G.edgeFinset \ (A ∪ X)) \ Q) r)
    (hbudget : (m : ℝ) / q + 2 * ((r : ℝ) + 2 * q) < α * Fintype.card V) :
    HasDecomp p F G.edgeFinset := by
  let L := (G.edgeFinset \ (A ∪ X)) \ Q
  have hLX : Disjoint L X := by
    apply disjoint_left.mpr
    intro e he heX
    exact (mem_sdiff.mp (mem_sdiff.mp he).1).2 (mem_union_right _ heX)
  have hdiag : ∀ e ∈ L, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (by
      have h := (mem_sdiff.mp (mem_sdiff.mp he).1).1
      simpa using h)
  obtain ⟨P, hPX, _, hLP, hLPdec, _⟩ :=
    exists_reserve_cover p F X L α hres hLX hdiag htype m r q hq hcard hdegree hbudget
  have hQLP : Disjoint Q (L ∪ P) := by
    rw [disjoint_union_right]
    refine ⟨disjoint_left.mpr (fun e heQ heL => (mem_sdiff.mp heL).2 heQ), ?_⟩
    apply disjoint_of_subset_right hPX
    apply disjoint_left.mpr
    intro e heQ heX
    exact (mem_sdiff.mp (hQ heQ)).2 (mem_union_right _ heX)
  refine hasDecomp_of_absorber_cover hE hA hX hAX habs (EQ := Q ∪ (L ∪ P))
    ?_ ?_ (hQdec.union hLPdec hQLP)
  · intro e he
    rcases mem_union.mp he with he | he
    · have h := hQ he
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp h).1,
        fun hA' => (mem_sdiff.mp h).2 (mem_union_left _ hA')⟩
    · rcases mem_union.mp he with he | he
      · have h := (mem_sdiff.mp he).1
        exact mem_sdiff.mpr ⟨(mem_sdiff.mp h).1,
          fun hA' => (mem_sdiff.mp h).2 (mem_union_left _ hA')⟩
      · exact mem_sdiff.mpr ⟨hX (hPX he), fun hA' => disjoint_left.mp hAX hA' (hPX he)⟩
  · intro e he
    by_cases heQ : e ∈ Q
    · exact mem_union_left _ heQ
    · exact mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨he, heQ⟩))

omit [DecidableEq V] in
/-- An empty reserve cannot supply any relevant positive anti-edge query. -/
theorem not_antiEdgeful_empty_reserve [Fintype V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (α : ℝ)
    [DecidableRel (reserveGraph (∅ : Finset (Sym2 V))).Adj]
    (i j k : Fin t) (hτ : ({i, j, k} : Multiset (Fin t)) ∈ F)
    (u v : V) (huv : u ≠ v) (hu : p u = i) (hv : p v = j)
    (hpos : 0 < α * Fintype.card V) :
    ¬ AntiEdgeful p F (reserveGraph (∅ : Finset (Sym2 V))) α := by
  intro h
  have hb := h _ hτ i j k rfl u v huv hu hv
  have hz : (univ.filter (fun w => (reserveGraph (∅ : Finset (Sym2 V))).Adj u w ∧
      (reserveGraph (∅ : Finset (Sym2 V))).Adj w v ∧ p w = k)) = ∅ := by
    ext w
    simp
  rw [hz, card_empty, Nat.cast_zero] at hb
  linarith

end PartitionedTriangleAbsorption.ReserveCoverDown
