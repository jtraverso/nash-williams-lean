/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ClassEvenProducer
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.LabelWalk

/-!
# The virtual even refiner on the components of the allowed-label graph

The classes are the connected components of the allowed-label graph (`compMap`), restricted
to active labels.  Only the component-closure property `compMap_link` is used (the first
clause of `IsCommonLinkClassMap`); there is NO common-neighbour hypothesis.

On each class `W_r` the existing heap refiner (`subset_refiner`) is run on the VIRTUAL
complete graph `⊤` restricted to `W_r`, which is anti-edgeful with density `1/2` as soon as
`|W_r| ≥ 4`.  A nonempty class has at least `ω n` vertices by the guarded supply.  The
result (`virtual_even_refiner`) is a single fixed virtual remainder (pairs inside one class,
not necessarily host edges) and a fixed library of loopless even pieces with at most `42`
edges, refining `R ∪ L` for every integrally divisible `L ⊆ X`, with the budgets
`Δ(R) ≤ 4096 t λ n`, `#library ≤ 4096 t ρ n²`, total library load `≤ 4096 t λ n`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.OnePart
open PartitionedTriangleAbsorption.TypedTransformer

variable {t : ℕ}

/-- Every type lies inside one component class or avoids it (component closure only). -/
theorem type_closed_comp {F : Finset (Multiset (Fin t))} (hF3 : ∀ τ ∈ F, Multiset.card τ = 3)
    (r : Fin t) :
    ∀ τ ∈ F, (∀ i ∈ τ, i ∈ classParts F (compMap F) r) ∨
      (∀ i ∈ τ, i ∉ classParts F (compMap F) r) := by
  intro τ hτ
  have key : ∀ i ∈ τ, ∀ j ∈ τ, ActivePart F i ∧ compMap F i = compMap F j := by
    intro i hi j hj
    obtain ⟨τ', rfl⟩ := Multiset.exists_cons_of_mem hi
    have hc : Multiset.card τ' = 2 := by
      have := hF3 _ hτ; simp at this; omega
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
    have hl : Link F i a b := by
      change ({i, a, b} : Multiset (Fin t)) ∈ F
      simpa using hτ
    refine ⟨(activePart_of_link hl).1, ?_⟩
    rcases Multiset.mem_cons.mp hj with rfl | hj
    · rfl
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact compMap_link hl
      · exact compMap_link ((link_swap F i a j).mp hl)
  by_cases h : ∃ i ∈ τ, i ∈ classParts F (compMap F) r
  · left
    obtain ⟨i, hi, hir⟩ := h
    intro j hj
    obtain ⟨hj1, hji⟩ := key j hj i hi
    rw [mem_classParts] at hir ⊢
    exact ⟨hj1, hji.trans hir.2⟩
  · right
    push_neg at h
    exact h

section Virtual

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem mem_compVerts_of_adj {F : Finset (Multiset (Fin t))} {p : V → Fin t} {u v : V}
    (huv : ∃ k, Link F (p u) (p v) k) :
    u ∈ classVerts F p (compMap F) (compMap F (p u)) ∧
      v ∈ classVerts F p (compMap F) (compMap F (p u)) := by
  obtain ⟨k, hk⟩ := huv
  obtain ⟨hu, hv⟩ := activePart_of_link hk
  rw [mem_classVerts, mem_classVerts, mem_classParts, mem_classParts]
  exact ⟨⟨hu, rfl⟩, ⟨hv, (compMap_link hk).symm⟩⟩

omit [DecidableEq V] in
theorem edge_inside_comp {F : Finset (Multiset (Fin t))} {p : V → Fin t}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hact : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) {r : Fin t} {e : Sym2 V}
    (he : e ∈ G.edgeFinset) {v : V} (hve : v ∈ e) (hv : v ∈ classVerts F p (compMap F) r) :
    ∀ x ∈ e, x ∈ classVerts F p (compMap F) r := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨ha, hb⟩ := mem_compVerts_of_adj (hact a b he)
    have hr : compMap F (p a) = r := by
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact classVerts_eq_of_mem ha hv
      · exact classVerts_eq_of_mem hb hv
    intro x hx
    rw [← hr]
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact ha
    · exact hb

omit [DecidableEq V] in
theorem comp_of_edge {F : Finset (Multiset (Fin t))} {p : V → Fin t}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hact : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) : ∃ r, ∀ x ∈ e, x ∈ classVerts F p (compMap F) r := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨ha, hb⟩ := mem_compVerts_of_adj (hact a b he)
    refine ⟨compMap F (p a), fun x hx => ?_⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact ha
    · exact hb

/-- A nonempty component class has at least `ω n` vertices. -/
theorem comp_card_ge (F : Finset (Multiset (Fin t))) (p : V → Fin t) (r : Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : ℝ) (hsup : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 2 (ω * Fintype.card V))
    {w : V} (hw : w ∈ classVerts F p (compMap F) r) :
    ω * Fintype.card V ≤ (classVerts F p (compMap F) r).card := by
  have hw' := hw
  rw [mem_classVerts, mem_classParts] at hw'
  obtain ⟨⟨a, k, hl⟩, hr⟩ := hw'
  have hn := hsup {w} (by simp) a (by
    intro x hx
    rw [mem_singleton.mp hx]
    exact ⟨k, hl⟩)
  refine hn.trans ?_
  have hsub : guardedNeighbours p G {w} a ⊆ classVerts F p (compMap F) r := by
    intro x hx
    obtain ⟨_, hxa, -⟩ := mem_filter.mp hx
    rw [mem_classVerts, mem_classParts, hxa]
    exact ⟨(activePart_of_link hl).2, (compMap_link hl).symm.trans hr⟩
  exact_mod_cast card_le_card hsub

omit [Fintype V] [DecidableEq V] in
/-- The virtual complete graph on a set of at least four vertices is anti-edgeful with
density `1/2` for the one-part triangle family. -/
theorem top_comap_antiEdgeful (W : Finset V)
    [DecidableRel ((⊤ : SimpleGraph V).comap (Subtype.val : W → V)).Adj]
    (hW : 4 ≤ W.card) :
    AntiEdgeful part1 triFam ((⊤ : SimpleGraph V).comap (Subtype.val : W → V)) (1 / 2) := by
  classical
  intro τ _ i j k _ u v huv _ _
  have hsub : (univ \ {u, v} : Finset W) ⊆ univ.filter (fun w : W =>
      ((⊤ : SimpleGraph V).comap Subtype.val).Adj u w ∧
        ((⊤ : SimpleGraph V).comap Subtype.val).Adj w v ∧ part1 w = k) := by
    intro w hw
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at hw
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, Subsingleton.elim _ _⟩
    · rw [SimpleGraph.comap_adj, SimpleGraph.top_adj]
      exact fun h => hw.1 (Subtype.ext h).symm
    · rw [SimpleGraph.comap_adj, SimpleGraph.top_adj]
      exact fun h => hw.2 (Subtype.ext h)
  have hc := card_le_card hsub
  have hcW : Fintype.card W = W.card := Fintype.card_coe W
  have h2 : (univ \ {u, v} : Finset W).card = W.card - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair huv, hcW]
  rw [h2] at hc
  refine le_trans ?_ (Nat.cast_le.mpr hc)
  rw [Nat.cast_sub (by omega), hcW]
  have : (4 : ℝ) ≤ W.card := by exact_mod_cast hW
  push_cast
  linarith

/-- The per-class VIRTUAL refiner data. -/
theorem virtual_class_data (F : Finset (Multiset (Fin t))) (p : V → Fin t) (r : Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ)
    (hsup : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 2 (ω * Fintype.card V))
    (hlam : 0 < lam) (h64 : 64 * lam ≤ ω) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (h4 : 4 ≤ ω * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset) (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (ind : Finset HeapIdx) (P : HeapIdx → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ (⊤ : SimpleGraph V).edgeFinset ∧
      (∀ e ∈ R, ∀ v ∈ e, v ∈ classVerts F p (compMap F) r) ∧ Disjoint R X ∧
      (∀ j ∈ ind, P j ⊆ X ∪ R ∧ (∀ e ∈ P j, ¬ e.IsDiag) ∧ (∀ v, Even (incidentLoad (P j) v)) ∧
        (P j).card ≤ 42 ∧ ∀ e ∈ P j, ∀ v ∈ e, v ∈ classVerts F p (compMap F) r) ∧
      (∀ L ⊆ X, (∀ e ∈ L, ∀ v ∈ e, v ∈ classVerts F p (compMap F) r) → Even3 L →
        ∃ s ⊆ ind, (s : Set HeapIdx).PairwiseDisjoint P ∧ s.biUnion P = R ∪ L) ∧
      (∀ v, (incidentLoad R v : ℝ) ≤ 4 * lam * Fintype.card V) ∧
      (ind.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ ind, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  classical
  by_cases hne : (classVerts F p (compMap F) r).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have hcard := comp_card_ge F p r G ω hsup hw
    set W := classVerts F p (compMap F) r with hWdef
    have hWpos : 0 < Fintype.card W := by
      rw [Fintype.card_coe]; exact card_pos.mpr ⟨w, hw⟩
    have hWc : (Fintype.card W : ℝ) = W.card := by rw [Fintype.card_coe]
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hW4 : 4 ≤ W.card := by
      have : (4 : ℝ) ≤ W.card := h4.trans hcard
      exact_mod_cast this
    letI : DecidableRel ((⊤ : SimpleGraph V).comap (Subtype.val : W → V)).Adj :=
      fun a b => inferInstanceAs (Decidable ((⊤ : SimpleGraph V).Adj a.1 b.1))
    have hXT : X ⊆ (⊤ : SimpleGraph V).edgeFinset := by
      refine hXG.trans ?_
      intro e he
      exact SimpleGraph.edgeFinset_mono le_top he
    refine subset_refiner (⊤ : SimpleGraph V) W hWpos lam rho (1 / 2) hlam hrho ?_ hscale hn1
      hn2 ?_ (top_comap_antiEdgeful W hW4) X hXT hX
    · rw [hWc]
      have := mul_le_mul_of_nonneg_right h64 hn0
      linarith
    · have hWr : (0 : ℝ) < Fintype.card W := by exact_mod_cast hWpos
      rw [mul_div_assoc', div_le_iff₀ hWr, hWc]
      have := mul_le_mul_of_nonneg_right h64 hn0
      linarith
  · rw [not_nonempty_iff_eq_empty] at hne
    refine ⟨∅, fun _ => ∅, ∅, empty_subset _, by simp, disjoint_empty_left _, by simp, ?_,
      ?_, by simp only [card_empty, Nat.cast_zero]; positivity, ?_⟩
    · intro L _ hLW _
      refine ⟨∅, empty_subset _, by simp, ?_⟩
      have hL : L = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨v, hv⟩ := exists_mem_sym2 e
        have := hLW e he v hv
        rw [hne] at this
        exact absurd this (notMem_empty v)
      simp [hL]
    · intro v
      simp only [incidentLoad, filter_empty, card_empty, Nat.cast_zero]
      positivity
    · intro v
      simp only [sum_empty, Nat.cast_zero]
      positivity

/-- **The virtual even refiner** on the component classes. -/
theorem virtual_even_refiner (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ)
    (hact : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k)
    (hsup : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 2 (ω * Fintype.card V))
    (hlam : 0 < lam) (h64 : 64 * lam ≤ ω) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (h4 : 4 ≤ ω * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset) (hXdeg : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ E : PredRefiner (Fin t × HeapIdx) X (IsIntDiv p F),
      E.R0 ⊆ (⊤ : SimpleGraph V).edgeFinset ∧
      (∀ e ∈ E.R0, ∃ r, ∀ v ∈ e, v ∈ classVerts F p (compMap F) r) ∧
      (∀ i ∈ E.lib, (E.P i).card ≤ 42) ∧
      DegBounded E.R0 (4096 * t * lam * Fintype.card V) ∧
      (E.lib.card : ℝ) ≤ 4096 * t * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ i ∈ E.lib, incidentLoad (E.P i) v : ℕ) : ℝ) ≤ 4096 * t * lam * Fintype.card V := by
  classical
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hdata := fun r => virtual_class_data F p r G ω lam rho hsup hlam h64 hrho hscale hn1 hn2
    h4 X hXG hXdeg
  choose ind P R hRG hRW hRX hP hrefi hRdeg hcard hload using hdata
  have hLG : ∀ L ⊆ X, L ⊆ G.edgeFinset := fun L hL => hL.trans hXG
  refine ⟨{ lib := univ.biUnion (fun r => (ind r).image (fun j => (r, j)))
            P := fun x => P x.1 x.2
            R0 := univ.biUnion R
            loopP := fun x hx => (hP x.1 x.2 (mem_classIdx.mp hx)).2.1
            evenP := fun x hx => (hP x.1 x.2 (mem_classIdx.mp hx)).2.2.1
            subP := fun x hx => by
              refine (hP x.1 x.2 (mem_classIdx.mp hx)).1.trans ?_
              rw [union_comm]
              exact union_subset_union (subset_biUnion_of_mem R (mem_univ x.1)) subset_rfl
            disjRX := by
              rw [disjoint_biUnion_left]
              exact fun r _ => hRX r
            refines := ?_ }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- refinement
    intro L hLX hdiv
    have hloopL : ∀ e ∈ L, ¬ e.IsDiag := fun e he =>
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hLG L hLX he))
    have hevenL := TypedDivisibilityCollapse.even_of_isIntDiv hF3 hloopL hdiv
    set Lr : Fin t → Finset (Sym2 V) :=
      fun r => L.filter (fun e => ∀ v ∈ e, v ∈ classVerts F p (compMap F) r) with hLr
    have hLr3 : ∀ r, Even3 (Lr r) := by
      intro r
      refine ⟨?_, ?_⟩
      · have h := three_dvd_card_classEdges p F hF3 (type_closed_comp hF3 r) hdiv
        convert h using 2
        ext e
        simp only [hLr, mem_filter, mem_classVerts]
      · intro v
        by_cases hv : v ∈ classVerts F p (compMap F) r
        · have heq : incidentLoad (Lr r) v = incidentLoad L v := by
            unfold incidentLoad
            rw [hLr, filter_filter]
            congr 1
            exact filter_congr fun e he => ⟨fun h => h.2, fun h =>
              ⟨edge_inside_comp hact (hLG L hLX he) h hv, h⟩⟩
          rw [heq]; exact hevenL v
        · have heq : incidentLoad (Lr r) v = 0 := by
            unfold incidentLoad
            rw [card_eq_zero, filter_eq_empty_iff]
            intro e he hve
            exact hv ((mem_filter.mp he).2 v hve)
          rw [heq]; exact ⟨0, rfl⟩
    have hs := fun r => hrefi r (Lr r) ((filter_subset _ _).trans hLX)
      (fun e he => (mem_filter.mp he).2) (hLr3 r)
    choose s hs1 hs2 hs3 using hs
    refine ⟨univ.biUnion (fun r => (s r).image (fun j => (r, j))), ?_, ?_, ?_⟩
    · intro x hx
      exact mem_classIdx.mpr (hs1 x.1 (mem_classIdx.mp hx))
    · intro x hx y hy hxy
      have hx' := mem_classIdx.mp hx
      have hy' := mem_classIdx.mp hy
      change Disjoint (P x.1 x.2) (P y.1 y.2)
      by_cases h1 : x.1 = y.1
      · have h2 : x.2 ≠ y.2 := fun h => hxy (Prod.ext h1 h)
        rw [h1] at hx' ⊢
        exact hs2 y.1 hx' hy' h2
      · exact disjoint_of_classes h1 (hP x.1 x.2 (hs1 _ hx')).2.2.2.2
          (hP y.1 y.2 (hs1 _ hy')).2.2.2.2
    · ext e
      simp only [mem_biUnion, mem_image, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨x, ⟨r, j, hj, rfl⟩, he⟩
        have : e ∈ (s r).biUnion (P r) := mem_biUnion.mpr ⟨j, hj, he⟩
        rw [hs3 r, mem_union] at this
        rcases this with h | h
        · exact Or.inl ⟨r, h⟩
        · exact Or.inr (mem_filter.mp h).1
      · rintro (⟨r, he⟩ | he)
        · have : e ∈ (s r).biUnion (P r) := by rw [hs3 r]; exact mem_union_left _ he
          obtain ⟨j, hj, hej⟩ := mem_biUnion.mp this
          exact ⟨(r, j), ⟨r, j, hj, rfl⟩, hej⟩
        · obtain ⟨r, hr⟩ := comp_of_edge hact (hLG L hLX he)
          have : e ∈ (s r).biUnion (P r) := by
            rw [hs3 r]; exact mem_union_right _ (mem_filter.mpr ⟨he, hr⟩)
          obtain ⟨j, hj, hej⟩ := mem_biUnion.mp this
          exact ⟨(r, j), ⟨r, j, hj, rfl⟩, hej⟩
  · exact biUnion_subset.mpr fun r _ => hRG r
  · intro e he
    obtain ⟨r, -, her⟩ := mem_biUnion.mp he
    exact ⟨r, hRW r e her⟩
  · intro x hx
    exact (hP x.1 x.2 (mem_classIdx.mp hx)).2.2.2.1
  · intro v
    change ((incidentLoad (univ.biUnion R) v : ℕ) : ℝ) ≤ _
    have h1 : ((incidentLoad (univ.biUnion R) v : ℕ) : ℝ) ≤ ∑ r, (incidentLoad (R r) v : ℝ) := by
      exact_mod_cast incidentLoad_biUnion_le univ R v
    have h2 : ∑ r, (incidentLoad (R r) v : ℝ) ≤ ∑ _r : Fin t, 4 * lam * Fintype.card V :=
      sum_le_sum fun r _ => hRdeg r v
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (t : ℝ) * (4 * lam * Fintype.card V) ≤ 4096 * t * lam * Fintype.card V := by
      have : (0 : ℝ) ≤ t * lam * Fintype.card V := by positivity
      nlinarith
    linarith
  · have h1 : ((univ.biUnion (fun r => (ind r).image (fun j => (r, j)))).card : ℝ) ≤
        ∑ r, ((ind r).card : ℝ) := by exact_mod_cast card_classIdx_le ind
    have h2 : ∑ r, ((ind r).card : ℝ) ≤ ∑ _r : Fin t, 1224 * rho * (Fintype.card V : ℝ) ^ 2 :=
      sum_le_sum fun r _ => hcard r
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (t : ℝ) * (1224 * rho * (Fintype.card V : ℝ) ^ 2) ≤
        4096 * t * rho * (Fintype.card V : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ t * rho * (Fintype.card V : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  · intro v
    change ((∑ x ∈ univ.biUnion (fun r => (ind r).image (fun j => (r, j))),
      incidentLoad (P x.1 x.2) v : ℕ) : ℝ) ≤ _
    rw [sum_classIdx ind (fun x => incidentLoad (P x.1 x.2) v), Nat.cast_sum]
    have h2 : ∑ r, ((∑ j ∈ ind r, incidentLoad (P r j) v : ℕ) : ℝ) ≤
        ∑ _r : Fin t, 4096 * lam * Fintype.card V := sum_le_sum fun r _ => hload r v
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (t : ℝ) * (4096 * lam * Fintype.card V) = 4096 * t * lam * Fintype.card V := by ring
    linarith

end Virtual

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
