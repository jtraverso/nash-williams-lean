/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Theorem146
public import RequestProject.NW18.Case125.SideCost

@[expose] public section

/-!
# The cleaned graph `G' = (G − E(T)) \ A` as a host of Theorem 14.6

`G'` is `residualGraph G A (⋃ T)` (vertex type `{x // x ∈ Aᶜ}`), with the bipartition
`p ∘ Subtype.val`.  Transfer lemmas:

* `isIntDiv_residual`: integral `F₀`-divisibility of `G'` (Lemma 13.18: Eulerian and
  cross-divisible);
* `isF0Idealized_residual`: hypotheses (a), (b) of Theorem 14.6 for `G'` from Lemma 15.6 and
  the minimum degree of `G'`;
* `not_isSideClose_residual`: hypothesis (c) of Theorem 14.6 for `G'` (with `θ/2`) from the
  corresponding property of `G` (with `θ`), since `G'[V_i']` differs from `G[V_i]` by few
  vertices and edges.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)
open PartitionedTriangleAbsorption.F0ParallelObstruction (typeEdgeVec_001 typeEdgeVec_011 F0_sum)

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_edgeFinset_filter_mem (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  rw [SimpleGraph.incidenceFinset_eq_filter]

/-- The degree in the cleaned graph is the number of residual edges at the vertex. -/
theorem residual_degree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (C : Finset (Sym2 V)) (hC : C ⊆ G.edgeFinset)
    (hcov : ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ C) (a : {x // x ∈ Aᶜ}) :
    (residualGraph G A C).degree a = ((G.edgeFinset \ C).filter (fun e => a.1 ∈ e)).card := by
  have h1 := residual_degree G A C hC hcov a
  have h2 : ((G.edgeFinset \ C).filter (fun e => a.1 ∈ e)).card +
      (C.filter (fun e => a.1 ∈ e)).card = G.degree a.1 := by
    rw [← card_edgeFinset_filter_mem, ← card_union_of_disjoint]
    · congr 1; ext e; simp only [mem_union, mem_filter, mem_sdiff]; constructor
      · rintro (⟨⟨h1, _⟩, h2⟩ | ⟨h1, h2⟩)
        exacts [⟨h1, h2⟩, ⟨hC h1, h2⟩]
      · rintro ⟨h1, h2⟩
        by_cases h : e ∈ C
        exacts [Or.inr ⟨h, h2⟩, Or.inl ⟨⟨h1, h⟩, h2⟩]
    · exact disjoint_filter_filter sdiff_disjoint
  omega

/-- Integral `F₀`-divisibility of the cleaned graph. -/
theorem isIntDiv_residual (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (A : Finset V) (T : Finset (Finset V)) (hdiv : NashWilliams.IsTriangleDivisible G)
    (hT : IsTrianglePacking G T)
    (hcov : ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ T.biUnion triEdges)
    (hsur : intSurplus p (G.edgeFinset \ T.biUnion triEdges) = 0) :
    IsIntDiv (fun a : {x // x ∈ Aᶜ} => p a.1) F0
      (residualGraph G A (T.biUnion triEdges)).edgeFinset := by
  set C := T.biUnion triEdges with hCdef
  set G' := residualGraph G A C
  have hC : C ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT.1 t ht)
  rw [PartitionedTriangleAbsorption.TypedPieceConditions.F0_isIntDiv_iff
    (fun e he => G'.not_isDiag_of_mem_edgeFinset he)]
  refine ⟨?_, ?_, ?_⟩
  · -- every pair of parts is typeable for `F₀`
    intro a b _
    refine ⟨if p a.1 = p b.1 then p a.1 + 1 else p a.1, ?_⟩
    simp only [PartitionedTriangleAbsorption.TypedTransformer.Link]
    rw [mem_F0_iff]
    rcases fin2_cases (p a.1) with h1 | h1 <;> rcases fin2_cases (p b.1) with h2 | h2 <;>
      simp [h1, h2]
  · -- even degrees
    intro a
    have hload : PartitionedTriangleAbsorption.AntiEdgeSelection.incidentLoad G'.edgeFinset a =
        G'.degree a := card_edgeFinset_filter_mem G' a
    rw [hload]
    have h1 : G'.degree a + (C.filter (fun e => a.1 ∈ e)).card = G.degree a.1 :=
      residual_degree G A C hC hcov a
    have h2 := covered_incident_card T (fun t ht => (hT.1 t ht).2) hT.2 a.1
    have h3 := hdiv.2 a.1
    rw [← hCdef] at h2
    obtain ⟨k, hk⟩ := h3
    refine ⟨k - (T.filter (fun t => a.1 ∈ t)).card, ?_⟩
    omega
  · -- the edge-vector lattice condition (cross-divisibility)
    have himg := residual_edgeFinset_image G A C hcov
    have hvec : edgeVec (fun a : {x // x ∈ Aᶜ} => p a.1) G'.edgeFinset =
        edgeVec p (G.edgeFinset \ C) := by
      rw [← himg, edgeVec_image_injective _ Subtype.val_injective]
      rfl
    rw [hvec]
    set E := G.edgeFinset \ C
    have hev : ∀ i, Even (edgeVec p E i i) := by
      intro i
      unfold edgeVec
      rw [Finset.sum_apply, Finset.sum_apply]
      refine Finset.even_sum _ fun e _ => ?_
      induction e using Sym2.ind with
      | _ x y =>
        simp only [pairVec, Sym2.lift_mk]
        by_cases h : p x = i ∧ p y = i
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; decide
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; decide
    obtain ⟨c0, hc0⟩ := hev 0
    obtain ⟨c1, hc1⟩ := hev 1
    have hsym := PartitionedTriangleAbsorption.TypedLoadFamilies.edgeVec_symm p E 1 0
    unfold intSurplus at hsur
    refine ⟨fun τ => if τ = {0, 0, 1} then c0 else c1, ?_⟩
    rw [F0_sum, typeEdgeVec_001, typeEdgeVec_011]
    have hne : ({0, 1, 1} : Multiset (Fin 2)) ≠ {0, 0, 1} := by decide
    funext i j
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
      simp <;> omega

omit [DecidableEq V] in
lemma partDeg_add_partDeg {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (q : W → Fin 2) (v : W) : partDeg H q v 0 + partDeg H q v 1 = H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, partDeg, partDeg,
    ← card_union_of_disjoint]
  · congr 1; ext w
    simp only [mem_union, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    rcases fin2_cases (q w) with h | h <;> simp [h]
  · exact disjoint_filter.mpr fun w _ h1 h2 => by rw [h1.2] at h2; exact absurd h2.2 (by decide)

omit [DecidableEq V] in
lemma partDeg_le_card_partClass {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (q : W → Fin 2) (v : W) (i : Fin 2) :
    partDeg H q v i ≤ (partClass q i).card :=
  card_le_card fun w hw => by
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [partClass, mem_filter, mem_univ, true_and]; exact hw.2

lemma partDeg_residual_le (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (A : Finset V) (C : Finset (Sym2 V)) (a : {x // x ∈ Aᶜ}) (i : Fin 2) :
    partDeg (residualGraph G A C) (fun b => p b.1) a i ≤ partDeg G p a.1 i := by
  unfold partDeg
  rw [← card_map (Function.Embedding.subtype _)]
  refine card_le_card fun x hx => ?_
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply] at hx
  obtain ⟨b, ⟨hab, hb⟩, rfl⟩ := hx
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hab.1, hb⟩

lemma card_partClass_residual (p : V → Fin 2) (A : Finset V) (i : Fin 2) :
    ((partClass p i).card : ℝ) - A.card ≤
      ((partClass (fun b : {x // x ∈ Aᶜ} => p b.1) i).card : ℝ) := by
  have h : (partClass p i \ A).card ≤ (partClass (fun b : {x // x ∈ Aᶜ} => p b.1) i).card := by
    rw [← card_map (Function.Embedding.subtype _)]
    refine card_le_card fun x hx => ?_
    simp only [mem_sdiff, partClass, mem_filter, mem_univ, true_and] at hx
    simp only [mem_map, partClass, mem_filter, mem_univ, true_and,
      Function.Embedding.subtype_apply, Subtype.exists, mem_compl]
    exact ⟨x, hx.2, hx.1, rfl⟩
  have h2 := le_card_sdiff A (partClass p i)
  have h2' : ((partClass p i).card : ℝ) - A.card ≤ ((partClass p i \ A).card : ℝ) := by
    have : (partClass p i).card ≤ (partClass p i \ A).card + A.card := by omega
    have : ((partClass p i).card : ℝ) ≤ (partClass p i \ A).card + A.card := by
      exact_mod_cast this
    linarith
  have h' : ((partClass p i \ A).card : ℝ) ≤
      ((partClass (fun b : {x // x ∈ Aᶜ} => p b.1) i).card : ℝ) := by exact_mod_cast h
  linarith

lemma card_residual_type (A : Finset V) :
    (Fintype.card {x // x ∈ Aᶜ} : ℝ) = Fintype.card V - A.card := by
  rw [Fintype.card_coe, card_compl]
  have : A.card ≤ Fintype.card V := card_le_univ A
  push_cast [this]; ring

/-- Hypotheses (a), (b) of Theorem 14.6 for the cleaned graph. -/
theorem isF0Idealized_residual (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (A : Finset V) (C : Finset (Sym2 V)) {β ε₀ : ℝ} (hε : 40 * Real.sqrt β ≤ ε₀) (hε1 : ε₀ ≤ 1 / 8)
    (hA : (A.card : ℝ) ≤ 2 * Real.sqrt β * Fintype.card V)
    (hcl : ∀ i, (1 - Real.sqrt β) * Fintype.card V / 2 ≤ ((partClass p i).card : ℝ))
    (hint : ∀ v, v ∉ A → (partDeg G p v (p v) : ℝ) ≤ (1 / 4 + 2 * Real.sqrt β) * Fintype.card V)
    (hdeg : ∀ a : {x // x ∈ Aᶜ}, (3 / 4 - 7 * Real.sqrt β) * ((Fintype.card V : ℝ) - A.card) ≤
      ((residualGraph G A C).degree a : ℝ)) :
    IsF0Idealized ε₀ (residualGraph G A C) (fun a => p a.1) := by
  set G' := residualGraph G A C
  set p' : {x // x ∈ Aᶜ} → Fin 2 := fun a => p a.1
  set s := Real.sqrt β with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hm := card_residual_type A
  set n : ℝ := (Fintype.card V : ℝ)
  set m : ℝ := (Fintype.card {x // x ∈ Aᶜ} : ℝ)
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hcl' : ∀ i, (1 - 5 * s) * n / 2 ≤ ((partClass p' i).card : ℝ) := by
    intro i; have := card_partClass_residual p A i; have := hcl i; linarith
  have hsum : ((partClass p' 0).card : ℝ) + (partClass p' 1).card = m := by
    have := card_partClass_add p'
    simp only [m]; exact_mod_cast this
  have hmn : m ≤ n := by linarith
  have hm2 : (1 - 2 * s) * n ≤ m := by linarith
  have hε0 : 0 ≤ ε₀ := by linarith
  -- upper bound on internal degrees, in terms of `m`
  have hup : ∀ a : {x // x ∈ Aᶜ}, (partDeg G' p' a (p' a) : ℝ) ≤ (1 / 4 + 2 * s) * n := by
    intro a
    have h1 : (partDeg G' p' a (p' a) : ℝ) ≤ partDeg G p a.1 (p a.1) := by
      exact_mod_cast partDeg_residual_le G p A C a (p a.1)
    exact h1.trans (hint a.1 (mem_compl.mp a.2))
  have key1 : (1 / 4 + 2 * s) * n ≤ (1 / 4 + ε₀) * m := by
    have : (1 / 4 + 2 * s) * n ≤ (1 / 4 + ε₀) * ((1 - 2 * s) * n) := by
      have h' : 0 ≤ (ε₀ - 40 * s) * n := mul_nonneg (by linarith) hn
      have h'' : 0 ≤ (1 / 8 - ε₀) * s * n := mul_nonneg (mul_nonneg (by linarith) hs0) hn
      have h''' : 0 ≤ s * n := mul_nonneg hs0 hn
      nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left hm2 (by linarith))
  refine ⟨fun i => ?_, fun a => ⟨?_, (hup a).trans key1⟩, fun a i hi => ?_⟩
  · -- (a)
    have h1 := hcl' i
    have : (1 - ε₀) * m / 2 ≤ (1 - 5 * s) * n / 2 := by
      have : (1 - ε₀) * m ≤ (1 - 5 * s) * m := mul_le_mul_of_nonneg_right (by linarith)
        (by linarith)
      have : (1 - 5 * s) * m ≤ (1 - 5 * s) * n := mul_le_mul_of_nonneg_left hmn (by linarith)
      linarith
    linarith
  · -- lower bound on internal degrees
    have hds := partDeg_add_partDeg G' p' a
    have hd := hdeg a
    rw [← hm] at hd
    have hcls := hsum
    have hc0 : (partDeg G' p' a 0 : ℝ) ≤ (partClass p' 0).card := by
      exact_mod_cast partDeg_le_card_partClass G' p' a 0
    have hc1 : (partDeg G' p' a 1 : ℝ) ≤ (partClass p' 1).card := by
      exact_mod_cast partDeg_le_card_partClass G' p' a 1
    have hds' : (partDeg G' p' a 0 : ℝ) + partDeg G' p' a 1 = G'.degree a := by
      exact_mod_cast hds
    have h0 := hcl' 0
    have h1 := hcl' 1
    have hlow : (1 / 4 - ε₀) * m ≤ (3 / 4 - 7 * s) * m - m + (1 - 5 * s) * n / 2 := by
      have : (1 - 5 * s) * m ≤ (1 - 5 * s) * n := mul_le_mul_of_nonneg_left hmn (by linarith)
      have : 0 ≤ (ε₀ - 40 * s) * m := mul_nonneg (by linarith) (by linarith)
      nlinarith
    rcases fin2_cases (p' a) with h | h <;> rw [h] <;> linarith
  · -- cross degrees
    have hds := partDeg_add_partDeg G' p' a
    have hd := hdeg a
    rw [← hm] at hd
    have hds' : (partDeg G' p' a 0 : ℝ) + partDeg G' p' a 1 = G'.degree a := by
      exact_mod_cast hds
    have hu := hup a
    have hcross : (1 / 2 - ε₀) * m ≤ (3 / 4 - 7 * s) * m - (1 / 4 + 2 * s) * n := by
      have : (1 / 4 + 2 * s) * n ≤ (1 / 4 - 7 * s + ε₀) * ((1 - 2 * s) * n) := by
        have h' : 0 ≤ (ε₀ - 40 * s) * n := mul_nonneg (by linarith) hn
        have h'' : 0 ≤ (1 / 8 - ε₀) * s * n := mul_nonneg (mul_nonneg (by linarith) hs0) hn
        have h''' : 0 ≤ s * n := mul_nonneg hs0 hn
        have h4 : 0 ≤ s * s * n := mul_nonneg (mul_nonneg hs0 hs0) hn
        nlinarith
      have := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ 1 / 4 - 7 * s + ε₀ by linarith)
      nlinarith
    rcases fin2_cases (p' a) with h | h <;> rcases fin2_cases i with h' | h'
    · exact absurd (h'.trans h.symm) hi
    · rw [h']; rw [h] at hu; linarith
    · rw [h']; rw [h] at hu; linarith
    · exact absurd (h'.trans h.symm) hi

open Classical in
/-- Comparison of the edit costs in the cleaned graph and in `G`. -/
lemma sideCost_map_residual_le (G : SimpleGraph V) (A : Finset V)
    (C : Finset (Sym2 V)) (D' X' : Finset {x // x ∈ Aᶜ}) (b : Bool) :
    sideCost G (D'.map (Function.Embedding.subtype _)) (X'.map (Function.Embedding.subtype _)) b
      ≤ sideCost (residualGraph G A C) D' X' b +
        2 * (C.filter (fun e => ∀ x ∈ e, x ∉ A)).card := by
  set emb : {x // x ∈ Aᶜ} ↪ V := Function.Embedding.subtype _
  set Cout := C.filter (fun e => ∀ x ∈ e, x ∉ A)
  unfold sideCost
  have hsub : ((D'.map emb) ×ˢ (D'.map emb)).filter (fun q => q.1 ≠ q.2 ∧
      ¬ (G.Adj q.1 q.2 ↔ sideTarget (X'.map emb) b q.1 q.2)) ⊆
      (((D' ×ˢ D').filter (fun q => q.1 ≠ q.2 ∧
        ¬ ((residualGraph G A C).Adj q.1 q.2 ↔ sideTarget X' b q.1 q.2))).map
          (emb.prodMap emb)) ∪
      (univ ×ˢ univ).filter (fun q : V × V => s(q.1, q.2) ∈ Cout) := by
    intro q hq
    simp only [mem_filter, mem_product, mem_map] at hq
    obtain ⟨⟨⟨a, ha, hqa⟩, ⟨c, hc, hqc⟩⟩, hne, hbad⟩ := hq
    by_cases hC : s(q.1, q.2) ∈ C
    · refine mem_union_right _ ?_
      simp only [mem_filter, mem_univ, mem_product, true_and, Cout]
      refine ⟨hC, fun x hx => ?_⟩
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · rw [← hqa]; exact mem_compl.mp a.2
      · rw [← hqc]; exact mem_compl.mp c.2
    · refine mem_union_left _ (mem_map.mpr ⟨(a, c), ?_, ?_⟩)
      · simp only [mem_filter, mem_product]
        refine ⟨⟨ha, hc⟩, fun h => hne (by rw [← hqa, ← hqc, h]), ?_⟩
        intro hiff
        apply hbad
        have e1 : (residualGraph G A C).Adj a c ↔ G.Adj q.1 q.2 := by
          rw [← hqa, ← hqc]
          change G.Adj a.1 c.1 ∧ s(a.1, c.1) ∉ C ↔ G.Adj a.1 c.1
          have e : s(a.1, c.1) = s(q.1, q.2) := by rw [← hqa, ← hqc]; rfl
          exact ⟨fun h => h.1, fun h => ⟨h, by rw [e]; exact hC⟩⟩
        have e2 : sideTarget (X'.map emb) b q.1 q.2 ↔ sideTarget X' b a c := by
          rw [← hqa, ← hqc]
          have hm : ∀ y, emb y ∈ X'.map emb ↔ y ∈ X' := fun y => by
            simp [emb]
          cases b <;> simp only [sideTarget, hm]
        rw [← e1, e2]; exact hiff
      · simp only [Function.Embedding.prodMap, Function.Embedding.coeFn_mk, Prod.map]
        exact Prod.ext hqa hqc
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [card_map]
  have := card_pairs_in_le Cout
  convert Nat.add_le_add_left this _ using 3
  ext q; simp only [mem_filter]

/-- Hypothesis (c) of Theorem 14.6 transfers to the cleaned graph. -/
theorem not_isSideClose_residual (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (A : Finset V) (C : Finset (Sym2 V)) {β θ : ℝ} (hθ : 0 < θ)
    (hβθ : 160 * Real.sqrt β ≤ θ) (hn : 12 / θ ≤ Fintype.card V)
    (hA : (A.card : ℝ) ≤ 2 * Real.sqrt β * Fintype.card V)
    (hC : ((C.filter (fun e => ∀ x ∈ e, x ∉ A)).card : ℝ) ≤
      3 * Real.sqrt β * (Fintype.card V : ℝ) ^ 2)
    (i : Fin 2) (hDi : (Fintype.card V : ℝ) / 3 ≤ ((partClass p i).card : ℝ))
    (hside : ¬ IsSideClose θ G (partClass p i)) :
    ¬ IsSideClose (θ / 2) (residualGraph G A C) (partClass (fun a => p a.1) i) := by
  rintro ⟨X', hX'D, hX'c, b, hcost⟩
  apply hside
  set emb : {x // x ∈ Aᶜ} ↪ V := Function.Embedding.subtype _
  set D' := partClass (fun a : {x // x ∈ Aᶜ} => p a.1) i
  set D := partClass p i
  set D₀ := D'.map emb
  set X₀ := X'.map emb
  have hD₀D : D₀ ⊆ D := by
    intro x hx
    simp only [D₀, D', mem_map, partClass, mem_filter, mem_univ, true_and] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [D, partClass, mem_filter, mem_univ, true_and]; exact ha
  have hDD₀ : D \ D₀ ⊆ A := by
    intro x hx
    rw [mem_sdiff] at hx
    by_contra hxA
    apply hx.2
    simp only [D₀, D', mem_map, partClass, mem_filter, mem_univ, true_and]
    refine ⟨⟨x, mem_compl.mpr hxA⟩, ?_, rfl⟩
    simpa [D, partClass] using hx.1
  have hX₀D : X₀ ⊆ D := (map_subset_map.mpr hX'D).trans hD₀D
  have hcardD₀ : D₀.card = D'.card := card_map _
  have hk : ((D \ D₀).card : ℝ) ≤ A.card := by exact_mod_cast card_le_card hDD₀
  have hDD₀c : D₀.card + (D \ D₀).card = D.card := by
    rw [add_comm]; exact card_sdiff_add_card_eq_card hD₀D
  -- costs
  have h1 := sideCost_map_residual_le G A C D' X' b
  have h2 := sideCost_le_of_subset G (D := D) (D' := D₀) (X := X₀) b
  obtain ⟨X, hXD, hXc, h3⟩ := exists_sideCost_rebalance G (X := X₀) b hX₀D (D.card / 2)
    (Nat.div_le_self _ _) ((D \ D₀).card + 1) (by rw [card_map]; omega) (by rw [card_map]; omega)
  refine ⟨X, hXD, hXc, b, ?_⟩
  have h1' : (sideCost G D₀ X₀ b : ℝ) ≤ sideCost (residualGraph G A C) D' X' b +
      2 * (C.filter (fun e => ∀ x ∈ e, x ∉ A)).card := by exact_mod_cast h1
  have h2' : (sideCost G D X₀ b : ℝ) ≤ sideCost G D₀ X₀ b + 2 * (D \ D₀).card * D.card := by
    exact_mod_cast h2
  have h3' : (sideCost G D X b : ℝ) ≤ sideCost G D X₀ b + 2 * D.card * ((D \ D₀).card + 1) := by
    exact_mod_cast h3
  have hD'D : (D'.card : ℝ) ≤ D.card := by
    rw [← hcardD₀]; exact_mod_cast card_le_card hD₀D
  set s := Real.sqrt β
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set n : ℝ := (Fintype.card V : ℝ)
  set d : ℝ := (D.card : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hcost' : (sideCost (residualGraph G A C) D' X' b : ℝ) ≤ θ * d ^ 2 := by
    have h' : (D'.card : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hD'D 2
    have h'' : θ * (D'.card : ℝ) ^ 2 ≤ θ * d ^ 2 := mul_le_mul_of_nonneg_left h' hθ.le
    linarith
  have hn3 : n ≤ 3 * d := by linarith
  have hθn : 12 ≤ θ * n := by have := (div_le_iff₀ hθ).mp hn; linarith
  have hsθ : s ≤ θ / 160 := by linarith
  have e1 : 6 * s * n ^ 2 ≤ 18 * (s * n * d) := by
    have := mul_le_mul_of_nonneg_left hn3 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hs0) hn0)
    have h1 : 6 * s * n * n = 6 * s * n ^ 2 := by ring
    have h2 : 6 * s * n * (3 * d) = 18 * (s * n * d) := by ring
    linarith
  have e2 : 2 * d ≤ θ * n * d / 6 := by
    have := mul_le_mul_of_nonneg_right hθn hd0
    linarith
  have e3 : s * n * d ≤ θ * n * d / 160 := by
    have := mul_le_mul_of_nonneg_right hsθ (mul_nonneg hn0 hd0)
    have h1 : s * (n * d) = s * n * d := by ring
    have h2 : θ / 160 * (n * d) = θ * n * d / 160 := by ring
    linarith
  have e4 : θ * n * d ≤ 3 * (θ * d ^ 2) := by
    have := mul_le_mul_of_nonneg_left hn3 (mul_nonneg hθ.le hd0)
    have h1 : θ * d * n = θ * n * d := by ring
    have h2 : θ * d * (3 * d) = 3 * (θ * d ^ 2) := by ring
    linarith
  set k : ℝ := ((D \ D₀).card : ℝ)
  have hkd : k * d ≤ 2 * (s * n * d) := by
    have := mul_le_mul_of_nonneg_right (hk.trans hA) hd0
    have h1 : 2 * s * n * d = 2 * (s * n * d) := by ring
    linarith
  have h2'' : (sideCost G D X₀ b : ℝ) ≤ sideCost G D₀ X₀ b + 2 * (k * d) := by
    have h1 : 2 * k * d = 2 * (k * d) := by ring
    linarith
  have h3'' : (sideCost G D X b : ℝ) ≤ sideCost G D X₀ b + 2 * (k * d) + 2 * d := by
    have h1 : 2 * d * (k + 1) = 2 * (k * d) + 2 * d := by ring
    linarith
  have hC' : (2 : ℝ) * (C.filter (fun e => ∀ x ∈ e, x ∉ A)).card ≤ 6 * s * n ^ 2 := by
    linarith
  linarith

end NashWilliams18
