/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128
public import RequestProject.NW18.HingeModel
public import RequestProject.NW18.StarAssembly
public import PartitionedTriangleAbsorption.PaperII.FourColourApplication

@[expose] public section

/-!
# Theorem 12.8 from an exceptional pre-clean (exact residual obligation)

`ExceptionalCleanup128` is the residual statement of case (5) of §12.2 (proved as
`exceptional_cleanup_128` in `Case128/Main.lean`):
a sparse packing `Q` of edge-disjoint triangles that covers every edge at a small exceptional
set `S` and every internal edge of a four-part partition, uses each non-exceptional vertex in
at most `εn` of its triangles, and leaves a residual satisfying the two pair-balance
equations of the F3 consumer.

`theorem_12_8_of_exceptional_cleanup` proves the conclusion of Theorem 12.8 from it, by
applying `PaperII.margin_four_colour_decomposition`, derived from Paper II's F3 theorem,
to the residual graph on the non-exceptional vertices and gluing the result with `Q`.
The residual is **not** assumed to have minimum degree `≥ 3n/4`: it is only shown to have
minimum degree `≥ (3/4 − ε₀)|W|`, which is what the consumer requires.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Residual graph on the non-exceptional vertices -/

/-- The residual graph: vertices outside `S`, edges of `G` not in `C`. -/
def residualGraph (G : SimpleGraph V) (S : Finset V) (C : Finset (Sym2 V)) :
    SimpleGraph {x // x ∈ Sᶜ} where
  Adj a b := G.Adj a.1 b.1 ∧ s(a.1, b.1) ∉ C
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1.ne rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (C : Finset (Sym2 V)) :
    DecidableRel (residualGraph G S C).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a.1 b.1 ∧ s(a.1, b.1) ∉ C))

omit [Fintype V] in
lemma triEdges_map_image {W : Type*} [DecidableEq W] (f : W ↪ V) (s : Finset W) :
    triEdges (s.map f) = (triEdges s).image (Sym2.map f) := by
  rw [triEdges_map, map_eq_image]
  rfl

omit [Fintype V] in
lemma edgeVec_image_injective {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (f : W → V) (hf : Function.Injective f) (p : V → Fin t) (E : Finset (Sym2 W)) :
    edgeVec p (E.image (Sym2.map f)) = edgeVec (p ∘ f) E := by
  unfold edgeVec
  rw [sum_image (fun x _ y _ h => Sym2.map.injective hf h)]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => rfl

lemma residual_edgeFinset_image (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (C : Finset (Sym2 V))
    (hcov : ∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S) → s(u, v) ∈ C) :
    (residualGraph G S C).edgeFinset.image (Sym2.map Subtype.val) = G.edgeFinset \ C := by
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ a b =>
      have hab : (residualGraph G S C).Adj a b := by simpa using he'
      rw [Sym2.map_mk]
      exact mem_sdiff.mpr ⟨G.mem_edgeFinset.mpr hab.1, hab.2⟩
  · intro he
    obtain ⟨heG, heC⟩ := mem_sdiff.mp he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := G.mem_edgeFinset.mp heG
      have hx : x ∈ Sᶜ := mem_compl.mpr fun hx => heC (hcov x y hxy (Or.inl hx))
      have hy : y ∈ Sᶜ := mem_compl.mpr fun hy => heC (hcov x y hxy (Or.inr hy))
      refine mem_image.mpr ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
      have : (residualGraph G S C).Adj ⟨x, hx⟩ ⟨y, hy⟩ := ⟨hxy, heC⟩
      simpa using this

omit [Fintype V] in
/-- In a family of edge-disjoint triangles, every vertex lies on exactly twice as many covered
edges as triangles. -/
lemma covered_incident_card (Q : Finset (Finset V)) (hQ3 : ∀ t ∈ Q, t.card = 3)
    (hQdisj : (Q : Set (Finset V)).PairwiseDisjoint triEdges) (x : V) :
    ((Q.biUnion triEdges).filter (fun e => x ∈ e)).card = 2 * (Q.filter (fun t => x ∈ t)).card := by
  have hsplit : (Q.biUnion triEdges).filter (fun e => x ∈ e) =
      (Q.filter (fun t => x ∈ t)).biUnion (fun t => (triEdges t).filter (fun e => x ∈ e)) := by
    ext e
    simp only [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨⟨t, ht, he⟩, hx⟩
      refine ⟨t, ⟨ht, ?_⟩, he, hx⟩
      have := (mem_sym2_iff.mp (mem_filter.mp he).1) x hx
      exact this
    · rintro ⟨t, ⟨ht, -⟩, he, hx⟩
      exact ⟨⟨t, ht, he⟩, hx⟩
  rw [hsplit, card_biUnion]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun t ht => ?_
    obtain ⟨htQ, hxt⟩ := mem_filter.mp ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (hQ3 t htQ)
    rw [triEdges_three hab hac hbc]
    simp only [mem_insert, mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl
    · rw [filter_insert, filter_insert, filter_singleton]
      simp [hab, hac, hbc, Sym2.mem_iff]
    · rw [filter_insert, filter_insert, filter_singleton]
      simp [hab, hac, hbc, Sym2.mem_iff, Ne.symm hab, Sym2.eq_swap]
    · rw [filter_insert, filter_insert, filter_singleton]
      simp [hab, hac, Sym2.mem_iff, Ne.symm hac, Ne.symm hbc, Sym2.eq_swap]
  · intro t ht t' ht' htt'
    exact (hQdisj (mem_filter.mp ht).1 (mem_filter.mp ht').1 htt').mono
      (filter_subset _ _) (filter_subset _ _)

lemma residual_degree (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (C : Finset (Sym2 V)) (hC : C ⊆ G.edgeFinset)
    (hcov : ∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S) → s(u, v) ∈ C) (a : {x // x ∈ Sᶜ}) :
    (residualGraph G S C).degree a + (C.filter (fun e => a.1 ∈ e)).card = G.degree a.1 := by
  classical
  have h1 : (residualGraph G S C).degree a =
      ((G.neighborFinset a.1).filter (fun y => s(a.1, y) ∉ C)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply card_bij (fun b _ => b.1)
    · intro b hb
      have hab : (residualGraph G S C).Adj a b := by simpa using hb
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab.1, hab.2⟩
    · intro b _ b' _ h
      exact Subtype.val_injective h
    · intro y hy
      obtain ⟨hyN, hyC⟩ := mem_filter.mp hy
      have hay : G.Adj a.1 y := (G.mem_neighborFinset _ _).mp hyN
      have hyS : y ∈ Sᶜ := mem_compl.mpr fun hyS => hyC (hcov _ _ hay (Or.inr hyS))
      refine ⟨⟨y, hyS⟩, ?_, rfl⟩
      have : (residualGraph G S C).Adj a ⟨y, hyS⟩ := ⟨hay, hyC⟩
      simpa using this
  have h2 : (C.filter (fun e => a.1 ∈ e)).card =
      ((G.neighborFinset a.1).filter (fun y => s(a.1, y) ∈ C)).card := by
    symm
    apply card_bij (fun y _ => s(a.1, y))
    · intro y hy
      exact mem_filter.mpr ⟨(mem_filter.mp hy).2, Sym2.mem_mk_left _ _⟩
    · intro y _ y' _ h
      rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', h''⟩
      · exact h'
      · exact h''.trans h'
    · intro e he
      obtain ⟨heC, hae⟩ := mem_filter.mp he
      have heG := hC heC
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : G.Adj x y := G.mem_edgeFinset.mp heG
        rcases Sym2.mem_iff.mp hae with h | h
        · subst h
          exact ⟨y, mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy, heC⟩, rfl⟩
        · subst h
          refine ⟨x, mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy.symm, ?_⟩,
            Sym2.eq_swap⟩
          rwa [Sym2.eq_swap]
  rw [h1, h2, add_comm, card_filter_add_card_filter_not,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Gluing: a triangle decomposition of the residual graph together with the covering packing
`Q` is a triangle decomposition of `G`. -/
lemma hasTriangleDecomposition_of_residual {t : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (Q : Finset (Finset V)) (hQ : ∀ s ∈ Q, G.IsNClique 3 s)
    (hQdisj : (Q : Set (Finset V)).PairwiseDisjoint triEdges)
    (hcov : ∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S) → s(u, v) ∈ Q.biUnion triEdges)
    (c : {x // x ∈ Sᶜ} → Fin t) (F : Finset (Multiset (Fin t)))
    (D : Finset (Finset {x // x ∈ Sᶜ}))
    (hD : IsDecomp c F (residualGraph G S (Q.biUnion triEdges)).edgeFinset D) :
    NashWilliams.HasTriangleDecomposition G := by
  classical
  set C := Q.biUnion triEdges with hCdef
  let f : {x // x ∈ Sᶜ} ↪ V := Function.Embedding.subtype _
  obtain ⟨hDt, hDdisj, hDU⟩ := hD
  have hC : C ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun s hs => triEdges_subset_of_isNClique (hQ s hs)
  have hEimg := residual_edgeFinset_image G S C hcov
  have hD'tri : ∀ s ∈ D, triEdges (s.map f) ⊆ G.edgeFinset \ C := by
    intro s hs
    rw [triEdges_map_image, ← hEimg, ← hDU]
    exact image_subset_image (subset_biUnion_of_mem triEdges hs)
  have hQtri : ∀ s ∈ Q, triEdges s ⊆ C := fun s hs => subset_biUnion_of_mem triEdges hs
  rw [← hasDecomp_K3_iff]
  refine ⟨D.image (fun s => s.map f) ∪ Q, ⟨?_, ?_, ?_⟩⟩
  · intro s hs
    have h3 : s.card = 3 := by
      rcases mem_union.mp hs with hs | hs
      · obtain ⟨s', hs', rfl⟩ := mem_image.mp hs
        rw [card_map]; exact (hDt s' hs').1
      · exact (hQ s hs).2
    exact ⟨h3, by rw [map_onePart h3]; simp [K3fam]⟩
  · intro s hs s' hs' hne
    simp only [coe_union, Set.mem_union, mem_coe] at hs hs'
    rcases hs with hs | hs <;> rcases hs' with hs' | hs'
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hs'
      have hab : a ≠ b := fun h => hne (h ▸ rfl)
      change Disjoint (triEdges (a.map f)) (triEdges (b.map f))
      rw [triEdges_map_image, triEdges_map_image]
      exact (disjoint_image (Sym2.map.injective Subtype.val_injective)).mpr (hDdisj ha hb hab)
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
      exact disjoint_of_subset_left (hD'tri a ha)
        (disjoint_of_subset_right (hQtri s' hs') sdiff_disjoint)
    · obtain ⟨b, hb, rfl⟩ := mem_image.mp hs'
      exact disjoint_of_subset_right (hD'tri b hb)
        (disjoint_of_subset_left (hQtri s hs) disjoint_sdiff)
    · exact hQdisj hs hs' hne
  · rw [union_biUnion, ← hCdef]
    have : (D.image (fun s => s.map f)).biUnion triEdges = G.edgeFinset \ C := by
      rw [← hEimg, ← hDU, image_biUnion, biUnion_image]
      exact biUnion_congr rfl fun s _ => triEdges_map_image f s
    rw [this, sdiff_union_of_subset hC]

/-! ### The residual obligation and the reduction -/

/-- **Exceptional pre-clean for case (5)** (the residual obligation of Theorem 12.8,
proved as `exceptional_cleanup_128` in `Case128/Main.lean`).
For every `ε > 0` there are `α > 0` and `n₀` such that every `K₃`-divisible graph `G` on
`n ≥ n₀` vertices with `δ(G) ≥ 3n/4` which is `α`-close to `T₂(n/2)+T₂(n/2)` admits
* a partition `p : V → Fin 4`, an exceptional set `S` with `|S| ≤ εn`, and
* a family `Q` of edge-disjoint triangles of `G`

such that every edge of `G` meeting `S` and every edge inside a class of `p` lies in a triangle
of `Q`, every vertex outside `S` lies in at most `εn` triangles of `Q`, and the residual edge
set `R = E(G) ∖ ⋃ Q` satisfies the two pair-balance equations
`e(V₀,V₁)+e(V₂,V₃) = e(V₀,V₂)+e(V₁,V₃) = e(V₀,V₃)+e(V₁,V₂)` (stated with the ordered
edge-count vector `edgeVec`, which counts each cross edge twice).

No minimum-degree condition on the residual is asserted. -/
def ExceptionalCleanup128 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
      3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2T2 (Fintype.card V)) →
      ∃ (p : V → Fin 4) (S : Finset V) (Q : Finset (Finset V)),
        (S.card : ℝ) ≤ ε * Fintype.card V ∧
        (∀ s ∈ Q, G.IsNClique 3 s) ∧
        (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
        (∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S ∨ p u = p v) → s(u, v) ∈ Q.biUnion triEdges) ∧
        (∀ x, x ∉ S → ((Q.filter (fun s => x ∈ s)).card : ℝ) ≤ ε * Fintype.card V) ∧
        (edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 1 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 2 3 =
          edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 2 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 1 3) ∧
        (edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 1 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 2 3 =
          edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 3 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 1 2)

/-- **Theorem 12.8 from the exceptional pre-clean.**  The conclusion of Theorem 12.8 follows
from `ExceptionalCleanup128` and the proved F3 consumer of Paper II. Theorem 13.16 is
not used in this case. -/
theorem theorem_12_8_of_exceptional_cleanup (h : ExceptionalCleanup128) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2T2 (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨eps, heps, heps1, N, hN⟩ := PaperII.margin_four_colour_decomposition
  obtain ⟨α, hα, n₀, hcl⟩ := h (eps / 4) (by positivity)
  refine ⟨α, hα, max n₀ (2 * N + 1), fun V _ _ G _ hn hdiv hδ hc => ?_⟩
  obtain ⟨p, S, Q, hS, hQ, hQdisj, hcov, hload, hb1, hb2⟩ :=
    hcl V G (le_trans (le_max_left _ _) hn) hdiv hδ hc
  classical
  set n := Fintype.card V with hndef
  set C := Q.biUnion triEdges with hCdef
  have hC : C ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun s hs => triEdges_subset_of_isNClique (hQ s hs)
  have hcovS : ∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S) → s(u, v) ∈ C := fun u v huv h' =>
    hcov u v huv (h'.elim Or.inl fun h'' => Or.inr (Or.inl h''))
  set J := residualGraph G S C with hJdef
  let col : J.Coloring (Fin 4) :=
    SimpleGraph.Coloring.mk (fun a => p a.1)
      (fun {a b} hab heq => hab.2 (hcov _ _ hab.1 (Or.inr (Or.inr heq))))
  have hcol : (⇑col : {x // x ∈ Sᶜ} → Fin 4) = p ∘ Subtype.val := rfl
  -- sizes
  have hnN : 2 * N + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (2 * N + 1 : ℝ) ≤ n := by exact_mod_cast hnN
  have hWcard : Fintype.card {x // x ∈ Sᶜ} = n - S.card := by
    rw [Fintype.card_coe, card_compl]
  have hSn : S.card ≤ n := by
    rw [hndef]; exact card_le_univ S
  have hWR : (Fintype.card {x // x ∈ Sᶜ} : ℝ) = n - S.card := by
    rw [hWcard, Nat.cast_sub hSn]
  have hWge : (N : ℝ) + 1 / 2 ≤ Fintype.card {x // x ∈ Sᶜ} := by
    rw [hWR]
    have : (S.card : ℝ) ≤ n / 2 := by
      have h1 : eps / 4 * (n : ℝ) ≤ n / 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        nlinarith
      linarith
    linarith
  have hWN : N ≤ Fintype.card {x // x ∈ Sᶜ} := by
    have : (N : ℝ) < Fintype.card {x // x ∈ Sᶜ} := by linarith
    exact_mod_cast this.le
  have hWle : (Fintype.card {x // x ∈ Sᶜ} : ℝ) ≤ n := by
    rw [hWR]; have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _; linarith
  have hWpos : 0 < Fintype.card {x // x ∈ Sᶜ} := by
    have : (0 : ℝ) < Fintype.card {x // x ∈ Sᶜ} := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  haveI : Nonempty {x // x ∈ Sᶜ} := Fintype.card_pos_iff.mp hWpos
  -- residual degrees
  have hdegJ : ∀ a : {x // x ∈ Sᶜ},
      J.degree a + 2 * (Q.filter (fun s => a.1 ∈ s)).card = G.degree a.1 := by
    intro a
    have h1 := residual_degree G S C hC hcovS a
    rw [hCdef, covered_incident_card Q (fun s hs => (hQ s hs).2) hQdisj] at h1
    exact h1
  have hδR : (3 * n : ℝ) ≤ 4 * G.minDegree := by exact_mod_cast hδ
  have hmin : (3 / 4 - eps) * Fintype.card {x // x ∈ Sᶜ} ≤ (J.minDegree : ℝ) := by
    obtain ⟨a, ha⟩ := J.exists_minimal_degree_vertex
    rw [ha]
    have h1 : (J.degree a : ℝ) + 2 * (Q.filter (fun s => a.1 ∈ s)).card = G.degree a.1 := by
      exact_mod_cast hdegJ a
    have h2 : (G.minDegree : ℝ) ≤ G.degree a.1 := by exact_mod_cast G.minDegree_le_degree a.1
    have hnot : a.1 ∉ S := by
      have := a.2; rw [mem_compl] at this; exact this
    have h3 := hload a.1 hnot
    have h4 : (3 / 4 - eps) * (Fintype.card {x // x ∈ Sᶜ} : ℝ) ≤ (3 / 4 - eps) * n :=
      mul_le_mul_of_nonneg_left hWle (by linarith)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have heven : ∀ a, Even (J.degree a) := by
    intro a
    have h1 := hdegJ a
    have h2 := hdiv.2 a.1
    rw [← h1] at h2
    exact (Nat.even_add.mp h2).mpr (even_two_mul _)
  have hEimg := residual_edgeFinset_image G S C hcovS
  have hvec : edgeVec col J.edgeFinset = edgeVec p (G.edgeFinset \ C) := by
    rw [hcol, ← edgeVec_image_injective Subtype.val Subtype.val_injective p, hEimg]
  obtain ⟨D, hD, -⟩ := hN _ hWN J col hmin heven (by rw [hvec]; exact hb1)
    (by rw [hvec]; exact hb2)
  exact hasTriangleDecomposition_of_residual G S Q hQ hQdisj hcovS col _ D hD

/-! The obligation `ExceptionalCleanup128` is proved as `exceptional_cleanup_128`, and
Theorem 12.8 is stated and derived as `theorem_12_8`, in `RequestProject/NW18/Case128/Main.lean`
(they need the case-(5) development of `RequestProject/NW18/Case128/`, which imports this file). -/

end NashWilliams18
