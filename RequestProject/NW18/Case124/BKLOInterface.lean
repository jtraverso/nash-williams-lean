/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# External interface C (BKLO Lemma 10.3 for triangles) and the BKLO cover-down family

This file only **states** the two BKLO results offered as external inputs for branch 12.4, in
the vocabulary of the request (`nbhdIn`, `degTo`, `edgesIn`, `edgesBtw`, `edeg`, `TriDecomp`),
and proves two facts **about the hypotheses** of Lemma 10.3 that do not use the lemma itself:

* `bklo103_hyp_of_degrees` (positive bridge): conditions 2 and 3 of Lemma 10.3 hold for the
  full neighbourhoods `N_x = N_H(x) ∩ W` as soon as every vertex has at least `(3/4 - τ)|W|`
  neighbours in `W`, `γ + 3τ/2 ≤ 1/8`, and the active side has at most `γ|W|/2` vertices.  This is
  exactly where the `3/4` threshold enters: the slack is `3/8 - 1/4 = 1/8`.
* `bklo103_active_card_le` (quantitative obstruction): conditions 2 and 3 force every active
  vertex `x` (one with `N_x ≠ ∅`) to have `|N_x| ≥ 2γ|W|`, hence at most `|W|/4` vertices of `U`
  are active.  So one application of Lemma 10.3 can never cover the cross edges of a vortex level
  in which more than `|W|/4` vertices of `U` still have an edge into `W`.

Neither external statement is proved here; they are named propositions to be supplied by the
BKLO sources (`BKLO.lemma103K3_holds`, `BKLO.exists_coverDown_family`).
-/

namespace NashWilliams18.BKLOIface

open Finset

variable {V : Type*} [DecidableEq V]

/-- `N_H(x) ∩ W`. -/
def nbhdIn (H : Finset (Sym2 V)) (x : V) (W : Finset V) : Finset V :=
  W.filter (fun y => s(x, y) ∈ H)

/-- `d_H(x, W) = |N_H(x) ∩ W|`. -/
def degTo (H : Finset (Sym2 V)) (x : V) (W : Finset V) : ℕ := (nbhdIn H x W).card

/-- Edges of `H` with both ends in `W`. -/
noncomputable def edgesIn (H : Finset (Sym2 V)) (W : Finset V) : Finset (Sym2 V) :=
  open Classical in H.filter (fun e => ∀ v ∈ e, v ∈ W)

/-- Edges of `H` with one end in `U` and the other in `W`. -/
noncomputable def edgesBtw (H : Finset (Sym2 V)) (U W : Finset V) : Finset (Sym2 V) :=
  open Classical in H.filter (fun e => ∃ u ∈ U, ∃ w ∈ W, e = s(u, w))

/-- `d_H(v)`: number of edges of `H` at `v`. -/
def edeg (H : Finset (Sym2 V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The three edges of a vertex triple. -/
def triEdges (t : Finset V) : Finset (Sym2 V) := t.sym2.filter (fun e => ¬ e.IsDiag)

/-- `D` is a triangle decomposition of `H`: 3-vertex sets with pairwise disjoint edge sets whose
union is exactly `H` (so each is a real triangle of `H`). -/
def IsTriDecomp (H : Finset (Sym2 V)) (D : Finset (Finset V)) : Prop :=
  (∀ t ∈ D, t.card = 3) ∧
    (∀ t ∈ D, ∀ t' ∈ D, t ≠ t' → Disjoint (triEdges t) (triEdges t')) ∧
    D.biUnion triEdges = H

/-- `H` has a triangle decomposition. -/
def TriDecomp (H : Finset (Sym2 V)) : Prop := ∃ D, IsTriDecomp H D

/-- **External interface C: BKLO Lemma 10.3 for triangles** (statement only; to be discharged by
`BKLO.lemma103K3_holds`).  For every `γ > 0` and `k > 0` there is `n₀` such that for every
loopless edge set `H` on an `n`-vertex type with `n ≥ n₀`, disjoint `U, W` with `|W| ≥ ⌊n/k⌋`,
(1) `|N_x|` even, (2) `d_H(y, N_x) ≥ |N_x|/2 + γ|W|` for `y ∈ N_x`, (3) `d_H(y, U) ≤ γ|W|/2` for
`y ∈ W`, there is `HV ⊆ E(H[W])` with `E_H(U,W) ∪ HV` triangle-decomposable and `Δ(HV) ≤ γ|W|`.
No minimum-degree premise. -/
def Lemma103K3 : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ k : ℕ, 0 < k → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
    n₀ ≤ Fintype.card V → ∀ (H : Finset (Sym2 V)), (∀ e ∈ H, ¬ e.IsDiag) →
    ∀ U W : Finset V, Disjoint U W → Fintype.card V / k ≤ W.card →
    (∀ x ∈ U, Even (degTo H x W)) →
    (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
      (degTo H x W : ℝ) / 2 + γ * W.card ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
    (∀ y ∈ W, (degTo H y U : ℝ) ≤ γ * W.card / 2) →
    ∃ HV ⊆ edgesIn H W, TriDecomp (edgesBtw H U W ∪ HV) ∧
      ∀ v, (edeg HV v : ℝ) ≤ γ * W.card

/-- The apexes in `W` of the pair `uv` with respect to `R`. -/
def apexes (R : Finset (Sym2 V)) (W : Finset V) (u v : V) : Finset V :=
  W.filter (fun w => s(u, w) ∈ R ∧ s(v, w) ∈ R)

/-- **BKLO cover-down family** (statement only; to be discharged by
`BKLO.exists_coverDown_family`).  `L, R` disjoint loopless edge sets, no edge of `L` meets `W`,
and `d_L(u) + d_L(v) ≤ |apexes_R(W,u,v)|` for every `uv ∈ L`: there is an edge-disjoint family of
triangles with all edges in `L ∪ R` covering every edge of `L`.  (Nothing is claimed about how
much of `R` is consumed.) -/
def CoverDownFamily : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (L R : Finset (Sym2 V)) (W : Finset V),
    (∀ e ∈ L, ¬ e.IsDiag) → (∀ e ∈ R, ¬ e.IsDiag) → Disjoint L R →
    (∀ e ∈ L, ∀ v ∈ e, v ∉ W) →
    (∀ u v, s(u, v) ∈ L → edeg L u + edeg L v ≤ (apexes R W u v).card) →
    ∃ D : Finset (Finset V), (∀ t ∈ D, t.card = 3 ∧ triEdges t ⊆ L ∪ R) ∧
      (∀ t ∈ D, ∀ t' ∈ D, t ≠ t' → Disjoint (triEdges t) (triEdges t')) ∧
      L ⊆ D.biUnion triEdges

/-! ### Facts about the hypotheses of Lemma 10.3 -/

/-- The common bound: `d_H(y, N_x) ≥ |N_x| + d_H(y, W) - |W|`. -/
lemma degTo_nbhd_ge (H : Finset (Sym2 V)) (x y : V) (W : Finset V) :
    (degTo H x W : ℤ) + degTo H y W - W.card ≤ degTo H y (nbhdIn H x W) := by
  classical
  have hsub : nbhdIn H x W ⊆ W := filter_subset _ _
  have hsub2 : nbhdIn H y W ⊆ W := filter_subset _ _
  -- `N_x ∩ N_y ⊆ nbhdIn H y N_x`
  have hinter : nbhdIn H x W ∩ nbhdIn H y W ⊆ nbhdIn H y (nbhdIn H x W) := by
    intro z hz
    simp only [mem_inter, nbhdIn, mem_filter] at hz ⊢
    exact ⟨⟨hz.1.1, hz.1.2⟩, hz.2.2⟩
  have hunion : (nbhdIn H x W ∪ nbhdIn H y W).card ≤ W.card :=
    card_le_card (union_subset hsub hsub2)
  have hcu := card_union_add_card_inter (nbhdIn H x W) (nbhdIn H y W)
  have hci := card_le_card hinter
  unfold degTo
  omega

/-- **Positive bridge for Lemma 10.3.**  If every `x ∈ U` and every `y ∈ W` has at least
`(3/4 - τ)|W|` neighbours in `W`, `γ + 3τ/2 ≤ 1/8` and `|U| ≤ γ|W|/2`, then conditions 2 and 3 of
Lemma 10.3 hold for `H` (with the full neighbourhoods `N_x = N_H(x) ∩ W`). -/
theorem bklo103_hyp_of_degrees (H : Finset (Sym2 V))
    (U W : Finset V) (γ τ : ℝ) (hγτ : γ + 3 / 2 * τ ≤ 1 / 8)
    (hU : ∀ x ∈ U, (3 / 4 - τ) * W.card ≤ (degTo H x W : ℝ))
    (hW : ∀ y ∈ W, (3 / 4 - τ) * W.card ≤ (degTo H y W : ℝ))
    (hUcard : (U.card : ℝ) ≤ γ * W.card / 2) :
    (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
      (degTo H x W : ℝ) / 2 + γ * W.card ≤ (degTo H y (nbhdIn H x W) : ℝ)) ∧
    (∀ y ∈ W, (degTo H y U : ℝ) ≤ γ * W.card / 2) := by
  refine ⟨fun x hx y hy => ?_, fun y _ => ?_⟩
  · have hyW : y ∈ W := (mem_filter.mp hy).1
    have h1 := degTo_nbhd_ge H x y W
    have h1' : (degTo H x W : ℝ) + degTo H y W - W.card ≤ degTo H y (nbhdIn H x W) := by
      exact_mod_cast h1
    have hx' := hU x hx
    have hy' := hW y hyW
    have hle : (degTo H x W : ℝ) ≤ W.card := by
      exact_mod_cast card_le_card (filter_subset _ W)
    nlinarith
  · have : degTo H y U ≤ U.card := card_le_card (filter_subset _ U)
    have : (degTo H y U : ℝ) ≤ U.card := by exact_mod_cast this
    linarith

/-- Double counting of cross edges: `∑_{x ∈ U} d_H(x, W) = ∑_{y ∈ W} d_H(y, U)`. -/
lemma sum_degTo_comm (H : Finset (Sym2 V)) (U W : Finset V) :
    ∑ x ∈ U, degTo H x W = ∑ y ∈ W, degTo H y U := by
  classical
  simp only [degTo, nbhdIn, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  rw [Sym2.eq_swap]

/-- **Quantitative obstruction for Lemma 10.3.**  Under conditions 2 and 3 with `γ > 0`, every
active vertex `x ∈ U` (with `N_H(x) ∩ W ≠ ∅`) satisfies `|N_x| ≥ 2γ|W|`, and the number of active
vertices is at most `|W|/4`. -/
theorem bklo103_active_card_le (H : Finset (Sym2 V)) (U W : Finset V) (γ : ℝ) (hγ : 0 < γ)
    (h2 : ∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
      (degTo H x W : ℝ) / 2 + γ * W.card ≤ (degTo H y (nbhdIn H x W) : ℝ))
    (h3 : ∀ y ∈ W, (degTo H y U : ℝ) ≤ γ * W.card / 2) :
    (∀ x ∈ U, (nbhdIn H x W).Nonempty → 2 * γ * W.card ≤ (degTo H x W : ℝ)) ∧
      4 * ((U.filter (fun x => (nbhdIn H x W).Nonempty)).card : ℝ) ≤ W.card := by
  classical
  have hbig : ∀ x ∈ U, (nbhdIn H x W).Nonempty → 2 * γ * W.card ≤ (degTo H x W : ℝ) := by
    rintro x hx ⟨y, hy⟩
    have := h2 x hx y hy
    have hle : degTo H y (nbhdIn H x W) ≤ degTo H x W :=
      card_le_card (filter_subset _ _)
    have hle' : (degTo H y (nbhdIn H x W) : ℝ) ≤ degTo H x W := by exact_mod_cast hle
    linarith
  refine ⟨hbig, ?_⟩
  set A := U.filter (fun x => (nbhdIn H x W).Nonempty)
  have hsumA : (A.card : ℝ) * (2 * γ * W.card) ≤ ∑ x ∈ U, (degTo H x W : ℝ) := by
    calc (A.card : ℝ) * (2 * γ * W.card) = ∑ x ∈ A, 2 * γ * W.card := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ A, (degTo H x W : ℝ) :=
          sum_le_sum fun x hx => hbig x (mem_filter.mp hx).1 (mem_filter.mp hx).2
      _ ≤ ∑ x ∈ U, (degTo H x W : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have hsumW : ∑ x ∈ U, (degTo H x W : ℝ) ≤ W.card * (γ * W.card / 2) := by
    have := sum_degTo_comm H U W
    have hc : ∑ x ∈ U, (degTo H x W : ℝ) = ∑ y ∈ W, (degTo H y U : ℝ) := by
      exact_mod_cast this
    rw [hc]
    calc ∑ y ∈ W, (degTo H y U : ℝ) ≤ ∑ _y ∈ W, γ * W.card / 2 := sum_le_sum h3
      _ = W.card * (γ * W.card / 2) := by rw [sum_const, nsmul_eq_mul]
  have hW0 : (0 : ℝ) ≤ W.card := by positivity
  rcases eq_or_lt_of_le hW0 with h0 | hpos
  · -- `W = ∅`: no vertex is active
    have hWe : W = ∅ := by
      have : W.card = 0 := by exact_mod_cast h0.symm
      exact card_eq_zero.mp this
    have hA : A = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hne
      obtain ⟨y, hy⟩ := hne
      simp [nbhdIn, hWe] at hy
    simp [hA]
  · have key : (A.card : ℝ) * (2 * γ * W.card) ≤ W.card * (γ * W.card / 2) :=
      hsumA.trans hsumW
    have hγW : 0 < γ * W.card := mul_pos hγ hpos
    nlinarith

/-- **Consequence for a vortex level.**  If more than `|W|/4` vertices of `U` have an `H`-edge into
`W`, conditions 2 and 3 of Lemma 10.3 cannot both hold (for any `γ > 0`). -/
theorem bklo103_not_applicable (H : Finset (Sym2 V)) (U W : Finset V) (γ : ℝ) (hγ : 0 < γ)
    (hmany : (W.card : ℝ) < 4 * ((U.filter (fun x => (nbhdIn H x W).Nonempty)).card : ℝ)) :
    ¬ ((∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
        (degTo H x W : ℝ) / 2 + γ * W.card ≤ (degTo H y (nbhdIn H x W) : ℝ)) ∧
      (∀ y ∈ W, (degTo H y U : ℝ) ≤ γ * W.card / 2)) := by
  rintro ⟨h2, h3⟩
  have := (bklo103_active_card_le H U W γ hγ h2 h3).2
  linarith

/-- **Small-set cover-down at degree `3/4` from Lemma 10.3** (conditional on the named external
interface `Lemma103K3`).  For `γ > 0`, `τ ≥ 0` with `γ + 3τ/2 ≤ 1/8` and `k > 0` there is `n₀`
such that: if `n ≥ n₀`, `U, W` are disjoint, `|W| ≥ ⌊n/k⌋`, `|U| ≤ γ|W|/2`, every vertex of
`U ∪ W` has at least `(3/4 - τ)|W|` `H`-neighbours in `W`, and every `x ∈ U` has an even number of
`H`-neighbours in `W`, then all cross edges `E_H(U,W)` are covered, together with some
`HV ⊆ E(H[W])` of maximum degree `≤ γ|W|`, by an exact triangle decomposition. -/
theorem small_set_coverDown_of_lemma103 (h103 : Lemma103K3) (γ τ : ℝ) (hγ : 0 < γ)
    (hγτ : γ + 3 / 2 * τ ≤ 1 / 8) (k : ℕ) (hk : 0 < k) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], n₀ ≤ Fintype.card V →
      ∀ (H : Finset (Sym2 V)), (∀ e ∈ H, ¬ e.IsDiag) →
      ∀ U W : Finset V, Disjoint U W → Fintype.card V / k ≤ W.card →
      (U.card : ℝ) ≤ γ * W.card / 2 →
      (∀ x ∈ U, (3 / 4 - τ) * W.card ≤ (degTo H x W : ℝ)) →
      (∀ y ∈ W, (3 / 4 - τ) * W.card ≤ (degTo H y W : ℝ)) →
      (∀ x ∈ U, Even (degTo H x W)) →
      ∃ HV ⊆ edgesIn H W, TriDecomp (edgesBtw H U W ∪ HV) ∧
        ∀ v, (edeg HV v : ℝ) ≤ γ * W.card := by
  obtain ⟨n₀, hn₀⟩ := h103 γ hγ k hk
  refine ⟨n₀, fun V _ _ hn H hH U W hUW hW hU hdU hdW heven => ?_⟩
  obtain ⟨h2, h3⟩ := bklo103_hyp_of_degrees H U W γ τ hγτ hdU hdW hU
  exact hn₀ V hn H hH U W hUW hW heven h2 h3

/-! ### What the conclusion of Lemma 10.3 costs inside `W` -/

lemma mk_mem_triEdges' {t : Finset V} {a b : V} :
    s(a, b) ∈ triEdges t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := by
  simp [triEdges, and_assoc]

/-- **Load identity for the conclusion of Lemma 10.3.**  If `E_H(U,W) ∪ HV` (with `U, W`
disjoint and `HV ⊆ E(H[W])`) has a triangle decomposition, then every `y ∈ W` has at least as
many `HV`-edges as cross edges: `d_H(y, U) ≤ d_HV(y)`.  (Each cross edge `xy` lies in a triangle
`xyz` with `z ∈ W` and `yz ∈ HV`, and distinct cross edges give distinct `yz`.)  So covering the
cross edges at `y` by star matchings removes at least as many edges inside `W` at `y`: a vertex of
`W` loses `2·d_H(y,U)` edges in total, which is why star matchings can only handle cross degree
that is small compared with the degree slack inside `W`. -/
theorem degTo_le_edeg_of_triDecomp (H HV : Finset (Sym2 V)) (U W : Finset V)
    (hUW : Disjoint U W) (hHV : HV ⊆ edgesIn H W) (D : Finset (Finset V))
    (hD : IsTriDecomp (edgesBtw H U W ∪ HV) D) (y : V) (hy : y ∈ W) :
    degTo H y U ≤ edeg HV y := by
  classical
  obtain ⟨h3, hdisj, hunion⟩ := hD
  have hHVW : ∀ e ∈ HV, ∀ v ∈ e, v ∈ W := fun e he => by
    have := hHV he
    unfold edgesIn at this
    exact (mem_filter.mp this).2
  have hU_notW : ∀ u ∈ U, u ∉ W := fun u hu hw => disjoint_left.mp hUW hu hw
  -- the relation: cross edge at `x` is matched with the `HV`-edge `yz`
  let r : V → Sym2 V → Prop := fun x e => ∃ t ∈ D, ∃ z, e = s(y, z) ∧ x ∈ t ∧ y ∈ t ∧ z ∈ t ∧
    x ∈ U ∧ z ∈ W ∧ z ≠ y
  apply card_le_card_of_forall_subsingleton r
  · intro x hx
    have hxU : x ∈ U := (mem_filter.mp hx).1
    have hxy : s(x, y) ∈ edgesBtw H U W := by
      unfold edgesBtw
      rw [mem_filter]
      exact ⟨by rw [Sym2.eq_swap]; exact (mem_filter.mp hx).2, x, hxU, y, hy, rfl⟩
    have : s(x, y) ∈ D.biUnion triEdges := by rw [hunion]; exact mem_union_left _ hxy
    obtain ⟨t, htD, hxt⟩ := mem_biUnion.mp this
    obtain ⟨hx_t, hy_t, hxyne⟩ := mk_mem_triEdges'.mp hxt
    -- third vertex
    obtain ⟨z, hz_t, hz_ne⟩ : ∃ z ∈ t, z ∉ ({x, y} : Finset V) := by
      by_contra hcon
      push_neg at hcon
      have : t ⊆ {x, y} := hcon
      have := card_le_card this
      rw [h3 t htD] at this
      have := card_le_two (a := x) (b := y)
      omega
    simp only [mem_insert, mem_singleton, not_or] at hz_ne
    -- `xz` is a cross edge, so `z ∈ W`
    have hxz : s(x, z) ∈ edgesBtw H U W ∪ HV := by
      rw [← hunion]
      exact mem_biUnion.mpr ⟨t, htD, mk_mem_triEdges'.mpr ⟨hx_t, hz_t, Ne.symm hz_ne.1⟩⟩
    have hzW : z ∈ W := by
      rcases mem_union.mp hxz with h | h
      · unfold edgesBtw at h
        obtain ⟨_, u, hu, w, hw, he⟩ := mem_filter.mp h
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hw
        · exact absurd hw (hU_notW _ hxU)
      · exact absurd (hHVW _ h x (Sym2.mem_mk_left _ _)) (hU_notW _ hxU)
    have hyz : s(y, z) ∈ edgesBtw H U W ∪ HV := by
      rw [← hunion]
      exact mem_biUnion.mpr ⟨t, htD, mk_mem_triEdges'.mpr ⟨hy_t, hz_t, Ne.symm hz_ne.2⟩⟩
    have hyzHV : s(y, z) ∈ HV := by
      rcases mem_union.mp hyz with h | h
      · unfold edgesBtw at h
        obtain ⟨_, u, hu, w, hw, he⟩ := mem_filter.mp h
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hy (hU_notW _ hu)
        · exact absurd hzW (hU_notW _ hu)
      · exact h
    exact ⟨s(y, z), mem_filter.mpr ⟨hyzHV, Sym2.mem_mk_left _ _⟩,
      t, htD, z, rfl, hx_t, hy_t, hz_t, hxU, hzW, hz_ne.2⟩
  · intro e _ x₁ hx₁ x₂ hx₂
    obtain ⟨_, t₁, ht₁, z₁, he₁, hx₁t, hyt₁, hzt₁, hx₁U, hz₁W, hz₁y⟩ := hx₁
    obtain ⟨_, t₂, ht₂, z₂, he₂, hx₂t, hyt₂, hzt₂, hx₂U, hz₂W, hz₂y⟩ := hx₂
    have hz : z₁ = z₂ := Sym2.congr_right.mp (he₁.symm.trans he₂)
    subst hz
    have ht : t₁ = t₂ := by
      by_contra hne
      have := hdisj t₁ ht₁ t₂ ht₂ hne
      exact disjoint_left.mp this (mk_mem_triEdges'.mpr ⟨hyt₁, hzt₁, Ne.symm hz₁y⟩)
        (mk_mem_triEdges'.mpr ⟨hyt₂, hzt₂, Ne.symm hz₁y⟩)
    subst ht
    -- `t₁ = {x₁, y, z₁}` and `x₂ ∈ t₁` is neither `y` nor `z₁`
    have hx₁y : x₁ ≠ y := fun h => hU_notW _ hx₁U (h ▸ hy)
    have hx₁z : x₁ ≠ z₁ := fun h => hU_notW _ hx₁U (h ▸ hz₁W)
    have hteq : t₁ = {x₁, y, z₁} := by
      have hsub : ({x₁, y, z₁} : Finset V) ⊆ t₁ := by
        intro v hv; simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      refine (eq_of_subset_of_card_le hsub ?_).symm
      rw [h3 t₁ ht₁, card_insert_of_notMem (by simp [hx₁y, hx₁z]), card_pair (Ne.symm hz₁y)]
    rw [hteq] at hx₂t
    simp only [mem_insert, mem_singleton] at hx₂t
    rcases hx₂t with h | h | h
    · exact h.symm
    · exact absurd (h ▸ hy) (hU_notW _ hx₂U)
    · exact absurd (h ▸ hz₁W) (hU_notW _ hx₂U)

end NashWilliams18.BKLOIface
