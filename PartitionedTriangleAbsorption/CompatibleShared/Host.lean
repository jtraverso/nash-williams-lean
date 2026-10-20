/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.Geometry
public import PartitionedTriangleAbsorption.CompatibleShared.GreedyTransport

/-! # One shared physical map for the Stage43 compatible F0 producer

The abstract compatible library (indices, concrete pieces `compatB p pV X hX`, remainder `R`)
is fixed first, from `p`, `pV` and the reserve `X` only; its charge correction is rebuilt
after choosing the compatible labels (`compatible_producer_exposed`). Then, for every host
graph `G` with `AntiEdgeful pV F0 G α`, `0 < α`, `3 ≤ |V|`, forbidden edges `F` of degree
`≤ d`, reserve degree `≤ Δ`, quota `0 < q` with all library loads `≤ Lmax ≤ q`, and the strict
budget `2·214·Lmax + 2·S̄/q + 2(d + Δ + 2q) < α |V|` with
`S̄ = 214 · 57635 · (|X| + 2M²)`, `M = 2^p`, a single map `f` realizes the whole library.
The actual-query geometry is *derived* (`compatible_geometry`), not assumed.
Every physical divisible leftover `L ⊆ X` is then absorbed by transported pieces of this one
map (`RefinesReserve` on the host).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner
open SharedGreedyPort TypedEmbeddingSelection F0FlexibleCompressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The root map: original vertices go to themselves; other identities are unconstrained
(they are overwritten by the greedy embedding). -/
noncomputable def compatRootMap [Nonempty V] (p : ℕ) : RefW V p → V
  | Sum.inl (Sum.inl (Sum.inl v)) => v
  | _ => Classical.arbitrary V

omit [Fintype V] [DecidableEq V] in
theorem compatRootMap_refEmb [Nonempty V] (p : ℕ) (v : V) :
    compatRootMap p (refEmb p v) = v := rfl

/-- **Shared physical realization of the Stage43 compatible F0 producer from
anti-edgefulness.**

First the compatible library is fixed from `p`, `pV`, `X` alone, with its bounds (pieces of
at most `214` edges; loads `99·deg_X` at originals, `66` at request middles, `88` at token
vertices, `330((n/M)+1)Δ + 1452M` at hubs; at most `57635(|X| + 2M²)` indices). Then for
every host satisfying the hypotheses there is ONE map `f`, fixed before any leftover, such
that: originals are fixed; parts are preserved on the support; `f` is injective on the
support of every piece and edge-injective on the whole library; every library edge with a
non-root end becomes a host edge avoiding `F` and `X`, and every root–root library edge is an
edge of `X`; transported pieces are loopless even F0-divisible graphs with at most `214`
edges inside `mapE f R ∪ X`; physical multiplicity loads are at most `2q`; and the host
refines every F0-divisible leftover of `X` with the transported pieces. -/
theorem compatible_shared_host (p : ℕ) (pV : V → Fin 2) (X : Finset (Sym2 V))
    (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V p)) (R : Finset (Sym2 (RefW V p))),
      Disjoint R (mapE (refEmb p) X) ∧
      RefinerAssembly.RefinesReserve (p := compatiblePart p pV) (F := F0) indices
        (compatB p pV X hX) (mapE (refEmb p) X) R ∧
      (∀ j ∈ indices, IsIntDiv (compatiblePart p pV) F0 (compatB p pV X hX j) ∧
        (∀ e ∈ compatB p pV X hX j, ¬ e.IsDiag) ∧
        compatB p pV X hX j ⊆ R ∪ mapE (refEmb p) X ∧ (compatB p pV X hX j).card ≤ 214) ∧
      (∀ v, libLoad indices (compatB p pV X hX) (refEmb p v) ≤ 99 * incidentLoad X v) ∧
      (∀ r, libLoad indices (compatB p pV X hX) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, libLoad indices (compatB p pV X hX) (Sum.inr (t, a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (p + 1)),
        libLoad indices (compatB p pV X hX) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p) ∧
      indices.card ≤ 57635 * (X.card + 2 * (2 ^ p) ^ 2) ∧
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V)) (q Lmax d Δ : ℕ)
        (alpha : ℝ), 0 < alpha → 3 ≤ Fintype.card V → AntiEdgeful pV F0 G alpha →
        0 < q → Lmax ≤ q →
        99 * Δ ≤ Lmax → 66 ≤ Lmax → 88 ≤ Lmax →
        330 * ((Fintype.card V / 2 ^ p + 1) * Δ) + 1452 * 2 ^ p ≤ Lmax →
        (∀ y, incidentLoad F y ≤ d) → (∀ y, incidentLoad X y ≤ Δ) →
        2 * (214 : ℝ) * Lmax + 2 * ((214 * (57635 * (X.card + 2 * (2 ^ p) ^ 2)) : ℕ) : ℝ) / q +
          2 * ((d : ℝ) + Δ + 2 * q) < alpha * Fintype.card V →
        ∃ f : RefW V p → V,
          (∀ v, f (refEmb p v) = v) ∧
          (∀ w ∈ vsupp (libU indices (compatB p pV X hX)), pV (f w) = compatiblePart p pV w) ∧
          (∀ j ∈ indices, Set.InjOn f ↑(vsupp (compatB p pV X hX j))) ∧
          Set.InjOn (Sym2.map f) ↑(libU indices (compatB p pV X hX)) ∧
          (∀ e ∈ libU indices (compatB p pV X hX), (∃ x ∈ e, x ∉ sharedRoots p) →
            Sym2.map f e ∈ G.edgeSet ∧ Sym2.map f e ∉ F ∧ Sym2.map f e ∉ X) ∧
          (∀ e ∈ libU indices (compatB p pV X hX), (∀ x ∈ e, x ∈ sharedRoots p) →
            Sym2.map f e ∈ X) ∧
          (∀ j ∈ indices, IsIntDiv pV F0 (mapE f (compatB p pV X hX j)) ∧
            (∀ e ∈ mapE f (compatB p pV X hX j), ¬ e.IsDiag) ∧
            (∀ y, Even (incidentLoad (mapE f (compatB p pV X hX j)) y)) ∧
            (mapE f (compatB p pV X hX j)).card ≤ 214 ∧
            mapE f (compatB p pV X hX j) ⊆ mapE f R ∪ X) ∧
          (∀ e ∈ mapE f R, e ∈ G.edgeSet ∧ e ∉ F ∧ e ∉ X) ∧
          (∀ y, ∑ j ∈ indices, incidentLoad (mapE f (compatB p pV X hX j)) y ≤ 2 * q) ∧
          RefinerAssembly.RefinesReserve (p := pV) (F := F0) indices
            (fun j => mapE f (compatB p pV X hX j)) X (mapE f R) := by
  obtain ⟨indices, R, hdisj, href, hpieces, hold, hreq, htok, hhub, hcard, hlib⟩ :=
    compatible_producer_exposed p pV X hX
  refine ⟨indices, R, hdisj, href, fun j hj => ⟨(hpieces j hj).1, (hpieces j hj).2.1,
    (hpieces j hj).2.2.2.1, (hpieces j hj).2.2.2.2⟩, hold, hreq, htok, hhub, hcard, ?_⟩
  intro G _ F q Lmax d Δ alpha ha hn hanti hq hLq h99 h66 h88 hhubL hF hXd hbudget
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  -- loads of every identity
  have hload : ∀ w, libLoad indices (compatB p pV X hX) w ≤ Lmax := by
    intro w
    rcases w with ((v | i) | r) | ⟨t, k⟩
    · have h1 : libLoad indices (compatB p pV X hX) (refEmb p v) ≤ 99 * incidentLoad X v :=
        hold v
      have h2 := hXd v
      change libLoad indices (compatB p pV X hX) (refEmb p v) ≤ Lmax
      have h3 : 99 * incidentLoad X v ≤ 99 * Δ := Nat.mul_le_mul_left _ h2
      omega
    · exact (hhub Δ hXd i).trans hhubL
    · exact (hreq r).trans h66
    · exact (htok t k).trans h88
  have hsize : libSize indices (compatB p pV X hX) ≤
      214 * (57635 * (X.card + 2 * (2 ^ p) ^ 2)) := by
    unfold libSize
    calc ∑ j ∈ indices, (compatB p pV X hX j).card ≤ ∑ _j ∈ indices, 214 :=
          sum_le_sum fun j hj => (hpieces j hj).2.2.2.2
      _ = 214 * indices.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hcard
  have hbudget' : 2 * ((214 : ℕ) : ℝ) * Lmax +
      2 * (libSize indices (compatB p pV X hX) : ℝ) / q +
      ((2 : ℕ) : ℝ) * ((d : ℝ) + Δ + 2 * q) < alpha * Fintype.card V := by
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hs : (libSize indices (compatB p pV X hX) : ℝ) ≤
        ((214 * (57635 * (X.card + 2 * (2 ^ p) ^ 2)) : ℕ) : ℝ) := by exact_mod_cast hsize
    have hdiv : 2 * (libSize indices (compatB p pV X hX) : ℝ) / q ≤
        2 * ((214 * (57635 * (X.card + 2 * (2 ^ p) ^ 2)) : ℕ) : ℝ) / q :=
      div_le_div_of_nonneg_right (by linarith) hq'.le
    push_cast at hbudget hdiv ⊢
    linarith
  have hr_inj : Set.InjOn (compatRootMap (V := V) p) ↑(sharedRoots (V := V) p) := by
    intro x hx y hy hxy
    obtain ⟨u, rfl⟩ := mem_sharedRoots.mp (mem_coe.mp hx)
    obtain ⟨w, rfl⟩ := mem_sharedRoots.mp (mem_coe.mp hy)
    rw [compatRootMap_refEmb, compatRootMap_refEmb] at hxy
    rw [hxy]
  have hr_part : ∀ v ∈ sharedRoots p, pV (compatRootMap p v) = compatiblePart p pV v := by
    intro x hx
    obtain ⟨u, rfl⟩ := mem_sharedRoots.mp hx
    rfl
  have hRR : ∀ e ∈ libU indices (compatB p pV X hX), (∀ x ∈ e, x ∈ sharedRoots p) →
      Sym2.map (compatRootMap p) e ∈ X := by
    intro e he hall
    obtain ⟨e₀, he₀, rfl⟩ := roots_edge hlib he hall
    have : Sym2.map (compatRootMap p) (Sym2.map (refEmb p) e₀) = e₀ := by
      induction e₀ using Sym2.ind with
      | _ a b => rfl
    rw [this]; exact he₀
  have hrank : ∀ u v, u ∉ sharedRoots p → v ∉ sharedRoots p → u ≠ v →
      sharedRank p u = sharedRank p v → s(u, v) ∉ libU indices (compatB p pV X hX) :=
    fun u v hu _ _ heq he => rank_ne hlib hu he heq
  have hD : ∀ v ∈ vsupp (libU indices (compatB p pV X hX)), v ∉ sharedRoots p →
      (earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v).card ≤ 2 :=
    fun v _ hv => earlier_card_le_two hlib hv
  have hpair : ∀ v ∈ vsupp (libU indices (compatB p pV X hX)), v ∉ sharedRoots p →
      ∀ u₁ ∈ earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v,
      ∀ u₂ ∈ earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v, u₁ ≠ u₂ →
        Coappear indices (compatB p pV X hX) u₁ u₂ :=
    fun v hvU hv u₁ h₁ u₂ h₂ _ => earlier_coappear hlib hvU hv h₁ h₂
  have hgeo := compatible_geometry pV hlib G F q (compatRootMap p) alpha ha hn hanti
  obtain ⟨f, hroot, hpart, hinj, hinjU, hnew, hRRf, -, hphys⟩ :=
    shared_greedy_embedding (idx := indices) (B := compatB p pV X hX) (R := sharedRoots p)
      (r := compatRootMap p) (pA := compatiblePart p pV) (pV := pV) (G := G) (F := F) (X := X)
      (q := q) (b := 214) (Lmax := Lmax) (D := 2) (d := d) (Δ := Δ)
      (a := alpha * Fintype.card V) (rk := sharedRank p)
      (fun j hj => (hpieces j hj).2.1) (fun j hj => (hpieces j hj).2.2.2.2)
      hr_inj hr_part hRR hrank hD hpair hq (fun w => (hload w).trans hLq) hload hF hXd
      hgeo hbudget'
  have hfemb : ∀ v, f (refEmb p v) = v := fun v =>
    (hroot _ (mem_sharedRoots.mpr ⟨v, rfl⟩)).trans (compatRootMap_refEmb p v)
  have hBU : ∀ j ∈ indices, compatB p pV X hX j ⊆ libU indices (compatB p pV X hX) :=
    fun j hj e he => mem_libU.mpr ⟨j, hj, he⟩
  have hpartU : ∀ w ∈ vsupp (libU indices (compatB p pV X hX)),
      pV (f w) = compatiblePart p pV w :=
    fun w hw => hpart w (mem_union_right _ hw)
  have hRU : R ⊆ libU indices (compatB p pV X hX) := by
    obtain ⟨s, hs, -, hsU⟩ := href ∅ (empty_subset _) RefinerAssembly.empty_isIntDiv
    intro e he
    have he' : e ∈ s.biUnion (compatB p pV X hX) := by rw [hsU]; exact mem_union_left _ he
    obtain ⟨j, hj, hej⟩ := mem_biUnion.mp he'
    exact mem_libU.mpr ⟨j, hs hj, hej⟩
  refine ⟨f, hfemb, hpartU, hinj, hinjU, hnew, hRRf, ?_, ?_, hphys, ?_⟩
  · intro j hj
    obtain ⟨hdiv, hloop, -, hsub, hc⟩ := hpieces j hj
    have hpartj : ∀ x ∈ vsupp (compatB p pV X hX j), pV (f x) = compatiblePart p pV x :=
      fun x hx => by
        obtain ⟨e, he, hxe⟩ := mem_vsupp.mp hx
        exact hpartU x (mem_vsupp.mpr ⟨e, hBU j hj he, hxe⟩)
    refine ⟨isIntDiv_map_on_support (compatiblePart p pV) pV f (compatB p pV X hX j)
        (hinj j hj) hpartj hloop hdiv,
      loopless_map_on_support f (compatB p pV X hX j) (hinj j hj) hloop,
      even_map_on_support f (compatB p pV X hX j) (hinj j hj)
        (TypedDivisibilityCollapse.even_of_isIntDiv
        TypedTransportExamples.F0_card hloop hdiv), ?_, ?_⟩
    · rw [SharedLibraryTransport.card_map_on_support f (libU indices (compatB p pV X hX))
        (compatB p pV X hX j) hinjU (hBU j hj)]
      exact hc
    · intro e he
      obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
      rcases mem_union.mp (hsub he') with h | h
      · exact mem_union_left _ (mem_mapE.mpr ⟨e', h, rfl⟩)
      · refine mem_union_right _ ?_
        rw [← mapE_id_of_leftInverse hfemb X]
        exact mem_mapE.mpr ⟨e', h, rfl⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
    refine hnew e' (hRU he') ?_
    by_contra hall
    push Not at hall
    obtain ⟨e₀, he₀, rfl⟩ := roots_edge hlib (hRU he') hall
    exact disjoint_left.mp hdisj he' (mem_mapE.mpr ⟨e₀, he₀, rfl⟩)
  · exact refinesReserve_host (compatiblePart p pV) pV f (refEmb p) hfemb (fun v => rfl)
      indices (compatB p pV X hX) X R hX hinjU href

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared
