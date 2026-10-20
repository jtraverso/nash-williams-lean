/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.GreedyBasic

/-! # One step of the shared-map greedy embedding

`Legal … P g` records the invariants of a partial placement `g` defined on the placed
identities `P` (roots included). One step inserts an identity `v` whose placed library
neighbours form a set `N` of at most `D` identities, pairwise coappearing in a piece.
The single map is updated at `v` only; the pieces are never embedded anew.

The candidate count is the actual common-neighbour count of the images of `N` in the part
of `v`, for this particular legal placement. It is an input, not a consequence.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SharedGreedyPort

open Finset AntiEdgeSelection TypedEmbeddingSelection

variable {A V I : Type*} [DecidableEq A] [Fintype V] [DecidableEq V] {t : ℕ}

/-- A **legal partial placement** `g` of the placed identities `P`:
roots are placed by `r`; parts are preserved; `g` is injective on the placed vertex support
of every piece; every placed library edge that is not root–root is a host edge avoiding the
forbidden edges `F` and the whole physical reserve `X`; the edge map is injective on placed
library edges; and every host vertex carries placed multiplicity load at most `2q`. -/
structure Legal (idx : Finset I) (B : I → Finset (Sym2 A)) (R : Finset A) (r : A → V)
    (pA : A → Fin t) (pV : V → Fin t) (G : SimpleGraph V) (F X : Finset (Sym2 V)) (q : ℕ)
    (P : Finset A) (g : A → V) : Prop where
  roots_sub : R ⊆ P
  roots_eq : ∀ v ∈ R, g v = r v
  part : ∀ v ∈ P, pV (g v) = pA v
  inj_piece : ∀ j ∈ idx, Set.InjOn g ↑(vsupp (B j) ∩ P)
  new_edge : ∀ e ∈ placedE idx B P, (∃ x ∈ e, x ∉ R) →
    Sym2.map g e ∈ G.edgeSet ∧ Sym2.map g e ∉ F ∧ Sym2.map g e ∉ X
  inj_edge : Set.InjOn (Sym2.map g) ↑(placedE idx B P)
  load : ∀ y, placedLoad idx B P g y ≤ 2 * q

omit [Fintype V] [DecidableEq V] in
theorem mem_placedE {idx : Finset I} {B : I → Finset (Sym2 A)} {P : Finset A} {e : Sym2 A} :
    e ∈ placedE idx B P ↔ e ∈ libU idx B ∧ ∀ x ∈ e, x ∈ P := by
  simp only [placedE, mem_filter, subset_iff, Sym2.mem_toFinset]

omit [Fintype V] [DecidableEq V] in
/-- Placed edges after inserting `v`: old ones, or `s(u,v)` with `u ∈ N`. -/
theorem placedE_insert {idx : Finset I} {B : I → Finset (Sym2 A)} {P N : Finset A} {v : A}
    (hloop : ∀ j ∈ idx, ∀ e ∈ B j, ¬ e.IsDiag)
    (hN : ∀ u ∈ P, s(u, v) ∈ libU idx B → u ∈ N) {e : Sym2 A}
    (he : e ∈ placedE idx B (insert v P)) :
    (v ∉ e → e ∈ placedE idx B P) ∧ (v ∈ e → ∃ u ∈ N, u ∈ P ∧ e = s(u, v)) := by
  obtain ⟨heU, hins⟩ := mem_placedE.mp he
  constructor
  · intro hve
    refine mem_placedE.mpr ⟨heU, fun x hx => ?_⟩
    rcases mem_insert.mp (hins x hx) with rfl | h
    · exact absurd hx hve
    · exact h
  · intro hve
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hve
    have hne : u ≠ v := by
      intro h
      subst h
      obtain ⟨j, hj, hej⟩ := mem_libU.mp heU
      exact hloop j hj _ hej (Sym2.mk_isDiag_iff.mpr rfl)
    have huP : u ∈ P := by
      rcases mem_insert.mp (hins u (Sym2.mem_mk_right v u)) with h | h
      · exact absurd h hne
      · exact h
    have hsw : s(u, v) = s(v, u) := Sym2.eq_swap
    exact ⟨u, hN u huP (hsw ▸ heU), huP, hsw.symm⟩

/-- **One greedy step.** -/
theorem legal_step {idx : Finset I} {B : I → Finset (Sym2 A)} {R : Finset A} {r : A → V}
    {pA : A → Fin t} {pV : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {F X : Finset (Sym2 V)} {q b Lmax D d Δ : ℕ} {a : ℝ}
    {P : Finset A} {g : A → V} {N : Finset A} {v : A}
    (hL : Legal idx B R r pA pV G F X q P g)
    (hloop : ∀ j ∈ idx, ∀ e ∈ B j, ¬ e.IsDiag)
    (hcard : ∀ j ∈ idx, (B j).card ≤ b)
    (hq : 0 < q) (hLq : libLoad idx B v ≤ q) (hLmax : libLoad idx B v ≤ Lmax)
    (hF : ∀ y, incidentLoad F y ≤ d) (hX : ∀ y, incidentLoad X y ≤ Δ)
    (hvP : v ∉ P) (hvR : v ∉ R)
    (hN : ∀ u ∈ P, s(u, v) ∈ libU idx B → u ∈ N)
    (hND : N.card ≤ D) (hpair : ∀ u₁ ∈ N, ∀ u₂ ∈ N, u₁ ≠ u₂ → Coappear idx B u₁ u₂)
    (hsupply : a ≤ (typedNeighbours pV G (N.image g) (pA v)).card)
    (hbudget : 2 * (b : ℝ) * Lmax + 2 * (libSize idx B : ℝ) / q +
      D * ((d : ℝ) + Δ + 2 * q) < a) :
    ∃ w, Legal idx B R r pA pV G F X q (insert v P) (Function.update g v w) := by
  classical
  -- the excluded images: identities already placed that share a piece with `v`
  have hZ : (((P.filter fun u => Coappear idx B u v).image g).card : ℝ) ≤ 2 * b * Lmax := by
    have h1 := card_coappear_le idx B b hcard P v
    have h2 : 2 * b * libLoad idx B v ≤ 2 * b * Lmax := Nat.mul_le_mul_left _ hLmax
    exact_mod_cast card_image_le.trans (h1.trans h2)
  -- handshake with multiplicity
  have hload : ((∑ y, placedLoad idx B P g y : ℕ) : ℝ) / q ≤ 2 * (libSize idx B : ℝ) / q := by
    have h : ∑ y, placedLoad idx B P g y ≤ 2 * libSize idx B := by
      rw [sum_placedLoad]; exact sum_libLoad_le idx B P
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    apply div_le_div_of_nonneg_right _ hq'.le
    exact_mod_cast h
  -- used new-edge degree is at most the load
  have hM : ∀ y, incidentLoad ((placedE idx B P).image (Sym2.map g)) y ≤ 2 * q := by
    intro y
    refine (incidentLoad_image_le g (placedE idx B P) P
      (fun e he x hx => (mem_placedE.mp he).2 x hx) y).trans ?_
    refine le_trans ?_ (hL.load y)
    exact sum_le_sum fun u _ => (incidentLoad_mono (fun e he => (mem_placedE.mp he).1) u).trans
      (incidentLoad_libU_le idx B u)
  have hBl : ∀ y, incidentLoad (F ∪ X ∪ (placedE idx B P).image (Sym2.map g)) y ≤
      d + Δ + 2 * q := by
    intro y
    have h1 := incidentLoad_union_le (F ∪ X) ((placedE idx B P).image (Sym2.map g)) y
    have h2 := incidentLoad_union_le F X y
    have h3 := hF y
    have h4 := hX y
    have h5 := hM y
    omega
  have hsumBl : ∑ u ∈ N.image g,
      (incidentLoad (F ∪ X ∪ (placedE idx B P).image (Sym2.map g)) u : ℝ) ≤
      D * ((d : ℝ) + Δ + 2 * q) := by
    have h1 : ∑ u ∈ N.image g, incidentLoad (F ∪ X ∪ (placedE idx B P).image (Sym2.map g)) u ≤
        (N.image g).card * (d + Δ + 2 * q) := by
      calc _ ≤ ∑ _u ∈ N.image g, (d + Δ + 2 * q) := sum_le_sum fun u _ => hBl u
        _ = _ := by rw [sum_const, smul_eq_mul]
    have h2 : (N.image g).card ≤ D := card_image_le.trans hND
    have h3 := h1.trans (Nat.mul_le_mul_right (d + Δ + 2 * q) h2)
    exact_mod_cast h3
  have hb : (((P.filter fun u => Coappear idx B u v).image g).card : ℝ) +
      ((∑ y, placedLoad idx B P g y : ℕ) : ℝ) / q +
      ∑ u ∈ N.image g,
        (incidentLoad (F ∪ X ∪ (placedE idx B P).image (Sym2.map g)) u : ℝ) < a := by
    linarith
  obtain ⟨w, hwp, hwadj, hwZ, -, hwl, hwB⟩ :=
    SharedLibrarySelection.exists_unsaturated_query pV G (N.image g)
      ((P.filter fun u => Coappear idx B u v).image g)
      (F ∪ X ∪ (placedE idx B P).image (Sym2.map g)) (pA v) a (placedLoad idx B P g) q
      (libLoad idx B v) hq hLq hsupply hb
  refine ⟨w, ?_⟩
  have hg'P : ∀ u ∈ P, Function.update g v w u = g u := fun u hu =>
    Function.update_of_ne (by rintro rfl; exact hvP hu) _ _
  have hg'v : Function.update g v w v = w := Function.update_self _ _ _
  have hwS : ∀ u ∈ N, G.Adj (g u) w := fun u hu => hwadj (g u) (mem_image_of_mem g hu)
  have hwBl : ∀ u ∈ N, s(g u, w) ∉ F ∪ X ∪ (placedE idx B P).image (Sym2.map g) :=
    fun u hu => hwB (g u) (mem_image_of_mem g hu)
  have hwZ' : ∀ u ∈ P, Coappear idx B u v → g u ≠ w := fun u hu hc h =>
    hwZ (h ▸ mem_image_of_mem g (mem_filter.mpr ⟨hu, hc⟩))
  have hmapN : ∀ u ∈ P, Sym2.map (Function.update g v w) s(u, v) = s(g u, w) := by
    intro u hu
    rw [map_pair, hg'P u hu, hg'v]
  have hmapO : ∀ e ∈ placedE idx B P,
      Sym2.map (Function.update g v w) e = Sym2.map g e := fun e he =>
    map_congr_of_eqOn fun x hx => hg'P x ((mem_placedE.mp he).2 x hx)
  have hfilt : ∀ y, (P.filter fun u => Function.update g v w u = y) =
      P.filter fun u => g u = y := fun y => filter_congr fun u hu => by rw [hg'P u hu]
  refine ⟨hL.roots_sub.trans (subset_insert _ _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [hg'P u (hL.roots_sub hu)]
    exact hL.roots_eq u hu
  · intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · rw [hg'v]; exact hwp
    · rw [hg'P u hu]; exact hL.part u hu
  · intro j hj x hx y hy hxy
    obtain ⟨hxj, hx⟩ := mem_inter.mp (mem_coe.mp hx)
    obtain ⟨hyj, hy⟩ := mem_inter.mp (mem_coe.mp hy)
    rcases mem_insert.mp hx with rfl | hxP <;> rcases mem_insert.mp hy with rfl | hyP
    · rfl
    · rw [hg'v, hg'P y hyP] at hxy
      exact absurd hxy.symm (hwZ' y hyP ⟨j, hj, hyj, hxj⟩)
    · rw [hg'v, hg'P x hxP] at hxy
      exact absurd hxy (hwZ' x hxP ⟨j, hj, hxj, hyj⟩)
    · rw [hg'P x hxP, hg'P y hyP] at hxy
      exact hL.inj_piece j hj (mem_coe.mpr (mem_inter.mpr ⟨hxj, hxP⟩))
        (mem_coe.mpr (mem_inter.mpr ⟨hyj, hyP⟩)) hxy
  · intro e he hnr
    obtain ⟨hold, hnew⟩ := placedE_insert hloop hN he
    by_cases hve : v ∈ e
    · obtain ⟨u, hu, huP, rfl⟩ := hnew hve
      rw [hmapN u huP]
      refine ⟨(SimpleGraph.mem_edgeSet _).mpr (hwS u hu), fun h => ?_, fun h => ?_⟩
      · exact hwBl u hu (mem_union_left _ (mem_union_left _ h))
      · exact hwBl u hu (mem_union_left _ (mem_union_right _ h))
    · have he' := hold hve
      rw [hmapO e he']
      exact hL.new_edge e he' hnr
  · intro e₁ he₁ e₂ he₂ h
    obtain ⟨hold₁, hnew₁⟩ := placedE_insert hloop hN (mem_coe.mp he₁)
    obtain ⟨hold₂, hnew₂⟩ := placedE_insert hloop hN (mem_coe.mp he₂)
    by_cases h₁ : v ∈ e₁ <;> by_cases h₂ : v ∈ e₂
    · obtain ⟨u₁, hu₁, hu₁P, rfl⟩ := hnew₁ h₁
      obtain ⟨u₂, hu₂, hu₂P, rfl⟩ := hnew₂ h₂
      rw [hmapN u₁ hu₁P, hmapN u₂ hu₂P] at h
      have hg : g u₁ = g u₂ := Sym2.congr_left.mp h
      by_cases hne : u₁ = u₂
      · rw [hne]
      · obtain ⟨j, hj, h₁j, h₂j⟩ := hpair u₁ hu₁ u₂ hu₂ hne
        exact absurd (hL.inj_piece j hj (mem_coe.mpr (mem_inter.mpr ⟨h₁j, hu₁P⟩))
          (mem_coe.mpr (mem_inter.mpr ⟨h₂j, hu₂P⟩)) hg) hne
    · obtain ⟨u₁, hu₁, hu₁P, rfl⟩ := hnew₁ h₁
      have he₂' := hold₂ h₂
      rw [hmapN u₁ hu₁P, hmapO e₂ he₂'] at h
      exact absurd (mem_union_right _ (h ▸ mem_image_of_mem _ he₂')) (hwBl u₁ hu₁)
    · obtain ⟨u₂, hu₂, hu₂P, rfl⟩ := hnew₂ h₂
      have he₁' := hold₁ h₁
      rw [hmapN u₂ hu₂P, hmapO e₁ he₁'] at h
      exact absurd (mem_union_right _ (h.symm ▸ mem_image_of_mem _ he₁')) (hwBl u₂ hu₂)
    · have he₁' := hold₁ h₁
      have he₂' := hold₂ h₂
      rw [hmapO e₁ he₁', hmapO e₂ he₂'] at h
      exact hL.inj_edge (mem_coe.mpr he₁') (mem_coe.mpr he₂') h
  · intro y
    unfold placedLoad
    rw [filter_insert, hg'v]
    split_ifs with hy
    · rw [sum_insert (fun h => hvP (mem_filter.mp h).1), hfilt]
      subst hy
      have hw' : placedLoad idx B P g w + libLoad idx B v ≤ 2 * q := hwl
      unfold placedLoad at hw'
      omega
    · rw [hfilt]
      exact hL.load y

end PartitionedTriangleAbsorption.SharedGreedyPort
