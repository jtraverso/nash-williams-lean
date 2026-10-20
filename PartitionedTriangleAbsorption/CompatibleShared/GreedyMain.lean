/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.GreedyStep

/-! # The finite shared-map greedy embedding theorem

Non-root support identities are inserted in an order compatible with a rank `rk`
(identities of equal rank are never library-adjacent, so ties are irrelevant).
Every insertion uses `legal_step`; one single map is updated throughout.

The geometric input `hgeo` is an actual-query count: for every *legal* partial placement
`g` of a set `P` containing the earlier neighbours of the next identity `v`, the host
vertices of part `pA v` adjacent to all images of those earlier neighbours number at least
`a`. It is not an existence statement for the placement.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SharedGreedyPort

open Finset AntiEdgeSelection TypedEmbeddingSelection

variable {A V I : Type*} [DecidableEq A] [Fintype V] [DecidableEq V] {t : ℕ}

/-- The non-root active support. -/
def auxSupp (idx : Finset I) (B : I → Finset (Sym2 A)) (R : Finset A) : Finset A :=
  vsupp (libU idx B) \ R

omit [DecidableEq A] [Fintype V] [DecidableEq V] in
theorem map_injOn_of_injOn {r : A → V} {R : Set A} (hr : Set.InjOn r R) {e₁ e₂ : Sym2 A}
    (h₁ : ∀ x ∈ e₁, x ∈ R) (h₂ : ∀ x ∈ e₂, x ∈ R) (h : Sym2.map r e₁ = Sym2.map r e₂) :
    e₁ = e₂ := by
  induction e₁ using Sym2.ind with
  | _ a b =>
  induction e₂ using Sym2.ind with
  | _ c d =>
    have ha := h₁ a (Sym2.mem_mk_left a b)
    have hb := h₁ b (Sym2.mem_mk_right a b)
    have hc := h₂ c (Sym2.mem_mk_left c d)
    have hd := h₂ d (Sym2.mem_mk_right c d)
    simp only [map_pair, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hr ha hc h1, hr hb hd h2]
    · rw [hr ha hd h1, hr hb hc h2, Sym2.eq_swap]

omit [Fintype V] in
/-- The roots alone form a legal placement. -/
theorem legal_roots {idx : Finset I} {B : I → Finset (Sym2 A)} {R : Finset A} {r : A → V}
    {pA : A → Fin t} {pV : V → Fin t} {G : SimpleGraph V} {F X : Finset (Sym2 V)} {q : ℕ}
    (hr_inj : Set.InjOn r ↑R) (hr_part : ∀ v ∈ R, pV (r v) = pA v)
    (hLq : ∀ v, libLoad idx B v ≤ q) :
    Legal idx B R r pA pV G F X q R r := by
  refine ⟨subset_refl _, fun _ _ => rfl, hr_part, ?_, ?_, ?_, ?_⟩
  · intro j _ x hx y hy hxy
    exact hr_inj (mem_coe.mpr (mem_inter.mp (mem_coe.mp hx)).2)
      (mem_coe.mpr (mem_inter.mp (mem_coe.mp hy)).2) hxy
  · intro e he hnr
    obtain ⟨x, hx, hxR⟩ := hnr
    exact absurd ((mem_placedE.mp he).2 x hx) hxR
  · intro e₁ he₁ e₂ he₂ h
    exact map_injOn_of_injOn hr_inj (fun x hx => (mem_placedE.mp (mem_coe.mp he₁)).2 x hx)
      (fun x hx => (mem_placedE.mp (mem_coe.mp he₂)).2 x hx) h
  · intro y
    unfold placedLoad
    have hc : (R.filter fun v => r v = y).card ≤ 1 := by
      refine card_le_one.mpr fun u hu w hw => ?_
      obtain ⟨hu, hu'⟩ := mem_filter.mp hu
      obtain ⟨hw, hw'⟩ := mem_filter.mp hw
      exact hr_inj (mem_coe.mpr hu) (mem_coe.mpr hw) (hu'.trans hw'.symm)
    calc ∑ v ∈ R.filter (fun v => r v = y), libLoad idx B v
        ≤ (R.filter fun v => r v = y).card • q := sum_le_card_nsmul _ _ _ fun v _ => hLq v
      _ ≤ 1 • q := Nat.mul_le_mul_right _ hc
      _ ≤ 2 * q := by rw [one_smul]; omega

/-- Rank-ordered induction: every down-closed set of non-root identities can be placed. -/
theorem exists_legal_downset {idx : Finset I} {B : I → Finset (Sym2 A)} {R : Finset A}
    {r : A → V} {pA : A → Fin t} {pV : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {F X : Finset (Sym2 V)} {q b Lmax D d Δ : ℕ} {a : ℝ} {rk : A → ℕ}
    (hloop : ∀ j ∈ idx, ∀ e ∈ B j, ¬ e.IsDiag)
    (hcard : ∀ j ∈ idx, (B j).card ≤ b)
    (hr_inj : Set.InjOn r ↑R) (hr_part : ∀ v ∈ R, pV (r v) = pA v)
    (hrank : ∀ u v, u ∉ R → v ∉ R → u ≠ v → rk u = rk v → s(u, v) ∉ libU idx B)
    (hD : ∀ v ∈ vsupp (libU idx B), v ∉ R → (earlier idx B R rk v).card ≤ D)
    (hpair : ∀ v ∈ vsupp (libU idx B), v ∉ R → ∀ u₁ ∈ earlier idx B R rk v,
      ∀ u₂ ∈ earlier idx B R rk v, u₁ ≠ u₂ → Coappear idx B u₁ u₂)
    (hq : 0 < q) (hLq : ∀ v, libLoad idx B v ≤ q) (hLmax : ∀ v, libLoad idx B v ≤ Lmax)
    (hF : ∀ y, incidentLoad F y ≤ d) (hX : ∀ y, incidentLoad X y ≤ Δ)
    (hgeo : ∀ (P : Finset A) (g : A → V) (v : A), Legal idx B R r pA pV G F X q P g →
      v ∈ vsupp (libU idx B) → v ∉ P → earlier idx B R rk v ⊆ P →
      a ≤ (typedNeighbours pV G ((earlier idx B R rk v).image g) (pA v)).card)
    (hbudget : 2 * (b : ℝ) * Lmax + 2 * (libSize idx B : ℝ) / q +
      D * ((d : ℝ) + Δ + 2 * q) < a) :
    ∀ k ≤ (auxSupp idx B R).card, ∃ T ⊆ auxSupp idx B R, T.card = k ∧
      (∀ u ∈ T, ∀ w ∈ auxSupp idx B R \ T, rk u ≤ rk w) ∧
      ∃ g, Legal idx B R r pA pV G F X q (R ∪ T) g := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨∅, empty_subset _, card_empty, fun u hu => absurd hu (notMem_empty u), r, ?_⟩
    rw [union_empty]
    exact legal_roots hr_inj hr_part hLq
  | succ k ih =>
    intro hk
    obtain ⟨T, hT, hTc, hdown, g, hL⟩ := ih (Nat.le_of_succ_le hk)
    have hne : (auxSupp idx B R \ T).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hT]
      omega
    obtain ⟨v, hv, hvmin⟩ := exists_min_image _ rk hne
    obtain ⟨hvA, hvT⟩ := mem_sdiff.mp hv
    obtain ⟨hvU, hvR⟩ := mem_sdiff.mp hvA
    have hvP : v ∉ R ∪ T := fun h => (mem_union.mp h).elim hvR hvT
    have hNP : earlier idx B R rk v ⊆ R ∪ T := by
      intro u hu
      obtain ⟨hun, hur⟩ := mem_filter.mp hu
      rcases hur with huR | hlt
      · exact mem_union_left _ huR
      · by_cases huR : u ∈ R
        · exact mem_union_left _ huR
        · by_cases huT : u ∈ T
          · exact mem_union_right _ huT
          · have huA : u ∈ auxSupp idx B R :=
              mem_sdiff.mpr ⟨(mem_filter.mp hun).1, huR⟩
            exact absurd (hvmin u (mem_sdiff.mpr ⟨huA, huT⟩)) (not_le.mpr hlt)
    have hN : ∀ u ∈ R ∪ T, s(u, v) ∈ libU idx B → u ∈ earlier idx B R rk v := by
      intro u hu hsu
      have huU : u ∈ vsupp (libU idx B) := mem_vsupp.mpr ⟨s(u, v), hsu, Sym2.mem_mk_left u v⟩
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨huU, hsu⟩, ?_⟩
      rcases mem_union.mp hu with huR | huT
      · exact Or.inl huR
      · right
        have hle := hdown u huT v hv
        have huR : u ∉ R := (mem_sdiff.mp (hT huT)).2
        have huv : u ≠ v := fun h => hvT (h ▸ huT)
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact absurd hsu (hrank u v huR hvR huv heq)
    obtain ⟨w, hL'⟩ := legal_step (N := earlier idx B R rk v) hL hloop hcard hq (hLq v)
      (hLmax v) hF hX hvP hvR hN (hD v hvU hvR) (hpair v hvU hvR)
      (hgeo (R ∪ T) g v hL hvU hvP hNP) hbudget
    refine ⟨insert v T, insert_subset hvA hT, by rw [card_insert_of_notMem hvT, hTc], ?_,
      Function.update g v w, by rw [union_insert]; exact hL'⟩
    intro u hu w' hw'
    obtain ⟨hw'A, hw'T⟩ := mem_sdiff.mp hw'
    have hw'T0 : w' ∉ T := fun h => hw'T (mem_insert_of_mem h)
    rcases mem_insert.mp hu with rfl | huT
    · exact hvmin w' (mem_sdiff.mpr ⟨hw'A, hw'T0⟩)
    · exact hdown u huT w' (mem_sdiff.mpr ⟨hw'A, hw'T0⟩)

/-- **Finite shared-map greedy embedding.**

A finite library `B j`, `j ∈ idx`, of loopless edge sets with at most `b` edges each,
multiplicity load `L(v) ≤ min(q, Lmax)` and total size `S`. Roots `R` are placed by a fixed
injective part-preserving map `r`; root–root library edges are mapped by `r` into the
physical reserve `X`. The rank `rk` orders the non-root support (equal ranks are never
adjacent); each non-root support identity has at most `D` earlier neighbours (roots count as
earlier), pairwise coappearing in a library piece. `F` has degree `≤ d`, `X` degree `≤ Δ`.
`hgeo` is the explicit common-neighbour count on legal partial placements, and
`2 b Lmax + 2 S / q + D (d + Δ + 2 q) < a`.

Then a single map `f` exists, agreeing with `r` on the roots, part-preserving on the roots and
the support, injective on the vertex support of every piece, with `Sym2.map f` injective on
the library union; every library edge that is not root–root becomes a host edge avoiding
`F` and `X`, root–root edges land in `X`, every transported piece is loopless, and the
physical multiplicity load at every host vertex is at most `2 q`. -/
theorem shared_greedy_embedding {idx : Finset I} {B : I → Finset (Sym2 A)} {R : Finset A}
    {r : A → V} {pA : A → Fin t} {pV : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {F X : Finset (Sym2 V)} {q b Lmax D d Δ : ℕ} {a : ℝ} {rk : A → ℕ}
    (hloop : ∀ j ∈ idx, ∀ e ∈ B j, ¬ e.IsDiag)
    (hcard : ∀ j ∈ idx, (B j).card ≤ b)
    (hr_inj : Set.InjOn r ↑R) (hr_part : ∀ v ∈ R, pV (r v) = pA v)
    (hRR : ∀ e ∈ libU idx B, (∀ x ∈ e, x ∈ R) → Sym2.map r e ∈ X)
    (hrank : ∀ u v, u ∉ R → v ∉ R → u ≠ v → rk u = rk v → s(u, v) ∉ libU idx B)
    (hD : ∀ v ∈ vsupp (libU idx B), v ∉ R → (earlier idx B R rk v).card ≤ D)
    (hpair : ∀ v ∈ vsupp (libU idx B), v ∉ R → ∀ u₁ ∈ earlier idx B R rk v,
      ∀ u₂ ∈ earlier idx B R rk v, u₁ ≠ u₂ → Coappear idx B u₁ u₂)
    (hq : 0 < q) (hLq : ∀ v, libLoad idx B v ≤ q) (hLmax : ∀ v, libLoad idx B v ≤ Lmax)
    (hF : ∀ y, incidentLoad F y ≤ d) (hX : ∀ y, incidentLoad X y ≤ Δ)
    (hgeo : ∀ (P : Finset A) (g : A → V) (v : A), Legal idx B R r pA pV G F X q P g →
      v ∈ vsupp (libU idx B) → v ∉ P → earlier idx B R rk v ⊆ P →
      a ≤ (typedNeighbours pV G ((earlier idx B R rk v).image g) (pA v)).card)
    (hbudget : 2 * (b : ℝ) * Lmax + 2 * (libSize idx B : ℝ) / q +
      D * ((d : ℝ) + Δ + 2 * q) < a) :
    ∃ f : A → V,
      (∀ v ∈ R, f v = r v) ∧
      (∀ v ∈ R ∪ vsupp (libU idx B), pV (f v) = pA v) ∧
      (∀ j ∈ idx, Set.InjOn f ↑(vsupp (B j))) ∧
      Set.InjOn (Sym2.map f) ↑(libU idx B) ∧
      (∀ e ∈ libU idx B, (∃ x ∈ e, x ∉ R) →
        Sym2.map f e ∈ G.edgeSet ∧ Sym2.map f e ∉ F ∧ Sym2.map f e ∉ X) ∧
      (∀ e ∈ libU idx B, (∀ x ∈ e, x ∈ R) → Sym2.map f e ∈ X) ∧
      (∀ j ∈ idx, ∀ e ∈ B j, ¬ (Sym2.map f e).IsDiag) ∧
      (∀ y, ∑ j ∈ idx, incidentLoad ((B j).image (Sym2.map f)) y ≤ 2 * q) := by
  obtain ⟨T, hT, hTc, -, f, hL⟩ := exists_legal_downset hloop hcard hr_inj hr_part hrank hD
    hpair hq hLq hLmax hF hX hgeo hbudget _ le_rfl
  have hTe : T = auxSupp idx B R := eq_of_subset_of_card_le hT (by rw [hTc])
  subst hTe
  have hsupp : vsupp (libU idx B) ⊆ R ∪ auxSupp idx B R := by
    intro v hv
    by_cases hvR : v ∈ R
    · exact mem_union_left _ hvR
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, hvR⟩)
  have hpieceU : ∀ j ∈ idx, B j ⊆ libU idx B := fun j hj e he => mem_libU.mpr ⟨j, hj, he⟩
  have hpiece : ∀ j ∈ idx, vsupp (B j) ⊆ R ∪ auxSupp idx B R := fun j hj v hv => by
    obtain ⟨e, he, hve⟩ := mem_vsupp.mp hv
    exact hsupp (mem_vsupp.mpr ⟨e, hpieceU j hj he, hve⟩)
  have hEP : placedE idx B (R ∪ auxSupp idx B R) = libU idx B := by
    refine filter_true_of_mem fun e he x hx =>
      hsupp (mem_vsupp.mpr ⟨e, he, Sym2.mem_toFinset.mp hx⟩)
  have hinj : ∀ j ∈ idx, Set.InjOn f ↑(vsupp (B j)) := by
    intro j hj x hx y hy hxy
    exact hL.inj_piece j hj (mem_coe.mpr (mem_inter.mpr ⟨mem_coe.mp hx, hpiece j hj hx⟩))
      (mem_coe.mpr (mem_inter.mpr ⟨mem_coe.mp hy, hpiece j hj hy⟩)) hxy
  refine ⟨f, hL.roots_eq, ?_, hinj, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases mem_union.mp hv with hvR | hvU
    · exact hL.part v (mem_union_left _ hvR)
    · exact hL.part v (hsupp hvU)
  · rw [← hEP]; exact hL.inj_edge
  · intro e he hnr
    exact hL.new_edge e (hEP ▸ he) hnr
  · intro e he hall
    rw [map_congr_of_eqOn fun x hx => hL.roots_eq x (hall x hx)]
    exact hRR e he hall
  · intro j hj e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := fun h => hloop j hj _ he (Sym2.mk_isDiag_iff.mpr h)
      have hx : x ∈ vsupp (B j) := mem_vsupp.mpr ⟨_, he, Sym2.mem_mk_left x y⟩
      have hy : y ∈ vsupp (B j) := mem_vsupp.mpr ⟨_, he, Sym2.mem_mk_right x y⟩
      rw [map_pair, Sym2.mk_isDiag_iff]
      exact fun h => hxy (hinj j hj (mem_coe.mpr hx) (mem_coe.mpr hy) h)
  · intro y
    calc ∑ j ∈ idx, incidentLoad ((B j).image (Sym2.map f)) y
        ≤ ∑ j ∈ idx, ∑ u ∈ (R ∪ auxSupp idx B R).filter (fun u => f u = y),
            incidentLoad (B j) u := sum_le_sum fun j hj =>
          incidentLoad_image_le f (B j) _
            (fun e he x hx => hpiece j hj (mem_vsupp.mpr ⟨e, he, hx⟩)) y
      _ = placedLoad idx B (R ∪ auxSupp idx B R) f y := by
          unfold placedLoad libLoad; exact sum_comm
      _ ≤ 2 * q := hL.load y

end PartitionedTriangleAbsorption.SharedGreedyPort
