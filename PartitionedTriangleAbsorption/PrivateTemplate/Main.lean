/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.TemplateOrder

/-!
# Private absorber templates exist for every even, three-divisible loopless piece

For a finite vertex type `V` and a loopless edge set `P` with all degrees even and
`3 ∣ |P|`, the roots are the vertices incident to `P` (`Root P`), the auxiliaries are
`AuxV |P|` (`34 |P| + 1` vertices when `P ≠ ∅`, none when `P = ∅`), and the root inclusion
is `Sum.inl`.  We construct an edge set `A` on `Root P ⊕ AuxV |P|` such that

* `A` has no edge between two roots (so it is disjoint from the lifted `P`);
* `A` and `A ∪ ι(P)` both have exact ordinary triangle decompositions
  (`HasDecomp OnePart.part1 OnePart.triFam`);
* `|A| = 105 |P|` and `deg_A (ι v) = 4 deg_P v`;
* in the explicit order `rank` (roots first, then auxiliaries in a fixed injective order),
  every auxiliary has at most four neighbours among the roots and preceding auxiliaries;
* `|Root P| + |AuxV| ≤ 36 |P| + 1`, hence `≤ 1513 < 2048` for `|P| ≤ 42`, and every degree
  in `A` is at most `16384` for `|P| ≤ 42`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The roots of the template for `P`: the vertices incident to `P`. -/
abbrev Root (P : Finset (Sym2 V)) := {v : V // v ∈ vertSet P}

/-- The piece `P` lifted to the roots of a template vertex type `Root P ⊕ U`. -/
def liftP (P : Finset (Sym2 V)) (U : Type*) [DecidableEq U] : Finset (Sym2 (Root P ⊕ U)) :=
  (univ.filter fun e : Sym2 (Root P) => e.map Subtype.val ∈ P).image (Sym2.map Sum.inl)

theorem mem_liftP {P : Finset (Sym2 V)} {U : Type*} [DecidableEq U] {e : Sym2 (Root P ⊕ U)} :
    e ∈ liftP P U ↔ ∃ e' : Sym2 (Root P), e'.map Subtype.val ∈ P ∧ e'.map Sum.inl = e := by
  simp [liftP]

/-- Every edge of `P` lifts to the roots. -/
theorem exists_lift {P : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ P) :
    ∃ e' : Sym2 (Root P), e'.map Subtype.val = e := by
  induction e using Sym2.ind with
  | _ a b =>
    refine ⟨s(⟨a, ?_⟩, ⟨b, ?_⟩), rfl⟩ <;>
      exact mem_filter.mpr ⟨mem_univ _, s(a, b), he, by simp⟩

theorem card_auxV_zero : Fintype.card (AuxV 0) = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun u => by
    rcases u with ⟨j, _⟩ | ⟨_, h⟩
    · exact j.elim0
    · exact absurd h (lt_irrefl 0)⟩

open Classical in
/-- **Existence of private absorber templates.** -/
theorem exists_privateTemplate (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ w, Even (incidentLoad P w)) (h3 : 3 ∣ P.card) :
    ∃ A : Finset (Sym2 (Root P ⊕ AuxV P.card)),
      (∀ r r' : Root P, s(Sum.inl r, Sum.inl r') ∉ A) ∧
      Disjoint A (liftP P (AuxV P.card)) ∧
      HasDecomp part1 triFam A ∧
      HasDecomp part1 triFam (A ∪ liftP P (AuxV P.card)) ∧
      A.card = 105 * P.card ∧
      (∀ r : Root P, incidentLoad A (Sum.inl r) = 4 * incidentLoad P r.val) ∧
      (∀ u : AuxV P.card, (univ.filter fun w : Root P ⊕ AuxV P.card =>
        s(Sum.inr u, w) ∈ A ∧ rank w < rank (Sum.inr u : Root P ⊕ AuxV P.card)).card ≤ 4) := by
  obtain ⟨σ, X, hX⟩ := exists_trailSystem P hloop heven
  have hXmem : ∀ j, X j ∈ vertSet P := fun j =>
    mem_filter.mpr ⟨mem_univ _, s(X j, X (σ j)), (hX.mem _).mpr ⟨j, rfl⟩, by simp⟩
  set xr : Fin P.card → Root P := fun j => ⟨X j, hXmem j⟩ with hxr
  have hne : ∀ j, xr j ≠ xr (σ j) := fun j h => hX.ne j (congrArg Subtype.val h)
  have hinj : Function.Injective fun j => s(xr j, xr (σ j)) := by
    intro j k h
    apply hX.inj
    simpa [xr] using congrArg (Sym2.map Subtype.val) h
  have hP : edgesP σ xr = liftP P (AuxV P.card) := by
    ext e
    rw [edgesP, mem_posEdges, mem_liftP]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨s(xr j, xr (σ j)), (hX.mem _).mpr ⟨j, rfl⟩, rfl⟩
    · rintro ⟨e', he', rfl⟩
      obtain ⟨i, hi⟩ := (hX.mem _).mp he'
      have : e' = s(xr i, xr (σ i)) :=
        Sym2.map.injective Subtype.val_injective (by simpa [xr] using hi)
      exact ⟨i, by simp [this]⟩
  refine ⟨template σ xr h3, template_no_root_edge σ xr h3, hP ▸ disjoint_template_P σ xr h3,
    hasDecomp_template h3 hne, hP ▸ hasDecomp_template_union h3 hne hinj,
    card_template h3 hne, fun r => ?_, fun u => ?_⟩
  · rw [incidentLoad_template_root h3 hne, ← hX.two_mul_card_tail r.val]
    have : (univ.filter fun j => xr j = r) = univ.filter fun j => X j = r.val := by
      ext j; simp [xr, Subtype.ext_iff]
    rw [this]; ring
  · convert card_preceding_le_four σ xr h3 u

/-- The roots number at most `|P|`. -/
theorem card_root_le (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ w, Even (incidentLoad P w)) : Fintype.card (Root P) ≤ P.card := by
  obtain ⟨σ, X, hX⟩ := exists_trailSystem P hloop heven
  rw [Fintype.card_coe]
  calc (vertSet P).card ≤ (univ.image X).card := by
        apply card_le_card
        intro v hv
        obtain ⟨-, e, he, hve⟩ := mem_filter.mp hv
        obtain ⟨i, rfl⟩ := (hX.mem e).mp he
        rcases Sym2.mem_iff.mp hve with rfl | rfl
        · exact mem_image_of_mem _ (mem_univ _)
        · exact mem_image_of_mem _ (mem_univ _)
    _ ≤ (univ : Finset (Fin P.card)).card := card_image_le
    _ = P.card := by simp

/-- Total support of the template: `|Root P| + |AuxV| ≤ 36 |P| + 1`. -/
theorem card_support_le (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ w, Even (incidentLoad P w)) :
    Fintype.card (Root P) + Fintype.card (AuxV P.card) ≤ 36 * P.card + 1 := by
  have h1 := card_root_le P hloop heven
  rcases Nat.eq_zero_or_pos P.card with h0 | hpos
  · have : Fintype.card (AuxV P.card) = 0 := by rw [h0]; exact card_auxV_zero
    omega
  · rw [card_auxV hpos]; omega

/-- For `|P| ≤ 42` the support has at most `1513 < 2048` vertices. -/
theorem card_support_le_1513 (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ w, Even (incidentLoad P w)) (h42 : P.card ≤ 42) :
    Fintype.card (Root P) + Fintype.card (AuxV P.card) ≤ 1513 ∧ (1513 : ℕ) < 2048 := by
  have := card_support_le P hloop heven
  omega

/-- A crude degree bound: any edge set of size `105 |P|` with `|P| ≤ 42` has all degrees at
most `16384`. -/
theorem incidentLoad_le_16384 {W : Type*} [DecidableEq W]
    (A : Finset (Sym2 W)) (m : ℕ) (hA : A.card = 105 * m) (h42 : m ≤ 42) (w : W) :
    incidentLoad A w ≤ 16384 := by
  have : incidentLoad A w ≤ A.card := card_filter_le _ _
  omega

theorem card_root_zero (P : Finset (Sym2 V)) (h0 : P.card = 0) : Fintype.card (Root P) = 0 := by
  rw [Finset.card_eq_zero] at h0
  subst h0
  rw [Fintype.card_coe, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨-, e, he, -⟩ := mem_filter.mp hv
  simp at he

open Classical in
/-- **Private absorber templates: all outputs together.**  For every loopless edge set `P`
on a finite vertex type with all degrees even and `3 ∣ |P|`, with roots `Root P` (the
vertices incident to `P`) and auxiliaries `AuxV |P|`, there is an edge set `A` such that:
no edge of `A` joins two roots; `A` is disjoint from the lifted `P`; `A` and `A ∪ ι(P)` have
exact triangle decompositions; `|A| = 105 |P|`; `|U| = 34 |P| + 1` if `P ≠ ∅` and everything
is empty if `P = ∅`; `deg_A (ι v) = 4 deg_P v`; in the explicit order `rank` (roots `0`,
auxiliaries distinct positive values) every auxiliary has at most four earlier neighbours;
`|R| + |U| ≤ 36 |P| + 1`; and for `|P| ≤ 42`, `|R| + |U| ≤ 1513 < 2048` and every degree of
`A` is at most `16384`. -/
theorem privateTemplate_spec (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ w, Even (incidentLoad P w)) (h3 : 3 ∣ P.card) :
    ∃ A : Finset (Sym2 (Root P ⊕ AuxV P.card)),
      (∀ r r' : Root P, s(Sum.inl r, Sum.inl r') ∉ A) ∧
      Disjoint A (liftP P (AuxV P.card)) ∧
      HasDecomp part1 triFam A ∧
      HasDecomp part1 triFam (A ∪ liftP P (AuxV P.card)) ∧
      A.card = 105 * P.card ∧
      (0 < P.card → Fintype.card (AuxV P.card) = 34 * P.card + 1) ∧
      (P.card = 0 → Fintype.card (Root P) = 0 ∧ Fintype.card (AuxV P.card) = 0 ∧ A = ∅) ∧
      (∀ r : Root P, incidentLoad A (Sum.inl r) = 4 * incidentLoad P r.val) ∧
      (∀ r : Root P, rank (Sum.inl r : Root P ⊕ AuxV P.card) = 0) ∧
      (∀ u : AuxV P.card, 0 < rank (Sum.inr u : Root P ⊕ AuxV P.card)) ∧
      Function.Injective (fun u : AuxV P.card => rank (Sum.inr u : Root P ⊕ AuxV P.card)) ∧
      (∀ u : AuxV P.card, (univ.filter fun w : Root P ⊕ AuxV P.card =>
        s(Sum.inr u, w) ∈ A ∧ rank w < rank (Sum.inr u : Root P ⊕ AuxV P.card)).card ≤ 4) ∧
      Fintype.card (Root P) + Fintype.card (AuxV P.card) ≤ 36 * P.card + 1 ∧
      (P.card ≤ 42 → Fintype.card (Root P) + Fintype.card (AuxV P.card) ≤ 1513 ∧
        (1513 : ℕ) < 2048 ∧ ∀ w, incidentLoad A w ≤ 16384) := by
  obtain ⟨A, h1, h2, h3', h4, h5, h6, h7⟩ := exists_privateTemplate P hloop heven h3
  refine ⟨A, h1, h2, h3', h4, h5, card_auxV, fun h0 => ⟨card_root_zero P h0, ?_, ?_⟩, h6,
    rank_root, rank_aux_pos, rank_injective_aux, h7, card_support_le P hloop heven,
    fun h42 => ⟨(card_support_le_1513 P hloop heven h42).1, by norm_num,
      incidentLoad_le_16384 A P.card h5 h42⟩⟩
  · rw [h0]; exact card_auxV_zero
  · rw [← Finset.card_eq_zero, h5, h0]

end PartitionedTriangleAbsorption.PrivateTemplate
