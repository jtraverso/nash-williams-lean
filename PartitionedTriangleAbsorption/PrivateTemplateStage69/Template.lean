/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.DeletedHost

/-! # Uniform bounded rooted structural F3 private templates

`rooted_template`: fix `m`. Let `W` be a finite root set with a structural labelling
`cls : W → Fin 4`, and `P` an edge set on `W` with `|P| ≤ m`, every edge joining two
distinct classes, `IsIntDiv cls F3 P` (unchanged predicate), and every root incident with
`P`. Then there is a finite extension `ι : W ↪ X` by auxiliary vertices, a labelling
`clsX : X → Fin 4` extending `cls`, and an edge set `A` on `X` such that

* every edge of `A` joins two distinct classes, and `A` has **no edge between two roots**;
* `A` is disjoint from the copy of `P`;
* both `A` and `A ∪ P` have edge-disjoint decompositions into structural `F3` triangles;
* `|A| ≤ C(m)`, `|X| ≤ |W| + C(m)`, every auxiliary vertex lies on an edge of `A`,
  every vertex has `A`-degree at most `C(m)`, and every root `w` has `A`-degree at most
  `C(m) · deg_P(w)`, where `C(m) = templateConst m = 2280 m`.

Construction: embed `W` into `W ⊕ (Fin 4 × Fin L)` with `L = templateHostSize m`, take the
complete four-class graph, delete every root–root pair outside `P` (ledger degree `≤ |W| ≤ 2m`),
apply `deleted_host_absorber`, and extract the finite support with `hasDecomp_comap`.
Disjointness from `P` and from the deleted ledger forces the absence of root–root edges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplateStage69

open Finset TypedApplicationLinks SignedHinge SparseReserveGeometry PhysicalHingeSupply
open ClassRepresentativesStage65

universe u

/-- The complete graph between distinct structural classes. -/
def fourClassGraph {V : Type*} (c : V → Fin 4) : SimpleGraph V where
  Adj a b := c a ≠ c b
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance {V : Type*} (c : V → Fin 4) : DecidableRel (fourClassGraph c).Adj :=
  fun a b => inferInstanceAs (Decidable (c a ≠ c b))

theorem fourClassGraph_adj {V : Type*} (c : V → Fin 4) (a b : V) :
    (fourClassGraph c).Adj a b ↔ c a ≠ c b := Iff.rfl

/-- Number of auxiliaries per class in the canonical host, fixed from `m` alone. -/
def templateHostSize (m : ℕ) : ℕ := 2 ^ 30 * (absorberBudget 6 (12 * m) + (m + 1) ^ 2)

section Lemmas

variable {W V : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

omit [DecidableEq W] in
/-- An embedded edge set has ledger degree at most `|W|` everywhere. -/
theorem card_filter_map_le (f : W ↪ V) (E : Finset (Sym2 W)) (v : V) :
    ((E.map (edgeEmb f)).filter fun e => v ∈ e).card ≤ Fintype.card W := by
  have hsub : (E.map (edgeEmb f)).filter (fun e => v ∈ e) ⊆
      (univ : Finset W).image fun x => s(v, f x) := by
    intro e he
    obtain ⟨he, hv⟩ := mem_filter.mp he
    obtain ⟨e', -, rfl⟩ := mem_map.mp he
    induction e' using Sym2.ind with
    | _ a b =>
      simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.map_mk, Sym2.mem_iff] at hv
      simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.map_mk, mem_image, mem_univ,
        true_and]
      rcases hv with rfl | rfl
      · exact ⟨b, rfl⟩
      · exact ⟨a, Sym2.eq_swap⟩
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

omit [Fintype W] [DecidableEq W] [DecidableEq V] in
theorem map_edgeEmb_trans {U : Type*} (f : W ↪ V) (g : V ↪ U)
    (E : Finset (Sym2 W)) :
    (E.map (edgeEmb f)).map (edgeEmb g) = E.map (edgeEmb (f.trans g)) := by
  rw [map_map]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b => simp [edgeEmb]

/-- Pulling back an edge set all of whose vertices lie in the image. -/
theorem map_comap_edges (S : Finset V) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ S) :
    ((univ : Finset (Sym2 S)).filter fun e => edgeEmb (Function.Embedding.subtype _) e ∈ E).map
      (edgeEmb (Function.Embedding.subtype _)) = E := by
  ext e
  simp only [mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact he'
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      have ha := hE _ he a (Sym2.mem_mk_left a b)
      have hb := hE _ he b (Sym2.mem_mk_right a b)
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa [edgeEmb] using he, by simp [edgeEmb]⟩

end Lemmas

/-- **Uniform bounded rooted structural F3 private template.** -/
theorem rooted_template (m : ℕ) {W : Type u} [Fintype W] [DecidableEq W]
    (cls : W → Fin 4) (P : Finset (Sym2 W))
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (hm : P.card ≤ m)
    (hdiv : IsIntDiv cls F3 P) (hroot : ∀ w, ∃ e ∈ P, w ∈ e) :
    ∃ (X : Type u) (_ : Fintype X) (_ : DecidableEq X) (ι : W ↪ X) (clsX : X → Fin 4)
      (A : Finset (Sym2 X)),
      (∀ w, clsX (ι w) = cls w) ∧
      (∀ a b, s(a, b) ∈ A → clsX a ≠ clsX b) ∧
      (∀ a b : W, s(ι a, ι b) ∉ A) ∧
      Disjoint A (P.map (edgeEmb ι)) ∧
      HasDecomp clsX F3 A ∧ HasDecomp clsX F3 (A ∪ P.map (edgeEmb ι)) ∧
      A.card ≤ templateConst m ∧
      Fintype.card X ≤ Fintype.card W + templateConst m ∧
      (∀ x, (∀ w, ι w ≠ x) → ∃ e ∈ A, x ∈ e) ∧
      (∀ x, (A.filter fun e => x ∈ e).card ≤ templateConst m) ∧
      ∀ w, (A.filter fun e => ι w ∈ e).card ≤
        templateConst m * (P.filter fun e => w ∈ e).card := by
  classical
  -- the canonical host
  obtain ⟨L, hL⟩ : ∃ L, L = templateHostSize m := ⟨_, rfl⟩
  let V := W ⊕ (Fin 4 × Fin L)
  let hostCls : V → Fin 4 := Sum.elim cls Prod.fst
  let inlE : W ↪ V := Function.Embedding.inl
  let G₀ := fourClassGraph hostCls
  let B : Finset (Sym2 V) := ((univ : Finset (Sym2 W)) \ P).map (edgeEmb inlE)
  let P' : Finset (Sym2 V) := P.map (edgeEmb inlE)
  -- numerical facts
  have hN : Fintype.card W ≤ 2 * m := by
    have hv : vertSet P = univ := eq_univ_of_forall fun w => by
      obtain ⟨e, he, hw⟩ := hroot w
      exact mem_filter.mpr ⟨mem_univ _, e, he, hw⟩
    have := card_vertSet_le P
    rw [hv, card_univ] at this
    omega
  have hcardV : (Fintype.card V : ℝ) = Fintype.card W + 4 * L := by
    simp only [V, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  set Bud : ℝ := (absorberBudget 6 (12 * m) : ℝ) with hBud
  have hBud0 : 0 ≤ Bud := by positivity
  have hLR : (L : ℝ) = 2 ^ 30 * (Bud + ((m : ℝ) + 1) ^ 2) := by
    rw [hL, hBud, templateHostSize]
    push_cast
    ring
  have hNR : (Fintype.card W : ℝ) ≤ 2 * m := by exact_mod_cast hN
  have hM0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hW0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  have hsize : ∀ i, (1 / 5 : ℝ) * Fintype.card V ≤ ((classSet hostCls i).card : ℝ) := by
    intro i
    have hcl : L ≤ (classSet hostCls i).card := by
      have h := card_le_card_of_injOn (fun k : Fin L => (Sum.inr (i, k) : V))
        (s := univ) (t := classSet hostCls i)
        (fun k _ => by simp [classSet, hostCls])
        (fun a _ b _ h => (Prod.mk.inj (Sum.inr_injective h)).2)
      simpa using h
    have hclR : (L : ℝ) ≤ (classSet hostCls i).card := by exact_mod_cast hcl
    rw [hcardV]
    nlinarith
  have hB : DegBounded B (Fintype.card W) := fun v => by
    exact_mod_cast card_filter_map_le inlE _ v
  have hPG : P' ⊆ G₀.edgeFinset := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    induction e' using Sym2.ind with
    | _ a b =>
      simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.map_mk,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hP a b he'
  have hPB : Disjoint P' B := (disjoint_map _).mpr disjoint_sdiff
  have hdiv' : IsIntDiv hostCls F3 P' := isIntDiv_map inlE (fun _ => rfl) hdiv
  obtain ⟨A, hAG, hAB, hAP, hdA, hdAP, hAc, hVc⟩ :=
    deleted_host_absorber m hostCls G₀ (fourClassGraph_adj hostCls) (1 / 5)
      (Fintype.card W) hW0 hsize B hB
      (by rw [hcardV, hLR]; nlinarith) (by rw [hcardV, hLR]; nlinarith)
      (by rw [hcardV, hLR]; nlinarith) (by rw [hcardV, hLR]; nlinarith)
      (by rw [hcardV, hLR]; nlinarith) (by rw [hcardV, hLR]; nlinarith)
      P' hPG hPB (by simpa [P'] using hm) hdiv'
  -- extraction of the finite support
  let S : Finset V := univ.map inlE ∪ vertSet A
  let X := {v : V // v ∈ S}
  let valE : X ↪ V := Function.Embedding.subtype _
  let ι : W ↪ X := ⟨fun w => ⟨inlE w, mem_union_left _ (mem_map_of_mem _ (mem_univ w))⟩,
    fun a b h => by simpa [inlE] using congrArg Subtype.val h⟩
  have hιval : ι.trans valE = inlE := by ext w; rfl
  let AX : Finset (Sym2 X) := univ.filter fun e => edgeEmb valE e ∈ A
  have hAX : AX.map (edgeEmb valE) = A := map_comap_edges S A fun e he v hv =>
    mem_union_right _ (mem_filter.mpr ⟨mem_univ _, e, he, hv⟩)
  have hPX : (P.map (edgeEmb ι)).map (edgeEmb valE) = P' := by
    rw [map_edgeEmb_trans, hιval]
  have hdisj : Disjoint AX (P.map (edgeEmb ι)) := by
    rw [← disjoint_map (edgeEmb valE), hAX, hPX]
    exact hAP
  have hmemA : ∀ a b : X, s(a, b) ∈ AX → s(valE a, valE b) ∈ A := by
    intro a b h
    have := mem_map_of_mem (edgeEmb valE) h
    rw [hAX] at this
    simpa [edgeEmb] using this
  refine ⟨X, inferInstance, inferInstance, ι, hostCls ∘ valE, AX, fun _ => rfl, ?_, ?_, hdisj,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have := SimpleGraph.mem_edgeFinset.mp (hAG (hmemA a b h))
    exact this
  · intro a b h
    have hA := hmemA _ _ h
    by_cases hab : s(a, b) ∈ P
    · have : s(valE (ι a), valE (ι b)) ∈ P' :=
        mem_map.mpr ⟨s(a, b), hab, rfl⟩
      exact disjoint_left.mp hAP hA this
    · have : s(valE (ι a), valE (ι b)) ∈ B :=
        mem_map.mpr ⟨s(a, b), mem_sdiff.mpr ⟨mem_univ _, hab⟩,
          rfl⟩
      exact disjoint_left.mp hAB hA this
  · apply hasDecomp_comap valE
    rw [hAX]
    exact hdA
  · apply hasDecomp_comap valE
    rw [map_union, hAX, hPX]
    exact hdAP
  · rw [← card_map (edgeEmb valE), hAX]
    exact hAc
  · have hS : S.card ≤ Fintype.card W + templateConst m := by
      refine (card_union_le _ _).trans ?_
      simp only [card_map, card_univ]
      omega
    simpa [X] using hS
  · intro x hx
    have hxS := x.2
    rcases mem_union.mp hxS with h | h
    · obtain ⟨w, -, hw⟩ := mem_map.mp h
      exact absurd (Subtype.ext hw) (hx w)
    · obtain ⟨-, e, he, hxe⟩ := mem_filter.mp h
      rw [← hAX] at he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      refine ⟨e', he', ?_⟩
      simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.mem_map] at hxe
      obtain ⟨y, hy, hyx⟩ := hxe
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
  · intro x
    refine (card_filter_le _ _).trans ?_
    rw [← card_map (edgeEmb valE), hAX]
    exact hAc
  · intro w
    obtain ⟨e, he, hw⟩ := hroot w
    have hpos : 1 ≤ (P.filter fun e => w ∈ e).card :=
      card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hw⟩⟩
    refine (card_filter_le _ _).trans ?_
    rw [← card_map (edgeEmb valE), hAX]
    calc A.card ≤ templateConst m := hAc
      _ = templateConst m * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hpos

end PartitionedTriangleAbsorption.PrivateTemplateStage69
