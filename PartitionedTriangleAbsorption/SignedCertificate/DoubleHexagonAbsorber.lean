/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon

/-! # Positive control: the double hexagon *is* absorbable in its scaled hosts

The first hexagon is absorbed by the central triangle `xyz`. The second is absorbed by a
24-edge gadget on six bulk vertices `w₁ … w₆` (classes `0, 3, 2, 3, 1, 2`):

* ears `x a' w₁, a' y w₂, y b' w₃, b' z w₄, z c' w₅, c' x w₆` and the hexagon-plus-triangle
  `w₁w₂w₃, w₃w₄w₅, w₅w₆w₁` decompose `A ∪ P`;
* `xyz, a'w₁w₂, b'w₃w₄, c'w₅w₆, xw₁w₆, yw₂w₃, zw₄w₅, w₁w₃w₅` decompose `A`.

This gadget is **not** 2-degenerate over the roots (as it must not be, by
`DoubleHexagon.no_degenerate_twoMode`): `w₁w₃w₅` and the three vertices around it need
common neighbours of more than two prescribed vertices. The finite checks are done on the
host with `m = 2` and transported along the class-preserving embedding into every `m ≥ 2`.

With the fresh destination of `SignedCertificate.Packing`, all conclusions of the Stage 49
candidate hold for this input with `C = 5` once `m ≥ 32` (`candidate_conclusion`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon

open Finset TypedApplicationLinks

/-! ### Typed transport along an embedding -/

section Transport

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

/-- Edge embedding induced by a vertex embedding. -/
def edgeEmb (f : W ↪ V) : Sym2 W ↪ Sym2 V := ⟨Sym2.map f, Sym2.map.injective f.injective⟩

/-- Vertex-set embedding induced by a vertex embedding. -/
def setEmb (f : W ↪ V) : Finset W ↪ Finset V := ⟨fun s => s.map f, map_injective f⟩

theorem isDecomp_map (f : W ↪ V) {pW : W → Fin 2} {pV : V → Fin 2}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} {D : Finset (Finset W)}
    (h : IsDecomp pW F0 E D) : IsDecomp pV F0 (E.map (edgeEmb f)) (D.map (setEmb f)) := by
  obtain ⟨hT, hP, hU⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := mem_map.mp hs
    refine ⟨by simpa [setEmb] using (hT s' hs').1, ?_⟩
    simp only [setEmb, Function.Embedding.coeFn_mk, map_val, Multiset.map_map]
    have : pV ∘ f = pW := funext hp
    rw [this]; exact (hT s' hs').2
  · intro s hs u hu hsu
    simp only [coe_map, Set.mem_image, mem_coe] at hs hu
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨u', hu', rfl⟩ := hu
    have hne : s' ≠ u' := fun h => hsu (by rw [h])
    simp only [Function.onFun, setEmb, Function.Embedding.coeFn_mk, triEdges_map]
    exact (disjoint_map _).mpr (hP hs' hu' hne)
  · rw [← hU]
    ext e
    simp only [mem_biUnion, mem_map, setEmb, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨s, ⟨s', hs', rfl⟩, he⟩
      rw [triEdges_map] at he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      exact ⟨e', ⟨s', hs', he'⟩, rfl⟩
    · rintro ⟨e', ⟨s', hs', he'⟩, rfl⟩
      refine ⟨s'.map f, ⟨s', hs', rfl⟩, ?_⟩
      rw [triEdges_map]
      exact mem_map_of_mem _ he'

theorem hasDecomp_map (f : W ↪ V) {pW : W → Fin 2} {pV : V → Fin 2}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} (h : HasDecomp pW F0 E) :
    HasDecomp pV F0 (E.map (edgeEmb f)) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨_, isDecomp_map f hp hD⟩

end Transport

/-! ### The gadget, encoded on `Fin 15`

Vertices `0 … 8` are the roots; `9 … 14` are `w₁ … w₆`, placed in bulk classes
`0, 3, 2, 3, 1, 2` with indices `0, 0, 0, 1, 0, 1`. -/

/-- Parts of the fifteen gadget vertices. -/
def partW (i : Fin 15) : Fin 2 := if i.val ∈ [2, 3, 5, 6, 8, 10, 11, 12, 14] then 1 else 0

/-- Bulk classes of `w₁ … w₆` (entries below `9` are unused). -/
def bulkClass : Fin 15 → Fin 4 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 3, 1, 2]

/-- Bulk indices of `w₁ … w₆` (entries below `9` are unused). -/
def bulkIdx : Fin 15 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]

/-- The absorber: `xyz` plus the 21-edge gadget for the second hexagon. -/
def AW : Finset (Sym2 (Fin 15)) :=
  {s(0, 1), s(1, 2), s(0, 2),
    s(6, 9), s(6, 10), s(0, 9), s(1, 10), s(9, 10),
    s(7, 11), s(7, 12), s(1, 11), s(2, 12), s(11, 12),
    s(8, 13), s(8, 14), s(2, 13), s(0, 14), s(13, 14),
    s(9, 14), s(10, 11), s(12, 13), s(9, 11), s(11, 13), s(9, 13)}

/-- The source on the gadget vertices. -/
def PW : Finset (Sym2 (Fin 15)) :=
  {s(0, 3), s(3, 1), s(1, 4), s(4, 2), s(2, 5), s(5, 0),
    s(0, 6), s(6, 1), s(1, 7), s(7, 2), s(2, 8), s(8, 0)}

/-- Decomposition of the absorber alone. -/
def Dm : Finset (Finset (Fin 15)) :=
  {{0, 1, 2}, {6, 9, 10}, {7, 11, 12}, {8, 13, 14}, {0, 9, 14}, {1, 10, 11}, {2, 12, 13},
    {9, 11, 13}}

/-- Decomposition of the absorber together with the source. -/
def Dp : Finset (Finset (Fin 15)) :=
  {{0, 3, 1}, {1, 4, 2}, {2, 5, 0}, {0, 6, 9}, {6, 1, 10}, {1, 7, 11}, {7, 2, 12},
    {2, 8, 13}, {8, 0, 14}, {9, 10, 11}, {11, 12, 13}, {13, 14, 9}}

theorem AW_card : AW.card = 24 := by
  unfold AW
  decide +kernel

/-- Edge set of a triangle given by three distinct vertices. -/
theorem triEdges_triple {V : Type*} [DecidableEq V] (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_insert,
      mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hu | hu | hu, hv | hv | hv⟩, huv⟩ <;> subst hu <;> subst hv <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]

theorem pairwiseDisjoint_of_forall {V : Type*} [DecidableEq V] {D : Finset (Finset V)}
    (h : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Disjoint (triEdges x) (triEdges y)) :
    (D : Set (Finset V)).PairwiseDisjoint triEdges :=
  fun x hx y hy hxy => h x hx y hy hxy

theorem Dm_typed : ∀ s ∈ Dm, IsTypedTri partW F0 s := by
  intro s hs
  simp only [Dm, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by unfold partW F0; decide⟩

theorem Dp_typed : ∀ s ∈ Dp, IsTypedTri partW F0 s := by
  intro s hs
  simp only [Dp, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by unfold partW F0; decide⟩

theorem Dm_isDecomp : IsDecomp partW F0 AW Dm := by
  refine ⟨Dm_typed, pairwiseDisjoint_of_forall ?_, ?_⟩
  · intro x hx y hy hne
    simp only [Dm, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp only [triEdges_triple, ne_eq, Fin.reduceEq, not_false_eq_true]; decide +kernel)
  · simp only [Dm, biUnion_insert, triEdges_triple, ne_eq, Fin.reduceEq, not_false_eq_true]
    unfold AW
    decide +kernel

theorem Dp_isDecomp : IsDecomp partW F0 (AW ∪ PW) Dp := by
  refine ⟨Dp_typed, pairwiseDisjoint_of_forall ?_, ?_⟩
  · intro x hx y hy hne
    simp only [Dp, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp only [triEdges_triple, ne_eq, Fin.reduceEq, not_false_eq_true]; decide +kernel)
  · simp only [Dp, biUnion_insert, triEdges_triple, ne_eq, Fin.reduceEq, not_false_eq_true]
    unfold AW PW
    decide +kernel

theorem AW_PW_disjoint : Disjoint AW PW := by
  unfold AW PW
  decide +kernel

theorem gadget_root_edges : ∀ i j : Fin 15, s(i, j) ∈ AW → ∀ (hi : i.val < 9) (hj : j.val < 9),
    s((⟨i.val, hi⟩ : Fin 9), ⟨j.val, hj⟩) ∈ Pc ∪ tc := by
  unfold AW Pc tc
  decide +kernel

theorem gadget_bulk_edges : ∀ i j : Fin 15, s(i, j) ∈ AW → 9 ≤ i.val → 9 ≤ j.val →
    bulkClass i ≠ bulkClass j := by
  unfold AW bulkClass
  decide +kernel

theorem gadget_bulk_inj : ∀ i j : Fin 15, 9 ≤ i.val → 9 ≤ j.val → bulkClass i = bulkClass j →
    bulkIdx i = bulkIdx j → i = j := by
  unfold bulkClass bulkIdx
  decide +kernel

theorem gadget_root_part : ∀ (i : Fin 15) (hi : i.val < 9), rootPart ⟨i.val, hi⟩ = partW i := by
  unfold rootPart partW
  decide +kernel

theorem gadget_bulk_part : ∀ i : Fin 15, 9 ≤ i.val → classPart (bulkClass i) = partW i := by
  unfold classPart bulkClass partW
  decide +kernel

theorem bulkIdx_le : ∀ i : Fin 15, bulkIdx i ≤ 1 := by
  unfold bulkIdx
  decide +kernel

theorem PW_eq : PW = Pc.map (edgeEmb (Fin.castLEEmb (by norm_num : 9 ≤ 15))) := by
  unfold PW Pc
  decide +kernel

/-! ### The embedding into every host `m ≥ 2` -/

/-- Vertex map of the gadget into the host. -/
def gmap (m : ℕ) (hm : 2 ≤ m) (i : Fin 15) : HV m :=
  if h : i.val < 9 then .inl ⟨i.val, h⟩
  else .inr (bulkClass i, ⟨bulkIdx i, by have := bulkIdx_le i; omega⟩)

/-- The gadget embedding. -/
def gemb (m : ℕ) (hm : 2 ≤ m) : Fin 15 ↪ HV m :=
  ⟨gmap m hm, by
    intro i j h
    unfold gmap at h
    by_cases hi : i.val < 9 <;> by_cases hj : j.val < 9 <;> simp only [hi, hj, dite_true,
      dite_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
    · exact Fin.ext h
    · exact gadget_bulk_inj i j (by omega) (by omega) h.1 h.2⟩

theorem part_gemb (m : ℕ) (hm : 2 ≤ m) (i : Fin 15) : part m (gemb m hm i) = partW i := by
  change part m (gmap m hm i) = partW i
  unfold gmap
  by_cases hi : i.val < 9
  · rw [dite_eq_left hi]; exact gadget_root_part i hi
  · rw [dite_eq_right hi]; exact gadget_bulk_part i (by omega)

theorem adj_gemb (m : ℕ) (hm : 2 ≤ m) (i j : Fin 15) (h : s(i, j) ∈ AW) :
    (host m).Adj (gemb m hm i) (gemb m hm j) := by
  change hAdj m (gmap m hm i) (gmap m hm j)
  unfold gmap
  by_cases hi : i.val < 9 <;> by_cases hj : j.val < 9
  · rw [dite_eq_left hi, dite_eq_left hj]; exact gadget_root_edges i j h hi hj
  · rw [dite_eq_left hi, dite_eq_right hj]; trivial
  · rw [dite_eq_right hi, dite_eq_left hj]; trivial
  · rw [dite_eq_right hi, dite_eq_right hj]; exact gadget_bulk_edges i j h (by omega) (by omega)

theorem src_gemb (m : ℕ) (hm : 2 ≤ m) : PW.map (edgeEmb (gemb m hm)) = src m := by
  rw [PW_eq, map_map, src]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Function.Embedding.trans_apply, edgeEmb, Function.Embedding.coeFn_mk,
      Sym2.map_mk, rootEdgeEmb]
    have ha : gemb m hm (Fin.castLEEmb (by norm_num : 9 ≤ 15) a) = .inl a := by
      change gmap m hm _ = _
      unfold gmap
      rw [dite_eq_left (by simp)]; rfl
    have hb : gemb m hm (Fin.castLEEmb (by norm_num : 9 ≤ 15) b) = .inl b := by
      change gmap m hm _ = _
      unfold gmap
      rw [dite_eq_left (by simp)]; rfl
    rw [ha, hb]

/-- The absorber in the host of size parameter `m`. -/
def absorber (m : ℕ) (hm : 2 ≤ m) : Finset (Sym2 (HV m)) := AW.map (edgeEmb (gemb m hm))

theorem absorber_card (m : ℕ) (hm : 2 ≤ m) : (absorber m hm).card = 24 := by
  simp only [absorber, card_map, AW_card]

theorem absorber_subset (m : ℕ) (hm : 2 ≤ m) : absorber m hm ⊆ (host m).edgeFinset := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_map.mp he
  induction e' using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset]
    change s(gemb m hm u, gemb m hm v) ∈ (host m).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact adj_gemb m hm u v he'

/-- **The double hexagon has a 24-edge absorber in every host `m ≥ 2`.** -/
theorem absorber_isAbsorber (m : ℕ) (hm : 2 ≤ m) :
    IsAbsorber (part m) (src m) (absorber m hm) := by
  have hp := part_gemb m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [absorber, ← src_gemb m hm]
    exact (disjoint_map _).mpr AW_PW_disjoint
  · exact hasDecomp_map (gemb m hm) hp ⟨Dm, Dm_isDecomp⟩
  · rw [absorber, ← src_gemb m hm, ← map_union]
    exact hasDecomp_map (gemb m hm) hp ⟨Dp, Dp_isDecomp⟩

/-! ### All candidate conclusions on this input -/

theorem vertSet_card_le {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) :
    (vertSet E).card ≤ 2 * E.card := by
  have hsub : vertSet E ⊆ E.biUnion fun e => univ.filter (· ∈ e) := by
    intro v hv
    simp only [vertSet, mem_filter, mem_univ, true_and] at hv
    obtain ⟨e, he, hve⟩ := hv
    exact mem_biUnion.mpr ⟨e, he, by simpa using hve⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have : univ.filter (· ∈ s(a, b)) ⊆ {a, b} := by
      intro v hv; simp only [mem_filter, mem_univ, true_and, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl <;> simp
    exact (card_le_card this).trans (card_le_two)

/-- **Positive control.** For `m ≥ 32` the double-hexagon input admits `A, Q` with every
conclusion of `DoubleHexagon.SignedAbsorptionCandidate` for `C = 5`, `K = 8`:
`|A| = 24`, `|Q| = 12`, at most `39` auxiliary vertices. -/
theorem candidate_conclusion (m : ℕ) (hm : 32 ≤ m) :
    ∃ A Q : Finset (Sym2 (HV m)), A ⊆ (host m).edgeFinset ∧ Q ⊆ (host m).edgeFinset ∧
      IsTwoMode (part m) (src m) A Q ∧ (∀ e ∈ Q, ∀ v ∈ e, v ∉ roots m) ∧
      pairCount (part m) Q 0 0 = pairCount (part m) (src m) 0 0 ∧
      pairCount (part m) Q 1 1 = pairCount (part m) (src m) 1 1 ∧
      pairCount (part m) Q 0 1 = pairCount (part m) (src m) 0 1 ∧
      (A.card : ℝ) ≤ 5 * 8 ∧ (Q.card : ℝ) ≤ 5 * 8 ∧
      ((auxVerts A Q (roots m)).card : ℝ) ≤ 5 * 8 := by
  have hm2 : 2 ≤ m := by omega
  set A := absorber m hm2
  set W := (univ : Finset (Fin 15)).map (gemb m hm2)
  have hWcard : W.card = 15 := by simp [W]
  have hsrc : (src m).card = 12 := by simp [src, Pc]
  have hcov : ∀ e ∈ A ∪ src m, ∀ v ∈ e, v ∈ W := by
    intro e he v hv
    simp only [A, absorber] at he
    rw [← src_gemb m hm2, ← map_union] at he
    obtain ⟨e', -, rfl⟩ := mem_map.mp he
    obtain ⟨w, -, rfl⟩ := Sym2.mem_map.mp hv
    exact mem_map_of_mem _ (mem_univ w)
  have hrootsW : roots m ⊆ W := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := mem_map.mp hv
    refine mem_map.mpr ⟨Fin.castLEEmb (by norm_num : 9 ≤ 15) i, mem_univ _, ?_⟩
    change gmap m hm2 _ = _
    unfold gmap
    rw [dite_eq_left (by simp)]; rfl
  obtain ⟨Q, D, hQD, -, hQG, hQW, hQc, h00, h11, h01⟩ :=
    exists_fresh_destination (part m) (host m) (1 / 5)
      (antiEdgeful m (by omega) (1 / 5) le_rfl) (parts_inhabited m) (src_cert m) W
      (by
        rw [hWcard, hsrc, card_HV]
        have : (32 : ℝ) ≤ m := by exact_mod_cast hm
        push_cast; linarith)
  have hQdisj : Disjoint Q (A ∪ src m) := by
    rw [disjoint_left]
    intro e heQ heA
    induction e using Sym2.ind with
    | _ a b => exact hQW _ heQ a (Sym2.mem_mk_left a b) (hcov _ heA a (Sym2.mem_mk_left a b))
  refine ⟨A, Q, absorber_subset m hm2, hQG,
    twoMode_of_absorber (absorber_isAbsorber m hm2) ⟨D, hQD⟩ hQdisj,
    fun e he v hv h => hQW e he v hv (hrootsW h), h00, h11, h01, ?_, ?_, ?_⟩
  · rw [absorber_card]; norm_num
  · rw [hQc, hsrc]; norm_num
  · have hsub : auxVerts A Q (roots m) ⊆ W ∪ vertSet Q := by
      intro v hv
      simp only [auxVerts, vertSet, mem_sdiff, mem_filter, mem_univ, true_and,
        mem_union] at hv ⊢
      obtain ⟨⟨e, he, hve⟩, -⟩ := hv
      rcases he with h | h
      · exact Or.inl (hcov e (mem_union_left _ h) v hve)
      · exact Or.inr ⟨e, h, hve⟩
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := vertSet_card_le Q
    rw [hWcard, hQc, hsrc] at *
    have : (auxVerts A Q (roots m)).card ≤ 39 := by omega
    have : ((auxVerts A Q (roots m)).card : ℝ) ≤ 39 := by exact_mod_cast this
    linarith

end PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon
