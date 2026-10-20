/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/-
Port of Aristotle continuation 841854b3 (Divisibility.lean).
Imports and visibility adapted to the local pin; existing triEdges_three and
union lemmas are reused, not redeclared. The original source is preserved.
-/
module

public import PartitionedTriangleAbsorption.Transformer
public import PartitionedTriangleAbsorption.ReturnedBridge
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Pi

/-!
# Step L0: bookkeeping and inherited divisibility

Deterministic facts about edge/degree vectors of partitioned triangles:

* the edge vector of a typed triangle is the edge vector of its type, and the degree vector
  of one of its vertices is the corresponding type degree vector;
* every `F`-decomposable edge set is integrally and fractionally `F`-divisible
  (so the divisibility hypotheses of Theorem 13.16 are necessary);
* integral divisibility is inherited by the residual edge set after removing an
  `F`-decomposable subset (`isIntDiv_sdiff_of_hasDecomp`);
* decompositions of disjoint edge sets can be glued (`IsDecomp.union`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-! ### Explicit triangles -/

lemma typeEdgeVec_three (A B C i j : Fin t) :
    typeEdgeVec ({A, B, C} : Multiset (Fin t)) i j =
      ((if A = i ∧ B = j then 1 else 0) + (if B = i ∧ A = j then 1 else 0)) +
      ((if A = i ∧ C = j then 1 else 0) + (if C = i ∧ A = j then 1 else 0)) +
      ((if B = i ∧ C = j then 1 else 0) + (if C = i ∧ B = j then 1 else 0)) := by
  simp only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  push_cast
  by_cases hA : A = i <;> by_cases hB : B = i <;> by_cases hC : C = i <;>
  by_cases hA' : A = j <;> by_cases hB' : B = j <;> by_cases hC' : C = j <;>
  by_cases hij : i = j <;> simp [hA, hB, hC, hA', hB', hC', hij, eq_comm]

lemma typeDegVec_three (A B C i : Fin t) :
    typeDegVec ({A, B, C} : Multiset (Fin t)) A i =
      (if B = i then 1 else 0) + (if C = i then 1 else 0) := by
  simp only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  push_cast
  by_cases hA : A = i <;> by_cases hB : B = i <;> by_cases hC : C = i <;>
  simp [hA, hB, hC, eq_comm]

lemma map_three (p : V → Fin t) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).val.map p = {p a, p b, p c} := by
  simp [Finset.insert_val, Multiset.ndinsert_of_notMem, hab, hac, hbc]

lemma sum_triEdges_three {M : Type*} [AddCommMonoid M] (f : Sym2 V → M) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ e ∈ triEdges ({a, b, c} : Finset V), f e = f s(a, b) + f s(a, c) + f s(b, c) := by
  rw [triEdges_three hab hac hbc]
  have h1 : s(a, b) ∉ ({s(a, c), s(b, c)} : Finset (Sym2 V)) := by
    simp [hab, hac, hbc]
  have h2 : s(a, c) ∉ ({s(b, c)} : Finset (Sym2 V)) := by
    simp [hab, hac]
  rw [sum_insert h1, sum_insert h2, sum_singleton, add_assoc]

lemma edgeVec_three (p : V → Fin t) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    edgeVec p (triEdges ({a, b, c} : Finset V)) = typeEdgeVec {p a, p b, p c} := by
  rw [edgeVec, sum_triEdges_three _ hab hac hbc]
  funext i j
  rw [typeEdgeVec_three]
  simp only [pairVec, Sym2.lift_mk, Pi.add_apply]

lemma degVec_three_self (p : V → Fin t) {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    degVec p (triEdges ({a, b, c} : Finset V)) a = typeDegVec {p a, p b, p c} (p a) := by
  rw [degVec, sum_triEdges_three _ hab hac hbc]
  funext i
  rw [typeDegVec_three]
  simp [degContrib, hab.symm, hac.symm]

lemma degVec_three_not_mem (p : V → Fin t) {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {v : V} (hv : v ∉ ({a, b, c} : Finset V)) :
    degVec p (triEdges ({a, b, c} : Finset V)) v = 0 := by
  rw [degVec, sum_triEdges_three _ hab hac hbc]
  simp only [mem_insert, mem_singleton, not_or] at hv
  obtain ⟨ha, hb, hc⟩ := hv
  funext i
  simp [degContrib, Ne.symm ha, Ne.symm hb, Ne.symm hc]

/-! ### Typed triangles -/

/-- The type of a vertex set: its multiset of parts. -/
def triType (p : V → Fin t) (s : Finset V) : Multiset (Fin t) := s.val.map p

lemma edgeVec_triEdges (p : V → Fin t) {s : Finset V} (hs : s.card = 3) :
    edgeVec p (triEdges s) = typeEdgeVec (triType p s) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  rw [edgeVec_three p hab hac hbc, triType, map_three p hab hac hbc]

lemma degVec_triEdges (p : V → Fin t) {s : Finset V} (hs : s.card = 3) (v : V) :
    degVec p (triEdges s) v = if v ∈ s then typeDegVec (triType p s) (p v) else 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  split_ifs with hv
  · rw [triType, map_three p hab hac hbc]
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact degVec_three_self p hab hac hbc
    · have e1 : ({a, v, c} : Finset V) = {v, a, c} := Finset.insert_comm _ _ _
      have e2 : ({p a, p v, p c} : Multiset (Fin t)) = {p v, p a, p c} :=
        Multiset.cons_swap _ _ _
      rw [e1, e2]; exact degVec_three_self p (Ne.symm hab) hbc hac
    · have e1 : ({a, b, v} : Finset V) = {v, a, b} := by
        ext x; simp only [mem_insert, mem_singleton]; tauto
      have e2 : ({p a, p b, p v} : Multiset (Fin t)) = {p v, p a, p b} :=
        Multiset.ext.2 fun x => by
          simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
          omega
      rw [e1, e2]; exact degVec_three_self p (Ne.symm hac) (Ne.symm hbc) hab
  · exact degVec_three_not_mem p hab hac hbc hv

omit [DecidableEq V] in
lemma mem_triType {p : V → Fin t} {s : Finset V} {v : V} (hv : v ∈ s) :
    p v ∈ triType p s :=
  Multiset.mem_map_of_mem p hv

/-! ### Additivity -/

lemma edgeVec_union (p : V → Fin t) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    edgeVec p (A ∪ B) = edgeVec p A + edgeVec p B := by
  simp only [edgeVec, sum_union h]

lemma degVec_union (p : V → Fin t) {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    degVec p (A ∪ B) v = degVec p A v + degVec p B v := by
  simp only [degVec, sum_union h]

/-! ### Decompositions -/

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

lemma IsDecomp.edgeVec_eq {E : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomp p F E D) :
    edgeVec p E = ∑ τ ∈ F, ((D.filter (fun s => triType p s = τ)).card : ℤ) • typeEdgeVec τ := by
  obtain ⟨hT, hdisj, rfl⟩ := hD
  have h1 : edgeVec p (D.biUnion triEdges) = ∑ s ∈ D, typeEdgeVec (triType p s) := by
    rw [edgeVec, sum_biUnion hdisj]
    exact sum_congr rfl fun s hs => edgeVec_triEdges p (hT s hs).1
  rw [h1, ← sum_fiberwise_of_maps_to (g := triType p) (t := F) (fun s hs => (hT s hs).2)]
  refine sum_congr rfl fun τ _ => ?_
  rw [natCast_zsmul, ← sum_const]
  exact sum_congr rfl fun s hs => by rw [(mem_filter.mp hs).2]

lemma IsDecomp.degVec_eq {E : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomp p F E D) (v : V) :
    degVec p E v = ∑ τ ∈ F with p v ∈ τ,
      ((D.filter (fun s => v ∈ s ∧ triType p s = τ)).card : ℤ) • typeDegVec τ (p v) := by
  obtain ⟨hT, hdisj, rfl⟩ := hD
  have h1 : degVec p (D.biUnion triEdges) v =
      ∑ s ∈ D with v ∈ s, typeDegVec (triType p s) (p v) := by
    rw [degVec, sum_biUnion hdisj, sum_filter]
    exact sum_congr rfl fun s hs => degVec_triEdges p (hT s hs).1 v
  rw [h1, ← sum_fiberwise_of_maps_to (g := triType p) (t := F.filter (p v ∈ ·))
    (fun s hs => by
      rw [mem_filter] at hs ⊢
      exact ⟨(hT s hs.1).2, mem_triType hs.2⟩)]
  refine sum_congr rfl fun τ _ => ?_
  rw [natCast_zsmul, ← sum_const, filter_filter]
  exact sum_congr rfl fun s hs => by rw [(mem_filter.mp hs).2.2]

/-- Every `F`-decomposable edge set is integrally `F`-divisible. -/
theorem isIntDiv_of_hasDecomp {E : Finset (Sym2 V)} (h : HasDecomp p F E) :
    IsIntDiv p F E := by
  obtain ⟨D, hD⟩ := h
  exact ⟨⟨_, hD.edgeVec_eq⟩, fun v => ⟨_, hD.degVec_eq v⟩⟩

/-- Every `F`-decomposable edge set is fractionally `F`-divisible. -/
theorem isFracDiv_of_hasDecomp {E : Finset (Sym2 V)} (h : HasDecomp p F E) :
    IsFracDiv p F E := by
  obtain ⟨D, hD⟩ := h
  refine ⟨⟨fun τ => ((D.filter (fun s => triType p s = τ)).card : ℝ), fun τ => Nat.cast_nonneg _,
    ?_⟩, fun v => ⟨fun τ => ((D.filter (fun s => v ∈ s ∧ triType p s = τ)).card : ℝ),
      fun τ => Nat.cast_nonneg _, ?_⟩⟩
  · funext i j
    rw [hD.edgeVec_eq]
    simp [Finset.sum_apply]
  · funext i
    rw [hD.degVec_eq v]
    simp [Finset.sum_apply]

/-- Integral divisibility is closed under disjoint unions. -/
theorem IsIntDiv.union {A B : Finset (Sym2 V)} (hA : IsIntDiv p F A) (hB : IsIntDiv p F B)
    (h : Disjoint A B) : IsIntDiv p F (A ∪ B) := by
  obtain ⟨⟨c, hc⟩, hcv⟩ := hA
  obtain ⟨⟨d, hd⟩, hdv⟩ := hB
  refine ⟨⟨c + d, ?_⟩, fun v => ?_⟩
  · rw [edgeVec_union p h, hc, hd, ← sum_add_distrib]
    exact sum_congr rfl fun τ _ => by simp [add_smul]
  · obtain ⟨c', hc'⟩ := hcv v
    obtain ⟨d', hd'⟩ := hdv v
    refine ⟨c' + d', ?_⟩
    rw [degVec_union p h, hc', hd', ← sum_add_distrib]
    exact sum_congr rfl fun τ _ => by simp [add_smul]

/-- Integral divisibility of `E` and of a subset `E'` gives integral divisibility of `E \ E'`. -/
theorem IsIntDiv.sdiff {E E' : Finset (Sym2 V)} (hE : IsIntDiv p F E) (hE' : IsIntDiv p F E')
    (hsub : E' ⊆ E) : IsIntDiv p F (E \ E') := by
  have hu : E' ∪ (E \ E') = E := Finset.union_sdiff_of_subset hsub
  have hd : Disjoint E' (E \ E') := Finset.disjoint_sdiff
  obtain ⟨⟨c, hc⟩, hcv⟩ := hE
  obtain ⟨⟨d, hd'⟩, hdv⟩ := hE'
  refine ⟨⟨c - d, ?_⟩, fun v => ?_⟩
  · have := edgeVec_union p hd
    rw [hu, hc, hd'] at this
    rw [eq_sub_of_add_eq' this.symm, ← sum_sub_distrib]
    exact sum_congr rfl fun τ _ => by simp [sub_smul]
  · obtain ⟨c', hc'⟩ := hcv v
    obtain ⟨d', hd''⟩ := hdv v
    refine ⟨c' - d', ?_⟩
    have := degVec_union p hd v
    rw [hu, hc', hd''] at this
    rw [eq_sub_of_add_eq' this.symm, ← sum_sub_distrib]
    exact sum_congr rfl fun τ _ => by simp [sub_smul]

/-- **L0 (inherited divisibility).** Removing an `F`-decomposable subset from an integrally
`F`-divisible edge set leaves an integrally `F`-divisible residual. -/
theorem isIntDiv_sdiff_of_hasDecomp {E E' : Finset (Sym2 V)} (hE : IsIntDiv p F E)
    (hE' : HasDecomp p F E') (hsub : E' ⊆ E) : IsIntDiv p F (E \ E') :=
  hE.sdiff (isIntDiv_of_hasDecomp hE') hsub

theorem hasDecomp_empty : HasDecomp p F (∅ : Finset (Sym2 V)) :=
  ⟨∅, by simp [IsDecomp]⟩

theorem isIntDiv_empty : IsIntDiv p F (∅ : Finset (Sym2 V)) :=
  isIntDiv_of_hasDecomp hasDecomp_empty

end PartitionedTriangleAbsorption


