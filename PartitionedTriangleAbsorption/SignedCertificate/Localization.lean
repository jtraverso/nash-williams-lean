/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Reduction

/-! # Localization: pairwise-supply constructions collapse to the roots

A construction that only uses two-root common-neighbour supply adds new vertices one at a
time, each joined to at most two earlier vertices (roots or earlier new vertices). We call
the resulting total edge set `H` *2-degenerate over the roots `Z`*
(`IsDegenerateOver H Z r`, with `r` an injective ranking of the new vertices).

* `weight_zero_of_degenerate` (**rigidity**): in a 2-degenerate extension, every integer
  combination of triangles of `H` whose signed edge-sum vanishes on all edges meeting a new
  vertex has zero weight on every triangle meeting a new vertex.
* `rootAbsorber_of_degenerate` (**localization**): if a two-mode solution `(A, Q)` for a
  root-supported `P` (with `Q` outside `Z`) has `A ∪ P ∪ Q` 2-degenerate over `Z`, then
  some `A' ⊆ A` with all vertices in `Z` is already an absorber for `P`, decomposed by
  triangles inside `Z`.

Hence pairwise supply alone can only succeed when `P` already has an absorber inside the
root set. `SignedCertificate.DoubleHexagon` exhibits an actual signed-certificate input
for which no such root absorber exists.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `H`-neighbours of `v` that are roots or earlier (lower rank) vertices. -/
def lowNbrs (H : Finset (Sym2 V)) (Z : Finset V) (r : V → ℕ) (v : V) : Finset V :=
  univ.filter fun u => s(u, v) ∈ H ∧ (u ∈ Z ∨ r u < r v)

/-- `H` is **2-degenerate over `Z`** for the ranking `r`: ranks of distinct new vertices
differ, and every new vertex has at most two `H`-neighbours among roots and earlier new
vertices. Root–root edges are unrestricted. -/
def IsDegenerateOver (H : Finset (Sym2 V)) (Z : Finset V) (r : V → ℕ) : Prop :=
  (∀ u v, u ∉ Z → v ∉ Z → r u = r v → u = v) ∧ ∀ v, v ∉ Z → (lowNbrs H Z r v).card ≤ 2

omit [Fintype V] in
theorem mk_mem_triEdges_of_mem {s : Finset V} {a b : V} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : s(a, b) ∈ triEdges s := by
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  exact ⟨⟨ha, hb⟩, hab⟩

omit [Fintype V] in
theorem mem_of_mk_mem_triEdges' {s : Finset V} {a b : V} (h : s(a, b) ∈ triEdges s) :
    a ∈ s ∧ b ∈ s := by
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff] at h
  exact h.1

/-- **Rigidity of 2-degenerate extensions.** Let `T` be a family of 3-sets whose edges lie
in `H`, and `w` integer weights such that the signed edge-sum vanishes on every edge with an
endpoint outside `Z`. If `H` is 2-degenerate over `Z`, then every triangle of `T` with a
vertex outside `Z` has weight zero. -/
theorem weight_zero_of_degenerate {H : Finset (Sym2 V)} {Z : Finset V} {r : V → ℕ}
    (hdeg : IsDegenerateOver H Z r) {T : Finset (Finset V)} (hT3 : ∀ s ∈ T, s.card = 3)
    (hTH : ∀ s ∈ T, triEdges s ⊆ H) (w : Finset V → ℤ)
    (hsum : ∀ e : Sym2 V, (∃ v ∈ e, v ∉ Z) → ∑ s ∈ T, w s * ind (triEdges s) e = 0) :
    ∀ s ∈ T, (∃ v ∈ s, v ∉ Z) → w s = 0 := by
  by_contra hcon
  push Not at hcon
  set S := T.filter fun s => w s ≠ 0 ∧ ∃ v ∈ s, v ∉ Z with hS
  set M := (S.biUnion id).filter fun v => v ∉ Z with hM
  have hMne : M.Nonempty := by
    obtain ⟨s, hs, ⟨v, hv, hvZ⟩, hw⟩ := hcon
    exact ⟨v, mem_filter.mpr ⟨mem_biUnion.mpr ⟨s, mem_filter.mpr ⟨hs, hw, v, hv, hvZ⟩, hv⟩,
      hvZ⟩⟩
  obtain ⟨v, hvM, hvmax⟩ := M.exists_max_image r hMne
  have hvZ : v ∉ Z := (mem_filter.mp hvM).2
  -- every nonzero-weight triangle through `v` lies in `insert v (lowNbrs H Z r v)`
  have hsubset : ∀ u ∈ T, w u ≠ 0 → v ∈ u → u ⊆ insert v (lowNbrs H Z r v) := by
    intro u hu hwu hvu a ha
    by_cases hav : a = v
    · exact hav ▸ mem_insert_self _ _
    refine mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩)
    · exact hTH u hu (mk_mem_triEdges_of_mem ha hvu hav)
    · by_cases haZ : a ∈ Z
      · exact Or.inl haZ
      · right
        have haM : a ∈ M := mem_filter.mpr ⟨mem_biUnion.mpr ⟨u, mem_filter.mpr ⟨hu, hwu, v,
          hvu, hvZ⟩, ha⟩, haZ⟩
        have hle := hvmax a haM
        have hne : r a ≠ r v := fun h => hav (hdeg.1 a v haZ hvZ h)
        omega
  have hcardU : (insert v (lowNbrs H Z r v)).card ≤ 3 :=
    (card_insert_le _ _).trans (by have := hdeg.2 v hvZ; omega)
  have huniq : ∀ u ∈ T, w u ≠ 0 → v ∈ u → u = insert v (lowNbrs H Z r v) := by
    intro u hu hwu hvu
    exact eq_of_subset_of_card_le (hsubset u hu hwu hvu) (by rw [hT3 u hu]; exact hcardU)
  -- pick the triangle through `v`
  obtain ⟨s, hsS, hvs⟩ : ∃ s ∈ S, v ∈ s := by
    obtain ⟨s, hs, hv⟩ := mem_biUnion.mp (mem_filter.mp hvM).1
    exact ⟨s, hs, hv⟩
  obtain ⟨hsT, hws, -⟩ := mem_filter.mp hsS
  obtain ⟨a, has, hav⟩ : ∃ a ∈ s, a ≠ v := by
    by_contra h
    push Not at h
    have : s ⊆ {v} := fun b hb => mem_singleton.mpr (h b hb)
    have := card_le_card this
    rw [hT3 s hsT, card_singleton] at this
    omega
  have hes : s(v, a) ∈ triEdges s := mk_mem_triEdges_of_mem hvs has (Ne.symm hav)
  have h0 := hsum s(v, a) ⟨v, Sym2.mem_mk_left v a, hvZ⟩
  rw [Finset.sum_eq_single_of_mem s hsT] at h0
  · rw [ind, ite_eq_left hes, mul_one] at h0
    exact hws h0
  · intro u hu hus
    by_cases heu : s(v, a) ∈ triEdges u
    · have hvu := (mem_of_mk_mem_triEdges' heu).1
      by_cases hwu : w u = 0
      · rw [hwu, zero_mul]
      · exact absurd ((huniq u hu hwu hvu).trans (huniq s hsT hws hvs).symm) hus
    · rw [ind, ite_eq_right heu, mul_zero]

omit [Fintype V] in
/-- A subfamily of a decomposition decomposes the union of its triangles. -/
theorem isDecomp_sub {p : V → Fin 2} {E : Finset (Sym2 V)} {D R : Finset (Finset V)}
    (h : IsDecomp p F0 E D) (hR : R ⊆ D) : IsDecomp p F0 (R.biUnion triEdges) R :=
  ⟨fun s hs => h.1 s (hR hs), h.2.1.subset (by exact_mod_cast hR), rfl⟩

omit [Fintype V] in
theorem triEdges_subset_of_isDecomp {p : V → Fin 2} {E : Finset (Sym2 V)}
    {D : Finset (Finset V)} (h : IsDecomp p F0 E D) {s : Finset V} (hs : s ∈ D) :
    triEdges s ⊆ E :=
  h.2.2 ▸ subset_biUnion_of_mem triEdges hs

omit [Fintype V] in
theorem ind_union_of_disjoint {E₁ E₂ : Finset (Sym2 V)} (h : Disjoint E₁ E₂) (e : Sym2 V) :
    ind (E₁ ∪ E₂) e = ind E₁ e + ind E₂ e := by
  simp only [ind, mem_union]
  by_cases h1 : e ∈ E₁ <;> by_cases h2 : e ∈ E₂ <;>
    simp only [h1, h2, ite_true, ite_false, or_true, or_false] <;> norm_num
  exact False.elim (disjoint_left.mp h h1 h2)

/-- **Localization.** Let `P` have all its vertices in `Z` and let `(A, Q)` be a two-mode
solution with `Q` avoiding `Z`. If `A ∪ P ∪ Q` is 2-degenerate over `Z`, then there is an
absorber `A' ⊆ A` for `P` all of whose edges have both endpoints in `Z`, with both
decompositions using only triangles inside `Z`. -/
theorem rootAbsorber_of_degenerate {p : V → Fin 2} {P A Q : Finset (Sym2 V)} {Z : Finset V}
    {r : V → ℕ} (hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z) (hQZ : ∀ e ∈ Q, ∀ v ∈ e, v ∉ Z)
    (h : IsTwoMode p P A Q) (hdeg : IsDegenerateOver (A ∪ P ∪ Q) Z r) :
    ∃ A' : Finset (Sym2 V), A' ⊆ A ∧ (∀ e ∈ A', ∀ v ∈ e, v ∈ Z) ∧ IsAbsorber p P A' ∧
      ∃ Dm Dp : Finset (Finset V), (∀ s ∈ Dm, s ⊆ Z) ∧ (∀ s ∈ Dp, s ⊆ Z) ∧
        IsDecomp p F0 A' Dm ∧ IsDecomp p F0 (A' ∪ P) Dp := by
  obtain ⟨hPA, hPQ, hAQ, ⟨D3, hD3⟩, ⟨D1, hD1⟩, ⟨D2, hD2⟩⟩ := h
  set T := D1 ∪ D2 ∪ D3 with hTdef
  let w : Finset V → ℤ := fun s =>
    (if s ∈ D1 then 1 else 0) + (if s ∈ D3 then 1 else 0) - (if s ∈ D2 then 1 else 0)
  -- splitting a weighted sum over any subfamily `R` of `T`
  have hsplit : ∀ (R : Finset (Finset V)) (f : Finset V → ℤ),
      ∑ s ∈ R, w s * f s = ∑ s ∈ R ∩ D1, f s + ∑ s ∈ R ∩ D3, f s - ∑ s ∈ R ∩ D2, f s := by
    intro R f
    simp only [w, sub_mul, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_mem]
  have hT1 : T ∩ D1 = D1 := inter_eq_right.mpr (subset_union_left.trans subset_union_left)
  have hT2 : T ∩ D2 = D2 := inter_eq_right.mpr (subset_union_right.trans subset_union_left)
  have hT3 : T ∩ D3 = D3 := inter_eq_right.mpr subset_union_right
  -- (I) the signed edge-sum is the indicator of `P`
  have hI : ∀ e, ∑ s ∈ T, w s * ind (triEdges s) e = ind P e := by
    intro e
    rw [hsplit, hT1, hT2, hT3, sum_ind_of_isDecomp hD1, sum_ind_of_isDecomp hD2,
      sum_ind_of_isDecomp hD3, ind_union_of_disjoint hPA.symm, ind_union_of_disjoint hAQ]
    ring
  -- (II) rigidity
  have hTtyped : ∀ s ∈ T, IsTypedTri p F0 s := by
    intro s hs
    simp only [hTdef, mem_union] at hs
    rcases hs with (hs | hs) | hs
    · exact hD1.1 s hs
    · exact hD2.1 s hs
    · exact hD3.1 s hs
  have hTH : ∀ s ∈ T, triEdges s ⊆ A ∪ P ∪ Q := by
    intro s hs
    simp only [hTdef, mem_union] at hs
    rcases hs with (hs | hs) | hs
    · exact (triEdges_subset_of_isDecomp hD1 hs).trans subset_union_left
    · refine (triEdges_subset_of_isDecomp hD2 hs).trans ?_
      intro e he; simp only [mem_union] at he ⊢; tauto
    · exact (triEdges_subset_of_isDecomp hD3 hs).trans subset_union_right
  have hzero := weight_zero_of_degenerate hdeg (fun s hs => (hTtyped s hs).1) hTH w
    (fun e ⟨v, hve, hvZ⟩ => by
      rw [hI, ind, ite_eq_right]
      exact fun heP => hvZ (hPZ e heP v hve))
  -- (III) only root triangles carry weight
  set Rp := D1.filter (· ⊆ Z) with hRp
  set Rm := D2.filter (· ⊆ Z) with hRm
  have hD3root : D3.filter (· ⊆ Z) = ∅ := by
    ext s
    simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hs hsZ
    obtain ⟨e, he⟩ := triEdges_nonempty_of_typed (hD3.1 s hs)
    induction e using Sym2.ind with
    | _ a b =>
      have hQ := triEdges_subset_of_isDecomp hD3 hs he
      exact hQZ _ hQ a (Sym2.mem_mk_left a b) (hsZ (mem_of_mk_mem_triEdges' he).1)
  have hIII : ∀ e, ind P e = ind (Rp.biUnion triEdges) e - ind (Rm.biUnion triEdges) e := by
    intro e
    rw [← hI e, ← Finset.sum_filter_of_ne (p := (· ⊆ Z)) (fun s hs hne => by
      by_contra hsZ
      rw [Finset.not_subset] at hsZ
      obtain ⟨v, hv, hvZ⟩ := hsZ
      exact hne (by rw [hzero s hs ⟨v, hv, hvZ⟩, zero_mul]))]
    rw [hsplit]
    have e1 : T.filter (· ⊆ Z) ∩ D1 = Rp := by
      ext s; simp only [hTdef, hRp, mem_inter, mem_filter, mem_union]; tauto
    have e2 : T.filter (· ⊆ Z) ∩ D2 = Rm := by
      ext s; simp only [hTdef, hRm, mem_inter, mem_filter, mem_union]; tauto
    have e3 : T.filter (· ⊆ Z) ∩ D3 = ∅ := by
      rw [← hD3root]
      ext s; simp only [hTdef, mem_inter, mem_filter, mem_union]; tauto
    rw [e1, e2, e3, sum_empty, add_zero,
      sum_ind_of_isDecomp (isDecomp_sub hD1 (filter_subset _ _)),
      sum_ind_of_isDecomp (isDecomp_sub hD2 (filter_subset _ _))]
  -- (IV) read off the root absorber
  set A' := Rm.biUnion triEdges with hA'
  have hval : ∀ e, ind (Rp.biUnion triEdges) e = ind P e + ind A' e := by
    intro e; rw [hIII e]; ring
  have hdisj : Disjoint A' P := by
    rw [disjoint_left]
    intro e h1 h2
    have := hval e
    simp only [ind, ite_eq_left h1, ite_eq_left h2] at this
    split_ifs at this <;> omega
  have hunion : Rp.biUnion triEdges = A' ∪ P := by
    ext e
    have := hval e
    simp only [mem_union]
    by_cases h1 : e ∈ A' <;> by_cases h2 : e ∈ P <;>
      by_cases h3 : e ∈ Rp.biUnion triEdges <;>
      simp only [ind, h1, h2, h3, ite_true, ite_false, or_true, or_false,
        iff_true, iff_false] at this ⊢ <;> omega
  have hA'Z : ∀ e ∈ A', ∀ v ∈ e, v ∈ Z := by
    intro e he v hv
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have hab := mem_of_mk_mem_triEdges' hes
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact (mem_filter.mp hs).2 hab.1
      · exact (mem_filter.mp hs).2 hab.2
  refine ⟨A', ?_, hA'Z, ⟨hdisj, ⟨Rm, isDecomp_sub hD2 (filter_subset _ _)⟩,
    ⟨Rp, hunion ▸ isDecomp_sub hD1 (filter_subset _ _)⟩⟩, Rm, Rp,
    fun s hs => (mem_filter.mp hs).2, fun s hs => (mem_filter.mp hs).2,
    isDecomp_sub hD2 (filter_subset _ _), hunion ▸ isDecomp_sub hD1 (filter_subset _ _)⟩
  intro e he
  obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
  have hAQe := triEdges_subset_of_isDecomp hD2 (mem_filter.mp hs).1 hes
  rcases mem_union.mp hAQe with h | h
  · exact h
  · exfalso
    induction e using Sym2.ind with
    | _ a b => exact hQZ _ h a (Sym2.mem_mk_left a b) (hA'Z _ he a (Sym2.mem_mk_left a b))

end PartitionedTriangleAbsorption.SignedCertificate
