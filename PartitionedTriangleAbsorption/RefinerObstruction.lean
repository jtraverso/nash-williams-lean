/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RefinerAssembly

/-!
# An obstruction for refiners: echelon libraries are rigid

`RefinerAssembly.RefinesReserve indices B X R` asks that every integrally divisible
`L ⊆ X` selects pairwise edge-disjoint library pieces covering exactly `R ∪ L`.

This file proves a structural *necessary* condition on any such library.

Call a library **echelon** if its pieces can be ranked so that every piece `B i`
contains a *leading* edge `lead i ∈ R` that lies in no other piece of smaller or equal
rank.  This is exactly what happens when pieces are produced one at a time and each new
piece brings in a fresh remainder edge: for instance a triangle `{w, a, b}` stacked on an
existing pair `a, b` through a fresh apex `w` obtained from a single anti-edge request.

* `selection_eq_of_echelon`: in an echelon library the selection covering `R` exactly is
  unique, whatever the leftover is.
* `leftover_eq_of_echelon`: hence two refined leftovers coincide.
* `eq_empty_of_refinesReserve_echelon`: an echelon library refines only the empty leftover.
  So it cannot be a refiner of any reserve that contains a nonempty divisible subgraph.
* `stacked_triangles_echelon`: triangles stacked through fresh apices form an echelon
  library.  Consequently such triangle libraries, i.e. the libraries obtained from
  anti-edge requests alone, with empty private absorbers, never refine a reserve with a
  nonempty divisible subgraph (`eq_empty_of_refinesReserve_stacked`).

This is an obstruction to one design, not to refiners in general: a refiner must contain
pieces all of whose remainder edges are shared with other pieces (alternative
decompositions), as in the two decompositions of a hinge or of a private absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RefinerObstruction

open Finset

variable {V I : Type*} [DecidableEq V]

/-- One half of the uniqueness argument: a disagreement of maximal rank is impossible. -/
theorem no_max_disagreement (indices : Finset I) (B : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) (rank : I → ℕ) (lead : I → Sym2 V)
    (hlead : ∀ i ∈ indices, lead i ∈ B i) (hleadR : ∀ i ∈ indices, lead i ∈ R)
    (hech : ∀ i ∈ indices, ∀ j ∈ indices, j ≠ i → lead i ∈ B j → rank i < rank j)
    {s s' : Finset I} (hs : s ⊆ indices) (hs' : s' ⊆ indices)
    (hdis : (s : Set I).PairwiseDisjoint B) (hcov' : R ⊆ s'.biUnion B)
    {i : I} (his : i ∈ s) (his' : i ∉ s')
    (hmax : ∀ j, rank i < rank j → (j ∈ s ↔ j ∈ s')) : False := by
  have hi : i ∈ indices := hs his
  obtain ⟨j, hjs', hjB⟩ := mem_biUnion.mp (hcov' (hleadR i hi))
  have hji : j ≠ i := fun h => his' (h ▸ hjs')
  have hrank : rank i < rank j := hech i hi j (hs' hjs') hji hjB
  have hjs : j ∈ s := (hmax j hrank).mpr hjs'
  have hd : Disjoint (B i) (B j) := hdis his hjs (Ne.symm hji)
  exact disjoint_left.mp hd (hlead i hi) hjB

/-- **Rigidity of echelon libraries.** Any two exact selections covering `R` agree. -/
theorem selection_eq_of_echelon (indices : Finset I) (B : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) (rank : I → ℕ) (lead : I → Sym2 V)
    (hlead : ∀ i ∈ indices, lead i ∈ B i) (hleadR : ∀ i ∈ indices, lead i ∈ R)
    (hech : ∀ i ∈ indices, ∀ j ∈ indices, j ≠ i → lead i ∈ B j → rank i < rank j)
    {s s' : Finset I} (hs : s ⊆ indices) (hs' : s' ⊆ indices)
    (hdis : (s : Set I).PairwiseDisjoint B) (hdis' : (s' : Set I).PairwiseDisjoint B)
    (hcov : R ⊆ s.biUnion B) (hcov' : R ⊆ s'.biUnion B) : s = s' := by
  classical
  by_contra hne
  set D := (s \ s') ∪ (s' \ s) with hD
  have hDne : D.Nonempty := by
    by_contra h
    apply hne
    rw [not_nonempty_iff_eq_empty] at h
    ext x
    constructor
    · intro hx
      by_contra hx'
      have : x ∈ D := mem_union_left _ (mem_sdiff.mpr ⟨hx, hx'⟩)
      simp [h] at this
    · intro hx
      by_contra hx'
      have : x ∈ D := mem_union_right _ (mem_sdiff.mpr ⟨hx, hx'⟩)
      simp [h] at this
  obtain ⟨i, hiD, himax⟩ := exists_max_image D rank hDne
  have hmax : ∀ j, rank i < rank j → (j ∈ s ↔ j ∈ s') := by
    intro j hj
    by_contra hiff
    have hjD : j ∈ D := by
      by_cases hjs : j ∈ s
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hjs, fun h => hiff ⟨fun _ => h, fun _ => hjs⟩⟩)
      · have hjs' : j ∈ s' := by
          by_contra hjs'
          exact hiff ⟨fun h => absurd h hjs, fun h => absurd h hjs'⟩
        exact mem_union_right _ (mem_sdiff.mpr ⟨hjs', hjs⟩)
    exact absurd (himax j hjD) (not_le.mpr hj)
  rcases mem_union.mp hiD with h | h
  · obtain ⟨his, his'⟩ := mem_sdiff.mp h
    exact no_max_disagreement indices B R rank lead hlead hleadR hech hs hs' hdis hcov'
      his his' hmax
  · obtain ⟨his', his⟩ := mem_sdiff.mp h
    exact no_max_disagreement indices B R rank lead hlead hleadR hech hs' hs hdis' hcov
      his' his (fun j hj => (hmax j hj).symm)

/-- Two leftovers refined by an echelon library coincide. -/
theorem leftover_eq_of_echelon (indices : Finset I) (B : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) (rank : I → ℕ) (lead : I → Sym2 V)
    (hlead : ∀ i ∈ indices, lead i ∈ B i) (hleadR : ∀ i ∈ indices, lead i ∈ R)
    (hech : ∀ i ∈ indices, ∀ j ∈ indices, j ≠ i → lead i ∈ B j → rank i < rank j)
    {L L' : Finset (Sym2 V)} (hL : Disjoint L R) (hL' : Disjoint L' R)
    {s s' : Finset I} (hs : s ⊆ indices) (hs' : s' ⊆ indices)
    (hdis : (s : Set I).PairwiseDisjoint B) (hdis' : (s' : Set I).PairwiseDisjoint B)
    (hcov : s.biUnion B = R ∪ L) (hcov' : s'.biUnion B = R ∪ L') : L = L' := by
  have hss := selection_eq_of_echelon indices B R rank lead hlead hleadR hech hs hs' hdis hdis'
    (hcov ▸ subset_union_left) (hcov' ▸ subset_union_left)
  subst hss
  have hRL : R ∪ L = R ∪ L' := hcov.symm.trans hcov'
  ext e
  constructor
  · intro he
    have : e ∈ R ∪ L' := hRL ▸ mem_union_right _ he
    rcases mem_union.mp this with h | h
    · exact absurd h (disjoint_left.mp hL he)
    · exact h
  · intro he
    have : e ∈ R ∪ L := hRL.symm ▸ mem_union_right _ he
    rcases mem_union.mp this with h | h
    · exact absurd h (disjoint_left.mp hL' he)
    · exact h

variable {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- **Echelon libraries are not refiners.** If an echelon library refines the reserve `X`
with remainder `R` disjoint from `X`, then the only divisible leftover inside `X` is `∅`. -/
theorem eq_empty_of_refinesReserve_echelon (indices : Finset I) (B : I → Finset (Sym2 V))
    (X R : Finset (Sym2 V)) (hRX : Disjoint R X)
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) indices B X R)
    (rank : I → ℕ) (lead : I → Sym2 V)
    (hlead : ∀ i ∈ indices, lead i ∈ B i) (hleadR : ∀ i ∈ indices, lead i ∈ R)
    (hech : ∀ i ∈ indices, ∀ j ∈ indices, j ≠ i → lead i ∈ B j → rank i < rank j)
    {L : Finset (Sym2 V)} (hLX : L ⊆ X) (hdiv : IsIntDiv p F L) : L = ∅ := by
  obtain ⟨s, hs, hdis, hcov⟩ := href L hLX hdiv
  obtain ⟨s', hs', hdis', hcov'⟩ := href ∅ (empty_subset X)
    (RefinerAssembly.empty_isIntDiv (p := p) (F := F))
  exact leftover_eq_of_echelon indices B R rank lead hlead hleadR hech
    (disjoint_of_subset_left hLX hRX.symm) (disjoint_empty_left R) hs hs' hdis hdis' hcov hcov'

/-- The edge `s(w, a)` belongs to the triangle on `{w, a, b}` when `w ≠ a`. -/
theorem mk_mem_triEdges_insert (w a b : V) (hwa : w ≠ a) :
    s(w, a) ∈ triEdges ({w, a, b} : Finset V) := by
  simp [triEdges, hwa]

/-- A vertex of an edge of `triEdges S` lies in `S`. -/
theorem mem_of_mk_mem_triEdges {S : Finset V} {x y : V} (h : s(x, y) ∈ triEdges S) : x ∈ S := by
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff] at h
  exact h.1.1

/-- **Stacked triangles form an echelon library.** Triangle `k` has apex `w k` and base
`a k, b k`; its apex is fresh: it is no vertex of any other triangle of smaller or equal rank.
The leading edge is the anti-edge half `s(w k, a k)`. -/
theorem stacked_triangles_echelon (indices : Finset I) (w a b : I → V) (rank : I → ℕ)
    (hwa : ∀ k ∈ indices, w k ≠ a k)
    (hfresh : ∀ k ∈ indices, ∀ l ∈ indices, l ≠ k → rank l ≤ rank k →
      w k ∉ ({w l, a l, b l} : Finset V)) :
    (∀ k ∈ indices, s(w k, a k) ∈ triEdges ({w k, a k, b k} : Finset V)) ∧
    ∀ k ∈ indices, ∀ l ∈ indices, l ≠ k →
      s(w k, a k) ∈ triEdges ({w l, a l, b l} : Finset V) → rank k < rank l := by
  refine ⟨fun k hk => mk_mem_triEdges_insert _ _ _ (hwa k hk), ?_⟩
  intro k hk l hl hlk he
  by_contra hlt
  exact hfresh k hk l hl hlk (not_lt.mp hlt) (mem_of_mk_mem_triEdges he)

/-- **Anti-edge-only triangle libraries do not refine.** Suppose the library consists of
stacked triangles `{w k, a k, b k}` with fresh apices, and each anti-edge half `s(w k, a k)`
belongs to the remainder `R`. If this library refines `X` with remainder `R` disjoint
from `X`, then no nonempty divisible `L ⊆ X` exists. -/
theorem eq_empty_of_refinesReserve_stacked (indices : Finset I) (w a b : I → V)
    (rank : I → ℕ) (X R : Finset (Sym2 V)) (hRX : Disjoint R X)
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) indices
      (fun k => triEdges ({w k, a k, b k} : Finset V)) X R)
    (hwa : ∀ k ∈ indices, w k ≠ a k)
    (hR : ∀ k ∈ indices, s(w k, a k) ∈ R)
    (hfresh : ∀ k ∈ indices, ∀ l ∈ indices, l ≠ k → rank l ≤ rank k →
      w k ∉ ({w l, a l, b l} : Finset V))
    {L : Finset (Sym2 V)} (hLX : L ⊆ X) (hdiv : IsIntDiv p F L) : L = ∅ := by
  obtain ⟨hlead, hech⟩ := stacked_triangles_echelon indices w a b rank hwa hfresh
  exact eq_empty_of_refinesReserve_echelon indices _ X R hRX href rank
    (fun k => s(w k, a k)) hlead hR hech hLX hdiv

end PartitionedTriangleAbsorption.RefinerObstruction

