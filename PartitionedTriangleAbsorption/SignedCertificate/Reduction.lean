/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Basic

/-! # Two-mode solutions, absorbers and simple certificates

For a physical source `P`, a *two-mode solution* is a pair `(A, Q)` of edge sets with
`P, A, Q` pairwise disjoint, `Q` F0-decomposable and both `A ∪ P` and `A ∪ Q`
F0-decomposable (the *same* `A`). An *absorber* is an edge set `A` disjoint from `P` with
`A` and `A ∪ P` both F0-decomposable.

* `twoMode_of_absorber`: an absorber plus any decomposable `Q` disjoint from it gives a
  two-mode solution;
* `absorber_of_twoMode`: a two-mode solution `(A, Q)` gives the absorber `A ∪ Q`;
* `signedCert_of_absorber`: an absorber inside `G` gives a *simple* signed certificate of
  `P` (coefficients `±1`, positive triangles edge-disjoint, negative triangles
  edge-disjoint).

Thus the common-`A` problem is exactly the existence of a bounded absorber; the
destination `Q` is a free decomposable add-on. The part-pair counts of `Q` are **not**
forced by the two modes (see `SignedCertificate.Controls.typeCounts_not_forced`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

/-- `A` is an F0 absorber for `P`. -/
def IsAbsorber (p : V → Fin 2) (P A : Finset (Sym2 V)) : Prop :=
  Disjoint A P ∧ HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P)

/-- `(A, Q)` is a two-mode solution for `P` (no size or physical conditions). -/
def IsTwoMode (p : V → Fin 2) (P A Q : Finset (Sym2 V)) : Prop :=
  Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧ HasDecomp p F0 Q ∧
    HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q)

omit [DecidableEq V] in
theorem triEdges_nonempty_of_typed {p : V → Fin 2} {s : Finset V}
    (hs : IsTypedTri p F0 s) [DecidableEq V] : (triEdges s).Nonempty := by
  obtain ⟨a, b, c, hab, -, -, rfl⟩ := Finset.card_eq_three.mp hs.1
  exact ⟨s(a, b), by simp [triEdges, hab]⟩

/-- Union of decompositions of two disjoint edge sets. -/
theorem hasDecomp_union {p : V → Fin 2} {E₁ E₂ : Finset (Sym2 V)}
    (h₁ : HasDecomp p F0 E₁) (h₂ : HasDecomp p F0 E₂) (hd : Disjoint E₁ E₂) :
    HasDecomp p F0 (E₁ ∪ E₂) := by
  obtain ⟨D₁, hT₁, hP₁, hU₁⟩ := h₁
  obtain ⟨D₂, hT₂, hP₂, hU₂⟩ := h₂
  refine ⟨D₁ ∪ D₂, ?_, ?_, ?_⟩
  · intro s hs
    rcases mem_union.mp hs with h | h
    · exact hT₁ s h
    · exact hT₂ s h
  · have hsub₁ : ∀ s ∈ D₁, triEdges s ⊆ E₁ := fun s hs => hU₁ ▸ subset_biUnion_of_mem _ hs
    have hsub₂ : ∀ s ∈ D₂, triEdges s ⊆ E₂ := fun s hs => hU₂ ▸ subset_biUnion_of_mem _ hs
    intro s hs u hu hsu
    simp only [coe_union, Set.mem_union, mem_coe] at hs hu
    rcases hs with hs | hs <;> rcases hu with hu | hu
    · exact hP₁ hs hu hsu
    · exact hd.mono (hsub₁ s hs) (hsub₂ u hu)
    · exact (hd.mono (hsub₁ u hu) (hsub₂ s hs)).symm
    · exact hP₂ hs hu hsu
  · rw [union_biUnion, hU₁, hU₂]

/-- **Absorber ⇒ two-mode solution**, for any decomposable `Q` disjoint from `A ∪ P`. -/
theorem twoMode_of_absorber {p : V → Fin 2} {P A Q : Finset (Sym2 V)}
    (hA : IsAbsorber p P A) (hQ : HasDecomp p F0 Q) (hQd : Disjoint Q (A ∪ P)) :
    IsTwoMode p P A Q := by
  have h1 := disjoint_union_right.mp hQd
  exact ⟨hA.1.symm, h1.2.symm, h1.1.symm, hQ, hA.2.2, hasDecomp_union hA.2.1 hQ h1.1.symm⟩

/-- **Two-mode solution ⇒ absorber** `A ∪ Q`. -/
theorem absorber_of_twoMode {p : V → Fin 2} {P A Q : Finset (Sym2 V)}
    (h : IsTwoMode p P A Q) : IsAbsorber p P (A ∪ Q) := by
  obtain ⟨hPA, hPQ, hAQ, hQ, hAP, hAQd⟩ := h
  refine ⟨disjoint_union_left.mpr ⟨hPA.symm, hPQ.symm⟩, hAQd, ?_⟩
  have : A ∪ Q ∪ P = (A ∪ P) ∪ Q := by
    ext e; simp only [mem_union]; tauto
  rw [this]
  exact hasDecomp_union hAP hQ (disjoint_union_left.mpr ⟨hAQ, hPQ⟩)

/-- **Positive control.** An F0-decomposable source has the empty absorber. -/
theorem absorber_empty_of_hasDecomp {p : V → Fin 2} {P : Finset (Sym2 V)}
    (h : HasDecomp p F0 P) : IsAbsorber p P ∅ :=
  ⟨disjoint_empty_left _, ⟨∅, by simp, by simp, by simp⟩, by simpa using h⟩

/-- In an F0 decomposition every edge lies in exactly the triangle-count prescribed by the
indicator. -/
theorem sum_ind_of_isDecomp {p : V → Fin 2} {E : Finset (Sym2 V)} {D : Finset (Finset V)}
    (h : IsDecomp p F0 E D) (e : Sym2 V) : ∑ s ∈ D, ind (triEdges s) e = ind E e := by
  obtain ⟨-, hP, hU⟩ := h
  have hcount : ∑ s ∈ D, ind (triEdges s) e = ((D.filter fun s => e ∈ triEdges s).card : ℤ) := by
    simp only [ind]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  rw [hcount]
  by_cases he : e ∈ E
  · rw [ind, ite_eq_left he]
    rw [← hU, mem_biUnion] at he
    obtain ⟨s, hs, hes⟩ := he
    have : D.filter (fun s => e ∈ triEdges s) = {s} := by
      ext u
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hu, heu⟩
        by_contra hne
        exact disjoint_left.mp (hP hu hs hne) heu hes
      · rintro rfl; exact ⟨hs, hes⟩
    rw [this]; simp
  · rw [ind, ite_eq_right he]
    have : D.filter (fun s => e ∈ triEdges s) = ∅ := by
      ext u
      simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hu heu
      exact he (hU ▸ mem_biUnion.mpr ⟨u, hu, heu⟩)
    rw [this]; simp

omit [DecidableEq V] in
theorem isNClique_of_triEdges_subset [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} (hs : s.card = 3) (hsub : triEdges s ⊆ G.edgeFinset) :
    G.IsNClique 3 s := by
  refine ⟨?_, hs⟩
  intro a ha b hb hab
  have : s(a, b) ∈ triEdges s := by
    simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    exact ⟨⟨ha, hb⟩, hab⟩
  have := hsub this
  simpa using this

/-- **Absorber ⇒ simple signed certificate.** If `A` is an absorber for `P` inside `G`,
the triangles of a decomposition of `A ∪ P` (coefficient `+1`) and of `A` (coefficient
`-1`) form a signed physical certificate of `P` of weight `(|A ∪ P| + |A|) / 3`. -/
theorem signedCert_of_absorber [Fintype V] (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] {P A : Finset (Sym2 V)} (hA : IsAbsorber p P A)
    (hG : A ∪ P ⊆ G.edgeFinset) :
    ∃ (Dp Dm : Finset (Finset V)),
      IsSignedCert p G P (Sum.elim (fun s : Dp => (s : Finset V)) (fun s : Dm => (s : Finset V)))
        (Sum.elim (fun _ => 1) (fun _ => -1)) ∧
      IsDecomp p F0 (A ∪ P) Dp ∧ IsDecomp p F0 A Dm := by
  obtain ⟨hd, ⟨Dm, hDm⟩, ⟨Dp, hDp⟩⟩ := hA
  refine ⟨Dp, Dm, ⟨?_, ?_⟩, hDp, hDm⟩
  · have hcopy : ∀ (D : Finset (Finset V)) (E : Finset (Sym2 V)), IsDecomp p F0 E D →
        E ⊆ G.edgeFinset → ∀ s ∈ D, IsCopy p F0 G s := by
      intro D E hD hE s hs
      refine ⟨isNClique_of_triEdges_subset (hD.1 s hs).1 ?_, (hD.1 s hs).2⟩
      exact (hD.2.2 ▸ subset_biUnion_of_mem triEdges hs).trans hE
    rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · exact hcopy Dp _ hDp hG s hs
    · exact hcopy Dm _ hDm (subset_union_left.trans hG) s hs
  · intro e
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_coe_sort Dp (fun s => ind (triEdges s) e),
      Finset.sum_coe_sort Dm (fun s => ind (triEdges s) e),
      sum_ind_of_isDecomp hDp e, sum_ind_of_isDecomp hDm e]
    simp only [ind, mem_union]
    by_cases h1 : e ∈ A <;> by_cases h2 : e ∈ P <;>
      simp only [h1, h2, ite_true, ite_false, or_true, or_false] <;> norm_num
    exact False.elim (disjoint_left.mp hd h1 h2)

end PartitionedTriangleAbsorption.SignedCertificate
