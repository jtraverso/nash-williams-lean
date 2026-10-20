/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalRootTrimStage181
public import PartitionedTriangleAbsorption.ReserveCoverDown

/-! # Retire the actual packing triangles meeting a reserve

The charge counts reserve edges opposite a root separately. A degree bound
on the reserve alone is not a bound on retired packing incidence.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveRetirementStage194

open Finset BalancedTrimStage170 PhysicalRootTrimStage181

variable {V : Type} [DecidableEq V]

noncomputable def touching (D : Finset (Finset V)) (X : Finset (Sym2 V)) :
    Finset (Finset V) := by
  classical
  exact D.filter fun s => ¬ Disjoint (triEdges s) X

noncomputable def incidentHits (D : Finset (Finset V)) (X : Finset (Sym2 V))
    (v : V) : Finset (Finset V) := by
  classical
  exact D.filter fun s => v ∈ s ∧ ∃ e ∈ triEdges s, e ∈ X ∧ v ∈ e

noncomputable def oppositeHits (D : Finset (Finset V)) (X : Finset (Sym2 V))
    (v : V) : Finset (Finset V) := by
  classical
  exact D.filter fun s => v ∈ s ∧ ∃ e ∈ triEdges s, e ∈ X ∧ v ∉ e

theorem incident_hits_le {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (X : Finset (Sym2 V)) (v : V) :
    (incidentHits D X v).card ≤ (X.filter fun e => v ∈ e).card := by
  classical
  let A := incidentHits D X v
  have hex : ∀ s ∈ A, ∃ e ∈ X.filter (fun e => v ∈ e), e ∈ triEdges s := by
    intro s hs
    obtain ⟨_, _, e, he, heX, hev⟩ := mem_filter.mp hs
    exact ⟨e, mem_filter.mpr ⟨heX, hev⟩, he⟩
  let f : A → (X.filter fun e => v ∈ e) := fun s =>
    ⟨Classical.choose (hex s.val s.property),
      (Classical.choose_spec (hex s.val s.property)).1⟩
  have hf : Function.Injective f := by
    intro s s' heq
    apply Subtype.ext
    by_contra hne
    have h₁ := Classical.choose_spec (hex s.val s.property)
    have h₂ := Classical.choose_spec (hex s'.val s'.property)
    have heq' := congrArg Subtype.val heq
    change Classical.choose (hex s.val s.property) =
      Classical.choose (hex s'.val s'.property) at heq'
    have hdis := hD.2.1 (mem_filter.mp s.property).1 (mem_filter.mp s'.property).1 hne
    rw [← heq'] at h₂
    exact disjoint_left.mp hdis h₁.2 h₂.2
  simpa only [Fintype.card_coe, A] using Fintype.card_le_of_injective f hf

theorem touching_incidence_le {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (X : Finset (Sym2 V)) (v : V) :
    incidence (touching D X) v ≤
      (X.filter fun e => v ∈ e).card + (oppositeHits D X v).card := by
  classical
  have hsub : (touching D X).filter (fun s => v ∈ s) ⊆
      incidentHits D X v ∪ oppositeHits D X v := by
    intro s hs
    obtain ⟨hs, hv⟩ := mem_filter.mp hs
    obtain ⟨hsD, htouch⟩ := mem_filter.mp hs
    obtain ⟨e, he, heX⟩ := not_disjoint_iff.mp htouch
    by_cases hev : v ∈ e
    · exact mem_union_left _ (mem_filter.mpr ⟨hsD, hv, e, he, heX, hev⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hsD, hv, e, he, heX, hev⟩)
  calc
    _ ≤ (incidentHits D X v ∪ oppositeHits D X v).card := card_le_card hsub
    _ ≤ (incidentHits D X v).card + (oppositeHits D X v).card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (incident_hits_le p F Q D hD X v) _

theorem retire_reserve {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q X : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (hQE : Q ⊆ E)
    (hI : IsIntDiv p F E)
    (hpos : ∃ a : Multiset (Fin t) → ℕ,
      edgeVec p (E \ Q) = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ) :
    ∃ D' Q', D' = D \ touching D X ∧ Q' = D'.biUnion triEdges ∧
      D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F Q' D' ∧ Disjoint Q' X ∧
      IsIntDiv p F (E \ Q') ∧
      (∃ a : Multiset (Fin t) → ℕ,
        edgeVec p (E \ Q') = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ) ∧
      (∀ v, ((E \ Q').filter fun e => v ∈ e).card ≤
        ((E \ Q).filter fun e => v ∈ e).card +
          2 * ((X.filter fun e => v ∈ e).card + (oppositeHits D X v).card)) := by
  classical
  let S := touching D X
  let D' := D \ S
  let Q' := D'.biUnion triEdges
  have hsub : D' ⊆ D := sdiff_subset
  have hD' : IsDecomp p F Q' D' :=
    ⟨fun s hs => hD.1 s (hsub hs), hD.2.1.subset hsub, rfl⟩
  have hQ' : Q' ⊆ Q := by
    rw [← hD.2.2]
    exact biUnion_subset_biUnion_of_subset_left triEdges hsub
  have hdiff : D \ D' = S := by
    have hS : S ⊆ D := filter_subset _ _
    ext s
    simp only [D', mem_sdiff]
    aesop
  have hdis : Disjoint Q' X := by
    apply disjoint_left.mpr
    intro e he heX
    obtain ⟨s, hs, he⟩ := mem_biUnion.mp he
    have hs' := mem_sdiff.mp hs
    have ht : ¬ Disjoint (triEdges s) X := not_disjoint_iff.mpr ⟨e, he, heX⟩
    exact hs'.2 (mem_filter.mpr ⟨hs'.1, ht⟩)
  refine ⟨D', Q', rfl, rfl, hsub, hQ', hD', hdis,
    isIntDiv_sdiff_of_hasDecomp hI ⟨D', hD'⟩ (hQ'.trans hQE),
    natural_quotas_after_subpacking p F E Q Q' D D' hD hD' hsub hQE
      (hQ'.trans hQE) hpos, ?_⟩
  intro v
  have h := residual_degree_after_subpacking p F E Q Q' D D' hD hD' hsub v
  rw [hdiff] at h
  have hc := touching_incidence_le p F Q D hD X v
  change incidence S v ≤ _ at hc
  omega


end PartitionedTriangleAbsorption.ReserveRetirementStage194
