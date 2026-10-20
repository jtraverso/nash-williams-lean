/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootBalancedSelectionStage180

/-! # Root-aware requests realized by discarding actual packing triangles

The same packing is used. Natural global quotas and integral divisibility are
preserved, and the increase in residual degree is controlled pointwise.
Root-family abundance remains an explicit input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalRootTrimStage181

open Finset BalancedTrimStage170 RootBalancedSelectionStage180

variable {V : Type} [DecidableEq V]

theorem root_family_incidence {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V)) (D A : Finset (Finset V))
    (hD : IsDecomp p F Q D) (hA : A ⊆ D) (r : V) (hroot : ∀ s ∈ A, r ∈ s)
    (v : V) (hvr : v ≠ r) : incidence A v ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro s hs s' hs'
  by_contra hne
  have hdis := hD.2.1 (hA (mem_filter.mp hs).1) (hA (mem_filter.mp hs').1) hne
  have he : s(r, v) ∈ triEdges s := TypedNibble.mem_triEdges_iff.mpr
    ⟨hroot s (mem_filter.mp hs).1, (mem_filter.mp hs).2, hvr.symm⟩
  have he' : s(r, v) ∈ triEdges s' := TypedNibble.mem_triEdges_iff.mpr
    ⟨hroot s' (mem_filter.mp hs').1, (mem_filter.mp hs').2, hvr.symm⟩
  exact disjoint_left.mp hdis he he'

theorem natural_quotas_after_subpacking {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q Q' : Finset (Sym2 V))
    (D D' : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (hD' : IsDecomp p F Q' D') (hsub : D' ⊆ D) (hQE : Q ⊆ E) (hQ'E : Q' ⊆ E)
    (hpos : ∃ a : Multiset (Fin t) → ℕ,
      edgeVec p (E \ Q) = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ) :
    ∃ a : Multiset (Fin t) → ℕ,
      edgeVec p (E \ Q') = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ := by
  classical
  obtain ⟨a, ha⟩ := hpos
  let c : Multiset (Fin t) → ℕ := fun τ => a τ + (D.filter fun s => triType p s = τ).card
  have hc : edgeVec p E = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ := by
    have h := edgeVec_union p (disjoint_sdiff : Disjoint Q (E \ Q))
    rw [union_sdiff_of_subset hQE, hD.edgeVec_eq, ha, ← sum_add_distrib] at h
    rw [h]
    apply sum_congr rfl
    intro τ _
    dsimp [c]
    rw [add_smul]
    exact add_comm _ _
  refine ⟨fun τ => c τ - (D'.filter fun s => triType p s = τ).card, ?_⟩
  rw [F1ResidualQuotasStage169.residual_representation p F E Q' D' hD' hQ'E
    (fun τ => (c τ : ℤ)) hc]
  apply sum_congr rfl
  intro τ _
  have hcount : (D'.filter fun s => triType p s = τ).card ≤ c τ := by
    have h := card_le_card (filter_subset_filter (fun s => triType p s = τ) hsub)
    dsimp [c]
    omega
  rw [Nat.cast_sub hcount]

theorem physical_root_trim [Finite V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F Q D) (hQE : Q ⊆ E) (hI : IsIntDiv p F E)
    (hpos : ∃ a : Multiset (Fin t) → ℕ,
      edgeVec p (E \ Q) = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ)
    (R : Finset V) (A : V → Finset (Finset V)) (k : V → ℕ) (d K M : ℕ)
    (hA : ∀ r ∈ R, A r ⊆ D) (hroot : ∀ r ∈ R, ∀ s ∈ A r, r ∈ s)
    (hd : 0 < d) (hK : ∀ r ∈ R, k r ≤ K) (hM : ∑ r ∈ R, k r ≤ M)
    (hsupply : ∀ r ∈ R, d * (d + K) + 3 * M < d * (A r).card) :
    ∃ S D' Q', S ⊆ D ∧ S.card = ∑ r ∈ R, k r ∧ D' = D \ S ∧
      Q' ⊆ Q ∧ IsDecomp p F Q' D' ∧ IsIntDiv p F (E \ Q') ∧
      (∃ a : Multiset (Fin t) → ℕ,
        edgeVec p (E \ Q') = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ) ∧
      (∀ r ∈ R, k r ≤ (S ∩ A r).card) ∧
      (∀ v, ((E \ Q').filter fun e => v ∈ e).card ≤
        ((E \ Q).filter fun e => v ∈ e).card + 2 * (d + K)) := by
  classical
  obtain ⟨S, hSA, hcard, hcap, hcredit⟩ := balanced_roots R A k 1 d K M
    (fun r hr s hs => (hD.1 s (hA r hr hs)).1) hroot
    (fun r hr v hv => root_family_incidence p F Q D (A r) hD (hA r hr) r
      (hroot r hr) v hv) hd hK hM (by simpa using hsupply)
  have hSD : S ⊆ D := by
    intro s hs
    obtain ⟨r, hr, hs⟩ := mem_biUnion.mp (hSA hs)
    exact hA r hr hs
  let D' := D \ S
  let Q' := D'.biUnion triEdges
  have hsub : D' ⊆ D := sdiff_subset
  have hD' : IsDecomp p F Q' D' :=
    ⟨fun s hs => hD.1 s (hsub hs), hD.2.1.subset hsub, rfl⟩
  have hQ' : Q' ⊆ Q := by
    rw [← hD.2.2]
    exact biUnion_subset_biUnion_of_subset_left triEdges hsub
  have hdiff : D \ D' = S := by
    ext s
    simp only [D', mem_sdiff]
    aesop
  refine ⟨S, D', Q', hSD, hcard, rfl, hQ', hD',
    isIntDiv_sdiff_of_hasDecomp hI ⟨D', hD'⟩ (hQ'.trans hQE),
    natural_quotas_after_subpacking p F E Q Q' D D' hD hD' hsub hQE
      (hQ'.trans hQE) hpos, hcredit, ?_⟩
  intro v
  have h := residual_degree_after_subpacking p F E Q Q' D D' hD hD' hsub v
  rw [hdiff] at h
  have hv : incidence S v ≤ d + K := by
    by_cases hvR : v ∈ R
    · have hk := hK v hvR
      have hc := hcap v
      simp only [hvR, ite_true] at hc
      omega
    · have hc := hcap v
      simp only [hvR, ite_false, add_zero] at hc
      omega
  omega

end PartitionedTriangleAbsorption.PhysicalRootTrimStage181

