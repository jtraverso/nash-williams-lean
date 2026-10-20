/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1UniformConeStage189

/-! # Physical repair of the F1 boundary-parity hole

Retire one paired-root triangle per root, with the balanced root selector.
Every own-label residual degree becomes positive. The already repaired cones,
global natural quotas and divisibility survive on the same subpacking.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1BoundaryRepairStage190

open Finset TypedApplicationLinks F1RootCountsStage182 F1PhysicalConeRepairStage183
open PhysicalRootTrimStage181

variable {V : Type} [DecidableEq V]

theorem same_degree_gain (p : V → Fin 4) (E Q Q' : Finset (Sym2 V))
    (D D' S : Finset (Finset V)) (hD : IsDecomp p F1 Q D)
    (hD' : IsDecomp p F1 Q' D') (hQ : Q ⊆ E) (hQ' : Q' ⊆ Q)
    (hSD : S ⊆ D) (hcut : D' = D \ S) (v : V) :
    degVec p (E \ Q') v (p v) = degVec p (E \ Q) v (p v) +
      ((pairedFamily p S v).card : ℤ) := by
  classical
  have hpair : pairedFamily p (D \ S) v =
      pairedFamily p D v \ pairedFamily p S v := by
    ext s
    simp only [pairedFamily, mem_filter, mem_sdiff]
    tauto
  have hsub : pairedFamily p S v ⊆ pairedFamily p D v := filter_subset_filter _ hSD
  have hcount : (pairedFamily p D' v).card + (pairedFamily p S v).card =
      (pairedFamily p D v).card := by
    rw [hcut, hpair]
    exact card_sdiff_add_card_eq_card hsub
  have hc : ((pairedFamily p D' v).card : ℤ) + (pairedFamily p S v).card =
      (pairedFamily p D v).card := by exact_mod_cast hcount
  have h1 := (packing_root_counts p Q D hD v).2
  have h2 := (packing_root_counts p Q' D' hD' v).2
  have h3 := congrFun (degVec_union p (disjoint_sdiff : Disjoint Q (E \ Q)) v) (p v)
  rw [union_sdiff_of_subset hQ] at h3
  have h4 := congrFun (degVec_union p (disjoint_sdiff : Disjoint Q' (E \ Q')) v) (p v)
  rw [union_sdiff_of_subset (hQ'.trans hQ)] at h4
  simp only [Pi.add_apply] at h3 h4
  omega

theorem physical_boundary_repair [Fintype V] (p : V → Fin 4)
    (E Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F1 Q D) (hQE : Q ⊆ E) (hI : IsIntDiv p F1 E)
    (hpos : ∃ a : Multiset (Fin 4) → ℕ,
      edgeVec p (E \ Q) = ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ)
    (hcones : ∀ v, 0 ≤ surplus p (E \ Q) v)
    (d : ℕ) (hd : 0 < d)
    (hsupply : ∀ v, d * (d + 1) + 3 * Fintype.card V < d * (pairedFamily p D v).card) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F1 Q' D' ∧
      IsIntDiv p F1 (E \ Q') ∧
      (∃ a : Multiset (Fin 4) → ℕ,
        edgeVec p (E \ Q') = ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ) ∧
      (∀ v, 0 ≤ surplus p (E \ Q') v) ∧
      (∀ v, 0 < degVec p (E \ Q') v (p v)) ∧
      (∀ v, ((E \ Q').filter fun e => v ∈ e).card ≤
        ((E \ Q).filter fun e => v ∈ e).card + 2 * (d + 1)) := by
  classical
  obtain ⟨S, D', Q', hSD, _, hcut, hQ', hD', hI', hpos', hcredit, hdeg⟩ :=
    physical_root_trim p F1 E Q D hD hQE hI hpos univ (pairedFamily p D)
      (fun _ => 1) d 1 (Fintype.card V)
      (fun _ _ => filter_subset _ _)
      (fun _ _ s hs => (mem_filter.mp hs).2.1) hd
      (fun _ _ => le_refl 1) (by simp) (fun v _ => hsupply v)
  refine ⟨D', Q', hcut ▸ sdiff_subset, hQ', hD', hI', hpos', ?_, ?_, hdeg⟩
  · intro v
    have h := residual_surplus_gain p E Q Q' D D' S hD hD' hQE hQ' hSD hcut v
    have hn : (0 : ℤ) ≤ (singletonFamily p S v).card := Int.natCast_nonneg _
    linarith [hcones v]
  · intro v
    have h := same_degree_gain p E Q Q' D D' S hD hD' hQE hQ' hSD hcut v
    have heq : S ∩ pairedFamily p D v = pairedFamily p S v := by
      ext s
      simp only [mem_inter, pairedFamily, mem_filter]
      constructor
      · tauto
      · rintro ⟨hs, hp⟩
        exact ⟨hs, hSD hs, hp⟩
    have hc := hcredit v (mem_univ v)
    rw [heq] at hc
    have hn : 0 ≤ degVec p (E \ Q) v (p v) := by
      simp only [degVec, Finset.sum_apply]
      exact sum_nonneg fun e _ => TypedDivisibilityCollapse.degContrib_nonneg p v e (p v)
    omega

end PartitionedTriangleAbsorption.F1BoundaryRepairStage190

