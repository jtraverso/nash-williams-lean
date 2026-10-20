/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1RootCountsStage182

/-! # Physical repair of F1 root cones

Requests are computed from the actual residual, not an independent witness.
The root-family supply and selection budget remain explicit. Boundary holes,
joint embeddings of links and confinement are not asserted by this leaf.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1PhysicalConeRepairStage183

open Finset TypedApplicationLinks F1RootCountsStage182 PhysicalRootTrimStage181

variable {V : Type} [DecidableEq V]

theorem surplus_partition (p : V → Fin 4) (E Q : Finset (Sym2 V))
    (hQ : Q ⊆ E) (v : V) :
    surplus p E v = surplus p Q v + surplus p (E \ Q) v := by
  have h := degVec_union p (disjoint_sdiff : Disjoint Q (E \ Q)) v
  rw [union_sdiff_of_subset hQ] at h
  simp only [surplus, h, Pi.add_apply]
  ring

theorem residual_surplus_gain (p : V → Fin 4) (E Q Q' : Finset (Sym2 V))
    (D D' S : Finset (Finset V)) (hD : IsDecomp p F1 Q D)
    (hD' : IsDecomp p F1 Q' D') (hQ : Q ⊆ E) (hQ' : Q' ⊆ Q)
    (hSD : S ⊆ D) (hcut : D' = D \ S) (v : V) :
    surplus p (E \ Q') v = surplus p (E \ Q) v +
      2 * ((singletonFamily p S v).card : ℤ) := by
  classical
  have hsing : singletonFamily p (D \ S) v =
      singletonFamily p D v \ singletonFamily p S v := by
    ext s
    simp only [singletonFamily, mem_filter, mem_sdiff]
    tauto
  have hsub : singletonFamily p S v ⊆ singletonFamily p D v :=
    filter_subset_filter _ hSD
  have hcount : (singletonFamily p D' v).card + (singletonFamily p S v).card =
      (singletonFamily p D v).card := by
    rw [hcut, hsing]
    exact card_sdiff_add_card_eq_card hsub
  have hc : ((singletonFamily p D' v).card : ℤ) + (singletonFamily p S v).card =
      (singletonFamily p D v).card := by exact_mod_cast hcount
  have h1 := (packing_root_counts p Q D hD v).1
  have h2 := (packing_root_counts p Q' D' hD' v).1
  have h3 := surplus_partition p E Q hQ v
  have h4 := surplus_partition p E Q' (hQ'.trans hQ) v
  omega

theorem physical_cone_repair [Fintype V] (p : V → Fin 4)
    (E Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F1 Q D) (hQE : Q ⊆ E) (hI : IsIntDiv p F1 E)
    (hpos : ∃ a : Multiset (Fin 4) → ℕ,
      edgeVec p (E \ Q) = ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ)
    (d K M : ℕ) (hd : 0 < d)
    (hK : ∀ v, (-surplus p (E \ Q) v).toNat ≤ K)
    (hM : ∑ v : V, (-surplus p (E \ Q) v).toNat ≤ M)
    (hsupply : ∀ v, d * (d + K) + 3 * M < d * (singletonFamily p D v).card) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F1 Q' D' ∧
      IsIntDiv p F1 (E \ Q') ∧
      (∃ a : Multiset (Fin 4) → ℕ,
        edgeVec p (E \ Q') = ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ) ∧
      (∀ v, 0 ≤ surplus p (E \ Q') v) ∧
      (∀ v, ((E \ Q').filter fun e => v ∈ e).card ≤
        ((E \ Q).filter fun e => v ∈ e).card + 2 * (d + K)) := by
  classical
  let k := fun v => (-surplus p (E \ Q) v).toNat
  obtain ⟨S, D', Q', hSD, _, hcut, hQ', hD', hI', hpos', hcredit, hdeg⟩ :=
    physical_root_trim p F1 E Q D hD hQE hI hpos univ
      (singletonFamily p D) k d K M
      (fun _ _ => filter_subset _ _)
      (fun _ _ s hs => (mem_filter.mp hs).2.1) hd
      (fun v _ => hK v) hM (fun v _ => hsupply v)
  refine ⟨D', Q', hcut ▸ sdiff_subset, hQ', hD', hI', hpos', ?_, hdeg⟩
  intro v
  have hg := residual_surplus_gain p E Q Q' D D' S hD hD' hQE hQ' hSD hcut v
  have heq : S ∩ singletonFamily p D v = singletonFamily p S v := by
    ext s
    simp only [mem_inter, singletonFamily, mem_filter]
    constructor
    · tauto
    · rintro ⟨hs, hp⟩
      exact ⟨hs, hSD hs, hp⟩
  have hc := hcredit v (mem_univ v)
  rw [heq] at hc
  have hc' : ((-surplus p (E \ Q) v).toNat : ℤ) ≤
      (singletonFamily p S v).card := by exact_mod_cast hc
  omega

end PartitionedTriangleAbsorption.F1PhysicalConeRepairStage183

