/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BaseCategoriesStage126

/-! # Balanced output of the physical slot constructor

This strengthens the frozen Stage124 interface by exporting the exact category
counts of the same packing. No balance hypothesis on the roots is added.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQuotaPackingStage124

open Finset AntiEdgeSelection CoverDownStage105 ReserveQueryGeometryStage123
open F3ReserveTrimStage109

variable {V : Type*} [DecidableEq V]

theorem exists_rich_balanced_base [Finite V] (p : V → Fin 4) (G : SimpleGraph V)
    (X W : Finset V) (F B : Finset (Sym2 V))
    (f d L q b : ℕ) (hF : ∀ x, incidentLoad F x ≤ f)
    (hB : ∀ x, incidentLoad B x ≤ d)
    (hG : ∀ x y, p x ≠ p y → s(x, y) ∉ F → G.Adj x y)
    (hpart : ∀ c, b + 2 * f ≤ (W.filter fun w => p w = c).card)
    (hXW : Disjoint X W)
    (hbudget : 2 * (3 * X.card * L) + 2 * (d + 2 * (3 * L + q)) * q < b * q) :
    ∃ T : Finset (V × V × V),
      (T : Set (V × V × V)).PairwiseDisjoint resTri ∧
      T.card = 3 * X.card * L ∧
      (∀ r ∈ T, r.1 ∈ X ∧ r.1 ∉ W ∧ r.2.1 ∈ W ∧ r.2.2 ∈ W ∧
        G.Adj r.1 r.2.1 ∧ G.Adj r.1 r.2.2 ∧ G.Adj r.2.1 r.2.2 ∧
        p r.1 ≠ p r.2.1 ∧ p r.1 ≠ p r.2.2 ∧ p r.2.1 ≠ p r.2.2 ∧
        Disjoint (resTri r) B) ∧
      (∀ v, incidentLoad (resEdges T) v ≤ 2 * (3 * L + q)) ∧
      (∀ c, (T.filter fun r => category p s(r.2.1, r.2.2) = c).card = X.card * L) ∧
      ∀ x ∈ X, ∀ y, y ≠ x → ∀ z, z ≠ x →
        ∃ R ⊆ T, L ≤ R.card + 2 * (f + d) + 2 ∧
          ∀ r ∈ R, r.1 = x ∧ G.Adj y r.2.1 ∧ G.Adj r.2.2 z ∧
            s(y, r.2.1) ∉ F ∪ B ∧ s(r.2.2, z) ∉ F ∪ B ∧
            Disjoint (connectors y z r) (resTri r) := by
  classical
  let _ := Fintype.ofFinite V
  let root : Slot X L → V := fun i => i.1.val
  let left : Slot X L → Fin 4 := fun i => pairLeft (p (root i)) i.2.1
  let right : Slot X L → Fin 4 := fun i => pairRight (p (root i)) i.2.1
  have hslots : (univ : Finset (Slot X L)).card = 3 * X.card * L := by
    simp [Slot, Nat.mul_comm, Nat.mul_left_comm]
  obtain ⟨a, c, hac, hd, hq⟩ := exists_dense_packing p G W F B f d (3 * L) q b
    hF hB hG hpart root left right univ
    (fun i _ => pair_types (p (root i)) i.2.1) (slot_root_load X L)
    (by simpa only [hslots] using hbudget)
  let T := triples univ root a c
  have hT := triples_disjoint univ root a c hd
  refine ⟨T, hT, (triples_card univ root a c hd).trans hslots, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, _, rfl⟩ := mem_image.mp hr
    obtain ⟨haW, hcW, hua, huc, hca, hpa, hpc, hdis⟩ := hac i (mem_univ _)
    have ht := pair_types (p (root i)) i.2.1
    change p (root i) ≠ left i ∧ p (root i) ≠ right i ∧ left i ≠ right i at ht
    exact ⟨i.1.property, fun h => disjoint_left.mp hXW i.1.property h,
      haW, hcW, hua, huc, hca,
      by simpa [hpa] using ht.1, by simpa [hpc] using ht.2.1,
      by simpa [hpa, hpc] using ht.2.2, hdis⟩
  · intro v
    rw [triples_edges]
    exact (packing_incident_le univ root a c v).trans
      (Nat.mul_le_mul_left 2 (Nat.add_le_add (slot_root_load X L v) (hq v)))
  · intro k
    exact physical_slot_category_card p X L a c
      (fun i => (hac i (mem_univ _)).2.2.2.2.2.1)
      (fun i => (hac i (mem_univ _)).2.2.2.2.2.2.1) hd k
  · intro x hx y hy z hz
    obtain ⟨j, hjy, hjz⟩ := pair_query (p x) (p y) (p z)
    let P : V × V × V → Prop := fun r => r.1 = x ∧
      p r.2.1 = pairLeft (p x) j ∧ p r.2.2 = pairRight (p x) j
    let S := T.filter P
    have hST : S ⊆ T := filter_subset _ _
    have hsize : L ≤ S.card := by
      rw [show S.card = (univ.filter fun i => P (root i, a i, c i)).card from
        triples_query_card univ root a c hd P]
      have hc : (univ : Finset (Fin L)).card ≤
          (univ.filter fun i => P (root i, a i, c i)).card := by
        apply card_le_card_of_injOn (fun l : Fin L => ((⟨x, hx⟩, j, l) : Slot X L))
        · intro l _
          have hi := hac ((⟨x, hx⟩, j, l) : Slot X L) (mem_univ _)
          exact mem_filter.mpr ⟨mem_univ _, rfl, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2.1⟩
        · intro i _ j' _ h
          exact congrArg (fun i : Slot X L => i.2.2) h
      simpa using hc
    have hFB : ∀ v, incidentLoad (F ∪ B) v ≤ f + d := fun v =>
      (incidentLoad_union_le F B v).trans (Nat.add_le_add (hF v) (hB v))
    obtain ⟨R, hRS, hcard, hR⟩ := raw_query p G (F ∪ B) (f + d) hFB
      (fun u v hcol hnot => hG u v hcol (fun h => hnot (mem_union_left _ h)))
      S (hT.subset hST) x y z hy hz (by
        intro r hr
        obtain ⟨_, hrx, hrl, hrr⟩ := mem_filter.mp hr
        refine ⟨hrx, ?_, ?_⟩
        · simpa [hrl] using hjy
        · simpa [hrr] using hjz)
    exact ⟨R, hRS.trans hST, hsize.trans hcard, hR⟩

end PartitionedTriangleAbsorption.RootQuotaPackingStage124



