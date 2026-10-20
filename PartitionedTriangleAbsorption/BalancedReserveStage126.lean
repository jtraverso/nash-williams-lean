/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BalancedBaseStage126
public import PartitionedTriangleAbsorption.BalancedSelectionStage126

/-! # Physical reserve with simultaneous query richness and inner balance

The packing and the thinning are both constructed here. The category budget
is not supplied as an assumption about an unspecified reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQuotaPackingStage124

open Finset AntiEdgeSelection CoverDownStage105 ReserveQueryGeometryStage123
open F3ReserveTrimStage109

variable {V Q : Type*} [Finite V] [DecidableEq V] [Fintype Q]

theorem exists_produced_balanced_reserve (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (X W : Finset V) (F B : Finset (Sym2 V)) (f d L q b a : ℕ)
    (hF : ∀ v, incidentLoad F v ≤ f) (hB : ∀ v, incidentLoad B v ≤ d)
    (hG : ∀ u v, p u ≠ p v → s(u, v) ∉ F → G.Adj u v)
    (hpart : ∀ c, b + 2 * f ≤ (W.filter fun w => p w = c).card)
    (hXW : Disjoint X W)
    (hquota : 2 * (3 * X.card * L) + 2 * (d + 2 * (3 * L + q)) * q < b * q)
    (x y z : Q → V) (hx : ∀ j, x j ∈ X) (hy : ∀ j, y j ≠ x j)
    (hz : ∀ j, z j ≠ x j) (ha : 0 < a) (hsupply : a + 2 * (f + d) + 2 ≤ L)
    (t : ℝ) (ht : 0 ≤ t) (hM : 0 < X.card * L)
    (hprob : (Fintype.card Q : ℝ) * Real.exp (-(a : ℝ) / 1536) +
      6 * Real.exp (-2 * t ^ 2 / (X.card * L)) < 1) :
    ∃ T : Finset (V × V × V),
      (T : Set (V × V × V)).PairwiseDisjoint resTri ∧
      (∀ r ∈ T, r.1 ∈ X ∧ r.1 ∉ W ∧ r.2.1 ∈ W ∧ r.2.2 ∈ W ∧
        G.Adj r.1 r.2.1 ∧ G.Adj r.1 r.2.2 ∧ G.Adj r.2.1 r.2.2 ∧
        p r.1 ≠ p r.2.1 ∧ p r.1 ≠ p r.2.2 ∧ p r.2.1 ≠ p r.2.2 ∧
        Disjoint (resTri r) B) ∧
      (∀ v, incidentLoad (resEdges T) v ≤ 2 * (3 * L + q)) ∧
      (∀ c, |((T.filter fun r => category p s(r.2.1, r.2.2) = c).card : ℝ) -
        (X.card * L : ℕ) / 2| ≤ t) ∧
      ∀ j, (a : ℝ) / 192 < ((T.filter fun r : V × V × V =>
        r.1 = x j ∧ G.Adj (y j) r.2.1 ∧ G.Adj r.2.2 (z j) ∧
        s(y j, r.2.1) ∉ F ∪ B ∧ s(r.2.2, z j) ∉ F ∪ B ∧
        Disjoint (connectors (y j) (z j) r) (resEdges T)).card : ℝ) := by
  classical
  obtain ⟨T, hd, _, hphys, hdeg, hcat, hrich⟩ := exists_rich_balanced_base p G X W F B f d L q b
    hF hB hG hpart hXW hquota
  have hr : ∀ j, ∃ R ⊆ T, L ≤ R.card + 2 * (f + d) + 2 ∧
      ∀ r ∈ R, r.1 = x j ∧ G.Adj (y j) r.2.1 ∧ G.Adj r.2.2 (z j) ∧
        s(y j, r.2.1) ∉ F ∪ B ∧ s(r.2.2, z j) ∉ F ∪ B ∧
        Disjoint (connectors (y j) (z j) r) (resTri r) :=
    fun j => hrich (x j) (hx j) (y j) (hy j) (z j) (hz j)
  choose S hST hsize hS using hr
  have hcard : ∀ j, (a : ℝ) ≤ ((S j).card : ℝ) := by
    intro j
    have hj := hsize j
    exact_mod_cast (show a ≤ (S j).card by omega)
  obtain ⟨T', hT', hd', hgood, hc⟩ :=
    BalancedSelectionStage126.exists_balanced_physical_thinning T hd S x y z hST
      (fun j r hr => (hS j r hr).1) (fun j r hr => (hS j r hr).2.2.2.2.2)
      (fun r => category p s(r.2.1, r.2.2)) (X.card * L) hM hcat
      a t (by exact_mod_cast ha) ht hcard (by simpa only [Nat.cast_mul] using hprob)
  refine ⟨T', hd', fun r hr => hphys r (hT' hr), ?_, hc, ?_⟩
  · intro v
    exact (incidentLoad_mono (resEdges_mono hT') v).trans (hdeg v)
  · intro j
    apply (hgood j).trans_le
    apply Nat.cast_le.mpr
    apply card_le_card
    intro r hr
    obtain ⟨hrT, hrS, hrD⟩ := mem_filter.mp hr
    obtain ⟨hrx, hey, hez, hFy, hFz, _⟩ := hS j r hrS
    exact mem_filter.mpr ⟨hrT, hrx, hey, hez, hFy, hFz, hrD⟩

end PartitionedTriangleAbsorption.RootQuotaPackingStage124



