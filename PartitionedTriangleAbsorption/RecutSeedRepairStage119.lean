/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TwoSidedRestrictionStage119
public import PartitionedTriangleAbsorption.QuantitativeSeedRepairStage111

/-! # Repair a two-sided approximate seed after the actual recut

The structural hypothesis is still a complete four-class host minus a
small-degree edge set. The recut contributes its real lost-copy error;
balance alone is not promoted to positivity or an exact seed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RecutSeedRepairStage119

open Finset TypedLoadNecessity TypedApplicationLinks FourClassCopyAdapterStage74
  CoverDownStage105 QuantitativeSeedRepairStage111

theorem window_abs_bound (C E n x : ℝ) (hC : 1 ≤ C) (hn : 0 < n)
    (hE : E ≤ 1 / (2 * C))
    (hlo : (1 / C - E) / n ≤ x) (hhi : x ≤ (C + E) / n) :
    |x| ≤ 2 * C / n := by
  have hCp : 0 < C := by linarith
  have hhalf : 1 / (2 * C) ≤ C := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
    nlinarith
  have hhalf' : 1 / (2 * C) ≤ 1 / C := by
    have heq : 1 / C = 2 * (1 / (2 * C)) := by field_simp
    have hp : 0 ≤ 1 / (2 * C) := by positivity
    linarith
  have hx : 0 ≤ x := (div_nonneg (by linarith) hn.le).trans hlo
  rw [abs_of_nonneg hx]
  exact hhi.trans (div_le_div_of_nonneg_right (by linarith) hn.le)

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem repair_recut (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (B Y Z : Finset (Sym2 V))
    (hZ : Z = B ∪ Y)
    (γ C δ ρ ε E : ℝ) (hγ : 0 < γ) (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hn : 0 < Fintype.card V)
    (hsmall : 72 * δ ≤ γ ^ 3)
    (hsize : ∀ i, γ * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hBY : DegBounded Z (δ * Fintype.card V))
    (hY : DegBounded Y (ρ * Fintype.card V))
    (hbal : ∀ k : Fin 2, bal p k (G.deleteEdges Z).edgeFinset = 0)
    (hmargin : E + 36 * (ε + 4 * C * ρ) / γ ^ 3 ≤ 1 / (2 * C))
    (φ : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F3 (G.deleteEdges B) s →
      (1 / C - E) / Fintype.card V ≤ φ s ∧ φ s ≤ (C + E) / Fintype.card V)
    (hl : ∀ e ∈ (G.deleteEdges B).edgeFinset,
      |1 - edgeLoad p F3 (G.deleteEdges B) φ e| ≤ ε) :
    ∃ ψ : Finset V → ℝ,
      (∀ s, |ψ s - φ s| ≤ 36 * (ε + 4 * C * ρ) / (γ ^ 3 * Fintype.card V)) ∧
      (∀ s, IsCopy p F3 (G.deleteEdges Z) s →
        (1 / C - (E + 36 * (ε + 4 * C * ρ) / γ ^ 3)) / Fintype.card V ≤ ψ s ∧
        ψ s ≤ (C + (E + 36 * (ε + 4 * C * ρ) / γ ^ 3)) / Fintype.card V) ∧
      IsRegularAlmostPacking p F3 (G.deleteEdges Z) (2 * C) 0 ψ := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hCp : 0 < C := by linarith
  have hcost : 0 ≤ 36 * (ε + 4 * C * ρ) / γ ^ 3 := by positivity
  have hE : E ≤ 1 / (2 * C) := by linarith
  have habs : ∀ s, IsCopy p F3 (G.deleteEdges B) s →
      |φ s| ≤ 2 * C / Fintype.card V := by
    intro s hs
    exact window_abs_bound C E (Fintype.card V) (φ s) hC hnR hE
      (hw s hs).1 (hw s hs).2
  have hsub : G.deleteEdges Z ≤ G.deleteEdges B := by
    intro u v huv
    obtain ⟨huv, hnot⟩ := SimpleGraph.deleteEdges_adj.mp huv
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨huv, fun hb => hnot ?_⟩
    change s(u, v) ∈ Z
    rw [hZ]
    exact mem_union_left Y hb
  have hremoved : ∀ a b, (G.deleteEdges B).Adj a b →
      ¬ (G.deleteEdges Z).Adj a b → s(a, b) ∈ Y := by
    intro a b hab hnot
    obtain ⟨hab, hB⟩ := SimpleGraph.deleteEdges_adj.mp hab
    change s(a, b) ∉ B at hB
    by_contra hY'
    apply hnot
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hab, ?_⟩
    change s(a, b) ∉ Z
    simpa only [hZ, mem_union, not_or] using And.intro hB hY'
  have he := TwoSidedRestrictionStage119.error_restrict p F3 (G.deleteEdges B)
    (G.deleteEdges Z) Y hsub hremoved φ ε (ρ * Fintype.card V)
    (2 * C / Fintype.card V) (by positivity) hY habs hl
  have hfactor : 2 * (ρ * Fintype.card V) * (2 * C / Fintype.card V) = 4 * C * ρ := by
    field_simp
    ring
  simp only [hfactor] at he
  obtain ⟨ψ, hchange, hload⟩ := repair_with_explicit_error p G hG Z
    γ (ε + 4 * C * ρ) δ hγ (by positivity) hδ hsmall hn hsize hBY φ he hbal
  have hwin : ∀ s, IsCopy p F3 (G.deleteEdges Z) s →
      (1 / C - (E + 36 * (ε + 4 * C * ρ) / γ ^ 3)) / Fintype.card V ≤ ψ s ∧
      ψ s ≤ (C + (E + 36 * (ε + 4 * C * ρ) / γ ^ 3)) / Fintype.card V := by
    intro s hs
    obtain ⟨hlo, hhi⟩ := hw s ⟨hs.1.mono hsub, hs.2⟩
    have hc := abs_le.mp (hchange s)
    have heq : 36 * (ε + 4 * C * ρ) / (γ ^ 3 * Fintype.card V) =
        (36 * (ε + 4 * C * ρ) / γ ^ 3) / Fintype.card V := by ring
    rw [heq] at hc
    constructor
    · calc
        _ = (1 / C - E) / Fintype.card V -
            (36 * (ε + 4 * C * ρ) / γ ^ 3) / Fintype.card V := by ring
        _ ≤ ψ s := by linarith
    · calc
        ψ s ≤ (C + E) / Fintype.card V +
            (36 * (ε + 4 * C * ρ) / γ ^ 3) / Fintype.card V := by linarith
        _ = _ := by ring
  exact ⟨ψ, hchange, hwin,
    regular_of_window p _ C _ hC hn hmargin ψ hwin hload⟩

end PartitionedTriangleAbsorption.RecutSeedRepairStage119
