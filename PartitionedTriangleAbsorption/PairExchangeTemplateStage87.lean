/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairExchangeStage86

/-! # The 27-edge exchange template as a rooted graph

The template contains only the 27 edges of `PairExchangeStage86.added`.
The six roots `0..5` span no template edge; the four old source edges are
supplied separately by the configuration. The parent lists below are the
exact rooted order used by the producer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairExchangeTemplateStage87

open Finset PairExchangeStage86

/-- The simple graph on fourteen positions whose edges are exactly `added`. -/
def tmpl : SimpleGraph (Fin 14) where
  Adj i j := i ≠ j ∧ s(i, j) ∈ added
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel tmpl.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ s(i, j) ∈ added))

/-- No edge of `added` is a loop, so the template edge set is all of `added`. -/
theorem added_not_diag : ∀ e ∈ added, ¬ e.IsDiag := by
  unfold added H₁ H₂ H₃ R₁ R₂ R₃ PairMoveStage85.gadget PairMoveStage85.target
    first second third PhysicalHingeSupply.edgeEmb
  decide

theorem mem_added_iff (i j : Fin 14) : s(i, j) ∈ added ↔ tmpl.Adj i j := by
  constructor
  · intro h
    exact ⟨fun hij => added_not_diag _ h (by simp [hij]), h⟩
  · exact fun h => h.2

/-- The six roots span no template edge. -/
theorem roots_independent : ∀ i j : Fin 14, i.val < 6 → j.val < 6 → ¬ tmpl.Adj i j := by
  unfold tmpl added H₁ H₂ H₃ R₁ R₂ R₃ PairMoveStage85.gadget PairMoveStage85.target
    first second third PhysicalHingeSupply.edgeEmb
  decide

/-- Every nonroot has at most four earlier template neighbours. -/
theorem order_budget : ∀ j : Fin 14, 6 ≤ j.val →
    (univ.filter (fun i : Fin 14 => i.val < j.val ∧ tmpl.Adj i j)).card ≤ 4 := by
  intro j _
  have h := parent_budget j
  convert h using 3
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (mem_added_iff _ _).mp h2 |>.1, h2⟩

/-- The exact ordered parent lists:
`6:{2,3,4,5}, 7:{3,5}, 8:{0,2,6}, 9:{0,3,6,8}, 10:{1,4,6}, 11:{1,5,6,10},
12:{3,6,7}, 13:{5,6,7,12}`. -/
theorem parent_pairs : ∀ i j : Fin 14, i < j → tmpl.Adj i j →
    (i, j) ∈ ({(2, 6), (3, 6), (4, 6), (5, 6), (3, 7), (5, 7),
      (0, 8), (2, 8), (6, 8), (0, 9), (3, 9), (6, 9), (8, 9),
      (1, 10), (4, 10), (6, 10), (1, 11), (5, 11), (6, 11), (10, 11),
      (3, 12), (6, 12), (7, 12), (5, 13), (6, 13), (7, 13), (12, 13)} :
      Finset (Fin 14 × Fin 14)) := by
  unfold tmpl added H₁ H₂ H₃ R₁ R₂ R₃ PairMoveStage85.gadget PairMoveStage85.target
    first second third PhysicalHingeSupply.edgeEmb
  decide

/-- The two initial source pairs of the exchange. -/
theorem initial_eq : initial = {s(0, 2), s(0, 3), s(1, 4), s(1, 5)} := by
  unfold initial Q₁ Q₂ PairMoveStage85.source first second PhysicalHingeSupply.edgeEmb
  decide

theorem host_sdiff_initial : host \ initial ⊆ added := by
  intro e he
  rcases mem_union.mp (mem_sdiff.mp he).1 with h | h
  · exact absurd h (mem_sdiff.mp he).2
  · exact h

end PartitionedTriangleAbsorption.PairExchangeTemplateStage87
