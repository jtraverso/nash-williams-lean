/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CloneSupply.Basic

/-! # Internal degree from F0 anti-edgefulness

For `x ∈ V_i` pick `z` in the other part and query the F0 type `{i,j,i}` with the
new corner in `V_i`. Every returned anti-edge middle vertex is an internal
neighbour of `x`, so `d_i(x) ≥ α n`. Consequently `α ≤ 1` whenever `n > 0` and a
part is nonempty; `α ≤ 1` is derived, never assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CloneSupply

open Finset

variable {V : Type*} [Fintype V]

/-- **Internal degree.** If the other part `j ≠ i` is nonempty then every
`x ∈ V_i` has at least `α n` neighbours inside `V_i`. -/
theorem internal_degree (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hanti : AntiEdgeful p TypedApplicationLinks.F0 G α)
    (i : Fin 2) (x : V) (hx : p x = i) (z : V) (hz : p z ≠ i) :
    α * (Fintype.card V : ℝ) ≤ (partDeg p G i x : ℝ) := by
  have hxz : x ≠ z := fun h => hz (h ▸ hx)
  have hq := hanti {i, p z, i} (iji_mem_F0 i (p z) (Ne.symm hz)) i (p z) i rfl x z hxz
    hx rfl
  refine hq.trans ?_
  exact_mod_cast card_le_card fun w hw => by
    simp only [mem_filter, mem_univ, true_and] at hw
    exact mem_partNbrs.mpr ⟨hw.2.2, hw.1⟩

/-- Internal degree under the standing hypothesis that both parts are nonempty. -/
theorem internal_degree_of_parts (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hanti : AntiEdgeful p TypedApplicationLinks.F0 G α)
    (hparts : ∀ j : Fin 2, ∃ v, p v = j) (i : Fin 2) (x : V) (hx : p x = i) :
    α * (Fintype.card V : ℝ) ≤ (partDeg p G i x : ℝ) := by
  obtain ⟨j, hj⟩ := exists_other i
  obtain ⟨z, hz⟩ := hparts j
  exact internal_degree p G α hanti i x hx z (hz ▸ hj)

/-- **`α ≤ 1`**, derived from the internal degree bound, `n > 0` and nonempty parts. -/
theorem alpha_le_one (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hanti : AntiEdgeful p TypedApplicationLinks.F0 G α)
    (hparts : ∀ j : Fin 2, ∃ v, p v = j) (hn : 0 < Fintype.card V) : α ≤ 1 := by
  obtain ⟨x, hx⟩ := hparts 0
  have h := internal_degree_of_parts p G α hanti hparts 0 x hx
  have hle : (partDeg p G 0 x : ℝ) ≤ Fintype.card V := by
    exact_mod_cast partDeg_le_card p G 0 x
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  by_contra hα
  push Not at hα
  have : (Fintype.card V : ℝ) < α * Fintype.card V := by nlinarith
  linarith

end PartitionedTriangleAbsorption.CloneSupply
