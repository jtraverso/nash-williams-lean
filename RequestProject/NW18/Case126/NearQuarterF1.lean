/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.RootedConeF1
public import RequestProject.NW18.Case126.Ideal

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: the near-quarter class invariant and its cone slack

The vortex levels of the `F₁` branch are specialised to the invariant the application actually
supplies: every class of every nested set is within `κ |S|` of a quarter of `S`
(`NearQuarter p S κ`).

* `classConeSlack_of_nearQuarter` (proved): near-quarter classes give the rooted cone slack
  `ClassConeSlack p S (1/4 - 3κ)` on EVERY set `S` with the invariant (so on `W`, `U`, `U'` of
  every level).
* `nearQuarter_of_idealized` (proved): the actual hosts of `Theorem147F1Statement`
  (`IsIdealizedT F1 ε G p`) have near-quarter classes, `κ = 3ε/4`, on the whole vertex set.
* `nearQuarter_outside` (proved): from near-quarter `W` and `U ⊆ W` one gets the class sizes of the
  OUTSIDE part `W \ U` around `(|W| - |U|)/4`, which is the form used by the punctured weighting.

How the invariant passes to the nested random sets `U ⊆ W` (concentration of a random subset) is
part of the sampling step and is NOT proved here.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every class of `S` has size within `κ |S|` of `|S| / 4`. -/
def NearQuarter (p : V → Fin 4) (S : Finset V) (κ : ℝ) : Prop :=
  ∀ j : Fin 4, |((S.filter fun z => p z = j).card : ℝ) - S.card / 4| ≤ κ * S.card

omit [Fintype V] [DecidableEq V] in
/-- **Near-quarter classes give rooted cone slack** on the same set. -/
theorem classConeSlack_of_nearQuarter (p : V → Fin 4) (S : Finset V) (κ : ℝ)
    (h : NearQuarter p S κ) : ClassConeSlack p S (1 / 4 - 3 * κ) := by
  intro c
  have h1 := abs_le.mp (h c)
  have h2 := abs_le.mp (h (partner1 c))
  have h3 := abs_le.mp (h (partner2 c))
  nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

omit [Fintype V] [DecidableEq V] in
/-- The classes of a finite set add up to its size. -/
lemma sum_card_classes (p : V → Fin 4) (S : Finset V) :
    ((S.filter fun z => p z = 0).card : ℝ) + (S.filter fun z => p z = 1).card +
      (S.filter fun z => p z = 2).card + (S.filter fun z => p z = 3).card = S.card := by
  have := (card_eq_sum_card_fiberwise (f := p) (s := S) (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _)))
  rw [Fin.sum_univ_four] at this
  exact_mod_cast this.symm

omit [DecidableEq V] in
/-- **The application hosts have near-quarter classes**: an `ε`-balanced `F₁`-blowup
(`IsIdealizedT F1 ε G p`) satisfies `NearQuarter p univ (3ε/4)`. -/
theorem nearQuarter_of_idealized {ε : ℝ} {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : V → Fin 4} (h : IsIdealizedT F1 ε G p) :
    NearQuarter p (univ : Finset V) (3 * ε / 4) := by
  intro j
  have hs := sum_card_classes p (univ : Finset V)
  have hlo : ∀ i : Fin 4, (1 - ε) * Fintype.card V / 4 ≤
      (((univ : Finset V).filter fun z => p z = i).card : ℝ) := fun i => by
    have := h.1 i; simpa [clsT] using this
  have h0 := hlo 0; have h1 := hlo 1; have h2 := hlo 2; have h3 := hlo 3
  rw [card_univ] at hs ⊢
  rw [abs_le]
  fin_cases j <;> simp <;> constructor <;> linarith

/-- Class sizes of the outside part `W \ U`. -/
theorem nearQuarter_outside (p : V → Fin 4) (W U : Finset V) (hUW : U ⊆ W) (κ : ℝ)
    (hW : NearQuarter p W κ) (hU : NearQuarter p U κ) (j : Fin 4) :
    |(((W \ U).filter fun z => p z = j).card : ℝ) - ((W.card : ℝ) - U.card) / 4| ≤
      2 * κ * W.card := by
  have hsplit : ((W \ U).filter fun z => p z = j).card + (U.filter fun z => p z = j).card =
      (W.filter fun z => p z = j).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext z; simp only [mem_union, mem_filter, mem_sdiff]
      constructor
      · rintro (⟨⟨h1, -⟩, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2⟩
        · exact ⟨hUW h1, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hz : z ∈ U
        · exact Or.inr ⟨hz, h2⟩
        · exact Or.inl ⟨⟨h1, hz⟩, h2⟩
    · exact disjoint_filter_filter (sdiff_disjoint)
  have hsplit' : (((W \ U).filter fun z => p z = j).card : ℝ) +
      (U.filter fun z => p z = j).card = (W.filter fun z => p z = j).card := by
    exact_mod_cast hsplit
  have hUle : (U.card : ℝ) ≤ W.card := by exact_mod_cast card_le_card hUW
  by_cases hW0 : W.card = 0
  · have hWe : W = ∅ := card_eq_zero.mp hW0
    have hUe : U = ∅ := subset_empty.mp (hWe ▸ hUW)
    subst hWe; subst hUe; simp
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast Nat.pos_of_ne_zero hW0
  have hκ : 0 ≤ κ := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hW j)) hWpos
  have a := abs_le.mp (hW j)
  have b := abs_le.mp (hU j)
  rw [abs_le]
  constructor <;> nlinarith

end NashWilliams18.SpreadF1
