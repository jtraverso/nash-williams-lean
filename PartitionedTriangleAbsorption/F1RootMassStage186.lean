/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1RootDebtStage185

/-! # Physical fractional mass around each F1 root

Only one opposite class is used. The ordered-pair fibre bound nine is
deliberately conservative. No root abundance is received as a premise.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1RootMassStage186

open Finset TypedApplicationLinks TypedHostMassStage176 F1RootCountsStage182

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem goodPairs_card (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (goodPairs G A B).card = ∑ x ∈ A, (B.filter (G.Adj x)).card := by
  classical
  unfold goodPairs
  rw [card_biUnion]
  · apply sum_congr rfl
    intro x _
    exact card_image_of_injective _ (Prod.mk_right_injective x)
  · intro x _ y _ hxy
    apply disjoint_left.mpr
    intro xy hx hy
    obtain ⟨a, _, ha⟩ := mem_image.mp hx
    obtain ⟨b, _, hb⟩ := mem_image.mp hy
    exact hxy (congrArg Prod.fst (ha.trans hb.symm))

theorem singleton_copies_lower (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (α ε : ℝ) (hα : 0 ≤ α) (hε : ε ≤ α / 4)
    (hsize : α * Fintype.card V ≤
      ((univ.filter fun x => p x = first1 (p v)).card : ℝ))
    (hmissRoot : ((univ.filter fun x => p x = first1 (p v) ∧ ¬ G.Adj v x).card : ℝ) ≤
      ε * Fintype.card V)
    (hmissClass : ∀ x, p x = first1 (p v) →
      ((univ.filter fun y => p y = first1 (p v) ∧ ¬ G.Adj x y).card : ℝ) ≤
        ε * Fintype.card V) :
    α ^ 2 * (Fintype.card V : ℝ) ^ 2 / 36 ≤
      ((singletonFamily p (copies p F1 G) v).card : ℝ) := by
  classical
  let C := univ.filter fun x => p x = first1 (p v)
  let A := C.filter (G.Adj v)
  let T := goodPairs G A A
  let D := singletonFamily p (copies p F1 G) v
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := by positivity
  have hA : α * n / 2 ≤ (A.card : ℝ) := by
    have h := filter_card_lower C (G.Adj v) (ε * n) (by
      simpa [C, filter_filter, n] using hmissRoot)
    have he := mul_le_mul_of_nonneg_right hε hn
    dsimp [n] at *
    linarith
  have hrow : ∀ x ∈ A, α * n / 2 ≤ ((A.filter (G.Adj x)).card : ℝ) := by
    intro x hx
    have hxc : p x = first1 (p v) := (mem_filter.mp (mem_filter.mp hx).1).2
    have hbad : ((A.filter fun y => ¬ G.Adj x y).card : ℝ) ≤ ε * n := by
      have hsub : (A.filter fun y => ¬ G.Adj x y) ⊆ C.filter fun y => ¬ G.Adj x y :=
        filter_subset_filter _ (filter_subset _ _)
      have hc : ((A.filter fun y => ¬ G.Adj x y).card : ℝ) ≤
          (C.filter fun y => ¬ G.Adj x y).card := by exact_mod_cast card_le_card hsub
      exact hc.trans (by simpa [C, filter_filter, n] using hmissClass x hxc)
    have h := filter_card_lower A (G.Adj x) (ε * n) hbad
    have hC := filter_card_lower C (G.Adj v) (ε * n) (by
      simpa [C, filter_filter, n] using hmissRoot)
    have he := mul_le_mul_of_nonneg_right hε hn
    dsimp [n] at *
    linarith
  have hT : α ^ 2 * n ^ 2 / 4 ≤ (T.card : ℝ) := by
    have hsum : (A.card : ℝ) * (α * n / 2) ≤ (T.card : ℝ) := by
      rw [show T = goodPairs G A A from rfl, goodPairs_card, Nat.cast_sum]
      calc
        _ = ∑ _x ∈ A, α * n / 2 := by simp
        _ ≤ _ := sum_le_sum hrow
    have h := mul_le_mul_of_nonneg_right hA (show 0 ≤ α * n / 2 by positivity)
    nlinarith
  have hpv : p v ≠ first1 (p v) := by generalize p v = r; revert r; decide
  have htype : ∀ r : Fin 4, ({r, first1 r, first1 r} : Multiset (Fin 4)) ∈ F1 := by decide
  have hmaps : ∀ xy ∈ T, ({v, xy.1, xy.2} : Finset V) ∈ D := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx, hy, hxy⟩ := (mem_goodPairs G A A x y).mp hxy
    have hvx := (mem_filter.mp hx).2
    have hvy := (mem_filter.mp hy).2
    have hpx := (mem_filter.mp (mem_filter.mp hx).1).2
    have hpy := (mem_filter.mp (mem_filter.mp hy).1).2
    have ht : triType p ({v,x,y} : Finset V) = {p v, first1 (p v), first1 (p v)} := by
      rw [triType, map_three p hvx.ne hvy.ne hxy.ne]
      simp only [hpx, hpy]
    have hc : G.IsNClique 3 ({v,x,y} : Finset V) := by
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, card_eq_three.mpr ⟨_, _, _, hvx.ne,hvy.ne,hxy.ne, rfl⟩⟩
      intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact False.elim (hab rfl)
      · exact hvx
      · exact hvy
      · exact hvx.symm
      · exact False.elim (hab rfl)
      · exact hxy
      · exact hvy.symm
      · exact hxy.symm
      · exact False.elim (hab rfl)
    apply mem_filter.mpr
    refine ⟨TypedNibble.mem_copies_iff.mpr ⟨hc, ?_⟩, by simp, ?_⟩
    · change triType p _ ∈ F1
      rw [ht]
      exact htype (p v)
    · rw [ht]
      simp [hpv]
  have hfibre : ∀ s ∈ D,
      (T.filter fun xy => ({v,xy.1,xy.2} : Finset V) = s).card ≤ 9 := by
    intro s hs
    have hc : s.card = 3 := (TypedNibble.mem_copies_iff.mp (mem_filter.mp hs).1).1.card_eq
    have hsub : (T.filter fun xy => ({v,xy.1,xy.2} : Finset V) = s) ⊆ s ×ˢ s := by
      intro xy hxy
      rw [mem_product]
      have he := (mem_filter.mp hxy).2
      constructor <;> rw [← he] <;> simp
    exact (card_le_card hsub).trans (by simp [card_product, hc])
  have hupper : T.card ≤ D.card * 9 := by
    rw [card_eq_sum_card_fiberwise hmaps]
    calc
      _ ≤ ∑ _s ∈ D, 9 := sum_le_sum hfibre
      _ = _ := by simp
  have hupper' : (T.card : ℝ) ≤ (D.card : ℝ) * 9 := by exact_mod_cast hupper
  change α ^ 2 * (Fintype.card V : ℝ) ^ 2 / 36 ≤ (D.card : ℝ)
  dsimp [n] at hT
  linarith

theorem singleton_fractional_mass (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (α ε b : ℝ) (hα : 0 ≤ α) (hε : ε ≤ α / 4)
    (hb : 0 < b) (hn : 0 < Fintype.card V)
    (hsize : α * Fintype.card V ≤
      ((univ.filter fun x => p x = first1 (p v)).card : ℝ))
    (hmissRoot : ((univ.filter fun x => p x = first1 (p v) ∧ ¬ G.Adj v x).card : ℝ) ≤
      ε * Fintype.card V)
    (hmissClass : ∀ x, p x = first1 (p v) →
      ((univ.filter fun y => p y = first1 (p v) ∧ ¬ G.Adj x y).card : ℝ) ≤
        ε * Fintype.card V)
    (φ : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F1 G s → 1 / (b * Fintype.card V) ≤ φ s) :
    α ^ 2 / (36 * b) * Fintype.card V ≤
      ∑ s ∈ singletonFamily p (copies p F1 G) v, φ s := by
  classical
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hc := singleton_copies_lower p G v α ε hα hε hsize hmissRoot hmissClass
  have hsum : ((singletonFamily p (copies p F1 G) v).card : ℝ) / (b * Fintype.card V) ≤
      ∑ s ∈ singletonFamily p (copies p F1 G) v, φ s := by
    calc
      _ = ∑ _s ∈ singletonFamily p (copies p F1 G) v, 1 / (b * Fintype.card V) :=
        by simp [div_eq_mul_inv]
      _ ≤ _ := sum_le_sum fun s hs => hw s (TypedNibble.mem_copies_iff.mp (mem_filter.mp hs).1)
  have h := div_le_div_of_nonneg_right hc (show 0 ≤ b * Fintype.card V by positivity)
  have he : (α ^ 2 * (Fintype.card V : ℝ) ^ 2 / 36) / (b * Fintype.card V) =
      α ^ 2 / (36 * b) * Fintype.card V := by field_simp
  rw [he] at h
  exact h.trans hsum

end PartitionedTriangleAbsorption.F1RootMassStage186

