/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedNibbleAdapter

/-! # Fractional type mass from the physical host

Three label classes have size at least `α n`. Missing neighbours in each
required class, including the vertex itself when labels repeat, number at most
`ε n`. For `ε ≤ α/4` this gives at least `α^3 n^3 / 108` physical copies.
The factor 27 is a deliberately conservative bound on the fibre of an ordered
triple over a three-element vertex set. No packing or type abundance is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedHostMassStage176

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def goodPairs (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : Finset (V × V) :=
  A.biUnion fun x => (B.filter (G.Adj x)).image fun y => (x, y)

def goodTriples (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V) :
    Finset ((V × V) × V) :=
  (goodPairs G A B).biUnion fun xy =>
    (C.filter fun z => G.Adj xy.1 z ∧ G.Adj xy.2 z).image fun z => (xy, z)

omit [Fintype V] in
theorem mem_goodPairs (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (x y : V) :
    (x, y) ∈ goodPairs G A B ↔ x ∈ A ∧ y ∈ B ∧ G.Adj x y := by
  classical simp [goodPairs]

omit [Fintype V] in
theorem mem_goodTriples (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V) (x y z : V) :
    ((x, y), z) ∈ goodTriples G A B C ↔
      x ∈ A ∧ y ∈ B ∧ z ∈ C ∧ G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  classical simp [goodTriples, mem_goodPairs, and_assoc, and_left_comm, and_comm]

omit [Fintype V] [DecidableEq V] in
theorem filter_card_lower (D : Finset V) (Q : V → Prop) [DecidablePred Q]
    (r : ℝ) (h : ((D.filter fun x => ¬ Q x).card : ℝ) ≤ r) :
    (D.card : ℝ) - r ≤ (D.filter Q).card := by
  have hc := card_filter_add_card_filter_not (s := D) Q
  have hc' : ((D.filter Q).card : ℝ) + (D.filter fun x => ¬ Q x).card = D.card :=
    by exact_mod_cast hc
  linarith

theorem ordered_triples_lower (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : ε ≤ α / 4)
    (hA : α * Fintype.card V ≤ (A.card : ℝ))
    (hB : α * Fintype.card V ≤ (B.card : ℝ))
    (hC : α * Fintype.card V ≤ (C.card : ℝ))
    (hAB : ∀ x ∈ A, ((B.filter fun y => ¬ G.Adj x y).card : ℝ) ≤ ε * Fintype.card V)
    (hAC : ∀ x ∈ A, ((C.filter fun z => ¬ G.Adj x z).card : ℝ) ≤ ε * Fintype.card V)
    (hBC : ∀ y ∈ B, ((C.filter fun z => ¬ G.Adj y z).card : ℝ) ≤ ε * Fintype.card V) :
    α ^ 3 * (Fintype.card V : ℝ) ^ 3 / 4 ≤ (goodTriples G A B C).card := by
  classical
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := by positivity
  have hrow : ∀ x ∈ A, α * n / 2 ≤ ((B.filter (G.Adj x)).card : ℝ) := by
    intro x hx
    have h := filter_card_lower B (G.Adj x) (ε * n) (hAB x hx)
    have he := mul_le_mul_of_nonneg_right hε hn
    dsimp [n] at *
    linarith
  have hp : (goodPairs G A B).card = ∑ x ∈ A, (B.filter (G.Adj x)).card := by
    unfold goodPairs
    rw [card_biUnion]
    · apply sum_congr rfl
      intro x _
      simp only [card_image_of_injective _ (Prod.mk_right_injective x)]
    · intro x _ y _ hxy
      apply disjoint_left.mpr
      intro xy hx hy
      obtain ⟨a, _, ha⟩ := mem_image.mp hx
      obtain ⟨b, _, hb⟩ := mem_image.mp hy
      exact hxy (by have := congrArg Prod.fst (ha.trans hb.symm); exact this)
  have hp' : (A.card : ℝ) * (α * n / 2) ≤ (goodPairs G A B).card := by
    rw [hp, Nat.cast_sum]
    calc
      (A.card : ℝ) * (α * n / 2) = ∑ _x ∈ A, α * n / 2 := by simp
      _ ≤ _ := sum_le_sum hrow
  have hp0 : α ^ 2 * n ^ 2 / 2 ≤ (goodPairs G A B).card := by
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ α * n / 2 by positivity)
    dsimp [n] at *
    nlinarith
  have htwo : ∀ xy ∈ goodPairs G A B,
      α * n / 2 ≤ ((C.filter fun z => G.Adj xy.1 z ∧ G.Adj xy.2 z).card : ℝ) := by
    intro xy hxy
    obtain ⟨hx, hy, _⟩ := (mem_goodPairs G A B xy.1 xy.2).mp hxy
    have hbad : ((C.filter fun z => ¬ (G.Adj xy.1 z ∧ G.Adj xy.2 z)).card : ℝ) ≤ 2 * ε * n := by
      have hsub : (C.filter fun z => ¬ (G.Adj xy.1 z ∧ G.Adj xy.2 z)) ⊆
          (C.filter fun z => ¬ G.Adj xy.1 z) ∪ (C.filter fun z => ¬ G.Adj xy.2 z) := by
        intro z hz
        simp only [mem_filter, mem_union] at hz ⊢
        tauto
      have hc := (card_le_card hsub).trans (card_union_le _ _)
      have hc' : ((C.filter fun z => ¬ (G.Adj xy.1 z ∧ G.Adj xy.2 z)).card : ℝ) ≤
          (C.filter fun z => ¬ G.Adj xy.1 z).card + (C.filter fun z => ¬ G.Adj xy.2 z).card :=
        by exact_mod_cast hc
      have ha := hAC xy.1 hx
      have hb := hBC xy.2 hy
      dsimp [n] at *
      linarith
    have h := filter_card_lower C (fun z => G.Adj xy.1 z ∧ G.Adj xy.2 z) (2 * ε * n) hbad
    have he := mul_le_mul_of_nonneg_right hε hn
    dsimp [n] at *
    linarith
  have ht : (goodTriples G A B C).card = ∑ xy ∈ goodPairs G A B,
      (C.filter fun z => G.Adj xy.1 z ∧ G.Adj xy.2 z).card := by
    unfold goodTriples
    rw [card_biUnion]
    · apply sum_congr rfl
      intro xy _
      simp only [card_image_of_injective _ (Prod.mk_right_injective xy)]
    · intro xy _ xy' _ hxy
      apply disjoint_left.mpr
      intro xyz hx hy
      obtain ⟨a, _, ha⟩ := mem_image.mp hx
      obtain ⟨b, _, hb⟩ := mem_image.mp hy
      exact hxy (by have := congrArg Prod.fst (ha.trans hb.symm); exact this)
  have ht' : ((goodPairs G A B).card : ℝ) * (α * n / 2) ≤ (goodTriples G A B C).card := by
    rw [ht, Nat.cast_sum]
    calc
      ((goodPairs G A B).card : ℝ) * (α * n / 2) =
          ∑ _xy ∈ goodPairs G A B, α * n / 2 := by simp
      _ ≤ _ := sum_le_sum htwo
  have h := mul_le_mul_of_nonneg_right hp0 (show 0 ≤ α * n / 2 by positivity)
  dsimp [n] at *
  nlinarith

omit [Fintype V] in
theorem triple_fibre_le (T : Finset ((V × V) × V)) (s : Finset V) (hs : s.card = 3) :
    (T.filter fun xyz => ({xyz.1.1, xyz.1.2, xyz.2} : Finset V) = s).card ≤ 27 := by
  classical
  have hsub : (T.filter fun xyz => ({xyz.1.1, xyz.1.2, xyz.2} : Finset V) = s) ⊆
      (s ×ˢ s) ×ˢ s := by
    intro xyz hxyz
    have he := (mem_filter.mp hxyz).2
    simp only [mem_product]
    constructor
    · constructor <;> rw [← he] <;> simp
    · rw [← he]; simp
  calc
    _ ≤ ((s ×ˢ s) ×ˢ s).card := card_le_card hsub
    _ = 27 := by simp [card_product, hs]

omit [DecidableEq V] in
theorem type_copies_lower {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j k : Fin t)
    (hτ : ({i, j, k} : Multiset (Fin t)) ∈ F)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : ε ≤ α / 4)
    (hsize : ∀ l ∈ ({i, j, k} : Finset (Fin t)),
      α * Fintype.card V ≤ ((univ.filter fun v => p v = l).card : ℝ))
    (hmiss : ∀ l₁ l₂, (l₁, l₂) ∈ ({(i,j), (i,k), (j,k)} : Finset (Fin t × Fin t)) →
      ∀ x, p x = l₁ →
      ((univ.filter fun y => p y = l₂ ∧ ¬ G.Adj x y).card : ℝ) ≤ ε * Fintype.card V) :
    α ^ 3 * (Fintype.card V : ℝ) ^ 3 / 108 ≤
      ((copies p F G).filter fun s => triType p s = {i,j,k}).card := by
  classical
  let A := univ.filter fun v => p v = i
  let B := univ.filter fun v => p v = j
  let C := univ.filter fun v => p v = k
  let T := goodTriples G A B C
  let D := (copies p F G).filter fun s => triType p s = {i,j,k}
  have hlower : α ^ 3 * (Fintype.card V : ℝ) ^ 3 / 4 ≤ (T.card : ℝ) := by
    apply ordered_triples_lower G A B C α ε hα hε
    · exact hsize i (by simp)
    · exact hsize j (by simp)
    · exact hsize k (by simp)
    · intro x hx
      simpa [A, B, filter_filter] using hmiss i j (by simp) x ((mem_filter.mp hx).2)
    · intro x hx
      simpa [A, C, filter_filter] using hmiss i k (by simp) x ((mem_filter.mp hx).2)
    · intro y hy
      simpa [B, C, filter_filter] using hmiss j k (by simp) y ((mem_filter.mp hy).2)
  have hmaps : ∀ xyz ∈ T, ({xyz.1.1,xyz.1.2,xyz.2} : Finset V) ∈ D := by
    rintro ⟨⟨x,y⟩,z⟩ hxyz
    obtain ⟨hx,hy,hz,hxy,hxz,hyz⟩ := (mem_goodTriples G A B C x y z).mp hxyz
    have hp : triType p ({x,y,z} : Finset V) = {i,j,k} := by
      rw [triType, map_three p hxy.ne hxz.ne hyz.ne]
      simp only [(mem_filter.mp hx).2, (mem_filter.mp hy).2, (mem_filter.mp hz).2]
    apply mem_filter.mpr
    refine ⟨TypedNibble.mem_copies_iff.mpr ⟨?_, by change triType p _ ∈ F; rw [hp]; exact hτ⟩, hp⟩
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, card_eq_three.mpr ⟨_, _, _, hxy.ne,hxz.ne,hyz.ne, rfl⟩⟩
    intro a ha b hb hab
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · exact hxy
    · exact hxz
    · exact hxy.symm
    · exact False.elim (hab rfl)
    · exact hyz
    · exact hxz.symm
    · exact hyz.symm
    · exact False.elim (hab rfl)
  have ht := card_eq_sum_card_fiberwise hmaps
  have hupper : T.card ≤ D.card * 27 := by
    rw [ht]
    calc
      _ ≤ ∑ _s ∈ D, 27 := by
        apply sum_le_sum
        intro s hs
        exact triple_fibre_le T s (TypedNibble.mem_copies_iff.mp (mem_filter.mp hs).1).1.card_eq
      _ = _ := by simp
  have hupper' : (T.card : ℝ) ≤ (D.card : ℝ) * 27 := by exact_mod_cast hupper
  change α ^ 3 * (Fintype.card V : ℝ) ^ 3 / 108 ≤ (D.card : ℝ)
  linarith

omit [DecidableEq V] in
theorem fractional_type_mass {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j k : Fin t) (hτ : ({i,j,k} : Multiset (Fin t)) ∈ F)
    (α ε b : ℝ) (hα : 0 ≤ α) (hε : ε ≤ α / 4) (hb : 0 < b)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ l ∈ ({i,j,k} : Finset (Fin t)),
      α * Fintype.card V ≤ ((univ.filter fun v => p v = l).card : ℝ))
    (hmiss : ∀ l₁ l₂, (l₁, l₂) ∈ ({(i,j),(i,k),(j,k)} : Finset (Fin t × Fin t)) →
      ∀ x, p x = l₁ →
      ((univ.filter fun y => p y = l₂ ∧ ¬ G.Adj x y).card : ℝ) ≤ ε * Fintype.card V)
    (φ : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F G s → 1 / (b * Fintype.card V) ≤ φ s) :
    α ^ 3 / (108 * b) * (Fintype.card V : ℝ) ^ 2 ≤
      ∑ s ∈ (copies p F G).filter (fun s => triType p s = {i,j,k}), φ s := by
  classical
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hc := type_copies_lower p F G i j k hτ α ε hα hε hsize hmiss
  have hsum : (((copies p F G).filter (fun s => triType p s = {i,j,k})).card : ℝ) /
      (b * Fintype.card V) ≤ ∑ s ∈ (copies p F G).filter (fun s => triType p s = {i,j,k}), φ s := by
    calc
      _ = ∑ _s ∈ (copies p F G).filter (fun s => triType p s = {i,j,k}),
          1 / (b * Fintype.card V) := by simp [div_eq_mul_inv]
      _ ≤ _ := sum_le_sum fun s hs => hw s (TypedNibble.mem_copies_iff.mp (mem_filter.mp hs).1)
  have h := div_le_div_of_nonneg_right hc (show 0 ≤ b * Fintype.card V by positivity)
  have he : (α ^ 3 * (Fintype.card V : ℝ) ^ 3 / 108) / (b * Fintype.card V) =
      α ^ 3 / (108 * b) * (Fintype.card V : ℝ) ^ 2 := by
    field_simp
  rw [he] at h
  exact h.trans hsum

end PartitionedTriangleAbsorption.TypedHostMassStage176

