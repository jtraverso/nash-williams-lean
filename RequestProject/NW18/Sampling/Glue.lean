/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Defs

@[expose] public section

/-!
# Finite glue for Lemma 11.6

Elementary counting facts relating cuts, ordered pairs and degrees of a graph on a finite type
`W` to sums over the positions of an injective sequence `ι : Fin m → W`.
-/

namespace NashWilliams18.Sampling

open Finset

section Cuts

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A cut has at most as many edges as there are ordered crossing pairs. -/
lemma cutSize_le_pairs (H : SimpleGraph W) [DecidableRel H.Adj] (T : Finset W) :
    (cutSize H T : ℝ) ≤ ∑ x, ∑ y, if H.Adj x y ∧ x ∈ T ∧ y ∉ T then (1 : ℝ) else 0 := by
  have hsum : (∑ x, ∑ y, if H.Adj x y ∧ x ∈ T ∧ y ∉ T then (1 : ℝ) else 0) =
      ((univ.filter fun p : W × W => H.Adj p.1 p.2 ∧ p.1 ∈ T ∧ p.2 ∉ T).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hsum]
  unfold cutSize
  exact_mod_cast card_le_card_of_surjOn (fun p : W × W => s(p.1, p.2)) (by
    intro e he
    simp only [coe_filter, Set.mem_setOf_eq, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, x, y, rfl, hx, hy⟩ := he
    refine ⟨(x, y), ?_, rfl⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨he, hx, hy⟩)

/-- Ordered crossing pairs inject into crossing edges. -/
lemma pairs_le_cutSize (H : SimpleGraph W) [DecidableRel H.Adj] (T : Finset W) :
    (∑ x, ∑ y, if H.Adj x y ∧ x ∈ T ∧ y ∉ T then (1 : ℝ) else 0) ≤ (cutSize H T : ℝ) := by
  have hsum : (∑ x, ∑ y, if H.Adj x y ∧ x ∈ T ∧ y ∉ T then (1 : ℝ) else 0) =
      ((univ.filter fun p : W × W => H.Adj p.1 p.2 ∧ p.1 ∈ T ∧ p.2 ∉ T).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hsum]
  unfold cutSize
  exact_mod_cast card_le_card_of_injOn (fun p : W × W => s(p.1, p.2)) (by
    intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
    simp only [coe_filter, Set.mem_setOf_eq, SimpleGraph.mem_edgeFinset]
    exact ⟨hp.1, p.1, p.2, rfl, hp.2.1, hp.2.2⟩) (by
    intro p hp q hq h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hq
    have h' : s(p.1, p.2) = s(q.1, q.2) := h
    rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ hp.2.1) hq.2.2)

end Cuts

/-- The doubled cut value is twice the number of ordered pairs from side `true` to side
`false`. -/
lemma doubled_eq {ι : Type*} [Fintype ι] (A : ι → ι → Prop) [DecidableRel A]
    (hA : ∀ x y, A x y → A y x) (X : ι → Bool) :
    (∑ x, ∑ y, if A x y ∧ X x ≠ X y then (1 : ℝ) else 0) =
      2 * ∑ x, ∑ y, if A x y ∧ X x = true ∧ X y = false then (1 : ℝ) else 0 := by
  have hsplit : ∀ x y, (if A x y ∧ X x ≠ X y then (1 : ℝ) else 0) =
      (if A x y ∧ X x = true ∧ X y = false then 1 else 0) +
      (if A y x ∧ X y = true ∧ X x = false then 1 else 0) := by
    intro x y
    have hiff : A x y ↔ A y x := ⟨hA x y, hA y x⟩
    cases hx : X x <;> cases hy : X y <;> simp [hiff]
  simp_rw [hsplit, sum_add_distrib]
  rw [sum_comm (f := fun x y => if A y x ∧ X y = true ∧ X x = false then (1 : ℝ) else 0)]
  ring

/-- Splitting a double sum over `W` into the positions of an injective sequence and the
`card W - m` remaining points. -/
lemma sum_pairs_le_of_injective {W : Type*} [Fintype W] [DecidableEq W] {m : ℕ}
    (ι : Fin m → W) (hι : Function.Injective ι) (hW : Fintype.card W = m + 2)
    (f : W → W → ℝ) (hf : ∀ x y, 0 ≤ f x y ∧ f x y ≤ 1) :
    (∑ x, ∑ y, f x y) ≤ (∑ i, ∑ j, f (ι i) (ι j)) + 4 * (m + 2) := by
  set I := univ.image ι
  have hI : I.card = m := by rw [card_image_of_injective _ hι]; simp
  have hIc : (univ \ I).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hW, hI]; omega
  have hrow : ∀ x, (∑ y, f x y) ≤ (∑ y ∈ I, f x y) + 2 := by
    intro x
    rw [← sum_sdiff (subset_univ I)]
    have : (∑ y ∈ univ \ I, f x y) ≤ 2 := by
      calc (∑ y ∈ univ \ I, f x y) ≤ ∑ _y ∈ univ \ I, (1 : ℝ) :=
            sum_le_sum fun y _ => (hf x y).2
        _ = 2 := by rw [sum_const, hIc]; norm_num
    linarith
  have h1 : (∑ x, ∑ y, f x y) ≤ ∑ x, ((∑ y ∈ I, f x y) + 2) := sum_le_sum fun x _ => hrow x
  have h2 : ∑ x, ((∑ y ∈ I, f x y) + 2) = (∑ x, ∑ y ∈ I, f x y) + 2 * (m + 2) := by
    rw [sum_add_distrib, sum_const, card_univ, hW]; ring
  have h3 : (∑ x, ∑ y ∈ I, f x y) ≤ (∑ x ∈ I, ∑ y ∈ I, f x y) + 2 * m := by
    rw [← sum_sdiff (subset_univ I)]
    have : (∑ x ∈ univ \ I, ∑ y ∈ I, f x y) ≤ 2 * m := by
      calc (∑ x ∈ univ \ I, ∑ y ∈ I, f x y) ≤ ∑ _x ∈ univ \ I, ∑ _y ∈ I, (1 : ℝ) :=
            sum_le_sum fun x _ => sum_le_sum fun y _ => (hf x y).2
        _ = 2 * m := by rw [sum_const, hIc]; simp [hI]
    linarith
  have h4 : (∑ x ∈ I, ∑ y ∈ I, f x y) = ∑ i, ∑ j, f (ι i) (ι j) := by
    rw [sum_image (fun a _ b _ h => hι h)]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_image (fun a _ b _ h => hι h)]
  have : (2 : ℝ) * m ≤ 2 * (m + 2) := by linarith
  linarith

section Degrees

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The degree of `w` is at least the number of sample positions adjacent to it. -/
lemma degree_ge_count {m : ℕ} (ι : Fin m → W) (hι : Function.Injective ι) (w : W) :
    (((univ.filter fun j => H.Adj w (ι j)).card : ℕ) : ℝ) ≤ H.degree w := by
  rw [← H.card_neighborFinset_eq_degree]
  have : (univ.filter fun j => H.Adj w (ι j)).card =
      ((univ.filter fun j => H.Adj w (ι j)).image ι).card :=
    (card_image_of_injective _ hι).symm
  rw [this]
  exact_mod_cast card_le_card (by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    simpa using (mem_filter.mp hj).2)

/-- Few low-degree vertices if many sample positions have high degree. -/
lemma card_low_le {m : ℕ} (ι : Fin m → W) (hι : Function.Injective ι) (X : ℝ) :
    (((univ.filter fun w => (H.degree w : ℝ) ≤ X).card : ℕ) : ℝ) +
      (((univ.filter fun j => X < (H.degree (ι j) : ℝ)).card : ℕ) : ℝ) ≤ Fintype.card W := by
  have hdisj : Disjoint (univ.filter fun w => (H.degree w : ℝ) ≤ X)
      ((univ.filter fun j => X < (H.degree (ι j) : ℝ)).image ι) := by
    rw [disjoint_left]
    intro w hw hw'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hw'
    have h1 := (mem_filter.mp hw).2
    have h2 := (mem_filter.mp hj).2
    linarith
  have := card_union_of_disjoint hdisj
  rw [card_image_of_injective _ hι] at this
  have hle := card_le_univ ((univ.filter fun w => (H.degree w : ℝ) ≤ X) ∪
      (univ.filter fun j => X < (H.degree (ι j) : ℝ)).image ι)
  rw [this] at hle
  exact_mod_cast hle

end Degrees

end NashWilliams18.Sampling
