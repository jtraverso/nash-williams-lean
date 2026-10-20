/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Defs

@[expose] public section

/-!
# Elementary estimates for the edit cost `sideCost`

`sideCost G D X b` counts the ordered pairs of distinct vertices of `D` on which `G` differs
from the target `T₂` (`b = true`) or `T̄₂` (`b = false`) with parts `X`, `D ∖ X`.

* `sideCost_le_of_subset`: enlarging `D` by `k` vertices costs at most `2k|D|`;
* `sideCost_le_graph`: changing the graph costs at most the number of changed ordered pairs;
* `exists_sideCost_rebalance`: moving to a part of any prescribed size `m` costs at most
  `2|D|·| |X| − m |`;
* `sideCost_map_residual_le`: comparison between the cleaned graph and `G`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma card_pairs_with (D : Finset V) (v : V) :
    ((D ×ˢ D).filter (fun q => q.1 = v ∨ q.2 = v)).card ≤ 2 * D.card := by
  have hsub : (D ×ˢ D).filter (fun q => q.1 = v ∨ q.2 = v) ⊆
      ({v} ×ˢ D) ∪ (D ×ˢ {v}) := by
    intro q hq
    simp only [mem_filter, mem_product] at hq
    simp only [mem_union, mem_product, mem_singleton]
    rcases hq.2 with h | h
    · exact Or.inl ⟨h, hq.1.2⟩
    · exact Or.inr ⟨hq.1.1, h⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  simp only [card_product, card_singleton]; omega

omit [Fintype V] in
open Classical in
/-- Comparing the side cost on `D` with the side cost on any `D'` (typically `D' ⊆ D`). -/
lemma sideCost_le_of_subset (G : SimpleGraph V) {D D' X : Finset V} (b : Bool) :
    sideCost G D X b ≤ sideCost G D' X b + 2 * (D \ D').card * D.card := by
  unfold sideCost
  have hsub : (D ×ˢ D).filter (fun q => q.1 ≠ q.2 ∧ ¬ (G.Adj q.1 q.2 ↔ sideTarget X b q.1 q.2)) ⊆
      (D' ×ˢ D').filter (fun q => q.1 ≠ q.2 ∧ ¬ (G.Adj q.1 q.2 ↔ sideTarget X b q.1 q.2)) ∪
        (((D \ D') ×ˢ D) ∪ (D ×ˢ (D \ D'))) := by
    intro q hq
    simp only [mem_filter, mem_product] at hq
    by_cases h1 : q.1 ∈ D'
    · by_cases h2 : q.2 ∈ D'
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨h1, h2⟩, hq.2⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_product.mpr ⟨hq.1.1,
          mem_sdiff.mpr ⟨hq.1.2, h2⟩⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_product.mpr ⟨mem_sdiff.mpr ⟨hq.1.1, h1⟩,
        hq.1.2⟩))
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := card_union_le ((D \ D') ×ˢ D) (D ×ˢ (D \ D'))
  simp only [card_product] at h1
  have h2 : 2 * (D \ D').card * D.card = (D \ D').card * D.card + D.card * (D \ D').card := by
    ring
  rw [h2]
  exact Nat.add_le_add_left h1 _

omit [Fintype V] in
open Classical in
/-- Changing the graph. -/
lemma sideCost_le_graph (G G' : SimpleGraph V) (D X : Finset V) (b : Bool) :
    sideCost G D X b ≤ sideCost G' D X b +
      ((D ×ˢ D).filter (fun q => q.1 ≠ q.2 ∧ ¬ (G.Adj q.1 q.2 ↔ G'.Adj q.1 q.2))).card := by
  unfold sideCost
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro q hq
  simp only [mem_filter, mem_product] at hq
  by_cases h : G.Adj q.1 q.2 ↔ G'.Adj q.1 q.2
  · refine mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr hq.1, hq.2.1, ?_⟩)
    rw [← h]; exact hq.2.2
  · refine mem_union_right _ ?_
    simp only [mem_filter, mem_product]
    exact ⟨hq.1, hq.2.1, h⟩

omit [Fintype V] in
lemma sideTarget_insert_of_ne {X : Finset V} {v x y : V} (b : Bool) (hx : x ≠ v) (hy : y ≠ v) :
    sideTarget (insert v X) b x y ↔ sideTarget X b x y := by
  simp only [sideTarget, mem_insert, hx, hy, false_or]

omit [Fintype V] in
lemma sideTarget_erase_of_ne {X : Finset V} {v x y : V} (b : Bool) (hx : x ≠ v) (hy : y ≠ v) :
    sideTarget (X.erase v) b x y ↔ sideTarget X b x y := by
  simp only [sideTarget, mem_erase, hx, hy, ne_eq, not_false_eq_true, true_and]

omit [Fintype V] in
open Classical in
lemma sideCost_change_le (G : SimpleGraph V) (D X X' : Finset V) (b : Bool) (v : V)
    (h : ∀ x y, x ≠ v → y ≠ v → (sideTarget X' b x y ↔ sideTarget X b x y)) :
    sideCost G D X' b ≤ sideCost G D X b + 2 * D.card := by
  unfold sideCost
  refine (card_le_card ?_).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_pairs_with D v) _))
  intro q hq
  simp only [mem_filter, mem_product] at hq
  by_cases hv : q.1 = v ∨ q.2 = v
  · refine mem_union_right _ ?_
    simp only [mem_filter, mem_product]
    exact ⟨hq.1, hv⟩
  · push_neg at hv
    refine mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr hq.1, hq.2.1, ?_⟩)
    rw [← h _ _ hv.1 hv.2]; exact hq.2.2

omit [Fintype V] in
lemma exists_sideCost_up (G : SimpleGraph V) (D : Finset V) (b : Bool) :
    ∀ k : ℕ, ∀ X ⊆ D, X.card + k ≤ D.card →
      ∃ X' ⊆ D, X'.card = X.card + k ∧ sideCost G D X' b ≤ sideCost G D X b + 2 * D.card * k := by
  intro k
  induction k with
  | zero => intro X hX _; exact ⟨X, hX, by simp, by simp⟩
  | succ k ih =>
    intro X hX hk
    obtain ⟨Y, hY, hYc, hYcost⟩ := ih X hX (by omega)
    have hlt : Y.card < D.card := by omega
    obtain ⟨v, hvD, hvY⟩ : ∃ v ∈ D, v ∉ Y := by
      by_contra hcon
      push_neg at hcon
      have : D ⊆ Y := fun v hv => hcon v hv
      have := card_le_card this
      omega
    refine ⟨insert v Y, insert_subset hvD hY, by rw [card_insert_of_notMem hvY]; omega, ?_⟩
    have := sideCost_change_le G D Y (insert v Y) b v
      (fun x y hx hy => sideTarget_insert_of_ne b hx hy)
    calc sideCost G D (insert v Y) b ≤ sideCost G D Y b + 2 * D.card := this
      _ ≤ sideCost G D X b + 2 * D.card * k + 2 * D.card := by omega
      _ = sideCost G D X b + 2 * D.card * (k + 1) := by ring

omit [Fintype V] in
lemma exists_sideCost_down (G : SimpleGraph V) (D : Finset V) (b : Bool) :
    ∀ k : ℕ, ∀ X ⊆ D, k ≤ X.card →
      ∃ X' ⊆ D, X'.card = X.card - k ∧ sideCost G D X' b ≤ sideCost G D X b + 2 * D.card * k := by
  intro k
  induction k with
  | zero => intro X hX _; exact ⟨X, hX, by simp, by simp⟩
  | succ k ih =>
    intro X hX hk
    obtain ⟨Y, hY, hYc, hYcost⟩ := ih X hX (by omega)
    have hpos : 0 < Y.card := by omega
    obtain ⟨v, hvY⟩ := card_pos.mp hpos
    refine ⟨Y.erase v, (erase_subset _ _).trans hY, by rw [card_erase_of_mem hvY]; omega, ?_⟩
    have := sideCost_change_le G D Y (Y.erase v) b v
      (fun x y hx hy => sideTarget_erase_of_ne b hx hy)
    calc sideCost G D (Y.erase v) b ≤ sideCost G D Y b + 2 * D.card := this
      _ ≤ sideCost G D X b + 2 * D.card * k + 2 * D.card := by omega
      _ = sideCost G D X b + 2 * D.card * (k + 1) := by ring

omit [Fintype V] in
/-- Rebalancing a part to a prescribed size `m ≤ |D|`. -/
lemma exists_sideCost_rebalance (G : SimpleGraph V) {D X : Finset V} (b : Bool) (hX : X ⊆ D)
    (m : ℕ) (hm : m ≤ D.card) (k : ℕ) (hk : X.card ≤ m + k) (hk' : m ≤ X.card + k) :
    ∃ X' ⊆ D, X'.card = m ∧ sideCost G D X' b ≤ sideCost G D X b + 2 * D.card * k := by
  by_cases h : X.card ≤ m
  · obtain ⟨X', h1, h2, h3⟩ := exists_sideCost_up G D b (m - X.card) X hX (by omega)
    refine ⟨X', h1, by omega, h3.trans ?_⟩
    have : m - X.card ≤ k := by omega
    have := Nat.mul_le_mul_left (2 * D.card) this
    omega
  · obtain ⟨X', h1, h2, h3⟩ := exists_sideCost_down G D b (X.card - m) X hX (by omega)
    refine ⟨X', h1, by omega, h3.trans ?_⟩
    have : X.card - m ≤ k := by omega
    have := Nat.mul_le_mul_left (2 * D.card) this
    omega

/-- Ordered pairs `(x, y)` whose unordered pair lies in `C` are at most `2|C|`. -/
lemma card_pairs_in_le (C : Finset (Sym2 V)) :
    ((univ ×ˢ univ).filter (fun q : V × V => s(q.1, q.2) ∈ C)).card ≤ 2 * C.card := by
  classical
  have hsub : (univ ×ˢ univ).filter (fun q : V × V => s(q.1, q.2) ∈ C) ⊆
      C.biUnion (fun e => (univ ×ˢ univ).filter (fun q : V × V => s(q.1, q.2) = e)) := by
    intro q hq
    simp only [mem_filter] at hq
    exact mem_biUnion.mpr ⟨_, hq.2, by simp⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y =>
    have : (univ ×ˢ univ).filter (fun q : V × V => s(q.1, q.2) = s(x, y)) ⊆ {(x, y), (y, x)} := by
      intro q hq
      simp only [mem_filter, Sym2.eq_iff] at hq
      simp only [mem_insert, mem_singleton]
      rcases hq.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact Prod.ext h1 h2
      · right; exact Prod.ext h1 h2
    exact (card_le_card this).trans (card_le_two)

end NashWilliams18
