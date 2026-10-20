/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.Hybrid

@[expose] public section

/-!
# Tuple statistics of vertex sets (for the 12.4 vortex)

`tup W k` is the set of all `k`-tuples (repetitions allowed) of vertices of `W`; it has
`|W|^k` elements.  We count tuples with prescribed coordinates and pairs of tuples that meet, and
prove the exact averaging identity

  `∑_{s ∈ W^k} cutQ G s (X ∘ s) = k (k-1) |W|^{k-2} · D_X(W)`,

where `D_X(W) = #{(a, b) ∈ W² : a ~ b, X a ≠ X b}` is the doubled cut of `G[W]` with labelling
`X`.  This is the "easy direction" relating cuts of `k`-samples to cuts of the whole level.
-/

namespace NashWilliams18.Vortex124

open Finset

variable {V : Type*} [DecidableEq V]

/-- All `k`-tuples of vertices of `W`. -/
def tup (W : Finset V) (k : ℕ) : Finset (Fin k → V) := Fintype.piFinset fun _ => W

omit [DecidableEq V] in
lemma card_tup (W : Finset V) (k : ℕ) : (tup W k).card = W.card ^ k :=
  Fintype.card_piFinset_const _ _

omit [DecidableEq V] in
lemma mem_tup {W : Finset V} {k : ℕ} {s : Fin k → V} : s ∈ tup W k ↔ ∀ l, s l ∈ W := by
  simp [tup, Fintype.mem_piFinset]

/-- Tuples of `W` with prescribed values on a set `P` of positions. -/
lemma card_tup_fix (W : Finset V) {k : ℕ} (P : Finset (Fin k)) (c : Fin k → V)
    (hc : ∀ l ∈ P, c l ∈ W) :
    ((tup W k).filter (fun s => ∀ l ∈ P, s l = c l)).card = W.card ^ (k - P.card) := by
  have hset : (tup W k).filter (fun s => ∀ l ∈ P, s l = c l) =
      Fintype.piFinset (fun l => if l ∈ P then ({c l} : Finset V) else W) := by
    ext s
    simp only [mem_filter, mem_tup, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ l
      split_ifs with hl
      · rw [mem_singleton]; exact h2 l hl
      · exact h1 l
    · intro h
      refine ⟨fun l => ?_, fun l hl => ?_⟩
      · have := h l
        split_ifs at this with hl
        · rw [mem_singleton] at this; rw [this]; exact hc l hl
        · exact this
      · have := h l
        rw [if_pos hl, mem_singleton] at this
        exact this
  rw [hset, Fintype.card_piFinset]
  have : ∀ l, ((if l ∈ P then ({c l} : Finset V) else W)).card =
      if l ∈ P then 1 else W.card := fun l => by split_ifs <;> simp
  simp only [this]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (· ∈ P)
  have h2 : (univ.filter (· ∈ P) : Finset (Fin k)) = P := by ext; simp
  rw [h2, card_univ, Fintype.card_fin] at h1
  omega

/-- Tuples with two prescribed (distinct) coordinates. -/
lemma card_tup_fix2 (W : Finset V) {k : ℕ} {i j : Fin k} (hij : i ≠ j) {a b : V}
    (ha : a ∈ W) (hb : b ∈ W) :
    ((tup W k).filter (fun s => s i = a ∧ s j = b)).card = W.card ^ (k - 2) := by
  have h := card_tup_fix W {i, j} (fun l => if l = i then a else b) (by
    intro l _
    dsimp (config := { failIfUnchanged := false }) only
    split_ifs
    · exact ha
    · exact hb)
  rw [card_pair hij] at h
  rw [← h]
  congr 1
  ext s
  simp only [mem_filter, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
    if_neg hij.symm, if_true]

/-- Tuples with one prescribed coordinate. -/
lemma card_tup_fix1 (W : Finset V) {k : ℕ} (i : Fin k) {a : V} (ha : a ∈ W) :
    ((tup W k).filter (fun s => s i = a)).card = W.card ^ (k - 1) := by
  have h := card_tup_fix W {i} (fun _ => a) (by intro l _; exact ha)
  rw [card_singleton] at h
  rw [← h]
  congr 1
  ext s
  simp

/-- Sum of a function of two distinct coordinates over all tuples. -/
lemma sum_tup_two (W : Finset V) {k : ℕ} {i j : Fin k} (hij : i ≠ j) (g : V → V → ℝ) :
    ∑ s ∈ tup W k, g (s i) (s j) = (W.card : ℝ) ^ (k - 2) * ∑ a ∈ W, ∑ b ∈ W, g a b := by
  rw [← sum_fiberwise_of_maps_to (s := tup W k) (t := W ×ˢ W) (g := fun s => (s i, s j))
    (fun s hs => mem_product.mpr ⟨mem_tup.mp hs i, mem_tup.mp hs j⟩), sum_product, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b hb => ?_
  have : ∀ s ∈ (tup W k).filter (fun s => (s i, s j) = (a, b)), g (s i) (s j) = g a b := by
    intro s hs
    have := (mem_filter.mp hs).2
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  congr 1
  have hf : (tup W k).filter (fun s => (s i, s j) = (a, b)) =
      (tup W k).filter (fun s => s i = a ∧ s j = b) := by
    ext s; simp
  rw [hf, card_tup_fix2 W hij ha hb]
  push_cast; ring

/-- Tuples with two equal (distinct) coordinates. -/
lemma card_tup_eq_le (W : Finset V) {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    ((tup W k).filter (fun s => s i = s j)).card ≤ W.card ^ (k - 1) := by
  have hk : 2 ≤ k := by
    have := i.isLt; have := j.isLt
    rcases Nat.lt_or_ge k 2 with h | h
    · exfalso; apply hij; ext; omega
    · exact h
  have hsub : (tup W k).filter (fun s => s i = s j) ⊆
      W.biUnion (fun a => (tup W k).filter (fun s => s i = a ∧ s j = a)) := by
    intro s hs
    rw [mem_filter] at hs
    rw [mem_biUnion]
    exact ⟨s i, mem_tup.mp hs.1 i, mem_filter.mpr ⟨hs.1, rfl, hs.2.symm⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a ∈ W, ((tup W k).filter (fun s => s i = a ∧ s j = a)).card := card_biUnion_le
    _ = ∑ _a ∈ W, W.card ^ (k - 2) := sum_congr rfl fun a ha => card_tup_fix2 W hij ha ha
    _ = W.card ^ (k - 1) := by
        rw [sum_const, smul_eq_mul, ← pow_succ']
        congr 1; omega

/-- Pairs of tuples with `s i = t j`. -/
lemma card_pairs_eq_le (W : Finset V) {k : ℕ} (i j : Fin k) :
    ((tup W k ×ˢ tup W k).filter (fun st => st.1 i = st.2 j)).card ≤ W.card ^ (2 * k - 1) := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  have hsub : (tup W k ×ˢ tup W k).filter (fun st => st.1 i = st.2 j) ⊆
      W.biUnion (fun a => ((tup W k).filter (fun s => s i = a)) ×ˢ
        ((tup W k).filter (fun t => t j = a))) := by
    intro st hst
    rw [mem_filter, mem_product] at hst
    rw [mem_biUnion]
    refine ⟨st.1 i, mem_tup.mp hst.1.1 i, mem_product.mpr ⟨mem_filter.mpr ⟨hst.1.1, rfl⟩,
      mem_filter.mpr ⟨hst.1.2, hst.2.symm⟩⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a ∈ W, (((tup W k).filter (fun s => s i = a)) ×ˢ
        ((tup W k).filter (fun t => t j = a))).card := card_biUnion_le
    _ = ∑ _a ∈ W, W.card ^ (k - 1) * W.card ^ (k - 1) := sum_congr rfl fun a ha => by
        rw [card_product, card_tup_fix1 W i ha, card_tup_fix1 W j ha]
    _ = W.card ^ (2 * k - 1) := by
        rw [sum_const, smul_eq_mul, ← pow_add, ← pow_succ']
        congr 1; omega

/-- Pairs of tuples that share a vertex. -/
lemma card_pairs_meet_le (W : Finset V) (k : ℕ) :
    ((tup W k ×ˢ tup W k).filter (fun st => ∃ i j, st.1 i = st.2 j)).card ≤
      k ^ 2 * W.card ^ (2 * k - 1) := by
  have hsub : (tup W k ×ˢ tup W k).filter (fun st => ∃ i j, st.1 i = st.2 j) ⊆
      (univ ×ˢ univ : Finset (Fin k × Fin k)).biUnion
        (fun ij => (tup W k ×ˢ tup W k).filter (fun st => st.1 ij.1 = st.2 ij.2)) := by
    intro st hst
    rw [mem_filter] at hst
    obtain ⟨i, j, h⟩ := hst.2
    rw [mem_biUnion]
    exact ⟨(i, j), by simp, mem_filter.mpr ⟨hst.1, h⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ ij ∈ (univ ×ˢ univ : Finset (Fin k × Fin k)),
        ((tup W k ×ˢ tup W k).filter (fun st => st.1 ij.1 = st.2 ij.2)).card := card_biUnion_le
    _ ≤ ∑ _ij ∈ (univ ×ˢ univ : Finset (Fin k × Fin k)), W.card ^ (2 * k - 1) :=
        sum_le_sum fun ij _ => card_pairs_eq_le W ij.1 ij.2
    _ = k ^ 2 * W.card ^ (2 * k - 1) := by
        rw [sum_const, smul_eq_mul, card_product, card_univ, Fintype.card_fin, sq]

/-- Doubled cut of `G[W]` with labelling `X`. -/
noncomputable def dcut (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (X : V → Bool) :
    ℝ :=
  ∑ a ∈ W, ∑ b ∈ W, if G.Adj a b ∧ X a ≠ X b then 1 else 0

/-- **Averaging identity**: the total doubled cut of all `k`-samples of `W` under the labelling
`X` is `k(k-1)|W|^{k-2}` times the doubled cut of `W`. -/
theorem sum_cutQ_tup (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (k : ℕ)
    (X : V → Bool) :
    ∑ s ∈ tup W k, Sampling.cutQ G s (fun l => X (s l)) =
      (k * (k - 1) : ℝ) * (W.card : ℝ) ^ (k - 2) * dcut G W X := by
  set g : V → V → ℝ := fun x y => if G.Adj x y ∧ X x ≠ X y then 1 else 0 with hg
  have hcut : ∀ s : Fin k → V, Sampling.cutQ G s (fun l => X (s l)) =
      ∑ i, ∑ j, g (s i) (s j) := fun s => rfl
  simp only [hcut]
  rw [sum_comm]
  have hrow : ∀ i : Fin k, ∑ s ∈ tup W k, ∑ j, g (s i) (s j) =
      ((k : ℝ) - 1) * ((W.card : ℝ) ^ (k - 2) * dcut G W X) := by
    intro i
    rw [sum_comm]
    rw [← sum_erase_add _ _ (mem_univ i)]
    have hdiag : ∑ s ∈ tup W k, g (s i) (s i) = 0 := by
      refine sum_eq_zero fun s _ => ?_
      simp [hg]
    rw [hdiag, add_zero]
    have : ∀ j ∈ (univ : Finset (Fin k)).erase i, ∑ s ∈ tup W k, g (s i) (s j) =
        (W.card : ℝ) ^ (k - 2) * dcut G W X := by
      intro j hj
      rw [sum_tup_two W (ne_of_mem_erase hj).symm g]
      rfl
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ i),
      card_univ, Fintype.card_fin]
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
    rw [Nat.cast_sub hk]; push_cast; ring
  rw [sum_congr rfl fun i _ => hrow i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end NashWilliams18.Vortex124
