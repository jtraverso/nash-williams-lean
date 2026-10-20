/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.Charge
import RequestProject.Fractional.Global

/-!
# The additional discharging rules of §7.3 / §10.2

We work with *ordered* negative pairs `(u, v)` (each negative edge appears twice).  Starting from
the final charges `ch_F` of the Demand Proportional rule (`chNeg`), two further rules are applied
(the paper's Rules 1 and 2, with threshold `t`, which is `√ε` in the paper):

* every negative pair `f` with charge at least `t |φ(f)|` sends half of its charge uniformly to
  the negative pairs sharing a vertex with `f`, and half of it uniformly to all negative pairs.

As in the paper the rules preserve the total charge (`sum_stepCh`).  The only difference with the
paper is that the "global" half is spread over the negative pairs instead of over all edges;
this only increases what each negative pair receives.

`sum_chNeg_le` is the global counting statement of Part I: the total final charge of the negative
pairs is at most the value of `φ`.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- Ordered negative pairs. -/
noncomputable def negPairs : Finset (V × V) := univ.filter fun p => G.Adj p.1 p.2 ∧ φ s(p.1, p.2) < 0

/-- Negative pairs sharing a vertex with `f`. -/
noncomputable def incPairs (f : V × V) : Finset (V × V) :=
  (negPairs G φ).filter fun g => g.1 = f.1 ∨ g.1 = f.2 ∨ g.2 = f.1 ∨ g.2 = f.2

omit [DecidableEq V] in
lemma mem_negPairs {p : V × V} : p ∈ negPairs G φ ↔ G.Adj p.1 p.2 ∧ φ s(p.1, p.2) < 0 := by
  simp [negPairs]

lemma self_mem_incPairs {f : V × V} (hf : f ∈ negPairs G φ) : f ∈ incPairs G φ f := by
  simp [incPairs, hf]

lemma incPairs_subset (f : V × V) : incPairs G φ f ⊆ negPairs G φ := filter_subset _ _

/-- One layer of the additional discharging: the pairs in `E` send out their charge `c`. -/
noncomputable def stepCh (c : V × V → ℝ) (E : Finset (V × V)) (g : V × V) : ℝ :=
  c g - (if g ∈ E then c g else 0) +
    ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ)) else 0) +
      1 / (2 * ((negPairs G φ).card : ℝ)))

/-- The additional rules preserve the total charge of the negative pairs. -/
lemma sum_stepCh (c : V × V → ℝ) {E : Finset (V × V)} (hE : E ⊆ negPairs G φ) :
    ∑ g ∈ negPairs G φ, stepCh G φ c E g = ∑ g ∈ negPairs G φ, c g := by
  unfold stepCh
  rw [sum_add_distrib, sum_sub_distrib, ← sum_filter]
  have h1 : (negPairs G φ).filter (· ∈ E) = E := by
    ext g; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hE h, h⟩⟩
  rw [h1, sum_comm]
  have h2 : ∀ f ∈ E, ∑ g ∈ negPairs G φ, c f * ((if g ∈ incPairs G φ f then
      1 / (2 * ((incPairs G φ f).card : ℝ)) else 0) + 1 / (2 * (negPairs G φ).card)) = c f := by
    intro f hf
    rw [← mul_sum, sum_add_distrib, ← sum_filter, sum_const, sum_const, nsmul_eq_mul,
      nsmul_eq_mul]
    have hI : (negPairs G φ).filter (· ∈ incPairs G φ f) = incPairs G φ f := by
      ext g; simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨incPairs_subset G φ f h, h⟩⟩
    rw [hI]
    have hIpos : (0 : ℝ) < (incPairs G φ f).card := by
      exact_mod_cast card_pos.2 ⟨f, self_mem_incPairs G φ (hE hf)⟩
    have hNpos : (0 : ℝ) < (negPairs G φ).card := by
      exact_mod_cast card_pos.2 ⟨f, hE hf⟩
    field_simp
    ring
  rw [sum_congr rfl h2]
  ring

/-- Initial charges: the final charges of the Demand Proportional rule. -/
noncomputable def ch0 (p : V × V) : ℝ := chNeg G φ p.1 p.2

/-- Pairs discharging in Rule 1 (threshold `t`). -/
noncomputable def E0 (t : ℝ) : Finset (V × V) :=
  (negPairs G φ).filter fun f => t * (-φ s(f.1, f.2)) ≤ ch0 G φ f

/-- Charges after Rule 1. -/
noncomputable def ch1 (t : ℝ) : V × V → ℝ := stepCh G φ (ch0 G φ) (E0 G φ t)

/-- Pairs discharging in Rule 2 (threshold `t`). -/
noncomputable def E1 (t : ℝ) : Finset (V × V) :=
  (negPairs G φ).filter fun f => t * (-φ s(f.1, f.2)) ≤ ch1 G φ t f

/-- Charges after Rule 2. -/
noncomputable def ch2 (t : ℝ) : V × V → ℝ := stepCh G φ (ch1 G φ t) (E1 G φ t)

omit [DecidableEq V] in
lemma E0_subset (t : ℝ) : E0 G φ t ⊆ negPairs G φ := filter_subset _ _

lemma E1_subset (t : ℝ) : E1 G φ t ⊆ negPairs G φ := filter_subset _ _

lemma sum_ch2 (t : ℝ) :
    ∑ g ∈ negPairs G φ, ch2 G φ t g = ∑ g ∈ negPairs G φ, ch0 G φ g := by
  unfold ch2
  rw [sum_stepCh G φ _ (E1_subset G φ t), ch1, sum_stepCh G φ _ (E0_subset G φ t)]

/-- The total charge received by negative pairs is at most the total positive weight. -/
lemma sum_chNeg_le (hφ : GoodWeighting G φ) :
    ∑ g ∈ negPairs G φ, ch0 G φ g ≤ ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) := by
  -- the value as positive minus negative part
  have h3 : ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) =
      ∑ a, ∑ b, posPart G φ a b - ∑ a, ∑ b, negPart G φ a b := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    unfold posPart negPart
    by_cases hab : G.Adj a b
    · rcases (hφ.nz s(a, b)).lt_or_gt with h | h
      · simp [hab, h, not_lt.2 h.le]
      · simp [hab, h, not_lt.2 h.le]
    · simp [hab]
  have hT : ∑ u, ∑ v, ∑ w, (trans G φ u w v + trans G φ v w u) =
      ∑ a, ∑ b, ∑ x, (trans G φ a b x + trans G φ b a x) := by
    simp only [sum_add_distrib]
    congr 1
    · rw [sum_congr rfl fun u _ => sum_comm]
    · rw [sum_comm]
      rw [sum_congr rfl fun u _ => sum_comm]
      exact sum_comm
  have h2 : ∑ a, ∑ b, ∑ x, (trans G φ a b x + trans G φ b a x) ≤ ∑ a, ∑ b, posPart G φ a b :=
    sum_le_sum fun a _ => sum_le_sum fun b _ => sum_trans_le_pos G φ a b
  have hrecv0 : ∀ u v, 0 ≤ recv G φ u v := fun u v =>
    sum_nonneg fun w _ => add_nonneg (trans_nonneg G φ _ _ _) (trans_nonneg G φ _ _ _)
  -- split the charges
  have hsplit : ∑ g ∈ negPairs G φ, ch0 G φ g =
      -(∑ a, ∑ b, negPart G φ a b) + ∑ g ∈ negPairs G φ, recv G φ g.1 g.2 := by
    have : ∑ g ∈ negPairs G φ, φ s(g.1, g.2) = -(∑ a, ∑ b, negPart G φ a b) := by
      rw [negPairs, sum_filter, ← Finset.univ_product_univ, sum_product, ← sum_neg_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun b _ => ?_
      unfold negPart
      split_ifs <;> simp
    rw [← this, ← sum_add_distrib]
    rfl
  have hrecv : ∑ g ∈ negPairs G φ, recv G φ g.1 g.2 ≤ ∑ u, ∑ v, recv G φ u v := by
    calc ∑ g ∈ negPairs G φ, recv G φ g.1 g.2 ≤ ∑ g : V × V, recv G φ g.1 g.2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun g _ _ => hrecv0 _ _
      _ = ∑ u, ∑ v, recv G φ u v := by
          rw [← Finset.univ_product_univ, sum_product]
  have : ∑ u, ∑ v, recv G φ u v = ∑ u, ∑ v, ∑ w, (trans G φ u w v + trans G φ v w u) := rfl
  linarith

end NashWilliams.Frac
