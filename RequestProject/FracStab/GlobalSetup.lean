/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.Rules
public import RequestProject.FracStab.Structure

@[expose] public section

/-!
# Setting up the proof of Theorem 10.9

Notation (for a threshold `t` and a reference weight `F₀ > 0`, which will be `|φ(f₀)|` for a
heaviest pair `f₀ ∈ E₂`):

* `negW φ f = |φ(f)|` for a negative pair `f`;
* `E2 = N ∖ (E₀ ∪ E₁)` — the negative pairs that discharge in neither additional rule;
* `HH F₀` — negative pairs `f` with `|φ(f)| ≥ (3/4) F₀`;
* `Qp t F₀ = HH F₀ ∖ E2` (the paper's `Q'`);
* `SS t F₀ s` — vertices incident with at least `s n` pairs of `Qp` (the paper's `S`).

Main results: `ch2_nonneg_of_mem` (pairs that discharge end nonnegative), `card_Qp_lt`
(Claim 10.9.1) and `card_SS_le`.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- `|φ(f)|` for a negative pair. -/
def negW (f : V × V) : ℝ := -φ s(f.1, f.2)

/-- Negative pairs discharging in neither additional rule. -/
noncomputable def E2 (t : ℝ) : Finset (V × V) := negPairs G φ \ (E0 G φ t ∪ E1 G φ t)

/-- Negative pairs of weight at least `(3/4) F₀`. -/
noncomputable def HH (F₀ : ℝ) : Finset (V × V) :=
  (negPairs G φ).filter fun f => 3 / 4 * F₀ ≤ negW φ f

/-- The paper's `Q'`. -/
noncomputable def Qp (t F₀ : ℝ) : Finset (V × V) := HH G φ F₀ \ E2 G φ t

open Classical in
/-- The paper's `S`: vertices incident with at least `s n` pairs of `Qp`. -/
noncomputable def SS (t F₀ s : ℝ) : Finset V :=
  univ.filter fun v => s * Fintype.card V ≤ ((univ.filter fun w => (v, w) ∈ Qp G φ t F₀).card : ℝ)

/-! ### Generic facts about one layer of the additional rules -/

lemma stepCh_of_mem {c : V × V → ℝ} {E : Finset (V × V)} {g : V × V} (hg : g ∈ E) :
    stepCh G φ c E g =
      ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ)) else 0) +
        1 / (2 * ((negPairs G φ).card : ℝ))) := by
  unfold stepCh; rw [if_pos hg]; ring

lemma stepCh_of_not_mem {c : V × V → ℝ} {E : Finset (V × V)} {g : V × V} (hg : g ∉ E) :
    stepCh G φ c E g = c g +
      ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ)) else 0) +
        1 / (2 * ((negPairs G φ).card : ℝ))) := by
  unfold stepCh; rw [if_neg hg]; ring

lemma recv_nonneg_of {c : V × V → ℝ} {E : Finset (V × V)} (hc : ∀ f ∈ E, 0 ≤ c f) (g : V × V) :
    0 ≤ ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ))
      else 0) + 1 / (2 * ((negPairs G φ).card : ℝ))) := by
  refine sum_nonneg fun f hf => mul_nonneg (hc f hf) ?_
  apply add_nonneg
  · split_ifs
    · positivity
    · exact le_rfl
  · positivity

/-- The "global half" received by `g`: at least `c f / (2 |N|)` from every `f ∈ E`. -/
lemma recv_ge_global {c : V × V → ℝ} {E : Finset (V × V)} (hc : ∀ f ∈ E, 0 ≤ c f)
    (g : V × V) (T : Finset (V × V)) (hT : T ⊆ E) :
    ∑ f ∈ T, c f / (2 * ((negPairs G φ).card : ℝ)) ≤
      ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ))
        else 0) + 1 / (2 * ((negPairs G φ).card : ℝ))) := by
  calc ∑ f ∈ T, c f / (2 * ((negPairs G φ).card : ℝ))
      ≤ ∑ f ∈ E, c f / (2 * ((negPairs G φ).card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hT fun f hf _ => div_nonneg (hc f hf) (by positivity)
    _ ≤ _ := by
        refine sum_le_sum fun f hf => ?_
        rw [div_eq_mul_one_div]
        refine mul_le_mul_of_nonneg_left ?_ (hc f hf)
        have : (0 : ℝ) ≤ if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ))
            else 0 := by split_ifs <;> positivity
        linarith

/-- The "local half" received by `g`: at least `c f / (2 |inc f|)` from every `f ∈ E` sharing
a vertex with `g`. -/
lemma recv_ge_local {c : V × V → ℝ} {E : Finset (V × V)} (hc : ∀ f ∈ E, 0 ≤ c f)
    (g : V × V) (T : Finset (V × V)) (hT : T ⊆ E) (hTg : ∀ f ∈ T, g ∈ incPairs G φ f) :
    ∑ f ∈ T, c f / (2 * ((incPairs G φ f).card : ℝ)) ≤
      ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ))
        else 0) + 1 / (2 * ((negPairs G φ).card : ℝ))) := by
  calc ∑ f ∈ T, c f / (2 * ((incPairs G φ f).card : ℝ))
      = ∑ f ∈ T, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ))
          else 0)) := by
        refine sum_congr rfl fun f hf => ?_
        rw [if_pos (hTg f hf)]; ring
    _ ≤ ∑ f ∈ E, c f * ((if g ∈ incPairs G φ f then 1 / (2 * ((incPairs G φ f).card : ℝ))
          else 0)) := by
        refine sum_le_sum_of_subset_of_nonneg hT fun f hf _ => mul_nonneg (hc f hf) ?_
        split_ifs <;> positivity
    _ ≤ _ := by
        refine sum_le_sum fun f hf => mul_le_mul_of_nonneg_left ?_ (hc f hf)
        have : (0 : ℝ) ≤ 1 / (2 * ((negPairs G φ).card : ℝ)) := by positivity
        linarith

omit [DecidableEq V] in
lemma ch0_nonneg_of_mem_E0 {t : ℝ} (ht : 0 ≤ t) {f : V × V} (hf : f ∈ E0 G φ t) :
    0 ≤ ch0 G φ f := by
  simp only [E0, mem_filter, mem_negPairs] at hf
  nlinarith [hf.1.2]

lemma ch1_nonneg_of_mem_E1 {t : ℝ} (ht : 0 ≤ t) {f : V × V} (hf : f ∈ E1 G φ t) :
    0 ≤ ch1 G φ t f := by
  simp only [E1, mem_filter, mem_negPairs] at hf
  nlinarith [hf.1.2]

/-- Pairs that discharge in one of the additional rules end with nonnegative charge. -/
lemma ch2_nonneg_of_mem {t : ℝ} (ht : 0 ≤ t) {g : V × V}
    (hg : g ∈ E0 G φ t ∨ g ∈ E1 G φ t) : 0 ≤ ch2 G φ t g := by
  have h0 : ∀ f ∈ E0 G φ t, 0 ≤ ch0 G φ f := fun f hf => ch0_nonneg_of_mem_E0 G φ ht hf
  have h1 : ∀ f ∈ E1 G φ t, 0 ≤ ch1 G φ t f := fun f hf => ch1_nonneg_of_mem_E1 G φ ht hf
  unfold ch2
  by_cases hg1 : g ∈ E1 G φ t
  · rw [stepCh_of_mem G φ hg1]; exact recv_nonneg_of G φ h1 g
  · have hg0 : g ∈ E0 G φ t := hg.resolve_right hg1
    rw [stepCh_of_not_mem G φ hg1]
    have : 0 ≤ ch1 G φ t g := by
      unfold ch1; rw [stepCh_of_mem G φ hg0]; exact recv_nonneg_of G φ h0 g
    have := recv_nonneg_of G φ h1 g
    linarith

omit [DecidableEq V] in
/-- The number of ordered negative pairs is at most `n²`. -/
lemma card_negPairs_le : ((negPairs G φ).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have : (negPairs G φ).card ≤ Fintype.card (V × V) := card_le_univ _
  rw [Fintype.card_prod] at this
  have h : ((negPairs G φ).card : ℝ) ≤ ((Fintype.card V * Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast this
  rw [Nat.cast_mul] at h; nlinarith

lemma Qp_subset_E01 {t F₀ : ℝ} : Qp G φ t F₀ ⊆ E0 G φ t ∪ E1 G φ t := by
  intro f hf
  rw [Qp, mem_sdiff, E2, mem_sdiff, not_and, not_not] at hf
  exact hf.2 (mem_filter.1 hf.1).1

/-- **Claim 10.9.1.** If some negative pair `g ∈ E2` with `|φ(g)| ≤ F₀` ends with negative
charge, then `|Q'| < (32/3) (ε / t) n²`. -/
theorem card_Qp_lt (hφ : GoodWeighting G φ) {ε t F₀ : ℝ} (hε0 : 0 ≤ ε) (ht : 0 < t) (hF₀ : 0 < F₀)
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree) {g : V × V}
    (hgN : g ∈ negPairs G φ) (hg : g ∉ E0 G φ t ∪ E1 G φ t) (hgF : negW φ g ≤ F₀)
    (hneg : ch2 G φ t g < 0) :
    ((Qp G φ t F₀).card : ℝ) < 32 / 3 * (ε / t) * (Fintype.card V : ℝ) ^ 2 := by
  have h0 : ∀ f ∈ E0 G φ t, 0 ≤ ch0 G φ f := fun f hf => ch0_nonneg_of_mem_E0 G φ ht.le hf
  have h1 : ∀ f ∈ E1 G φ t, 0 ≤ ch1 G φ t f := fun f hf => ch1_nonneg_of_mem_E1 G φ ht.le hf
  rw [mem_union, not_or] at hg
  set N : ℝ := ((negPairs G φ).card : ℝ)
  have hNpos : 0 < N := by simp only [N]; exact_mod_cast card_pos.2 ⟨g, hgN⟩
  set Q := Qp G φ t F₀
  -- the two parts of `Q`
  set Q0 := Q.filter (· ∈ E0 G φ t)
  set Q1 := Q.filter (· ∉ E0 G φ t)
  have hQ1 : Q1 ⊆ E1 G φ t := by
    intro f hf
    simp only [Q1, mem_filter] at hf
    have := Qp_subset_E01 G φ hf.1
    rw [mem_union] at this; exact this.resolve_left hf.2
  have hQ0 : Q0 ⊆ E0 G φ t := fun f hf => (mem_filter.1 hf).2
  have r1 := recv_ge_global G φ h0 g Q0 hQ0
  have r2 := recv_ge_global G φ h1 g Q1 hQ1
  -- charges after the two rules
  have hch1 : ch1 G φ t g = ch0 G φ g + _ := stepCh_of_not_mem G φ hg.1
  have hch2 : ch2 G φ t g = ch1 G φ t g + _ := stepCh_of_not_mem G φ hg.2
  -- lower bounds on the senders
  have hwQ : ∀ f ∈ Q, 3 / 4 * F₀ ≤ negW φ f := fun f hf => by
    simp only [Q, Qp, HH, mem_sdiff, mem_filter] at hf; exact hf.1.2
  have s0 : ∀ f ∈ Q0, t * (3 / 4 * F₀) / (2 * N) ≤ ch0 G φ f / (2 * N) := by
    intro f hf
    have hfE := hQ0 hf
    simp only [E0, mem_filter] at hfE
    have := hwQ f (mem_filter.1 hf).1
    apply div_le_div_of_nonneg_right _ (by positivity)
    unfold negW at this; nlinarith
  have s1 : ∀ f ∈ Q1, t * (3 / 4 * F₀) / (2 * N) ≤ ch1 G φ t f / (2 * N) := by
    intro f hf
    have hfE := hQ1 hf
    simp only [E1, mem_filter] at hfE
    have := hwQ f (mem_filter.1 hf).1
    apply div_le_div_of_nonneg_right _ (by positivity)
    unfold negW at this; nlinarith
  have t0 := sum_le_sum s0
  have t1 := sum_le_sum s1
  rw [sum_const, nsmul_eq_mul] at t0 t1
  have hsplit : (Q0.card : ℝ) + Q1.card = Q.card := by
    exact_mod_cast card_filter_add_card_filter_not _
  -- the initial charge of `g`
  have hlb := chNeg_lb G φ hφ hδ (mem_negPairs G φ |>.1 hgN).1 (mem_negPairs G φ |>.1 hgN).2
  have hg0 : ch0 G φ g = chNeg G φ g.1 g.2 := rfl
  have hgF' : -φ s(g.1, g.2) ≤ F₀ := hgF
  have hchg : -4 * ε * F₀ ≤ ch0 G φ g := by
    rw [hg0]
    have : -4 * ε * F₀ ≤ -4 * ε * (-φ s(g.1, g.2)) := by nlinarith
    linarith
  -- combine
  have hQ : (Q.card : ℝ) * (t * (3 / 4 * F₀) / (2 * N)) < 4 * ε * F₀ := by
    have : ch0 G φ g + ((Q0.card : ℝ) * (t * (3 / 4 * F₀) / (2 * N)) +
        (Q1.card : ℝ) * (t * (3 / 4 * F₀) / (2 * N))) < 0 := by linarith
    rw [← hsplit]; nlinarith
  have hNle := card_negPairs_le G φ
  set n2 : ℝ := (Fintype.card V : ℝ) ^ 2
  have hkey : (Q.card : ℝ) * (t * (3 / 4 * F₀)) < 4 * ε * F₀ * (2 * N) := by
    have e : (Q.card : ℝ) * (t * (3 / 4 * F₀) / (2 * N)) * (2 * N) =
        (Q.card : ℝ) * (t * (3 / 4 * F₀)) := by field_simp
    have := mul_lt_mul_of_pos_right hQ (by positivity : (0:ℝ) < 2 * N)
    linarith
  have hkey2 : (Q.card : ℝ) * t * (3 / 4) * F₀ < 8 * ε * n2 * F₀ := by
    have : 4 * ε * F₀ * (2 * N) ≤ 8 * ε * n2 * F₀ := by
      have := mul_le_mul_of_nonneg_left hNle (by positivity : (0:ℝ) ≤ 8 * ε * F₀)
      linarith
    nlinarith
  have hkey3 : (Q.card : ℝ) * t * (3 / 4) < 8 * ε * n2 := lt_of_mul_lt_mul_right hkey2 hF₀.le
  rw [show 32 / 3 * (ε / t) * n2 = (32 / 3 * ε * n2) / t by ring, lt_div_iff₀ ht]
  linarith

open Classical in
/-- `|S| · s n ≤ |Q'|`. -/
lemma card_SS_mul_le (t F₀ s : ℝ) :
    ((SS G φ t F₀ s).card : ℝ) * (s * Fintype.card V) ≤ ((Qp G φ t F₀).card : ℝ) := by
  have hsum : ∑ v, (((univ.filter fun w => (v, w) ∈ Qp G φ t F₀).card : ℕ) : ℝ) =
      ((Qp G φ t F₀).card : ℝ) := by
    have : ∑ v, (univ.filter fun w => (v, w) ∈ Qp G φ t F₀).card = (Qp G φ t F₀).card := by
      rw [← card_sigma]
      refine card_bij (fun p _ => (p.1, p.2)) ?_ ?_ ?_
      · intro p hp; simp only [mem_sigma, mem_filter, mem_univ, true_and] at hp; exact hp
      · intro p _ q _ h
        simp only [Prod.mk.injEq] at h
        exact Sigma.ext h.1 (heq_of_eq h.2)
      · intro q hq
        exact ⟨⟨q.1, q.2⟩, by simp only [mem_sigma, mem_filter, mem_univ, true_and]; exact hq, rfl⟩
    exact_mod_cast this
  rw [← hsum]
  calc ((SS G φ t F₀ s).card : ℝ) * (s * Fintype.card V)
      = ∑ v ∈ SS G φ t F₀ s, s * (Fintype.card V : ℝ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ v ∈ SS G φ t F₀ s, (((univ.filter fun w => (v, w) ∈ Qp G φ t F₀).card : ℕ) : ℝ) := by
        refine sum_le_sum fun v hv => ?_
        simp only [SS, mem_filter] at hv; exact hv.2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _

end NashWilliams.Frac
