/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TeoremaB

/-! # BlowupB.TeoremaBBalanced — Theorem B for ε-balanced blowups under a finite condition on `F`

`BalancedWeights F w`: positive type weights with `∑_{c : c ::ₘ {a,b} ∈ F} w (c ::ₘ {a,b}) = t` for
every allowed pair `ab` — a finite linear feasibility condition on the family alone (the load
equations of the balanced complete blowup).

**`teoremaB_balanced`**: under `KeevashTypedSpec F`, a family with balanced weights has the
following property. There are `η, δ > 0` and `N` such that every graph on `n ≥ N` vertices using
only allowed pairs, with at most `δ n` allowed non-neighbours per vertex, all classes of size in
`[(1/t - η) n, (1/t + η) n]`, and integrally `F`-divisible (Definition 13.5), has an
`F`-decomposition. This is the form of Theorem B in `PLAN_17_DESDE_13_16_20261010.md` §1, with
the hinge hypothesis removed and the fractional hypothesis replaced by `BalancedWeights`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

/-- Balanced type weights (finite condition on the family). -/
def BalancedWeights (F : Finset (Multiset (Fin t))) (w : Multiset (Fin t) → ℝ) : Prop :=
  (∀ τ ∈ F, 0 < w τ) ∧ ∀ a b, AllowedPair F a b →
    ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F),
      w (c ::ₘ ({a, b} : Multiset (Fin t))) = t

theorem sum_types_swap (F : Finset (Multiset (Fin t))) (w : Multiset (Fin t) → ℝ) (x : Fin t → ℝ)
    (a b : Fin t) (n : ℝ) :
    ∑ τ ∈ F, w τ * ((∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) = τ), x c) / n) =
      ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F),
        w (c ::ₘ ({a, b} : Multiset (Fin t))) * x c / n := by
  classical
  simp only [sum_div, mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  simp only [mul_ite, mul_zero, ite_div, zero_div]
  rw [sum_ite_eq]
  split_ifs <;> ring

/-- **Theorem B for ε-balanced nearly complete blowups**, from the typed Keevash interface. -/
theorem teoremaB_balanced {F : Finset (Multiset (Fin t))} (hK : KeevashTypedSpec F)
    (w : Multiset (Fin t) → ℝ) (hw : BalancedWeights F w) (ht : 1 ≤ t) :
    ∃ η : ℝ, 0 < η ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, (1 / t - η) * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) ∧
          ((univ.filter fun v => p v = i).card : ℝ) ≤ (1 / t + η) * Fintype.card V) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset := by
  obtain ⟨hwpos, hwsum⟩ := hw
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  -- weight bounds
  set S : ℝ := 1 + ∑ τ ∈ F, (w τ + 1 / w τ) with hS
  have hS1 : 1 ≤ S := by
    have : 0 ≤ ∑ τ ∈ F, (w τ + 1 / w τ) :=
      sum_nonneg fun τ hτ => add_nonneg (hwpos τ hτ).le (one_div_pos.mpr (hwpos τ hτ)).le
    linarith
  set ω₁ : ℝ := 1 / S with hω₁
  have hω₁0 : 0 < ω₁ := by positivity
  have hwb : ∀ τ ∈ F, ω₁ ≤ w τ ∧ w τ ≤ 1 / ω₁ := by
    intro τ hτ
    have hpos := hwpos τ hτ
    have hle : w τ + 1 / w τ ≤ ∑ τ ∈ F, (w τ + 1 / w τ) :=
      single_le_sum (f := fun τ => w τ + 1 / w τ)
        (fun σ hσ => add_nonneg (hwpos σ hσ).le (one_div_pos.mpr (hwpos σ hσ)).le) hτ
    have hinv : 0 < 1 / w τ := one_div_pos.mpr hpos
    constructor
    · rw [hω₁, div_le_iff₀ (by linarith)]
      have : 1 / w τ ≤ S := by linarith
      calc 1 = w τ * (1 / w τ) := by field_simp
        _ ≤ w τ * S := mul_le_mul_of_nonneg_left this hpos.le
    · rw [hω₁, one_div_one_div]; linarith
  obtain ⟨ε, hε, N₁, δ, hδ, hB⟩ := teoremaB_of_keevash hK (1 / (2 * t)) ω₁ (by positivity) hω₁0
  set η : ℝ := min (ε / (2 * t)) (1 / (2 * t)) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨η, hη0, max N₁ ⌈8 * t / ε⌉₊, δ, hδ, ?_⟩
  intro V _ _ G _ p d hN hadj hmiss hd hcls hdiv
  have hN1 : N₁ ≤ Fintype.card V := le_trans (le_max_left _ _) hN
  have hN2 : ⌈8 * (t : ℝ) / ε⌉₊ ≤ Fintype.card V := le_trans (le_max_right _ _) hN
  have hnb : 8 * (t : ℝ) / ε ≤ Fintype.card V := (Nat.le_ceil _).trans (by exact_mod_cast hN2)
  have hnpos : (0 : ℝ) < Fintype.card V := by
    have : (0 : ℝ) < 8 * t / ε := by positivity
    linarith
  have hεn : 8 * (t : ℝ) ≤ ε * Fintype.card V := by
    have := (div_le_iff₀ hε).mp hnb; linarith
  refine hB G p d hN1 hadj hmiss hd (fun i => ?_) ⟨w, hwb, ?_⟩ hdiv
  · -- classes are large
    have h1 := (hcls i).1
    have hη : η ≤ 1 / (2 * t) := min_le_right _ _
    have : 1 / (2 * (t : ℝ)) ≤ 1 / t - η := by
      have e : 1 / (t : ℝ) = 1 / (2 * t) + 1 / (2 * t) := by field_simp; ring
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right this hnpos.le) h1
  · -- loads
    intro a b hab
    rw [sum_types_swap]
    set Sc := univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F) with hSc
    have hsumw := hwsum a b hab
    have hterm : ∀ c ∈ Sc, |w (c ::ₘ ({a, b} : Multiset (Fin t))) * nPrime (clsz p) {a, b} c /
        Fintype.card V - w (c ::ₘ ({a, b} : Multiset (Fin t))) / t| ≤
        w (c ::ₘ ({a, b} : Multiset (Fin t))) * (η + 2 / Fintype.card V) := by
      intro c hc
      have hwc := hwpos _ (mem_filter.mp hc).2
      have hc1 := (hcls c).1
      have hc2 := (hcls c).2
      have hcnt := count_pair_le_two a b c
      have hcnt0 := count_nonneg' ({a, b} : Multiset (Fin t)) c
      have e : w (c ::ₘ ({a, b} : Multiset (Fin t))) * nPrime (clsz p) {a, b} c / Fintype.card V -
          w (c ::ₘ ({a, b} : Multiset (Fin t))) / t =
          w (c ::ₘ ({a, b} : Multiset (Fin t))) *
            (nPrime (clsz p) {a, b} c / Fintype.card V - 1 / t) := by
        field_simp
      rw [e, abs_mul, abs_of_pos hwc]
      refine mul_le_mul_of_nonneg_left ?_ hwc.le
      have hlo : (1 / t - η) - 2 / Fintype.card V ≤ nPrime (clsz p) {a, b} c / Fintype.card V := by
        unfold nPrime clsz
        rw [le_div_iff₀ hnpos]
        have : (1 / (t : ℝ) - η - 2 / Fintype.card V) * Fintype.card V =
            (1 / t - η) * Fintype.card V - 2 := by field_simp
        rw [this]; linarith
      have hhi : nPrime (clsz p) {a, b} c / Fintype.card V ≤ 1 / t + η := by
        unfold nPrime clsz
        rw [div_le_iff₀ hnpos]; linarith
      have h2n : 0 ≤ 2 / (Fintype.card V : ℝ) := by positivity
      rw [abs_sub_le_iff]; constructor <;> linarith
    have hone : (1 : ℝ) = ∑ c ∈ Sc, w (c ::ₘ ({a, b} : Multiset (Fin t))) / t := by
      rw [← sum_div, hsumw, div_self ht0.ne']
    rw [hone, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← sum_mul, hsumw]
    have hη : η ≤ ε / (2 * t) := min_le_left _ _
    have h2 : 2 / (Fintype.card V : ℝ) ≤ ε / (4 * t) := by
      rw [div_le_div_iff₀ hnpos (by positivity)]; linarith
    calc (t : ℝ) * (η + 2 / Fintype.card V) ≤ t * (ε / (2 * t) + ε / (4 * t)) :=
          mul_le_mul_of_nonneg_left (by linarith) ht0.le
      _ = 3 / 4 * ε := by field_simp; ring
      _ ≤ ε := by linarith

end PartitionedTriangleAbsorption.BlowupB
