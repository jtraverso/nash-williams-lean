/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Global

@[expose] public section

/-!
# Proposition 4.7: perturbing to a nonzero untied weighting

Together with the discharging argument this proves Conjecture 4.5: every triangle-covered
edge weighting of a graph with `δ(G) ≥ 3n/4` has nonnegative value.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Proposition 4.7 (in the form used): a triangle-covered weighting of negative value can be
perturbed into a nonzero untied triangle-covered weighting of negative value. -/
lemma exists_good_perturbation (φ : Sym2 V → ℝ)
    (hcov : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → 0 ≤ φ s(a, b) + φ s(a, c) + φ s(b, c))
    (hS : ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) < 0) :
    ∃ ψ, GoodWeighting G ψ ∧ ∑ a, ∑ b, (if G.Adj a b then ψ s(a, b) else 0) < 0 := by
  set eqv := Fintype.equivFin (Sym2 V)
  set c : Sym2 V → ℝ := fun e => ((eqv e : ℕ) : ℝ) + 1 with hc
  have cpos : ∀ e, 0 < c e := fun e => by simp only [hc]; positivity
  have cinj : ∀ e e', c e = c e' → e = e' := by
    intro e e' h
    simp only [hc, add_left_inj, Nat.cast_inj] at h
    exact eqv.injective (Fin.ext h)
  set S := ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0)
  set K := ∑ a, ∑ b, (if G.Adj a b then c s(a, b) else 0)
  have hK : 0 ≤ K := sum_nonneg fun a _ => sum_nonneg fun b _ => by
    split_ifs
    · exact (cpos _).le
    · exact le_rfl
  set t0 := -S / (K + 1)
  have ht0 : 0 < t0 := div_pos (by linarith) (by linarith)
  set B : Finset ℝ := univ.image (fun e => -φ e / c e) ∪
    (univ ×ˢ univ).image (fun p : Sym2 V × Sym2 V => (φ p.2 - φ p.1) / (c p.1 - c p.2))
  obtain ⟨t, ⟨ht1, ht2⟩, htB⟩ :=
    ((Set.Ioo_infinite ht0).diff B.finite_toSet).nonempty
  simp only [SetLike.mem_coe] at htB
  set ψ : Sym2 V → ℝ := fun e => φ e + t * c e with hψ
  refine ⟨ψ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b d hab had hbd
    have := hcov a b d hab had hbd
    have := cpos s(a, b); have := cpos s(a, d); have := cpos s(b, d)
    simp only [hψ]
    nlinarith
  · intro e he
    apply htB
    refine mem_union_left _ (mem_image.2 ⟨e, mem_univ _, ?_⟩)
    have hce := (cpos e).ne'
    simp only [hψ] at he
    field_simp
    linarith
  · intro e e' he
    by_contra hne
    apply htB
    refine mem_union_right _ (mem_image.2 ⟨(e, e'), mem_univ _, ?_⟩)
    have hcc : c e - c e' ≠ 0 := fun h => hne (cinj e e' (by linarith))
    simp only [hψ] at he
    field_simp
    linarith
  · have e : ∑ a, ∑ b, (if G.Adj a b then ψ s(a, b) else 0) = S + t * K := by
      simp only [S, K, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [hψ]
    rw [e]
    have : t * (K + 1) < t0 * (K + 1) := mul_lt_mul_of_pos_right ht2 (by linarith)
    have h2 : t0 * (K + 1) = -S := div_mul_cancel₀ _ (by linarith)
    nlinarith

/-- **Conjecture 4.5** (the Fractional Nash-Williams' Conjecture in dual form, proved here):
every triangle-covered edge weighting of a graph with `δ(G) ≥ 3n/4` has nonnegative value.
The value is computed over ordered pairs of adjacent vertices, i.e. it is twice `|φ|`. -/
theorem covered_sum_nonneg (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (φ : Sym2 V → ℝ)
    (hcov : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      0 ≤ φ s(a, b) + φ s(a, c) + φ s(b, c)) :
    0 ≤ ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) := by
  by_contra h
  push_neg at h
  obtain ⟨ψ, hψ, hneg⟩ := exists_good_perturbation G φ hcov h
  have := good_sum_nonneg G ψ hδ hψ
  linarith

end NashWilliams.Frac
