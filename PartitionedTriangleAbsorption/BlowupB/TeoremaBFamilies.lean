/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TeoremaBBalanced
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # BlowupB.TeoremaBFamilies — Theorem B for `F₁, F₂, F₃` (ε-balanced, nearly complete)

`F₁, F₂, F₃` (`TypedApplicationLinks`) have balanced weights `w ≡ 2` (`t = 4`): every allowed pair
has exactly two completing classes. Hence, under `KeevashTypedSpec`, every ε-balanced, nearly
complete, integrally divisible `Fᵢ`-blowup is `Fᵢ`-decomposable (the setting of Theorem 14.7, for
the three families). `F₀ = {001, 011}` has no balanced weights for any class proportions (the pair
`01` would need `π₀/π₁ + π₁/π₀ = 1`); this matches the hinge hypothesis of Theorem 14.6.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks

variable {t : ℕ}

theorem balancedWeights_const (F : Finset (Multiset (Fin t))) (k : ℝ) (hk : 0 < k)
    (hcard : ∀ a b, AllowedPair F a b →
      ((univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F).card : ℝ) * k = t) :
    BalancedWeights F (fun _ => k) := by
  refine ⟨fun _ _ => hk, fun a b hab => ?_⟩
  rw [sum_const, nsmul_eq_mul]
  exact hcard a b hab

/-- Every allowed pair of `F₁` has two completing classes. -/
theorem two_completions_F1 : ∀ a b : Fin 4, AllowedPair F1 a b →
    (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ F1).card = 2 := by
  unfold AllowedPair F1; decide

theorem two_completions_F2 : ∀ a b : Fin 4, AllowedPair F2 a b →
    (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ F2).card = 2 := by
  unfold AllowedPair F2; decide

theorem two_completions_F3 : ∀ a b : Fin 4, AllowedPair F3 a b →
    (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ F3).card = 2 := by
  unfold AllowedPair F3; decide

theorem balancedWeights_two {F : Finset (Multiset (Fin 4))}
    (h : ∀ a b : Fin 4, AllowedPair F a b →
      (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ F).card = 2) :
    BalancedWeights F (fun _ => 2) :=
  balancedWeights_const F 2 (by norm_num) fun a b hab => by
    rw [h a b hab]; norm_num

/-- **Theorem B for `F₁`, `F₂`, `F₃`** (ε-balanced, nearly complete), from the Keevash interface. -/
theorem teoremaB_F123 {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2 ∨ F = F3)
    (hK : KeevashTypedSpec F) :
    ∃ η : ℝ, 0 < η ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, (1 / 4 - η) * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) ∧
          ((univ.filter fun v => p v = i).card : ℝ) ≤ (1 / 4 + η) * Fintype.card V) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset := by
  have hw : BalancedWeights F (fun _ => 2) := by
    rcases hF with rfl | rfl | rfl
    · exact balancedWeights_two two_completions_F1
    · exact balancedWeights_two two_completions_F2
    · exact balancedWeights_two two_completions_F3
  have := teoremaB_balanced hK (fun _ => 2) hw (by norm_num)
  simpa using this

end PartitionedTriangleAbsorption.BlowupB
