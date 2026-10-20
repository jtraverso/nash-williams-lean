/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashReserve

/-! # BlowupB.ReserveWeights — densities and type weights with exact unit loads

Class sizes `nc : Fin t → ℝ`, total `n`, scale `θ`. For a pair of classes `s = {a, b}`
(a 2-multiset) the density is

`ρ s = θ · (∑_{c : c ::ₘ s ∈ F} (nc c - count c s)) / n`,

the weight of a type is `wt τ = θ / ∏_{pairs σ of τ} ρ σ` (pairs = `τ.powersetCard 2`), and the
expected number of `τ`-thirds through an `ab` pair, divided by `n`, is

`κ τ a b = ∑_{c : c ::ₘ {a,b} = τ} ρ {a,c} ρ {b,c} (nc c - count c {a,b}) / n`.

**`load_identity`**: `∑_{τ ∈ F} wt τ · κ τ a b = 1` for every allowed pair, exactly.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

/-- Eligible third vertices of class `c` for a pair of classes `s`. -/
def nPrime (nc : Fin t → ℝ) (s : Multiset (Fin t)) (c : Fin t) : ℝ := nc c - s.count c

/-- Density of the class pair `s`. -/
noncomputable def rhoM (F : Finset (Multiset (Fin t))) (nc : Fin t → ℝ) (n θ : ℝ)
    (s : Multiset (Fin t)) : ℝ :=
  θ * (∑ c ∈ univ.filter (fun c => c ::ₘ s ∈ F), nPrime nc s c) / n

/-- Product of the densities of the three pairs of a type. -/
def piT (ρ : Multiset (Fin t) → ℝ) (τ : Multiset (Fin t)) : ℝ :=
  ((τ.powersetCard 2).map ρ).prod

/-- Weight of a type. -/
noncomputable def wtT (θ : ℝ) (ρ : Multiset (Fin t) → ℝ) (τ : Multiset (Fin t)) : ℝ :=
  θ / piT ρ τ

/-- Expected `τ`-thirds through an `ab` pair, divided by `n`. -/
noncomputable def kappaT (ρ : Multiset (Fin t) → ℝ) (nc : Fin t → ℝ) (n : ℝ)
    (τ : Multiset (Fin t)) (a b : Fin t) : ℝ :=
  ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) = τ),
    ρ {a, c} * ρ {b, c} * nPrime nc {a, b} c / n

theorem piT_triple (ρ : Multiset (Fin t) → ℝ) (a b c : Fin t) :
    piT ρ (c ::ₘ ({a, b} : Multiset (Fin t))) = ρ {a, b} * (ρ {c, a} * ρ {c, b}) := by
  unfold piT
  have e : (c ::ₘ ({a, b} : Multiset (Fin t))) = c ::ₘ a ::ₘ b ::ₘ 0 := by
    rw [Multiset.insert_eq_cons, Multiset.cons_zero]
  rw [e, show (2 : ℕ) = 1 + 1 from rfl, Multiset.powersetCard_cons, Multiset.powersetCard_cons,
    Multiset.powersetCard_cons, Multiset.powersetCard_zero_right]
  simp only [Multiset.powersetCard_one, Multiset.map_cons, Multiset.map_zero, Multiset.zero_add, Multiset.map_add,
    Multiset.prod_add, Multiset.prod_cons, Multiset.prod_zero, mul_one, Multiset.cons_zero,
    Multiset.insert_eq_cons, Multiset.map_singleton, Multiset.prod_singleton]

theorem pair_comm' (a b : Fin t) : ({a, b} : Multiset (Fin t)) = {b, a} := Multiset.pair_comm a b

/-- **Exact unit loads.** -/
theorem load_identity (F : Finset (Multiset (Fin t))) (nc : Fin t → ℝ) (n θ : ℝ)
    (hn : 0 < n) (a b : Fin t)
    (hpos : ∀ c, c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F →
      rhoM F nc n θ {a, b} ≠ 0 ∧ rhoM F nc n θ {c, a} ≠ 0 ∧ rhoM F nc n θ {c, b} ≠ 0) :
    ∑ τ ∈ F, wtT θ (rhoM F nc n θ) τ * kappaT (rhoM F nc n θ) nc n τ a b = 1 ∨
      (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F) = ∅ := by
  classical
  set ρ := rhoM F nc n θ with hρ
  by_cases hE : (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F) = ∅
  · exact Or.inr hE
  left
  have hswap : ∑ τ ∈ F, wtT θ ρ τ * kappaT ρ nc n τ a b =
      ∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F),
        wtT θ ρ (c ::ₘ {a, b}) * (ρ {a, c} * ρ {b, c} * nPrime nc {a, b} c / n) := by
    unfold kappaT
    simp only [mul_sum, sum_filter, mul_ite, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_ite_eq]
  rw [hswap]
  have hterm : ∀ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F),
      wtT θ ρ (c ::ₘ {a, b}) * (ρ {a, c} * ρ {b, c} * nPrime nc {a, b} c / n) =
        θ * nPrime nc {a, b} c / n / ρ {a, b} := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hpos c (mem_filter.mp hc).2
    unfold wtT
    rw [piT_triple, pair_comm' c a, pair_comm' c b]
    rw [pair_comm' c a] at h2
    rw [pair_comm' c b] at h3
    have hn0 := hn.ne'
    field_simp
  rw [sum_congr rfl hterm, ← sum_div, ← sum_div, ← mul_sum]
  obtain ⟨c0, hc0⟩ := nonempty_iff_ne_empty.mpr hE
  have hne := (hpos c0 (mem_filter.mp hc0).2).1
  have hρab : ρ {a, b} = θ * (∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F),
      nPrime nc {a, b} c) / n := rfl
  rw [← hρab]
  exact div_self hne

end PartitionedTriangleAbsorption.BlowupB
