/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteLinearity
import Mathlib.Tactic.Positivity

/-!
# Uniform coefficient bounds for the complete-crossing inverse

These estimates use the deliberately looser intermediate constants 7, 140,
147. They still give the final constant `512/tau` when the internal signless
inverse has constant `3/(2*tau)`.
-/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete

open Finset

variable {A B EA EB : Type*}
variable [Fintype A] [Fintype B] [Fintype EA] [Fintype EB]

structure SizeBounds (IA : A → EA → ℝ) (IB : B → EB → ℝ) (n : ℝ) : Prop where
  npos : 0 < n
  a_lower : n / 3 ≤ Fintype.card A
  b_lower : n / 3 ≤ Fintype.card B
  b_upper : (Fintype.card B : ℝ) ≤ n
  ia_row : ∀ u, (∑ f, |IA u f|) ≤ n
  ib_row : ∀ v, (∑ f, |IB v f|) ≤ n
  eb_lower : n ^ 2 / 40 ≤ Fintype.card EB

def DemandBound (g : Demand A B EA EB) (M : ℝ) : Prop :=
  (∀ f, |g.1 f| ≤ M) ∧ (∀ f, |g.2.1 f| ≤ M) ∧ ∀ uv, |g.2.2 uv| ≤ M

theorem inc_abs_le (I : A → EA → ℝ) (u : A) (d M : ℝ)
    (hrow : (∑ f, |I u f|) ≤ d) (hM : 0 ≤ M)
    (x : EA → ℝ) (hx : ∀ f, |x f| ≤ M) : |inc I x u| ≤ d * M := by
  calc
    _ ≤ ∑ f, |I u f * x f| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ f, |I u f| * M := by
      apply sum_le_sum
      intro f _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hx f) (abs_nonneg _)
    _ = (∑ f, |I u f|) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ d * M := mul_le_mul_of_nonneg_right hrow hM

theorem abs_div_le_three (n a M x : ℝ) (hn : 0 < n) (ha : n / 3 ≤ a)
    (hM : 0 ≤ M) (hx : |x| ≤ M) : |x / a| ≤ 3 * M / n := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  rw [abs_div, abs_of_pos ha0]
  calc
    _ ≤ M / a := div_le_div_of_nonneg_right hx ha0.le
    _ ≤ M / (n / 3) := div_le_div_of_nonneg_left hM (by positivity) ha
    _ = 3 * M / n := by ring

theorem firstWeights_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n : ℝ) (h : SizeBounds IA IB n) (g : Demand A B EA EB)
    (M : ℝ) (hM : 0 ≤ M) (hg : DemandBound g M) :
    (∀ fv, |(firstWeights g).1 fv| ≤ 3 * M / n) ∧
    (∀ uf, |(firstWeights g).2 uf| ≤ 3 * M / n) := by
  constructor
  · intro fv
    exact abs_div_le_three n _ M _ h.npos h.b_lower hM (hg.1 fv.1)
  · intro uf
    exact abs_div_le_three n _ M _ h.npos h.a_lower hM (hg.2.1 uf.2)

theorem firstResidual_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n : ℝ) (h : SizeBounds IA IB n) (g : Demand A B EA EB)
    (M : ℝ) (hM : 0 ≤ M) (hg : DemandBound g M) (uv : A × B) :
    |firstResidual IA IB g uv| ≤ 7 * M := by
  have hn : 0 < n := h.npos
  obtain ⟨hWA, hWB⟩ := firstWeights_abs_le IA IB n h g M hM hg
  have hloadA := inc_abs_le IA uv.1 n (3 * M / n) (h.ia_row uv.1)
    (by positivity) (fun f => (firstWeights g).1 (f, uv.2)) (fun f => hWA (f, uv.2))
  have hloadB := inc_abs_le IB uv.2 n (3 * M / n) (h.ib_row uv.2)
    (by positivity) (fun f => (firstWeights g).2 (uv.1, f)) (fun f => hWB (uv.1, f))
  have hcancel : n * (3 * M / n) = 3 * M := by field_simp
  rw [hcancel] at hloadA hloadB
  have hcross : |crossLoad IA IB (firstWeights g) uv| ≤ 6 * M :=
    (abs_add_le _ _).trans (by linarith)
  change |g.2.2 uv - crossLoad IA IB (firstWeights g) uv| ≤ _
  have htriangle : |g.2.2 uv - crossLoad IA IB (firstWeights g) uv| ≤
      |g.2.2 uv| + |crossLoad IA IB (firstWeights g) uv| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (g.2.2 uv) (-crossLoad IA IB (firstWeights g) uv)
  linarith [hg.2.2 uv]

theorem rowResidual_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n : ℝ) (h : SizeBounds IA IB n) (g : Demand A B EA EB)
    (M : ℝ) (hM : 0 ≤ M) (hg : DemandBound g M) (u : A) :
    |rowResidual IA IB g u| ≤ 7 * M * n := by
  calc
    _ ≤ ∑ v : B, |firstResidual IA IB g (u, v)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : B, 7 * M := sum_le_sum fun v _ => firstResidual_abs_le IA IB n h g M hM hg (u,v)
    _ = (Fintype.card B : ℝ) * (7 * M) := by simp
    _ ≤ n * (7 * M) := mul_le_mul_of_nonneg_right h.b_upper (by positivity)
    _ = 7 * M * n := by ring

theorem rowWeight_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n : ℝ) (h : SizeBounds IA IB n) (g : Demand A B EA EB)
    (M : ℝ) (hM : 0 ≤ M) (hg : DemandBound g M) (u : A) :
    |rowResidual IA IB g u / (2 * Fintype.card EB)| ≤ 140 * M / n := by
  have hn : 0 < n := h.npos
  have heB : 0 < (Fintype.card EB : ℝ) := lt_of_lt_of_le (by positivity) h.eb_lower
  rw [abs_div, abs_of_pos (show 0 < 2 * (Fintype.card EB : ℝ) by positivity)]
  calc
    _ ≤ (7 * M * n) / (2 * Fintype.card EB) :=
      div_le_div_of_nonneg_right (rowResidual_abs_le IA IB n h g M hM hg u) (by positivity)
    _ ≤ (7 * M * n) / (n ^ 2 / 20) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [h.eb_lower])
    _ = 140 * M / n := by field_simp; ring

theorem degree_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n : ℝ) (h : SizeBounds IA IB n) (v : B) : |degree IB v| ≤ n :=
  (abs_sum_le_sum_abs _ _).trans (h.ib_row v)

theorem finalResidual_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n : ℝ) (h : SizeBounds IA IB n) (g : Demand A B EA EB)
    (M : ℝ) (hM : 0 ≤ M) (hg : DemandBound g M) (uv : A × B) :
    |finalResidual IA IB g uv| ≤ 147 * M := by
  have hn : 0 < n := h.npos
  have hw := rowWeight_abs_le IA IB n h g M hM hg uv.1
  have hd := degree_abs_le IA IB n h uv.2
  have hc : |rowResidual IA IB g uv.1 * degree IB uv.2 / (2 * Fintype.card EB)| ≤
      140 * M := by
    calc
      _ = |rowResidual IA IB g uv.1 / (2 * Fintype.card EB)| * |degree IB uv.2| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (140 * M / n) * n := mul_le_mul hw hd (abs_nonneg _) (by positivity)
      _ = 140 * M := by field_simp
  have htri : |finalResidual IA IB g uv| ≤ |firstResidual IA IB g uv| +
      |rowResidual IA IB g uv.1 * degree IB uv.2 / (2 * Fintype.card EB)| := by
    simpa only [finalResidual, sub_eq_add_neg, abs_neg] using
      abs_add_le (firstResidual IA IB g uv)
        (-(rowResidual IA IB g uv.1 * degree IB uv.2 / (2 * Fintype.card EB)))
  linarith [firstResidual_abs_le IA IB n h g M hM hg uv]

theorem completeWeights_abs_le (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (n Cq : ℝ) (h : SizeBounds IA IB n) (hCq : 0 ≤ Cq)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (hQ : ∀ (x : A → ℝ) (L : ℝ), 0 ≤ L → (∀ u, |x u| ≤ L) →
      ∀ f, |Q x f| ≤ Cq * L / n)
    (g : Demand A B EA EB) (M : ℝ) (hM : 0 ≤ M) (hg : DemandBound g M) :
    (∀ fv, |(completeWeights IA IB Q g).1 fv| ≤ (143 + 147 * Cq) * M / n) ∧
    (∀ uf, |(completeWeights IA IB Q g).2 uf| ≤ (143 + 147 * Cq) * M / n) := by
  have hn : 0 < n := h.npos
  obtain ⟨hWA, hWB⟩ := firstWeights_abs_le IA IB n h g M hM hg
  constructor
  · intro fv
    have hq := hQ (fun u => finalResidual IA IB g (u, fv.2)) (147 * M)
      (by positivity) (fun u => finalResidual_abs_le IA IB n h g M hM hg (u, fv.2)) fv.1
    change |g.1 fv.1 / Fintype.card B + Q (fun u => finalResidual IA IB g (u, fv.2)) fv.1| ≤ _
    have hbase := hWA fv
    change |g.1 fv.1 / Fintype.card B| ≤ _ at hbase
    have hsum := abs_add_le (g.1 fv.1 / Fintype.card B)
      (Q (fun u => finalResidual IA IB g (u, fv.2)) fv.1)
    have hslack : 0 ≤ 140 * M / n := by positivity
    have heq : (143 + 147 * Cq) * M / n =
        3 * M / n + Cq * (147 * M) / n + 140 * M / n := by ring
    rw [heq]
    linarith
  · intro uf
    have hr := rowWeight_abs_le IA IB n h g M hM hg uf.1
    have hbase := hWB uf
    change |g.2.1 uf.2 / Fintype.card A| ≤ _ at hbase
    change |g.2.1 uf.2 / Fintype.card A + rowResidual IA IB g uf.1 / (2 * Fintype.card EB)| ≤ _
    have hsum := abs_add_le (g.2.1 uf.2 / Fintype.card A)
      (rowResidual IA IB g uf.1 / (2 * Fintype.card EB))
    have hslack : 0 ≤ 147 * Cq * M / n := by positivity
    have heq : (143 + 147 * Cq) * M / n =
        3 * M / n + 140 * M / n + 147 * Cq * M / n := by ring
    rw [heq]
    linarith

theorem complete_constant_le (tau : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1) :
    143 + 147 * (3 / (2 * tau)) ≤ 512 / tau := by
  rw [le_div_iff₀ htau]
  have hcancel : (143 + 147 * (3 / (2 * tau))) * tau = 143 * tau + 441 / 2 := by
    field_simp
    ring
  rw [hcancel]
  linarith

#print axioms completeWeights_abs_le
#print axioms complete_constant_le

end PartitionedTriangleAbsorption.F0Direct.RealComplete
