/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case128.FinalStage

/-!
# Case (5): the forced matched counts fit in the quotas

After removing a family of triangles that uses at most `2s` edges at every exceptional vertex,
the forced lower bounds `a_v + b_{v,i} − d(v)/2` of the star allocation still sum to at most
`29/30` of a sixth of the original six-fold quota (Claim 15.20.1 in quantitative form).  We also
prove the large-pair statement used to choose the colours of the pre-clean (Claim 12.8.8(ii)).
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 ExceptionalQuotaStage142

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma natSub_cast_le_max (x y : ℕ) : ((x - y : ℕ) : ℝ) ≤ max 0 ((x : ℝ) - y) := by
  rcases le_total x y with h | h
  · rw [Nat.sub_eq_zero_of_le h]; simp
  · rw [Nat.cast_sub h]; exact le_max_right _ _

omit [DecidableEq V] in
lemma classLoad_le_classSet (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (j : Fin 4) : classLoad p G v j ≤ (classSet p j).card := by
  unfold classLoad classSet
  apply card_le_card
  intro w hw
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hw).2⟩

lemma farMissing_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (i : Fin 3) (v : V) :
    ((farMissing G p S i v).card : ℝ) ≤ Fintype.card V := by
  exact_mod_cast card_le_univ _

/-- **Forced counts after removing a few edges at `S`.** -/
theorem forced_sum_le (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (p : V → Fin 4) (S : Finset V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j)
    (hsize : ∀ j, ((classSet p j).card : ℝ) ≤ (1 / 4 + 8 * ρ) * Fintype.card V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hload : ∀ v ∈ S, ∀ j, classLoad p H v j ≤ classLoad p G v j)
    (hdegH : ∀ v ∈ S, G.degree v ≤ H.degree v + 2 * S.card)
    (heven : ∀ v, H.degree v = 2 * (H.degree v / 2))
    (h1 : 11 * ρ * Fintype.card V + 3 * S.card / 2 ≤ Fintype.card V / 120) (i : Fin 3) :
    6 * (((∑ v ∈ S, (classLoad p H v (p v) + classLoad p H v (partner i (p v)) -
        H.degree v / 2) : ℕ) : ℝ)) ≤ 29 / 30 * (sixQuota p G.edgeFinset i : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  let K : V → ℝ := fun v => (G.degree v : ℝ) - 3 / 4 * n + 3 * (farMissing G p S i v).card
  let lo : V → ℝ := fun v => (classLoad p G v (p v) : ℝ) + classLoad p G v (partner i (p v)) -
    (G.degree v : ℝ) / 2 + S.card
  have hterm : ∀ v ∈ S, (((classLoad p H v (p v) + classLoad p H v (partner i (p v)) -
      H.degree v / 2) : ℕ) : ℝ) ≤ max 0 (lo v) := by
    intro v hv
    refine (natSub_cast_le_max _ _).trans (max_le_max (le_refl _) ?_)
    have e1 : (classLoad p H v (p v) : ℝ) ≤ classLoad p G v (p v) := by
      exact_mod_cast hload v hv _
    have e2 : (classLoad p H v (partner i (p v)) : ℝ) ≤ classLoad p G v (partner i (p v)) := by
      exact_mod_cast hload v hv _
    have e3 : (G.degree v : ℝ) ≤ H.degree v + 2 * (S.card : ℝ) := by exact_mod_cast hdegH v hv
    have e4 : (H.degree v : ℝ) = 2 * ((H.degree v / 2 : ℕ) : ℝ) := by
      exact_mod_cast heven v
    push_cast
    simp only [lo]
    linarith
  have hsum1 : (((∑ v ∈ S, (classLoad p H v (p v) + classLoad p H v (partner i (p v)) -
      H.degree v / 2) : ℕ) : ℝ)) ≤ ∑ v ∈ S, max 0 (lo v) := by
    push_cast
    exact sum_le_sum hterm
  have hcol : ∑ v ∈ S, max 0 (lo v) ≤ 29 / 30 * ∑ v ∈ S, K v / 6 := by
    apply column_bound S (fun v => K v / 6) lo n
      (n / 24 - 11 * ρ * n - (S.card : ℝ) / 2 - S.card)
    · linarith
    · intro v _
      have := hdeg v
      have : (0 : ℝ) ≤ (farMissing G p S i v).card := Nat.cast_nonneg _
      simp only [K]
      linarith
    · intro v _
      have h1 : (G.degree v : ℝ) ≤ n := by
        have := G.degree_lt_card_verts v
        simp only [hn]; exact_mod_cast this.le
      have h2 := farMissing_card_le G p S i v
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      simp only [K]
      linarith
    · intro v _
      have := quota_slack G p S ρ hρ hloc hsize i v
      simp only [lo, K]
      linarith
  have hsq : ∑ v ∈ S, K v ≤ (sixQuota p G.edgeFinset i : ℝ) :=
    sixQuota_ge_sum G p S i hdeg
  have hsum2 : ∑ v ∈ S, K v / 6 = (∑ v ∈ S, K v) / 6 := by
    rw [sum_div]
  rw [hsum2] at hcol
  linarith

/-- **Large pairs** (Claim 12.8.8(ii)): when `S` consists of exceptional vertices, two of the
three six-fold quotas are at least `180 |S|²`. -/
theorem large_pairs (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (S : Finset V)
    (ρ τ : ℝ) (hτ : 0 < τ)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hlow : ∀ j, (1 / 4 - 24 * ρ) * Fintype.card V ≤ ((classSet p j).card : ℝ))
    (hS : ∀ v ∈ S, τ * Fintype.card V < classLoad p G v (p v))
    (h2 : 12 * ρ * Fintype.card V + S.card / 2 ≤ τ * Fintype.card V / 180)
    (h3 : (S.card : ℝ) ≤ τ * Fintype.card V / 1800) :
    ∃ ℓ₀ : Fin 3, ∀ i, i ≠ ℓ₀ → (180 * (S.card : ℝ) ^ 2) ≤ (sixQuota p G.edgeFinset i : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  let f : V → Fin 3 → ℝ := fun v i =>
    ((G.degree v : ℝ) - 3 / 4 * n + 3 * (farMissing G p S i v).card) / 6
  have hτn : 0 ≤ τ * n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    positivity
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_large_pair S f (τ * n / 20) (by positivity)
    (fun v _ i => by
      have := hdeg v
      have : (0 : ℝ) ≤ (farMissing G p S i v).card := Nat.cast_nonneg _
      simp only [f]
      linarith)
    (fun v hv => two_large G p S ρ τ v (hdeg v) hlow (hS v hv) h2)
  refine ⟨ℓ₀, fun i hi => ?_⟩
  have hA := hℓ₀ i hi
  have hB : ∑ v ∈ S, f v i ≤ (sixQuota p G.edgeFinset i : ℝ) / 6 := by
    have := sixQuota_ge_sum G p S i hdeg
    simp only [f]
    rw [← sum_div]
    linarith
  have hs0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have : (S.card : ℝ) * (S.card : ℝ) ≤ S.card * (τ * n / 1800) :=
    mul_le_mul_of_nonneg_left h3 hs0
  nlinarith

end NashWilliams18.C128
