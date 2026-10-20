/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Claim1464Tools

@[expose] public section

/-!
# Claim 14.6.4: the three cases

Let `T₁ = u₁u₂v₁`, `T₂ = u₁u₂v₂` be two `F₀`-copies of an idealized host.

* Case 1 (`u₁, u₂` in the same part `a`, hence `v₁, v₂` in the other part `b`):
  - if `V_a` is not close to `T₂`/`T̄₂` (`case1a_walks`), the common neighbourhood
    `D = N(v₁) ∩ N(v₂) ∩ V_a` contains `Ω(n⁴)` walks `u₁ x₁ x₂ x₃ x₄ u₂`, giving typed
    homomorphic copies of the type-1 hinge;
  - if `V_b` is not close (`case1b_walks`), for each of the `Ω(n)` vertices
    `w ∈ N(u₁) ∩ N(v₁) ∩ N(v₂) ∩ V_a` the set `N(w) ∩ N(u₂) ∩ V_b` contains `Ω(n³)` walks
    `v₁ a b c v₂`, giving typed homomorphic copies of the type-2 hinge.
* Case 2 (`u₁, u₂` in different parts, `case2_pairs`): there are `Ω(n²)` admissible pairs for
  the six-vertex hinge.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Case 1, `V_a` not close -/

theorem case1a_walks (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {e0 σ θ : ℝ}
    (hf : IdFacts e0 G p) (he0 : 0 ≤ e0) (he0σ : 9 * e0 ≤ σ ^ 2) (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 100) (hθ : 100 * σ + 36 * e0 ≤ θ) (hn : 18 ≤ θ * Fintype.card V)
    {a b : Fin 2} (hab : a ≠ b) (hnc : ¬ IsSideClose θ G (partClass p a)) {u₁ u₂ v₁ v₂ : V}
    (a11 : G.Adj u₁ v₁) (a12 : G.Adj u₁ v₂) (a21 : G.Adj u₂ v₁) (a22 : G.Adj u₂ v₂)
    (pu₁ : p u₁ = a) (pu₂ : p u₂ = a) (pv₁ : p v₁ = b) (pv₂ : p v₂ = b) :
    σ ^ 6 * (Fintype.card V : ℝ) ^ 4 / 243 ≤ (thomCount mH1 (q1 a b) G p u₁ u₂ v₁ v₂ : ℝ) := by
  have he1 : e0 ≤ 1 / 100 := by nlinarith
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set C := partClass p a with hC
  set D := (C.filter (G.Adj v₁)).filter (G.Adj v₂) with hD
  have hDC : D ⊆ C := (filter_subset _ _).trans (filter_subset _ _)
  have hD1 := card_filter_adj_ge G p (j := a) (S := C) subset_rfl v₁
  have hD2 := card_filter_adj_ge G p (j := a) (S := C.filter (G.Adj v₁)) (filter_subset _ _) v₂
  have hm1 := hf.cross v₁ a (by rw [pv₁]; exact hab.symm)
  have hm2 := hf.cross v₂ a (by rw [pv₂]; exact hab.symm)
  have hDsz : (C.card : ℝ) - 3 * e0 * n ≤ D.card := by linarith
  have hmemD : ∀ x, x ∈ D ↔ (p x = a ∧ G.Adj v₁ x) ∧ G.Adj v₂ x := by
    intro x; simp [hD, hC, partClass]
  have hu₁D : u₁ ∈ D := (hmemD u₁).mpr ⟨⟨pu₁, a11.symm⟩, a12.symm⟩
  have hu₂D : u₂ ∈ D := (hmemD u₂).mpr ⟨⟨pu₂, a21.symm⟩, a22.symm⟩
  have hdeg := hdeg_of_large G p hf he0 he1 hDC hDsz
  set m : ℝ := (D.card : ℝ) with hmdef
  have hlo := hf.lo a
  have hm3 : n / 3 ≤ m := by nlinarith
  have hm0 : 0 < m := by
    have : (0 : ℝ) < D.card := by exact_mod_cast card_pos.mpr ⟨u₁, hu₁D⟩
    exact this
  -- the number of walks of length five
  have hW5 : σ ^ 6 * m ^ 4 / 3 ≤ ∑ d ∈ nbIn G D u₂, (walk4 G D u₁ d : ℝ) := by
    by_contra hlt
    push_neg at hlt
    have hN := hdeg u₂ hu₂D
    have hN3 : m / 3 ≤ ((nbIn G D u₂).card : ℝ) := by nlinarith
    have hNne : (nbIn G D u₂).Nonempty := by
      rw [← card_pos]
      have : (0 : ℝ) < (nbIn G D u₂).card := by linarith
      exact_mod_cast this
    obtain ⟨d, hdN, hd⟩ := exists_mul_card_le_sum (nbIn G D u₂) hNne
      (fun d => (walk4 G D u₁ d : ℝ))
    have hdD : d ∈ D := nbIn_subset G D u₂ hdN
    have hmany := many_walks_of_not_sideClose G p hf he0 he0σ hσ0 hσ hθ hn hnc hDC hDsz hu₁D hdD
    have hw0 : (0 : ℝ) ≤ walk4 G D u₁ d := Nat.cast_nonneg _
    have h1 : (walk4 G D u₁ d : ℝ) * (m / 3) ≤ (walk4 G D u₁ d : ℝ) * (nbIn G D u₂).card :=
      mul_le_mul_of_nonneg_left hN3 hw0
    have h2 : σ ^ 6 * m ^ 3 * (m / 3) < (walk4 G D u₁ d : ℝ) * (m / 3) :=
      mul_lt_mul_of_pos_right hmany (by positivity)
    nlinarith
  have hthom := walk_le_thom1 G p D (fun x hx => by
      have := (hmemD x).mp hx; exact ⟨this.1.2, this.2, this.1.1⟩) pu₁ pu₂ pv₁ pv₂
  have hthom' : ∑ d ∈ nbIn G D u₂, (walk4 G D u₁ d : ℝ) ≤
      (thomCount mH1 (q1 a b) G p u₁ u₂ v₁ v₂ : ℝ) := by exact_mod_cast hthom
  have hm4 : (n / 3) ^ 4 ≤ m ^ 4 := pow_le_pow_left₀ (by positivity) hm3 4
  have : σ ^ 6 * n ^ 4 / 243 = σ ^ 6 * (n / 3) ^ 4 / 3 := by ring
  rw [this]
  have hσ6 : 0 ≤ σ ^ 6 := by positivity
  nlinarith

/-! ### Case 1, `V_b` not close -/

set_option maxHeartbeats 1000000 in
theorem case1b_walks (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {e0 σ θ : ℝ}
    (hf : IdFacts e0 G p) (he0 : 0 ≤ e0) (he0σ : 9 * e0 ≤ σ ^ 2) (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 100) (hθ : 100 * σ + 36 * e0 ≤ θ) (hn : 18 ≤ θ * Fintype.card V)
    {a b : Fin 2} (hab : a ≠ b) (hnc : ¬ IsSideClose θ G (partClass p b)) {u₁ u₂ v₁ v₂ : V}
    (a21 : G.Adj u₂ v₁) (a22 : G.Adj u₂ v₂)
    (pu₁ : p u₁ = a) (pu₂ : p u₂ = a) (pv₁ : p v₁ = b) (pv₂ : p v₂ = b) :
    σ ^ 6 * (Fintype.card V : ℝ) ^ 4 / 135 ≤ (thomCount mH2 (q2 a b) G p u₁ u₂ v₁ v₂ : ℝ) := by
  have he1 : e0 ≤ 1 / 100 := by nlinarith
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set L := (((partClass p a).filter (G.Adj u₁)).filter (G.Adj v₁)).filter (G.Adj v₂) with hL
  have hmemL : ∀ w, w ∈ L ↔ ((p w = a ∧ G.Adj u₁ w) ∧ G.Adj v₁ w) ∧ G.Adj v₂ w := by
    intro w; simp [hL, partClass]
  have hL1 := card_filter_adj_ge G p (j := a) (S := partClass p a) subset_rfl u₁
  have hL2 := card_filter_adj_ge G p (j := a) (S := (partClass p a).filter (G.Adj u₁))
    (filter_subset _ _) v₁
  have hL3 := card_filter_adj_ge G p (j := a)
    (S := ((partClass p a).filter (G.Adj u₁)).filter (G.Adj v₁))
    ((filter_subset _ _).trans (filter_subset _ _)) v₂
  have hmu := hf.int u₁
  rw [pu₁] at hmu
  have hm1 := hf.cross v₁ a (by rw [pv₁]; exact hab.symm)
  have hm2 := hf.cross v₂ a (by rw [pv₂]; exact hab.symm)
  have hLsz : n / 5 ≤ (L.card : ℝ) := by nlinarith
  set C := partClass p b with hC
  set Dw : V → Finset V := fun w => (C.filter (G.Adj w)).filter (G.Adj u₂) with hDw
  have hmemD : ∀ w y, y ∈ Dw w ↔ (p y = b ∧ G.Adj w y) ∧ G.Adj u₂ y := by
    intro w y; simp [hDw, hC, partClass]
  have hlo := hf.lo b
  have hwalk : ∀ w ∈ L, σ ^ 6 * (n / 3) ^ 3 ≤ (walk4 G (Dw w) v₁ v₂ : ℝ) := by
    intro w hw
    have hwL := (hmemL w).mp hw
    have hDC : Dw w ⊆ C := (filter_subset _ _).trans (filter_subset _ _)
    have hD1 := card_filter_adj_ge G p (j := b) (S := C) subset_rfl w
    have hD2 := card_filter_adj_ge G p (j := b) (S := C.filter (G.Adj w)) (filter_subset _ _) u₂
    have hmw := hf.cross w b (by rw [hwL.1.1.1]; exact hab)
    have hmu₂ := hf.cross u₂ b (by rw [pu₂]; exact hab)
    have hDsz : (C.card : ℝ) - 3 * e0 * n ≤ (Dw w).card := by
      have : ((Dw w).card : ℝ) = ((C.filter (G.Adj w)).filter (G.Adj u₂)).card := rfl
      linarith
    have hv₁D : v₁ ∈ Dw w := (hmemD w v₁).mpr ⟨⟨pv₁, SimpleGraph.Adj.symm hwL.1.2⟩, a21⟩
    have hv₂D : v₂ ∈ Dw w := (hmemD w v₂).mpr ⟨⟨pv₂, SimpleGraph.Adj.symm hwL.2⟩, a22⟩
    have hmany := many_walks_of_not_sideClose G p hf he0 he0σ hσ0 hσ hθ hn hnc hDC hDsz hv₁D hv₂D
    have hm3 : n / 3 ≤ ((Dw w).card : ℝ) := by nlinarith
    have : (n / 3) ^ 3 ≤ ((Dw w).card : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hm3 3
    have hσ6 : 0 ≤ σ ^ 6 := by positivity
    nlinarith
  have hsum : (L.card : ℝ) * (σ ^ 6 * (n / 3) ^ 3) ≤ ∑ w ∈ L, (walk4 G (Dw w) v₁ v₂ : ℝ) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hwalk
  have hthom := walk_le_thom2 G p L Dw (fun w hw => by
      have h := (hmemL w).mp hw
      exact ⟨SimpleGraph.Adj.symm h.1.1.2, SimpleGraph.Adj.symm h.1.2, SimpleGraph.Adj.symm h.2, h.1.1.1⟩)
    (fun w _ y hy => by
      have h := (hmemD w y).mp hy
      exact ⟨h.1.2, h.2, h.1.1⟩) pu₁ pu₂ pv₁ pv₂
  have hthom' : ∑ w ∈ L, (walk4 G (Dw w) v₁ v₂ : ℝ) ≤
      (thomCount mH2 (q2 a b) G p u₁ u₂ v₁ v₂ : ℝ) := by exact_mod_cast hthom
  have hσ6 : 0 ≤ σ ^ 6 * (n / 3) ^ 3 := by positivity
  have : σ ^ 6 * n ^ 4 / 135 = n / 5 * (σ ^ 6 * (n / 3) ^ 3) := by ring
  rw [this]
  nlinarith

end NashWilliams18
