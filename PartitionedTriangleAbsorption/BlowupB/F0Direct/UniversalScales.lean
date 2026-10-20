/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.UniversalBudget
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Scalar schedules for the compatible physical refiner

All densities are fixed before the graph and before the residue.  The power
of two and integer capacities depend on the host order alone.  This module
checks the complete numerical budget, including the number of pieces.
-/

set_option maxHeartbeats 2000000

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset AntiEdgeSelection StructuralF3General.PrivateFamily
open StructuralF3General.FiniteLibrary TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_power_above (x : ℝ) (hx : 1 ≤ x) :
    ∃ p : ℕ, x ≤ (2 : ℝ)^p ∧ (2 : ℝ)^p ≤ 2*x := by
  obtain ⟨p,hp,hp'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  refine ⟨p+1,hp'.le,?_⟩
  rw [pow_succ]
  nlinarith

theorem universal_from_small_reserve
    (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ℕ) (hC : 1 ≤ C) (κ δ η : ℝ)
    (hk : 0 < κ) (hk_small : 134217728*κ ≤ 1)
    (hroot : 524288*(C:ℝ)*κ ≤ δ)
    (hcost : 2097152*(C:ℝ)*κ ≤ 1)
    (hmass_scale : 4194304*κ ≤ δ*η)
    (hδ : 0 < δ) (hη : 0 < η)
    (hn : 1 ≤ κ^2*Fintype.card V)
    (hfixed : (C:ℝ) ≤ δ*Fintype.card V/4)
    (hanti : AntiEdgeful p F0 G (1/8))
    (hstep : PrivateStep p F0 G 214 C (δ*Fintype.card V/4)
      (δ*Fintype.card V) (η*Fintype.card V))
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (κ^2*Fintype.card V)) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp p F0 A ∧ DegBounded A (δ*Fintype.card V) ∧
      ∀ L ⊆ X, IsIntDiv p F0 L → HasDecomp p F0 (A ∪ L) := by
  classical
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < n := by
    by_contra hn'
    have : n=0 := le_antisymm (le_of_not_gt hn') hn0
    change 1 ≤ κ^2*n at hn
    rw [this,mul_zero] at hn
    norm_num at hn
  have hk1 : κ ≤ 1 := by linarith only [hk_small]
  have hk2 : κ^2 ≤ κ := by nlinarith only [hk, hk1]
  change (C:ℝ) ≤ δ*n/4 at hfixed
  have hkn : 1 ≤ κ*n := by
    exact hn.trans (mul_le_mul_of_nonneg_right hk2 hn0)
  have hC1 : (1:ℝ) ≤ C := by exact_mod_cast hC
  obtain ⟨power,hMlo,hMhi⟩ := exists_power_above (κ*n) hkn
  let Δ : ℕ := ⌈κ^2*n⌉₊
  let q : ℕ := ⌈8192*κ*n⌉₊
  let M : ℕ := 2^power
  have hM : (M:ℝ)=(2:ℝ)^power := by simp [M]
  have hMlo' : κ*n ≤ (M:ℝ) := hM ▸ hMlo
  have hMhi' : (M:ℝ) ≤ 2*κ*n := by rw [hM]; nlinarith
  have hMpos : 0 < (M:ℝ) := lt_of_lt_of_le (by positivity) hMlo'
  have hDlo : κ^2*n ≤ (Δ:ℝ) := Nat.le_ceil _
  have hDhi : (Δ:ℝ) ≤ 2*κ^2*n := by
    have := Nat.ceil_lt_add_one (show 0≤κ^2*n by positivity)
    change (Δ:ℝ) < κ^2*n+1 at this
    nlinarith
  have hqlo : 8192*κ*n ≤ (q:ℝ) := Nat.le_ceil _
  have hqhi : (q:ℝ) ≤ 8193*κ*n := by
    have := Nat.ceil_lt_add_one (show 0≤8192*κ*n by positivity)
    change (q:ℝ) < 8192*κ*n+1 at this
    linarith
  have hqpos : 0 < (q:ℝ) := lt_of_lt_of_le (by positivity) hqlo
  have hqn : 0 < q := by exact_mod_cast hqpos
  have hndeg : ∀ v, incidentLoad X v ≤ Δ := by
    intro v
    exact_mod_cast (hX v).trans hDlo
  have hXcard : (X.card:ℝ) ≤ κ^2*n^2 := by
    have hc := card_le_order_mul_degree X (κ^2*n) hX
    change (X.card:ℝ) ≤ n*(κ^2*n) at hc
    nlinarith
  have hcount : ((57635*(X.card+2*M^2):ℕ):ℝ) ≤ 524288*(κ*n)^2 := by
    push_cast
    have hm2 : (M:ℝ)^2 ≤ (2*κ*n)^2 := by gcongr
    nlinarith [sq_nonneg (κ*n)]
  have hcap : (Δ:ℝ)+2*q ≤ 32768*κ*n := by
    have := mul_le_mul_of_nonneg_right hk2 hn0
    nlinarith
  have h99 : 99*Δ ≤ q := by
    have hkr := mul_le_mul_of_nonneg_right hk2 hn0
    have : (99:ℝ)*Δ ≤ q := by nlinarith
    exact_mod_cast this
  have h88 : 88 ≤ q := by
    have : (88:ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hhub : 330*((Fintype.card V/M+1)*Δ)+1452*M ≤ q := by
    have hdiv : ((Fintype.card V/M:ℕ):ℝ) ≤ n/(M:ℝ) := by
      dsimp [n]
      exact Nat.cast_div_le
    have hdivmul : ((Fintype.card V/M:ℕ):ℝ)*κ*n ≤ n := by
      have hm := (le_div_iff₀ hMpos).mp hdiv
      have hmul := mul_le_mul_of_nonneg_left hMlo'
        (Nat.cast_nonneg (Fintype.card V/M) : (0:ℝ) ≤ _)
      nlinarith only [hm, hmul]
    have hmul : (((Fintype.card V/M:ℕ):ℝ)+1)*(Δ:ℝ) ≤ 4*κ*n := by
      have hd := mul_le_mul_of_nonneg_left hDhi
        (by positivity : (0:ℝ)≤((Fintype.card V/M:ℕ):ℝ)+1)
      have hdivk := mul_le_mul_of_nonneg_left hdivmul (show 0≤κ by positivity)
      have hkk := mul_le_mul_of_nonneg_right hk2 hn0
      nlinarith only [hd, hdivk, hkk]
    have : (330:ℝ)*((((Fintype.card V/M:ℕ):ℝ)+1)*Δ)+1452*M ≤ q := by
      nlinarith only [hmul, hMhi', hqlo]
    exact_mod_cast this
  have hterm : 2*((214*(57635*(X.card+2*M^2)):ℕ):ℝ)/(q:ℝ) ≤ 32768*κ*n := by
    apply (div_le_iff₀ hqpos).mpr
    have hqmul := mul_le_mul_of_nonneg_left hqlo (show 0≤32768*κ*n by positivity)
    push_cast at hcount ⊢
    nlinarith only [hcount, hqmul, sq_nonneg (κ*n)]
  have hembed : 2*(214:ℝ)*q+
      2*((214*(57635*(X.card+2*(2^power)^2)):ℕ):ℝ)/q+
      2*((Δ:ℝ)+2*q) < (1/8:ℝ)*Fintype.card V := by
    have hknsmall := mul_le_mul_of_nonneg_right hk_small hn0
    change 2*(214:ℝ)*q+2*((214*(57635*(X.card+2*M^2)):ℕ):ℝ)/q+
      2*((Δ:ℝ)+2*q) < (1/8:ℝ)*n
    nlinarith only [hqhi, hcap, hterm, hknsmall, hnpos]
  have hrootn : 524288*(C:ℝ)*κ*n ≤ δ*n :=
    mul_le_mul_of_nonneg_right hroot hn0
  have hCkn : κ*n ≤ (C:ℝ)*κ*n := by
    nlinarith only [mul_le_mul_of_nonneg_right hC1 (show 0≤κ*n by positivity)]
  have hdegree : max ((Δ:ℝ)+2*q) (δ*n/4+C)+(C:ℝ)*(2*q) ≤ δ*n := by
    have hqC := mul_le_mul_of_nonneg_left hqhi (Nat.cast_nonneg C : (0:ℝ)≤C)
    have hmax : max ((Δ:ℝ)+2*q) (δ*n/4+C) ≤ δ*n/2 := by
      apply max_le
      · nlinarith only [hcap,hrootn,hCkn,hkn]
      · nlinarith only [hfixed]
    nlinarith only [hmax,hqC,hrootn,hCkn,hkn]
  have hmass : 4*(n*((Δ:ℝ)+2*q)+((57635*(X.card+2*(2^power)^2):ℕ):ℝ)*C) ≤
      (δ*n/4)*(η*n) := by
    have hcapn := mul_le_mul_of_nonneg_left hcap hn0
    have hcountC := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg C : (0:ℝ)≤C)
    have hco : 524288*(C:ℝ)*κ^2 ≤ κ := by
      nlinarith only [mul_le_mul_of_nonneg_right hcost hk.le, hk]
    have hcon := mul_le_mul_of_nonneg_right hco (sq_nonneg n)
    have hscalen := mul_le_mul_of_nonneg_right hmass_scale (sq_nonneg n)
    change 4*(n*((Δ:ℝ)+2*q)+((57635*(X.card+2*M^2):ℕ):ℝ)*C) ≤
      (δ*n/4)*(η*n)
    nlinarith only [hcapn,hcountC,hcon,hscalen, mul_nonneg hk.le (sq_nonneg n)]
  have hn3 : 3 ≤ Fintype.card V := by
    have hknsmall := mul_le_mul_of_nonneg_right hk_small hn0
    have : (3:ℝ) ≤ n := by nlinarith only [hknsmall,hkn]
    dsimp [n] at this
    exact_mod_cast this
  exact universal_of_compatible_budgets p G C (δ*n/4) (δ*n) (η*n) (1/8)
    power q q Δ (by norm_num) hn3 hanti hstep X hXG hndeg hqn le_rfl h99
    (by omega) h88 (by simpa [M] using hhub) hembed hdegree hmass

#print axioms exists_power_above
#print axioms universal_from_small_reserve

end PartitionedTriangleAbsorption.BlowupB.F0Direct
