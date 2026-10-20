/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0ParallelObstruction
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Conditional F0 boost from a bounded balanced right inverse (intermediate)

This is a **conditional reduction**, not a producer. It isolates exactly what
is missing after `F0ParallelObstruction`: if the F0 copy-edge incidence map of
`J` has a right inverse on the F0-balanced edge functions whose output per copy
is at most `K/n` times the input sup norm (`HasBoundedBalancedInverse`), then
the seed, anti-edgefulness and `κ`-balance produce nonnegative weights `≤ b/n`
with every load within `τ` of one, with `b, ε` depending only on `C, K` and not
on `τ`.

The hypothesis is a linear-algebraic property of the actual copy system of `J`,
not a statement about the desired weights; but it is strong. The parallel
example fails it for every fixed `K` (`fam_not_boundedBalancedInverse`), and
deriving it on `J = G - (A ∪ X)` from geometric hypotheses on `G` is OPEN.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0RigidBoost

open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks
  TypedLoadCounterexample TypedLoadPreparation F0ParallelObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The F0 balance functional on a single edge (`2` crossing, `-4` internal). -/
def gFun (p : V → Fin 2) (e : Sym2 V) : ℝ := (pairFun (groupPair g0) (pairVec p e) : ℝ)

/-- **Bounded balanced right inverse** of the F0 copy-edge incidence map of `J`:
every edge function `x` with zero F0 balance and `|x| ≤ M` on `E(J)` is the load
vector of signed copy weights of absolute value at most `K M / n`. -/
def HasBoundedBalancedInverse (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj]
    (K : ℝ) : Prop :=
  ∀ (x : Sym2 V → ℝ) (M : ℝ), 0 ≤ M → (∀ e ∈ J.edgeFinset, |x e| ≤ M) →
    ∑ e ∈ J.edgeFinset, gFun p e * x e = 0 →
    ∃ η : Finset V → ℝ, (∀ e ∈ J.edgeFinset, edgeLoad p F0 J η e = x e) ∧
      ∀ s ∈ copies p F0 J, |η s| ≤ K * M / Fintype.card V

omit [Fintype V] [DecidableEq V] in
theorem gFun_sq_ge (p : V → Fin 2) (e : Sym2 V) : 4 ≤ gFun p e ^ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have key : ∀ i j : Fin 2, 4 ≤ (groupPair g0 i j + groupPair g0 j i) ^ 2 := by decide
    have h := key (p a) (p b)
    unfold gFun
    rw [pairFun_pairVec_mk]
    exact_mod_cast h

omit [Fintype V] [DecidableEq V] in
theorem abs_gFun_le (p : V → Fin 2) (e : Sym2 V) : |gFun p e| ≤ 4 :=
  abs_groupPair_g0_pairVec_le p e

theorem edgeLoad_add (p : V → Fin 2) (J : SimpleGraph V)
    (φ η : Finset V → ℝ) (e : Sym2 V) :
    edgeLoad p F0 J (fun s => φ s + η s) e = edgeLoad p F0 J φ e + edgeLoad p F0 J η e := by
  unfold edgeLoad
  rw [Finset.sum_add_distrib]

theorem exists_F0_type (a b : Fin 2) : ∃ k : Fin 2, ({a, b, k} : Multiset (Fin 2)) ∈ F0 := by
  revert a b
  decide

omit [DecidableEq V] in
/-- Anti-edgefulness forces linear minimum degree, hence quadratically many edges. -/
theorem card_edges_lower (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] {α : ℝ}
    (hJ : AntiEdgeful p F0 J α) (hn : 2 ≤ Fintype.card V) :
    α * (Fintype.card V : ℝ) ^ 2 ≤ 2 * J.edgeFinset.card := by
  classical
  have hdeg : ∀ v : V, α * (Fintype.card V : ℝ) ≤ J.degree v := by
    intro v
    obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
    obtain ⟨k, hk⟩ := exists_F0_type (p v) (p u)
    have h := hJ _ hk (p v) (p u) k rfl v u hu.symm rfl rfl
    refine h.trans ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast Finset.card_le_card (fun w hw => by
      simpa using (Finset.mem_filter.mp hw).2.1)
  have hsum : ∑ _v : V, α * (Fintype.card V : ℝ) ≤ ∑ v : V, (J.degree v : ℝ) :=
    Finset.sum_le_sum fun v _ => hdeg v
  rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  push_cast at hsum
  nlinarith

/-- **Conditional F0 boost (intermediate theorem).** `b = C + 1` and
`ε = 1/(4CK)` depend only on `C` and `K`; `κ` and `N` depend on `τ` (and `α`).
The bounded balanced right inverse is an explicit hypothesis on `J`. -/
theorem rigid_boost (C α K : ℝ) (hC : 1 ≤ C) (hα : 0 < α) (hK : 0 < K) :
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧ ∀ τ : ℝ, 0 < τ → ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] (φ : Finset V → ℝ),
        IsRegularAlmostPacking p F0 J C ε φ → AntiEdgeful p F0 J α →
        |(pairFun (groupPair g0) (edgeVec p J.edgeFinset) : ℝ)| ≤
          κ * (Fintype.card V : ℝ) ^ 2 →
        HasBoundedBalancedInverse p J K →
        ∃ ψ : Finset V → ℝ,
          (∀ s, IsCopy p F0 J s → 0 ≤ ψ s ∧ ψ s ≤ b / Fintype.card V) ∧
          ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ := by
  have hC0 : 0 < C := by linarith
  refine ⟨C + 1, 1 / (4 * C * K), by linarith, by positivity, fun τ hτ => ?_⟩
  set ε : ℝ := 1 / (4 * C * K) with hεdef
  have hε : 0 < ε := by positivity
  set τ' : ℝ := min τ ε with hτ'
  have hτ'0 : 0 < τ' := lt_min hτ hε
  refine ⟨α * τ' / 2, by positivity, 2, ?_⟩
  intro V _ _ hV p J _ φ hseed hJ hbal hinv
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast (show 0 < Fintype.card V by omega)
  set E := J.edgeFinset
  set Q : ℝ := (pairFun (groupPair g0) (edgeVec p E) : ℝ) with hQ
  set S : ℝ := ∑ e ∈ E, gFun p e ^ 2 with hS
  have hE : α * n ^ 2 ≤ 2 * (E.card : ℝ) := card_edges_lower p J hJ hV
  have hαn : 0 < α * n ^ 2 := by positivity
  have hS4 : 4 * (E.card : ℝ) ≤ S := by
    have := Finset.sum_le_sum (fun e (_ : e ∈ E) => gFun_sq_ge p e)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have hEpos : 0 < (E.card : ℝ) := by nlinarith
  have hSpos : 0 < S := by linarith
  -- the uniform correction removing the global charge
  let y : Sym2 V → ℝ := fun e => Q / S * gFun p e
  have hy : ∀ e, |y e| ≤ τ' := by
    intro e
    have h1 : |y e| = |Q| * |gFun p e| / S := by
      simp only [y, abs_mul, abs_div, abs_of_pos hSpos]
      ring
    rw [h1, div_le_iff₀ hSpos]
    have h2 : |Q| * |gFun p e| ≤ (α * τ' / 2 * n ^ 2) * 4 :=
      mul_le_mul hbal (abs_gFun_le p e) (abs_nonneg _) (by positivity)
    nlinarith
  let d : Sym2 V → ℝ := fun e => 1 - edgeLoad p F0 J φ e
  have hd : ∀ e ∈ E, 0 ≤ d e ∧ d e ≤ ε := by
    intro e he
    have h := hseed.2 e he
    change 1 - ε ≤ edgeLoad p F0 J φ e ∧ edgeLoad p F0 J φ e ≤ 1 at h
    exact ⟨by simp only [d]; linarith, by simp only [d]; linarith⟩
  let x : Sym2 V → ℝ := fun e => d e - y e
  have hxM : ∀ e ∈ E, |x e| ≤ 2 * ε := by
    intro e he
    have h1 := hd e he
    have h2 := hy e
    have h3 : τ' ≤ ε := min_le_right _ _
    simp only [x]
    rw [abs_le] at h2 ⊢
    constructor <;> linarith
  have hgsum : ∑ e ∈ E, gFun p e = Q := by
    simp only [gFun, hQ, pairFun_edgeVec, Int.cast_sum]
  have hgload : ∑ e ∈ E, gFun p e * edgeLoad p F0 J φ e = 0 :=
    annihilator_load_identity p F0 J φ annihilates_F0
  have hxbal : ∑ e ∈ E, gFun p e * x e = 0 := by
    have h1 : ∑ e ∈ E, gFun p e * x e =
        ∑ e ∈ E, gFun p e - ∑ e ∈ E, gFun p e * edgeLoad p F0 J φ e -
          Q / S * ∑ e ∈ E, gFun p e ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [x, d, y]
      ring
    rw [h1, hgsum, hgload, ← hS]
    field_simp
    ring
  obtain ⟨η, hηload, hηbound⟩ := hinv x (2 * ε) (by positivity) hxM hxbal
  refine ⟨fun s => φ s + η s, fun s hs => ?_, fun e he => ?_⟩
  · have hφ := hseed.1 s hs
    have hη := hηbound s (mem_copies_iff.mpr hs)
    have hKε : K * (2 * ε) / n = 1 / (2 * C * n) := by
      rw [hεdef]
      field_simp
      ring
    rw [hKε] at hη
    have hη' := abs_le.mp hη
    have h1 : 1 / (C * n) - 1 / (2 * C * n) = 1 / (2 * C * n) := by
      field_simp
      ring
    have h2 : 1 / (2 * C * n) ≤ 1 / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      nlinarith
    have h3 : 0 ≤ 1 / (2 * C * n) := by positivity
    constructor
    · linarith [hφ.1, hη'.1]
    · have h4 : (C + 1) / n = C / n + 1 / n := by ring
      rw [h4]
      linarith [hφ.2, hη'.2]
  · rw [edgeLoad_add, hηload e he]
    have h1 : edgeLoad p F0 J φ e + x e - 1 = -(y e) := by
      simp only [x, d]
      ring
    rw [h1, abs_neg]
    exact (hy e).trans (min_le_left _ _)

/-- **The rigidity hypothesis genuinely fails on the parallel example.** For each
fixed `K > 0`, once `q` is large and then `k` is large, the complete four-partite
example has no `K`-bounded balanced right inverse (otherwise `rigid_boost` would
produce weights contradicting `fam_no_near_loads`). -/
theorem fam_not_boundedBalancedInverse (K : ℝ) (hK : 0 < K) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ¬ HasBoundedBalancedInverse (qpart (fam k q)) (qgraph (fam k q)) K := by
  obtain ⟨b, ε, -, hε, H⟩ := rigid_boost 2 (1 / 8) K (by norm_num) (by norm_num) hK
  refine ⟨⌈14 / ε⌉₊ + 7, fun q hq => ?_⟩
  have hq7 : 7 ≤ q := by omega
  have hqR : 14 / ε ≤ (q : ℝ) := by
    have h1 : (⌈14 / ε⌉₊ : ℝ) ≤ q := by exact_mod_cast (by omega : ⌈14 / ε⌉₊ ≤ q)
    linarith [Nat.le_ceil (14 / ε)]
  have hqε : 14 / (2 * (q : ℝ) + 20) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at hqR
    nlinarith
  obtain ⟨κ, hκ, N, hN⟩ := H (24 / ((2 * (q : ℝ) + 18) * (2 * q + 8))) (by positivity)
  refine ⟨N + 1, fun k hk hinv => ?_⟩
  have hkpos : 0 < k := by omega
  have hcard : N ≤ Fintype.card (QV (fam k q)) := by
    have h1 : (N : ℝ) ≤ Fintype.card (QV (fam k q)) := by
      rw [card_fam]
      have : (N : ℝ) + 1 ≤ k := by exact_mod_cast hk
      nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast h1
  have hseed := fam_seed (q := q) hkpos
  have hseed' : IsRegularAlmostPacking (qpart (fam k q)) F0 (qgraph (fam k q)) 2 ε
      (fun _ => 1 / (2 * (k : ℝ) * (2 * q + 20))) :=
    ⟨hseed.1, fun e he => ⟨by linarith [(hseed.2 e he).1], (hseed.2 e he).2⟩⟩
  obtain ⟨ψ, -, hψ⟩ := hN (QV (fam k q)) hcard (qpart _) (qgraph _) _ hseed'
    (fam_antiEdgeful hq7)
    (by rw [fam_balance, Int.cast_zero, abs_zero]; positivity) hinv
  exact fam_no_near_loads hkpos ψ hψ

end PartitionedTriangleAbsorption.F0RigidBoost
