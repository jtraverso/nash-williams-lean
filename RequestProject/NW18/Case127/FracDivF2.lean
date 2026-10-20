/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.FracDivF1

/-!
# Claim 14.7.2 for `F₂`: fractional `F₂`-divisibility of an idealized `F₂`-blowup

`F₂ = {T₀₀₂, T₀₀₃, T₁₁₂, T₁₁₃, T₀₂₃, T₁₂₃}` (classes `0, 1, 2, 3` are the paper's `1, 2, 3, 4`).
The edge-count map of `F₂` is injective (rank `6`), so the integral representation given by
integral divisibility is the only one; its coefficients are non-negative since all edge counts
between allowed pairs of parts are `≈ n²/16`.  The degree vectors lie in the degree cones
(Lemma 13.20 (ii)) since all degrees into allowed parts are `≈ n/4`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma twoThirds_F2 : TwoThirds F2 := by unfold TwoThirds; decide

lemma allowedT_F2_iff (i j : Fin 4) :
    AllowedT F2 i j ↔ ((i.val < 2 ↔ ¬ j.val < 2) ∨ (i = j ∧ i.val < 2) ∨
      (i ≠ j ∧ ¬ i.val < 2 ∧ ¬ j.val < 2)) := by revert i j; decide

lemma F2_card_three' : ∀ τ ∈ F2, Multiset.card τ = 3 := by decide

lemma F2_sum {M : Type*} [AddCommMonoid M] (f : Multiset (Fin 4) → M) :
    ∑ τ ∈ F2, f τ = f {0, 0, 2} + (f {0, 0, 3} + (f {1, 1, 2} + (f {1, 1, 3} +
      (f {0, 2, 3} + f {1, 2, 3})))) := by
  rw [show F2 = {{0, 0, 2}, {0, 0, 3}, {1, 1, 2}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}} from rfl]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_pair (by decide)]

/-! ### The edge part -/

lemma typeEdgeVec_F2_vals :
    (∀ i j, typeEdgeVec ({0, 0, 2} : Multiset (Fin 4)) i j = (![![2, 0, 2, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({0, 0, 3} : Multiset (Fin 4)) i j = (![![2, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 1, 2} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 2, 2, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 1, 3} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 2, 0, 2], ![0, 0, 0, 0], ![0, 2, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) i j = (![![0, 0, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0]] : Fin 4 → Fin 4 → ℤ) i j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro i j; fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 1000000 in
/-- The edge part of fractional `F₂`-divisibility. -/
lemma fracDiv_edge_F2 {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (h : IsIdealizedT F2 ε G p)
    (hint : IsIntDiv p F2 G.edgeFinset) :
    ∃ c : Multiset (Fin 4) → ℝ, (∀ τ, 0 ≤ c τ) ∧
      (fun i j => (edgeVec p G.edgeFinset i j : ℝ)) =
        ∑ τ ∈ F2, c τ • fun i j => (typeEdgeVec τ i j : ℝ) := by
  obtain ⟨⟨c, hc⟩, -⟩ := hint
  set E := edgeVec p G.edgeFinset with hE
  have eq : ∀ i j, (E i j : ℝ) = ∑ τ ∈ F2, (c τ : ℝ) * (typeEdgeVec τ i j : ℝ) := by
    intro i j
    have := congrFun (congrFun hc i) j
    rw [Finset.sum_apply, Finset.sum_apply] at this
    rw [this, Int.cast_sum]
    refine sum_congr rfl fun τ _ => ?_
    simp [Pi.smul_apply]
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := typeEdgeVec_F2_vals
  have eqs : ∀ i j, (E i j : ℝ) = (c {0, 0, 2} : ℝ) * (typeEdgeVec {0, 0, 2} i j : ℝ) +
      ((c {0, 0, 3} : ℝ) * (typeEdgeVec {0, 0, 3} i j : ℝ) +
      ((c {1, 1, 2} : ℝ) * (typeEdgeVec {1, 1, 2} i j : ℝ) +
      ((c {1, 1, 3} : ℝ) * (typeEdgeVec {1, 1, 3} i j : ℝ) +
      ((c {0, 2, 3} : ℝ) * (typeEdgeVec {0, 2, 3} i j : ℝ) +
      (c {1, 2, 3} : ℝ) * (typeEdgeVec {1, 2, 3} i j : ℝ))))) := by
    intro i j; rw [eq]; exact F2_sum _
  have e00 := eqs 0 0
  have e11 := eqs 1 1
  have e23 := eqs 2 3
  have e02 := eqs 0 2
  have e03 := eqs 0 3
  have e12 := eqs 1 2
  have e13 := eqs 1 3
  simp only [v1, v2, v3, v4, v5, v6, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one, mul_zero, mul_one,
    zero_add, add_zero] at e00 e11 e23 e02 e03 e12 e13
  have B : ∀ i j, AllowedT F2 i j → 9 / 10 * ((Fintype.card V : ℝ) / 4) ^ 2 ≤ (E i j : ℝ) ∧
      (E i j : ℝ) ≤ 11 / 10 * ((Fintype.card V : ℝ) / 4) ^ 2 :=
    fun i j hij => edgeVec_bounds_ideal hε0 hε h hij
  obtain ⟨l00, u00⟩ := B 0 0 (by decide)
  obtain ⟨l11, u11⟩ := B 1 1 (by decide)
  obtain ⟨l23, u23⟩ := B 2 3 (by decide)
  obtain ⟨l02, u02⟩ := B 0 2 (by decide)
  obtain ⟨l03, u03⟩ := B 0 3 (by decide)
  obtain ⟨l12, u12⟩ := B 1 2 (by decide)
  obtain ⟨l13, u13⟩ := B 1 3 (by decide)
  have hs : 0 ≤ ((Fintype.card V : ℝ) / 4) ^ 2 := sq_nonneg _
  refine ⟨fun τ => if τ ∈ F2 then (c τ : ℝ) else 0, fun τ => ?_, ?_⟩
  · dsimp (config := { failIfUnchanged := false }) only
    split_ifs with hτ
    · have hτ' : τ = {0, 0, 2} ∨ τ = {0, 0, 3} ∨ τ = {1, 1, 2} ∨ τ = {1, 1, 3} ∨
          τ = {0, 2, 3} ∨ τ = {1, 2, 3} := by
        revert hτ; revert τ; decide
      rcases hτ' with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
    · exact le_rfl
  · funext i j
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [sum_congr rfl (fun τ hτ => by rw [if_pos hτ])]
    exact eq i j

/-! ### The vertex part -/

lemma typeDegVec_F2_vals :
    (∀ i, typeDegVec ({0, 0, 2} : Multiset (Fin 4)) 0 i = (![1, 0, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 0, 3} : Multiset (Fin 4)) 0 i = (![1, 0, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 2, 3} : Multiset (Fin 4)) 0 i = (![0, 0, 1, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 2} : Multiset (Fin 4)) 1 i = (![0, 1, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 3} : Multiset (Fin 4)) 1 i = (![0, 1, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 2, 3} : Multiset (Fin 4)) 1 i = (![0, 0, 1, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 0, 2} : Multiset (Fin 4)) 2 i = (![2, 0, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 2} : Multiset (Fin 4)) 2 i = (![0, 2, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 2, 3} : Multiset (Fin 4)) 2 i = (![1, 0, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 2, 3} : Multiset (Fin 4)) 2 i = (![0, 1, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 0, 3} : Multiset (Fin 4)) 3 i = (![2, 0, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 3} : Multiset (Fin 4)) 3 i = (![0, 2, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 2, 3} : Multiset (Fin 4)) 3 i = (![1, 0, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 2, 3} : Multiset (Fin 4)) 3 i = (![0, 1, 1, 0] : Fin 4 → ℤ) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A degree vector in the `F₂` degree cone of part `a`: it vanishes on the parts not allowed
for `a`, and its entries on the allowed parts lie in `[L, U]` with `U ≤ 2 L`. -/
lemma vertex_cone_F2 (d : Fin 4 → ℝ) (a : Fin 4) (L U : ℝ) (hL : 0 < L) (hLU : U ≤ 2 * L)
    (hz : ∀ j, ¬ AllowedT F2 a j → d j = 0) (hlo : ∀ j, AllowedT F2 a j → L ≤ d j)
    (hup : ∀ j, d j ≤ U) :
    ∃ c : Multiset (Fin 4) → ℝ, (∀ τ, 0 ≤ c τ) ∧
      d = ∑ τ ∈ F2 with a ∈ τ, c τ • fun i => (typeDegVec τ a i : ℝ) := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := typeDegVec_F2_vals
  have u0 := hup 0
  have u1 := hup 1
  have u2 := hup 2
  have u3 := hup 3
  rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) a with rfl | rfl | rfl | rfl
  · have hz1 := hz 1 (by decide)
    have l0 := hlo 0 (by decide)
    have l2 := hlo 2 (by decide)
    have l3 := hlo 3 (by decide)
    refine ⟨fun τ => if τ = {0, 0, 2} then (d 0 + d 2 - d 3) / 2 else
      if τ = {0, 0, 3} then (d 0 + d 3 - d 2) / 2 else
      if τ = {0, 2, 3} then (d 2 + d 3 - d 0) / 2 else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> linarith
    · rw [show F2.filter (fun τ => ((0 : Fin 4) ∈ τ)) = {{0, 0, 2}, {0, 0, 3}, {0, 2, 3}}
        by decide]
      rw [sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1, w2, w3]
      fin_cases i <;> simp +decide <;> linarith
  · have hz0 := hz 0 (by decide)
    have l1 := hlo 1 (by decide)
    have l2 := hlo 2 (by decide)
    have l3 := hlo 3 (by decide)
    refine ⟨fun τ => if τ = {1, 1, 2} then (d 1 + d 2 - d 3) / 2 else
      if τ = {1, 1, 3} then (d 1 + d 3 - d 2) / 2 else
      if τ = {1, 2, 3} then (d 2 + d 3 - d 1) / 2 else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> linarith
    · rw [show F2.filter (fun τ => ((1 : Fin 4) ∈ τ)) = {{1, 1, 2}, {1, 1, 3}, {1, 2, 3}}
        by decide]
      rw [sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w4, w5, w6]
      fin_cases i <;> simp +decide <;> linarith
  · have hz2 := hz 2 (by decide)
    have l0 := hlo 0 (by decide)
    have l1 := hlo 1 (by decide)
    have l3 := hlo 3 (by decide)
    obtain ⟨x, y, z, w, hx, hy, hz', hw, e1, e2, e3⟩ :=
      cone_two (d 3) (d 0) (d 1) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith)
    refine ⟨fun τ => if τ = {0, 2, 3} then x else if τ = {1, 2, 3} then y else
      if τ = {0, 0, 2} then z else if τ = {1, 1, 2} then w else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> first | assumption | exact le_rfl
    · rw [show F2.filter (fun τ => ((2 : Fin 4) ∈ τ)) = {{0, 0, 2}, {1, 1, 2}, {0, 2, 3}, {1, 2, 3}}
        by decide]
      rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w7, w8, w9, w10]
      fin_cases i <;> simp +decide <;> linarith
  · have hz3 := hz 3 (by decide)
    have l0 := hlo 0 (by decide)
    have l1 := hlo 1 (by decide)
    have l2 := hlo 2 (by decide)
    obtain ⟨x, y, z, w, hx, hy, hz', hw, e1, e2, e3⟩ :=
      cone_two (d 2) (d 0) (d 1) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith)
    refine ⟨fun τ => if τ = {0, 2, 3} then x else if τ = {1, 2, 3} then y else
      if τ = {0, 0, 3} then z else if τ = {1, 1, 3} then w else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> first | assumption | exact le_rfl
    · rw [show F2.filter (fun τ => ((3 : Fin 4) ∈ τ)) = {{0, 0, 3}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}}
        by decide]
      rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w11, w12, w13, w14]
      fin_cases i <;> simp +decide <;> linarith

/-- **Claim 14.7.2 for `F₂`.** An integrally `F₂`-divisible `ε`-balanced `ε`-nearly-complete
`F₂`-blowup (`ε ≤ 1/100`, `n > 0`) is fractionally `F₂`-divisible. -/
lemma isFracDiv_F2 {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (hn : 0 < Fintype.card V) (h : IsIdealizedT F2 ε G p)
    (hint : IsIntDiv p F2 G.edgeFinset) : IsFracDiv p F2 G.edgeFinset := by
  refine ⟨fracDiv_edge_F2 hε0 hε h hint, fun v => ?_⟩
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn' : (0 : ℝ) < n := by rw [hndef]; exact_mod_cast hn
  set d : Fin 4 → ℝ := fun i => (degT G p v i : ℝ) with hd
  have hdv : (fun i => (degVec p G.edgeFinset v i : ℝ)) = d := by
    funext i; rw [hd, degVec_eq_degT]; rfl
  rw [hdv]
  have hlo : ∀ j, AllowedT F2 (p v) j → (1 - 5 * ε) * n / 4 ≤ d j := by
    intro j hj
    have h1 := h.2.2 v j hj
    have h2 := h.lo j
    simp only [hd]; rw [← hndef] at h1 h2; linarith
  have hup : ∀ j, d j ≤ (1 + 3 * ε) * n / 4 := by
    intro j
    have h1 : (degT G p v j : ℝ) ≤ (clsT p j).card := by exact_mod_cast degT_le_class G p v j
    have h2 := card_clsT_le_four p h.lo j
    simp only [hd]; rw [← hndef] at h2; linarith
  have hzero : ∀ j, ¬ AllowedT F2 (p v) j → d j = 0 := by
    intro j hj
    simp only [hd]; rw [degT_eq_zero_of_not_allowed h.2.1 hj]; simp
  exact vertex_cone_F2 d (p v) _ _ (by nlinarith) (by nlinarith) hzero hlo hup

/-- **Theorem 14.7 for `F₂` as a proposition** (open premise of branch (4), Theorem 12.7): there
are `ε > 0` and `n₀` such that every integrally `F₂`-divisible `ε`-balanced `ε`-nearly-complete
`F₂`-blowup (`IsIdealizedT`) on `n ≥ n₀` vertices has an `F₂`-decomposition.  In its hosts
every allowed pair of classes is near-complete (classes `0` and `1` are near-cliques, classes `2`
and `3` are independent), so the sub-block parity construction recorded against the
arbitrary-host interface does not apply to them.  It is
implied by `Theorem1316Statement` (`theorem_14_7_F2`).  **Not proved.** -/
def Theorem147F2Statement : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
    IsIntDiv p F2 G.edgeFinset → IsIdealizedT F2 ε G p → HasDecomp p F2 G.edgeFinset

/-- **Theorem 14.7 for `F₂`** (from Theorem 13.16). -/
theorem theorem_14_7_F2 (h1316 : Theorem1316Statement) : Theorem147F2Statement := by
  obtain ⟨ε, hε, n₀, h⟩ := theorem_14_7_of_fracDiv h1316 F2 F2_card_three' twoThirds_F2
  refine ⟨min ε (1 / 100), lt_min hε (by norm_num), max n₀ 1, fun V _ _ p G _ hn hint hid => ?_⟩
  have hid' : IsIdealizedT F2 ε G p := by
    refine ⟨fun i => le_trans ?_ (hid.1 i), hid.2.1, fun v j hj => le_trans ?_ (hid.2.2 v j hj)⟩
    · have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have := min_le_left ε (1 / 100)
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    · have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have := min_le_left ε (1 / 100)
      nlinarith
  exact h V p G (le_trans (le_max_left _ _) hn)
    (isFracDiv_F2 (le_min hε.le (by norm_num)) (min_le_right _ _)
      (lt_of_lt_of_le (by omega) hn) hid hint) hint hid'

end NashWilliams18
