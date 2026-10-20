/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Theorem147

/-!
# Claim 14.7.2 for `F₁`: fractional `F₁`-divisibility of an idealized `F₁`-blowup

`F₁ = {T₀₀₂, T₀₀₃, T₁₁₂, T₁₁₃, T₀₂₂, T₁₂₂, T₀₃₃, T₁₃₃}` (classes `0, 1, 2, 3` are the paper's
`1, 2, 3, 4`).  The edge-count map of `F₁` has a one-dimensional kernel spanned by `kF1`;
starting from an integral representation (integral divisibility) we shift along the kernel to
make all coefficients non-negative, which is possible since all edge counts between allowed
pairs of parts are `≈ n²/16`.  The degree vectors lie in the degree cones since the internal
degree of a vertex is at most about `n/4` while its degree to the two parts of the other side is
about `n/2`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The kernel direction of the edge-count map of `F₁`. -/
def kF1 (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 2} ∨ τ = {1, 1, 3} ∨ τ = {1, 2, 2} ∨ τ = {0, 3, 3} then 1 else
  if τ = {0, 0, 3} ∨ τ = {1, 1, 2} ∨ τ = {0, 2, 2} ∨ τ = {1, 3, 3} then -1 else 0

lemma kF1_kernel : ∑ τ ∈ F1, kF1 τ • typeEdgeVec τ = 0 := by decide

lemma twoThirds_F1 : TwoThirds F1 := by unfold TwoThirds; decide

lemma allowedT_F1_iff (i j : Fin 4) :
    AllowedT F1 i j ↔ ¬ (i ≠ j ∧ (i.val < 2 ↔ j.val < 2)) := by revert i j; decide

lemma F1_card_three' : ∀ τ ∈ F1, Multiset.card τ = 3 := by decide

lemma F1_sum {M : Type*} [AddCommMonoid M] (f : Multiset (Fin 4) → M) :
    ∑ τ ∈ F1, f τ = f {0, 0, 2} + (f {0, 0, 3} + (f {1, 1, 2} + (f {1, 1, 3} +
      (f {0, 2, 2} + (f {1, 2, 2} + (f {0, 3, 3} + f {1, 3, 3})))))) := by
  rw [show F1 = {{0, 0, 2}, {0, 0, 3}, {1, 1, 2}, {1, 1, 3}, {0, 2, 2}, {1, 2, 2}, {0, 3, 3},
    {1, 3, 3}} from rfl]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_pair (by decide)]

/-- The non-negative solution of the two-colour cone: `x + y = D`, `x + 2z = P`,
`y + 2w = Q`. -/
lemma cone_two (D P Q : ℝ) (hD : 0 ≤ D) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hPQ : 0 < P + Q)
    (h : D ≤ P + Q) : ∃ x y z w : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ w ∧ x + y = D ∧
      x + 2 * z = P ∧ y + 2 * w = Q := by
  refine ⟨D * P / (P + Q), D * Q / (P + Q), (P - D * P / (P + Q)) / 2,
    (Q - D * Q / (P + Q)) / 2, by positivity, by positivity, ?_, ?_, ?_, by ring, by ring⟩
  · have : D * P / (P + Q) ≤ P := by
      rw [div_le_iff₀ hPQ]; nlinarith
    linarith
  · have : D * Q / (P + Q) ≤ Q := by
      rw [div_le_iff₀ hPQ]; nlinarith
    linarith
  · field_simp

/-! ### Degree and edge counts in an idealized blowup -/

lemma degVec_eq_degT {t : ℕ} (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (j : Fin t) : degVec p G.edgeFinset v j = (degT G p v j : ℤ) := by
  classical
  exact PartitionedTriangleAbsorption.TypedLoadCounterexample.degVec_edgeFinset p G v j

omit [DecidableEq V] in
lemma degT_eq_zero_of_not_allowed {t : ℕ} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin t}
    (hbl : ∀ u v, G.Adj u v → AllowedT F (p u) (p v)) {v : V} {j : Fin t}
    (hj : ¬ AllowedT F (p v) j) : degT G p v j = 0 := by
  unfold degT
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro w - ⟨hw, rfl⟩
  exact hj (hbl v w hw)

lemma edgeVec_eq_sum_degT {t : ℕ} (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : Fin t) : edgeVec p G.edgeFinset i j = ∑ v ∈ clsT p i, (degT G p v j : ℤ) := by
  rw [PartitionedTriangleAbsorption.TypedLoadCounterexample.edgeVec_eq_sum_degVec]
  exact sum_congr rfl fun v _ => degVec_eq_degT p G v j

/-- Edge counts between allowed pairs of parts of an idealized four-part blowup. -/
lemma edgeVec_bounds_ideal {F : Finset (Multiset (Fin 4))} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4}
    (h : IsIdealizedT F ε G p) {i j : Fin 4} (hij : AllowedT F i j) :
    9 / 10 * ((Fintype.card V : ℝ) / 4) ^ 2 ≤ (edgeVec p G.edgeFinset i j : ℝ) ∧
      (edgeVec p G.edgeFinset i j : ℝ) ≤ 11 / 10 * ((Fintype.card V : ℝ) / 4) ^ 2 := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn : 0 ≤ n := Nat.cast_nonneg _
  rw [edgeVec_eq_sum_degT]
  push_cast
  have hlo : ∀ v ∈ clsT p i, ((clsT p j).card : ℝ) - ε * n ≤ (degT G p v j : ℝ) := by
    intro v hv
    have hv' : p v = i := (mem_filter.mp hv).2
    exact h.2.2 v j (hv' ▸ hij)
  have hup : ∀ v ∈ clsT p i, (degT G p v j : ℝ) ≤ (clsT p j).card := by
    intro v _; exact_mod_cast degT_le_class G p v j
  have s1 := card_nsmul_le_sum _ _ _ hlo
  have s2 := sum_le_card_nsmul _ _ _ hup
  rw [nsmul_eq_mul] at s1 s2
  have li := h.lo i
  have lj := h.lo j
  have ui := card_clsT_le_four p h.lo i
  have uj := card_clsT_le_four p h.lo j
  rw [← hndef] at li lj ui uj
  have hεn : ε * n ≤ n / 100 := by nlinarith
  set a : ℝ := ((clsT p i).card : ℝ)
  set b : ℝ := ((clsT p j).card : ℝ)
  constructor
  · have hb : (1 - 5 * ε) * n / 4 ≤ b - ε * n := by linarith
    have h1 : (1 - ε) * n / 4 * ((1 - 5 * ε) * n / 4) ≤ a * (b - ε * n) :=
      mul_le_mul li hb (by linarith) (by linarith)
    have h2 : 9 / 10 * (n / 4) ^ 2 ≤ (1 - ε) * n / 4 * ((1 - 5 * ε) * n / 4) := by
      have : (9 / 10 : ℝ) ≤ (1 - ε) * (1 - 5 * ε) := by nlinarith
      nlinarith [sq_nonneg n]
    linarith
  · have h1 : a * b ≤ (1 + 3 * ε) * n / 4 * ((1 + 3 * ε) * n / 4) :=
      mul_le_mul ui uj (by linarith) (by linarith)
    have h2 : (1 + 3 * ε) * n / 4 * ((1 + 3 * ε) * n / 4) ≤ 11 / 10 * (n / 4) ^ 2 := by
      have : (1 + 3 * ε) * (1 + 3 * ε) ≤ 11 / 10 := by nlinarith
      nlinarith [sq_nonneg n]
    linarith

/-! ### The edge part -/

lemma typeEdgeVec_F1_vals :
    (∀ i j, typeEdgeVec ({0, 0, 2} : Multiset (Fin 4)) i j = (![![2, 0, 2, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({0, 0, 3} : Multiset (Fin 4)) i j = (![![2, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 1, 2} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 2, 2, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 1, 3} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 2, 0, 2], ![0, 0, 0, 0], ![0, 2, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({0, 2, 2} : Multiset (Fin 4)) i j = (![![0, 0, 2, 0], ![0, 0, 0, 0], ![2, 0, 2, 0], ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 2, 2} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 0, 2, 0], ![0, 2, 2, 0], ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({0, 3, 3} : Multiset (Fin 4)) i j = (![![0, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 2]] : Fin 4 → Fin 4 → ℤ) i j) ∧
    (∀ i j, typeEdgeVec ({1, 3, 3} : Multiset (Fin 4)) i j = (![![0, 0, 0, 0], ![0, 0, 0, 2], ![0, 0, 0, 0], ![0, 2, 0, 2]] : Fin 4 → Fin 4 → ℤ) i j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro i j; fin_cases i <;> fin_cases j <;> decide

/-- Shifting an integral representation along the kernel keeps the edge vector. -/
lemma shift_eq_F1 (c : Multiset (Fin 4) → ℤ) (s : ℝ) {E : Fin 4 → Fin 4 → ℤ}
    (eq : ∀ i j, (E i j : ℝ) = ∑ τ ∈ F1, (c τ : ℝ) * (typeEdgeVec τ i j : ℝ)) :
    (fun i j => (E i j : ℝ)) = ∑ τ ∈ F1,
      (fun τ => if τ ∈ F1 then (c τ : ℝ) + s * (kF1 τ : ℝ) else 0) τ •
        fun i j => (typeEdgeVec τ i j : ℝ) := by
  have ker : ∀ i j, ∑ τ ∈ F1, (kF1 τ : ℝ) * (typeEdgeVec τ i j : ℝ) = 0 := by
    intro i j
    have := congrFun (congrFun kF1_kernel i) j
    rw [Finset.sum_apply, Finset.sum_apply] at this
    have h' : ((∑ τ ∈ F1, (kF1 τ • typeEdgeVec τ) i j : ℤ) : ℝ) = 0 := by
      rw [this]; simp
    rw [Int.cast_sum] at h'
    rw [← h']
    refine sum_congr rfl fun τ _ => ?_
    simp [Pi.smul_apply]
  funext i j
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [sum_congr rfl (fun τ hτ => by rw [if_pos hτ])]
  simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum, ker, mul_zero, add_zero]
  exact eq i j

set_option maxHeartbeats 1000000 in
/-- The edge part of fractional `F₁`-divisibility. -/
lemma fracDiv_edge_F1 {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (h : IsIdealizedT F1 ε G p)
    (hint : IsIntDiv p F1 G.edgeFinset) :
    ∃ c : Multiset (Fin 4) → ℝ, (∀ τ, 0 ≤ c τ) ∧
      (fun i j => (edgeVec p G.edgeFinset i j : ℝ)) =
        ∑ τ ∈ F1, c τ • fun i j => (typeEdgeVec τ i j : ℝ) := by
  obtain ⟨⟨c, hc⟩, -⟩ := hint
  set E := edgeVec p G.edgeFinset with hE
  have eq : ∀ i j, (E i j : ℝ) = ∑ τ ∈ F1, (c τ : ℝ) * (typeEdgeVec τ i j : ℝ) := by
    intro i j
    have := congrFun (congrFun hc i) j
    rw [Finset.sum_apply, Finset.sum_apply] at this
    rw [this, Int.cast_sum]
    refine sum_congr rfl fun τ _ => ?_
    simp [Pi.smul_apply]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := typeEdgeVec_F1_vals
  have eqs : ∀ i j, (E i j : ℝ) = (c {0, 0, 2} : ℝ) * (typeEdgeVec {0, 0, 2} i j : ℝ) +
      ((c {0, 0, 3} : ℝ) * (typeEdgeVec {0, 0, 3} i j : ℝ) +
      ((c {1, 1, 2} : ℝ) * (typeEdgeVec {1, 1, 2} i j : ℝ) +
      ((c {1, 1, 3} : ℝ) * (typeEdgeVec {1, 1, 3} i j : ℝ) +
      ((c {0, 2, 2} : ℝ) * (typeEdgeVec {0, 2, 2} i j : ℝ) +
      ((c {1, 2, 2} : ℝ) * (typeEdgeVec {1, 2, 2} i j : ℝ) +
      ((c {0, 3, 3} : ℝ) * (typeEdgeVec {0, 3, 3} i j : ℝ) +
      (c {1, 3, 3} : ℝ) * (typeEdgeVec {1, 3, 3} i j : ℝ))))))) := by
    intro i j; rw [eq]; exact F1_sum _
  have e00 := eqs 0 0
  have e11 := eqs 1 1
  have e22 := eqs 2 2
  have e33 := eqs 3 3
  have e02 := eqs 0 2
  have e03 := eqs 0 3
  have e12 := eqs 1 2
  have e13 := eqs 1 3
  simp only [v1, v2, v3, v4, v5, v6, v7, v8, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_ofNat, Int.cast_zero, mul_zero, zero_add, add_zero] at e00 e11 e22 e33 e02 e03 e12 e13
  have B : ∀ i j, AllowedT F1 i j → 9 / 10 * ((Fintype.card V : ℝ) / 4) ^ 2 ≤ (E i j : ℝ) ∧
      (E i j : ℝ) ≤ 11 / 10 * ((Fintype.card V : ℝ) / 4) ^ 2 :=
    fun i j hij => edgeVec_bounds_ideal hε0 hε h hij
  obtain ⟨l00, u00⟩ := B 0 0 (by decide)
  obtain ⟨l11, u11⟩ := B 1 1 (by decide)
  obtain ⟨l22, u22⟩ := B 2 2 (by decide)
  obtain ⟨l33, u33⟩ := B 3 3 (by decide)
  obtain ⟨l02, u02⟩ := B 0 2 (by decide)
  obtain ⟨l03, u03⟩ := B 0 3 (by decide)
  obtain ⟨l12, u12⟩ := B 1 2 (by decide)
  obtain ⟨l13, u13⟩ := B 1 3 (by decide)
  have hs : 0 ≤ ((Fintype.card V : ℝ) / 4) ^ 2 := sq_nonneg _
  set a := (c {0, 0, 2} : ℝ)
  set b := (c {0, 0, 3} : ℝ)
  set cc := (c {1, 1, 2} : ℝ)
  set d := (c {1, 1, 3} : ℝ)
  set e := (c {0, 2, 2} : ℝ)
  set f := (c {1, 2, 2} : ℝ)
  set g := (c {0, 3, 3} : ℝ)
  set hh := (c {1, 3, 3} : ℝ)
  set s := max (max (-a) (-d)) (max (-f) (-g)) with hsdef
  have sa : -a ≤ s := le_trans (le_max_left _ _) (le_max_left _ _)
  have sd : -d ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
  have sf : -f ≤ s := le_trans (le_max_left _ _) (le_max_right _ _)
  have sg : -g ≤ s := le_trans (le_max_right _ _) (le_max_right _ _)
  have upper : ∀ x : ℝ, -a ≤ x → -d ≤ x → -f ≤ x → -g ≤ x → s ≤ x := fun x h1 h2 h3 h4 =>
    max_le (max_le h1 h2) (max_le h3 h4)
  have sb : s ≤ b := upper b (by linarith) (by linarith) (by linarith) (by linarith)
  have scc : s ≤ cc := upper cc (by linarith) (by linarith) (by linarith) (by linarith)
  have se : s ≤ e := upper e (by linarith) (by linarith) (by linarith) (by linarith)
  have shh : s ≤ hh := upper hh (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨fun τ => if τ ∈ F1 then (c τ : ℝ) + s * (kF1 τ : ℝ) else 0, fun τ => ?_, ?_⟩
  · dsimp (config := { failIfUnchanged := false }) only
    split_ifs with hτ
    · have hτ' : τ = {0, 0, 2} ∨ τ = {0, 0, 3} ∨ τ = {1, 1, 2} ∨ τ = {1, 1, 3} ∨
          τ = {0, 2, 2} ∨ τ = {1, 2, 2} ∨ τ = {0, 3, 3} ∨ τ = {1, 3, 3} := by
        revert hτ; revert τ; decide
      rcases hτ' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show kF1 {0, 0, 2} = 1 by decide]; push_cast; linarith
      · rw [show kF1 {0, 0, 3} = -1 by decide]; push_cast; linarith
      · rw [show kF1 {1, 1, 2} = -1 by decide]; push_cast; linarith
      · rw [show kF1 {1, 1, 3} = 1 by decide]; push_cast; linarith
      · rw [show kF1 {0, 2, 2} = -1 by decide]; push_cast; linarith
      · rw [show kF1 {1, 2, 2} = 1 by decide]; push_cast; linarith
      · rw [show kF1 {0, 3, 3} = 1 by decide]; push_cast; linarith
      · rw [show kF1 {1, 3, 3} = -1 by decide]; push_cast; linarith
    · exact le_rfl
  · exact shift_eq_F1 c s (fun i j => eq i j)

/-! ### The vertex part -/

lemma typeDegVec_F1_vals :
    (∀ i, typeDegVec ({0, 0, 2} : Multiset (Fin 4)) 0 i = (![1, 0, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 0, 3} : Multiset (Fin 4)) 0 i = (![1, 0, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 2, 2} : Multiset (Fin 4)) 0 i = (![0, 0, 2, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 3, 3} : Multiset (Fin 4)) 0 i = (![0, 0, 0, 2] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 2} : Multiset (Fin 4)) 1 i = (![0, 1, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 3} : Multiset (Fin 4)) 1 i = (![0, 1, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 2, 2} : Multiset (Fin 4)) 1 i = (![0, 0, 2, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 3, 3} : Multiset (Fin 4)) 1 i = (![0, 0, 0, 2] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 0, 2} : Multiset (Fin 4)) 2 i = (![2, 0, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 2} : Multiset (Fin 4)) 2 i = (![0, 2, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 2, 2} : Multiset (Fin 4)) 2 i = (![1, 0, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 2, 2} : Multiset (Fin 4)) 2 i = (![0, 1, 1, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 0, 3} : Multiset (Fin 4)) 3 i = (![2, 0, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 1, 3} : Multiset (Fin 4)) 3 i = (![0, 2, 0, 0] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({0, 3, 3} : Multiset (Fin 4)) 3 i = (![1, 0, 0, 1] : Fin 4 → ℤ) i) ∧
    (∀ i, typeDegVec ({1, 3, 3} : Multiset (Fin 4)) 3 i = (![0, 1, 0, 1] : Fin 4 → ℤ) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A degree vector in the `F₁` degree cone. -/
lemma vertex_cone_F1 (d : Fin 4 → ℝ) (a : Fin 4) (hd : ∀ i, 0 ≤ d i)
    (h01 : a.val < 2 → d (if a = 0 then 1 else 0) = 0 ∧ d a ≤ d 2 + d 3 ∧ 0 < d 2 + d 3)
    (h23 : 2 ≤ a.val → d (if a = 2 then 3 else 2) = 0 ∧ d a ≤ d 0 + d 1 ∧ 0 < d 0 + d 1) :
    ∃ c : Multiset (Fin 4) → ℝ, (∀ τ, 0 ≤ c τ) ∧
      d = ∑ τ ∈ F1 with a ∈ τ, c τ • fun i => (typeDegVec τ a i : ℝ) := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16⟩ :=
    typeDegVec_F1_vals
  rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) a with rfl | rfl | rfl | rfl
  · obtain ⟨hz, hD, hpos⟩ := h01 (by decide)
    simp at hz hD
    obtain ⟨x, y, z, w, hx, hy, hz', hw, e1, e2, e3⟩ :=
      cone_two (d 0) (d 2) (d 3) (hd 0) (hd 2) (hd 3) hpos hD
    refine ⟨fun τ => if τ = {0, 0, 2} then x else if τ = {0, 0, 3} then y else
      if τ = {0, 2, 2} then z else if τ = {0, 3, 3} then w else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> first | assumption | exact le_rfl
    · rw [show F1.filter (fun τ => ((0 : Fin 4) ∈ τ)) = {{0, 0, 2}, {0, 0, 3}, {0, 2, 2}, {0, 3, 3}}
        by decide]
      rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1, w2, w3, w4]
      fin_cases i <;> simp +decide <;> linarith
  · obtain ⟨hz, hD, hpos⟩ := h01 (by decide)
    simp at hz hD
    obtain ⟨x, y, z, w, hx, hy, hz', hw, e1, e2, e3⟩ :=
      cone_two (d 1) (d 2) (d 3) (hd 1) (hd 2) (hd 3) hpos hD
    refine ⟨fun τ => if τ = {1, 1, 2} then x else if τ = {1, 1, 3} then y else
      if τ = {1, 2, 2} then z else if τ = {1, 3, 3} then w else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> first | assumption | exact le_rfl
    · rw [show F1.filter (fun τ => ((1 : Fin 4) ∈ τ)) = {{1, 1, 2}, {1, 1, 3}, {1, 2, 2}, {1, 3, 3}}
        by decide]
      rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w5, w6, w7, w8]
      fin_cases i <;> simp +decide <;> linarith
  · obtain ⟨hz, hD, hpos⟩ := h23 (by decide)
    simp at hz hD
    obtain ⟨x, y, z, w, hx, hy, hz', hw, e1, e2, e3⟩ :=
      cone_two (d 2) (d 0) (d 1) (hd 2) (hd 0) (hd 1) hpos hD
    refine ⟨fun τ => if τ = {0, 2, 2} then x else if τ = {1, 2, 2} then y else
      if τ = {0, 0, 2} then z else if τ = {1, 1, 2} then w else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> first | assumption | exact le_rfl
    · rw [show F1.filter (fun τ => ((2 : Fin 4) ∈ τ)) = {{0, 0, 2}, {1, 1, 2}, {0, 2, 2}, {1, 2, 2}}
        by decide]
      rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w9, w10, w11, w12]
      fin_cases i <;> simp +decide <;> linarith
  · obtain ⟨hz, hD, hpos⟩ := h23 (by decide)
    simp at hz hD
    obtain ⟨x, y, z, w, hx, hy, hz', hw, e1, e2, e3⟩ :=
      cone_two (d 3) (d 0) (d 1) (hd 3) (hd 0) (hd 1) hpos hD
    refine ⟨fun τ => if τ = {0, 3, 3} then x else if τ = {1, 3, 3} then y else
      if τ = {0, 0, 3} then z else if τ = {1, 1, 3} then w else 0, fun τ => ?_, ?_⟩
    · dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> first | assumption | exact le_rfl
    · rw [show F1.filter (fun τ => ((3 : Fin 4) ∈ τ)) = {{0, 0, 3}, {1, 1, 3}, {0, 3, 3}, {1, 3, 3}}
        by decide]
      rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w13, w14, w15, w16]
      fin_cases i <;> simp +decide <;> linarith

end NashWilliams18

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Claim 14.7.2 for `F₁`.** An integrally `F₁`-divisible `ε`-balanced `ε`-nearly-complete
`F₁`-blowup (`ε ≤ 1/100`, `n > 0`) is fractionally `F₁`-divisible. -/
lemma isFracDiv_F1 {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (hn : 0 < Fintype.card V) (h : IsIdealizedT F1 ε G p)
    (hint : IsIntDiv p F1 G.edgeFinset) : IsFracDiv p F1 G.edgeFinset := by
  refine ⟨fracDiv_edge_F1 hε0 hε h hint, fun v => ?_⟩
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn' : (0 : ℝ) < n := by rw [hndef]; exact_mod_cast hn
  set d : Fin 4 → ℝ := fun i => (degT G p v i : ℝ) with hd
  have hdv : (fun i => (degVec p G.edgeFinset v i : ℝ)) = d := by
    funext i; rw [hd, degVec_eq_degT]; rfl
  rw [hdv]
  have hlo : ∀ j, AllowedT F1 (p v) j → (1 - 5 * ε) * n / 4 ≤ d j := by
    intro j hj
    have h1 := h.2.2 v j hj
    have h2 := h.lo j
    simp only [hd]; rw [← hndef] at h1 h2; linarith
  have hup : ∀ j, d j ≤ (1 + 3 * ε) * n / 4 := by
    intro j
    have h1 : (degT G p v j : ℝ) ≤ (clsT p j).card := by exact_mod_cast degT_le_class G p v j
    have h2 := card_clsT_le_four p h.lo j
    simp only [hd]; rw [← hndef] at h2; linarith
  have hzero : ∀ j, ¬ AllowedT F1 (p v) j → d j = 0 := by
    intro j hj
    simp only [hd]; rw [degT_eq_zero_of_not_allowed h.2.1 hj]; simp
  have hnn : ∀ j, 0 ≤ d j := fun j => by simp only [hd]; positivity
  have hεn : ε * n ≤ n / 100 := by nlinarith
  refine vertex_cone_F1 d (p v) hnn (fun ha => ⟨?_, ?_, ?_⟩) (fun ha => ⟨?_, ?_, ?_⟩)
  · apply hzero; rw [allowedT_F1_iff]
    rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) (p v) with h' | h' | h' | h' <;>
      rw [h'] at ha ⊢ <;> simp at ha ⊢
  · have h2 := hlo 2 (by rw [allowedT_F1_iff]; omega)
    have h3 := hlo 3 (by rw [allowedT_F1_iff]; omega)
    have := hup (p v)
    linarith
  · have h2 := hlo 2 (by rw [allowedT_F1_iff]; omega)
    have h3 := hlo 3 (by rw [allowedT_F1_iff]; omega)
    linarith
  · apply hzero; rw [allowedT_F1_iff]
    rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) (p v) with h' | h' | h' | h' <;>
      rw [h'] at ha ⊢ <;> simp at ha ⊢
  · have h2 := hlo 0 (by rw [allowedT_F1_iff]; omega)
    have h3 := hlo 1 (by rw [allowedT_F1_iff]; omega)
    have := hup (p v)
    linarith
  · have h2 := hlo 0 (by rw [allowedT_F1_iff]; omega)
    have h3 := hlo 1 (by rw [allowedT_F1_iff]; omega)
    linarith

/-- **Theorem 14.7 for `F₁` as a proposition** (open premise of branch (3), Theorem 12.6): there
are `ε > 0` and `n₀` such that every integrally `F₁`-divisible `ε`-balanced `ε`-nearly-complete
`F₁`-blowup (`IsIdealizedT`) on `n ≥ n₀` vertices has an `F₁`-decomposition.  In its hosts
every allowed pair of classes (including each class with itself) is near-complete, so the
sub-block parity construction recorded against the arbitrary-host interface does not apply to
them.  It is
implied by `Theorem1316Statement` (`theorem_14_7_F1`).  It is proved unconditionally (without
`Theorem1316Statement`) by `theorem_14_7_F1_of_vortex` in `Case126/VortexF1.lean`. -/
def Theorem147F1Statement : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
    IsIntDiv p F1 G.edgeFinset → IsIdealizedT F1 ε G p → HasDecomp p F1 G.edgeFinset

/-- **Theorem 14.7 for `F₁`** (from Theorem 13.16). -/
theorem theorem_14_7_F1 (h1316 : Theorem1316Statement) : Theorem147F1Statement := by
  obtain ⟨ε, hε, n₀, h⟩ := theorem_14_7_of_fracDiv h1316 F1 F1_card_three' twoThirds_F1
  refine ⟨min ε (1 / 100), lt_min hε (by norm_num), max n₀ 1, fun V _ _ p G _ hn hint hid => ?_⟩
  have hid' : IsIdealizedT F1 ε G p := by
    refine ⟨fun i => le_trans ?_ (hid.1 i), hid.2.1, fun v j hj => le_trans ?_ (hid.2.2 v j hj)⟩
    · have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have := min_le_left ε (1 / 100)
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    · have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have := min_le_left ε (1 / 100)
      nlinarith
  exact h V p G (le_trans (le_max_left _ _) hn)
    (isFracDiv_F1 (le_min hε.le (by norm_num)) (min_le_right _ _)
      (lt_of_lt_of_le (by omega) hn) hid hint) hint hid'

end NashWilliams18
