/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Discharging

@[expose] public section

/-!
# The key lemma: every negative edge ends with nonnegative charge

This combines Proposition 4.15 (linear approximation), Lemma 4.21 (cleaning), the value lemma
(Lemma 4.29) and the triangle-thin lemma (Lemma 4.31) as in the proof of Conjecture 4.22.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

omit [DecidableEq V] in
lemma dem_le_Dtot {a b x : V} (hax : G.Adj a x) (hbx : G.Adj b x) :
    dem φ a b x ≤ Dtot G φ a b := by
  have hx : x ∈ cn G a b := (mem_cn G).2 ⟨hax, hbx⟩
  have := single_le_sum (f := fun y => dem φ a b y + dem φ b a y)
    (fun y _ => add_nonneg (dem_nonneg φ a b y) (dem_nonneg φ b a y)) hx
  have := dem_nonneg φ b a x
  unfold Dtot; linarith

omit [DecidableEq V] in
/-- Proposition 4.15 (linear approximation lower bound), for one transfer. -/
lemma trans_lb {n : ℝ} (hn : 0 < n) {a b x : V} (hab : G.Adj a b) (hax : G.Adj a x)
    (hbx : G.Adj b x) :
    4 / n * dem φ a b x - 4 / n ^ 2 * (dem φ a b x * Dtot G φ a b / φ s(a, b)) ≤
      trans G φ a b x := by
  unfold trans
  rw [if_pos ⟨hab, hax, hbx⟩]
  set d := dem φ a b x with hd
  set D := Dtot G φ a b with hD
  set p := φ s(a, b) with hp
  rcases le_or_gt p 0 with h | h
  · have : d = 0 := dem_eq_zero_of_nonpos φ h
    rw [this]; simp
  have hd0 : 0 ≤ d := dem_nonneg φ a b x
  rcases hd0.lt_or_eq with hd0 | hd0
  · have hdD : d ≤ D := dem_le_Dtot G φ hax hbx
    have hD0 : 0 < D := lt_of_lt_of_le hd0 hdD
    have key : p * d / D - (4 / n * d - 4 / n ^ 2 * (d * D / p)) =
        d * (n * p - 2 * D) ^ 2 / (n ^ 2 * p * D) := by
      field_simp; ring
    have : 0 ≤ d * (n * p - 2 * D) ^ 2 / (n ^ 2 * p * D) := by positivity
    linarith
  · rw [← hd0]; simp

omit [DecidableEq V] in
/-- Proposition 4.19 / Definition 4.20: rewriting the normalized demands. -/
lemma dem_mul_Dtot_div (a b x : V) :
    dem φ a b x * Dtot G φ a b / φ s(a, b) =
      ∑ y ∈ cn G a b, dem φ a b x * normT (φ s(a, b)) (φ s(a, y)) (φ s(b, y)) := by
  unfold Dtot
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun y _ => ?_
  unfold normT dem
  rw [show s(b, a) = s(a, b) from Sym2.eq_swap]
  ring

/-- Number of neighbours of `a` that are not neighbours of `b`. -/
lemma card_nbr_diff (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (a b : V) :
    ((univ.filter fun y => G.Adj a y ∧ ¬G.Adj b y).card : ℝ) * 4 ≤ Fintype.card V := by
  have hsub : (univ.filter fun y => G.Adj a y ∧ ¬G.Adj b y) ⊆ univ \ G.neighborFinset b := by
    intro y hy; simp only [mem_filter, mem_univ, true_and] at hy
    simp [hy.2]
  have h1 := card_le_card hsub
  rw [card_sdiff_of_subset (subset_univ _), card_univ, G.card_neighborFinset_eq_degree] at h1
  have h2 := G.minDegree_le_degree b
  have h3 : G.degree b ≤ Fintype.card V := by
    rw [← G.card_neighborFinset_eq_degree]; exact card_le_univ _
  have : (univ.filter fun y => G.Adj a y ∧ ¬G.Adj b y).card * 4 ≤ Fintype.card V := by omega
  exact_mod_cast this

/-- The part of the cleaning bound coming from vertices outside the common neighbourhood
(Lemma 4.21). -/
lemma outer_bound (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hφ : GoodWeighting G φ)
    {a b w : V} (haw : G.Adj a w) :
    ∑ y ∈ (cn G a w).filter (fun y => y ∉ cn G a b),
        dem φ a w b * normT (φ s(a, w)) (φ s(a, y)) (φ s(w, y)) ≤
      dem φ a w b * (Fintype.card V / 4) := by
  have hd := dem_nonneg φ a w b
  calc ∑ y ∈ (cn G a w).filter (fun y => y ∉ cn G a b),
        dem φ a w b * normT (φ s(a, w)) (φ s(a, y)) (φ s(w, y))
      ≤ ∑ y ∈ (cn G a w).filter (fun y => y ∉ cn G a b), dem φ a w b := by
        refine sum_le_sum fun y hy => ?_
        simp only [mem_filter, mem_cn] at hy
        exact mul_le_of_le_one_right hd
          (normT_le_one _ _ _ (hφ.cov a w y haw hy.1.1 hy.1.2))
    _ = ((cn G a w).filter (fun y => y ∉ cn G a b)).card * dem φ a w b := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((univ.filter fun y => G.Adj a y ∧ ¬G.Adj b y).card : ℝ) * dem φ a w b := by
        refine mul_le_mul_of_nonneg_right ?_ hd
        exact_mod_cast card_le_card (fun y hy => by
          simp only [mem_filter, mem_cn, mem_univ, true_and, not_and] at hy ⊢
          exact ⟨hy.1.1, hy.2 hy.1.1⟩)
    _ ≤ dem φ a w b * (Fintype.card V / 4) := by
        have := card_nbr_diff G hδ a b
        nlinarith

lemma card_cn_ge (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (u v : V) :
    (Fintype.card V : ℝ) ≤ 2 * (cn G u v).card := by
  have e : cn G u v = G.neighborFinset u ∩ G.neighborFinset v := by
    ext x; simp [cn]
  have h1 := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h2 : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V := card_le_univ _
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h1
  have h3 := G.minDegree_le_degree u
  have h4 := G.minDegree_le_degree v
  rw [e]
  have : Fintype.card V ≤ 2 * (G.neighborFinset u ∩ G.neighborFinset v).card := by omega
  exact_mod_cast this

omit [DecidableEq V] in
lemma card_cn_le (u v : V) : ((cn G u v).card : ℝ) ≤ Fintype.card V := by
  exact_mod_cast card_le_univ _

/-! ### The value part (Section 4.5) -/

/-- The contribution `Val` of the ordered pair `(w, y)` to the value of the edge `wy`
with respect to the negative edge `uv`. -/
noncomputable def valW (u v w y : V) : ℝ :=
  vterm (φ s(u, v)) (φ s(u, w)) (φ s(v, w)) (φ s(u, y)) (φ s(w, y)) +
    vterm (φ s(u, v)) (φ s(v, w)) (φ s(u, w)) (φ s(v, y)) (φ s(w, y))

/-- The value `Val_f(wy)` of the edge `wy` with respect to `f = uv`. -/
noncomputable def VE (u v w y : V) : ℝ :=
  ValE (φ s(u, v)) (φ s(u, w)) (φ s(v, w)) (φ s(u, y)) (φ s(v, y)) (φ s(w, y))

omit [Fintype V] [DecidableEq V] in
lemma VE_eq (u v w y : V) : VE φ u v w y = valW φ u v w y + valW φ u v y w := by
  unfold VE valW ValE; rw [show s(y, w) = s(w, y) from Sym2.eq_swap]; ring

omit [Fintype V] [DecidableEq V] in
lemma VE_comm (u v w y : V) : VE φ u v w y = VE φ u v y w := by
  rw [VE_eq, VE_eq]; ring

/-- The rescaled value weighting on the common neighbourhood. -/
noncomputable def aW (u v w y : V) : ℝ :=
  if w ∈ cn G u v ∧ y ∈ cn G u v ∧ G.Adj w y then VE φ u v w y / (2 * -φ s(u, v)) else 0

omit [Fintype V] [DecidableEq V] in
lemma ne_sym2 {a b c : V} (hab : a ≠ b) : s(a, c) ≠ s(b, c) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hab h1
  · exact hab (h1.trans h2)

omit [DecidableEq V] in
/-- The hypotheses of the local lemma hold for every triangle in the common neighbourhood. -/
lemma mkLH (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    {w x y : V} (hw : w ∈ cn G u v) (hx : x ∈ cn G u v) (hy : y ∈ cn G u v)
    (hwx : G.Adj w x) (hwy : G.Adj w y) (hxy : G.Adj x y) :
    LH (φ s(u, v)) (φ s(u, w)) (φ s(v, w)) (φ s(u, x)) (φ s(v, x)) (φ s(u, y)) (φ s(v, y))
      (φ s(w, x)) (φ s(w, y)) (φ s(x, y)) := by
  rw [mem_cn] at hw hx hy
  have n1 := huv.ne; have n2 := hw.1.ne; have n3 := hw.2.ne; have n4 := hx.1.ne
  have n5 := hx.2.ne; have n6 := hy.1.ne; have n7 := hy.2.ne; have n8 := hwx.ne
  have n9 := hwy.ne; have n10 := hxy.ne
  refine ⟨hneg, ?_, ⟨hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _,
    hφ.nz _⟩, hφ.cov u v w huv hw.1 hw.2, hφ.cov u v x huv hx.1 hx.2,
    hφ.cov u v y huv hy.1 hy.2, hφ.cov u w x hw.1 hx.1 hwx, hφ.cov u w y hw.1 hy.1 hwy,
    hφ.cov u x y hx.1 hy.1 hxy, hφ.cov v w x hw.2 hx.2 hwx, hφ.cov v w y hw.2 hy.2 hwy,
    hφ.cov v x y hx.2 hy.2 hxy, hφ.cov w x y hwx hwy hxy⟩
  have hE : [s(u, v), s(u, w), s(v, w), s(u, x), s(v, x), s(u, y), s(v, y), s(w, x), s(w, y),
      s(x, y)].Nodup := by
    simp [List.nodup_cons, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n1.symm,
      n2.symm, n3.symm, n4.symm, n5.symm, n7.symm, n8.symm, n9.symm, n10.symm]
  exact hE.map hφ.inj

omit [DecidableEq V] in
lemma VE_le (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    {w y : V} (hw : w ∈ cn G u v) (hy : y ∈ cn G u v) (hwy : G.Adj w y) :
    VE φ u v w y ≤ -2 * φ s(u, v) := by
  rw [mem_cn] at hw hy
  exact ValE_le hneg (hφ.nz _) (hφ.nz _) (hφ.inj.ne (ne_sym2 huv.ne)) (hφ.nz _) (hφ.nz _)
    (hφ.inj.ne (ne_sym2 huv.ne)) (hφ.cov u v w huv hw.1 hw.2) (hφ.cov u v y huv hy.1 hy.2)
    (hφ.cov u w y hw.1 hy.1 hwy) (hφ.cov v w y hw.2 hy.2 hwy)

lemma aW_le_one (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    (w y : V) : aW G φ u v w y ≤ 1 := by
  unfold aW
  split_ifs with h
  · rw [div_le_one (by linarith)]
    have := VE_le G φ hφ huv hneg h.1 h.2.1 h.2.2
    linarith
  · exact zero_le_one

lemma aW_nonneg {u v : V} (hneg : φ s(u, v) < 0) (w y : V) : 0 ≤ aW G φ u v w y := by
  unfold aW
  split_ifs
  · exact div_nonneg (ValE_nonneg _ _ _ _ _ _) (by linarith)
  · exact le_rfl

lemma aW_symm (u v w y : V) : aW G φ u v w y = aW G φ u v y w := by
  unfold aW
  rw [VE_comm φ u v w y]
  by_cases h : w ∈ cn G u v ∧ y ∈ cn G u v ∧ G.Adj w y
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]

lemma VE_pos_of_aW_pos {u v w y : V} (hneg : φ s(u, v) < 0) (h : 0 < aW G φ u v w y) :
    w ∈ cn G u v ∧ y ∈ cn G u v ∧ G.Adj w y ∧ 0 < VE φ u v w y := by
  unfold aW at h
  split_ifs at h with hc
  · refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
    have h2 : 0 < 2 * -φ s(u, v) := by linarith
    exact (div_pos_iff_of_pos_right h2).1 h
  · exact absurd h (lt_irrefl 0)

/-- Proposition 4.25 (the filtered common neighbourhood graph is `K₅`-free), in the form needed
for the value lemma. -/
lemma clique_le_four (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v)
    (hneg : φ s(u, v) < 0) (T : Finset V) (hTC : T ⊆ cn G u v)
    (hT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 0 < aW G φ u v i j) : T.card ≤ 4 := by
  have pos : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → G.Adj i j ∧ 0 < VE φ u v i j := fun i hi j hj hij =>
    let h := VE_pos_of_aW_pos G φ hneg (hT i hi j hj hij); ⟨h.2.2.1, h.2.2.2⟩
  have zero : ∀ i ∈ T, ∀ j ∈ T,
      (φ s(u, i) ≤ 0 ∨ (0 ≤ φ s(u, j) ∧ 0 ≤ φ s(i, j))) →
      (φ s(v, i) ≤ 0 ∨ (0 ≤ φ s(v, j) ∧ 0 ≤ φ s(i, j))) →
      (φ s(u, j) ≤ 0 ∨ (0 ≤ φ s(u, i) ∧ 0 ≤ φ s(i, j))) →
      (φ s(v, j) ≤ 0 ∨ (0 ≤ φ s(v, i) ∧ 0 ≤ φ s(i, j))) → VE φ u v i j = 0 :=
    fun i _ j _ h1 h2 h3 h4 => ValE_eq_zero h1 h2 h3 h4
  set TP := T.filter (fun i => 0 < φ s(u, i) ∧ φ s(v, i) < 0)
  set TM := T.filter (fun i => φ s(u, i) < 0 ∧ 0 < φ s(v, i))
  set TB := T.filter (fun i => 0 < φ s(u, i) ∧ 0 < φ s(v, i))
  have hP : TP.card ≤ 1 := by
    refine card_le_one.2 fun i hi j hj => ?_
    by_contra hij
    simp only [TP, mem_filter] at hi hj
    obtain ⟨hadj, hpos⟩ := pos i hi.1 j hj.1 hij
    have hiC := (mem_cn G).1 (hTC hi.1)
    have hjC := (mem_cn G).1 (hTC hj.1)
    have := hφ.cov v i j hiC.2 hjC.2 hadj
    have := zero i hi.1 j hj.1 (Or.inr ⟨by linarith, by linarith⟩) (Or.inl hi.2.2.le)
      (Or.inr ⟨by linarith, by linarith⟩) (Or.inl hj.2.2.le)
    linarith
  have hM : TM.card ≤ 1 := by
    refine card_le_one.2 fun i hi j hj => ?_
    by_contra hij
    simp only [TM, mem_filter] at hi hj
    obtain ⟨hadj, hpos⟩ := pos i hi.1 j hj.1 hij
    have hiC := (mem_cn G).1 (hTC hi.1)
    have hjC := (mem_cn G).1 (hTC hj.1)
    have := hφ.cov u i j hiC.1 hjC.1 hadj
    have := zero i hi.1 j hj.1 (Or.inl hi.2.1.le) (Or.inr ⟨by linarith, by linarith⟩)
      (Or.inl hj.2.1.le) (Or.inr ⟨by linarith, by linarith⟩)
    linarith
  have negB : ∀ i ∈ TB, ∀ j ∈ TB, i ≠ j → G.Adj i j ∧ φ s(i, j) < 0 := by
    intro i hi j hj hij
    simp only [TB, mem_filter] at hi hj
    obtain ⟨hadj, hpos⟩ := pos i hi.1 j hj.1 hij
    refine ⟨hadj, ?_⟩
    by_contra hq
    push_neg at hq
    have := zero i hi.1 j hj.1 (Or.inr ⟨hj.2.1.le, hq⟩) (Or.inr ⟨hj.2.2.le, hq⟩)
      (Or.inr ⟨hi.2.1.le, hq⟩) (Or.inr ⟨hi.2.2.le, hq⟩)
    linarith
  have hB : TB.card ≤ 2 := by
    by_contra hc
    push_neg at hc
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := two_lt_card_iff.1 hc
    obtain ⟨a1, q1⟩ := negB i hi j hj hij
    obtain ⟨a2, q2⟩ := negB i hi k hk hik
    obtain ⟨a3, q3⟩ := negB j hj k hk hjk
    have := hφ.cov i j k a1 a2 a3
    linarith
  have hsub : T ⊆ TP ∪ TM ∪ TB := by
    intro i hi
    have hiC := (mem_cn G).1 (hTC hi)
    rcases type_cases hneg (hφ.cov u v i huv hiC.1 hiC.2) (hφ.nz _) (hφ.nz _) with h | h | h
    · simp [TP, hi, h]
    · simp [TM, hi, h]
    · simp [TB, hi, h]
  calc T.card ≤ (TP ∪ TM ∪ TB).card := card_le_card hsub
    _ ≤ (TP ∪ TM).card + TB.card := card_union_le _ _
    _ ≤ TP.card + TM.card + TB.card := by
        have := card_union_le TP TM; omega
    _ ≤ 4 := by omega

lemma thin_aW (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0) :
    ThinWeights (cn G u v) (aW G φ u v) where
  symm := aW_symm G φ u v
  diag := fun i => by unfold aW; rw [if_neg (fun h => G.irrefl h.2.2)]
  nonneg := aW_nonneg G φ hneg
  le_one := aW_le_one G φ hφ huv hneg
  thin := by
    intro i hi j hj k hk hij hik hjk
    have b1 := aW_le_one G φ hφ huv hneg i j
    have b2 := aW_le_one G φ hφ huv hneg i k
    have b3 := aW_le_one G φ hφ huv hneg j k
    by_cases h1 : G.Adj i j
    · by_cases h2 : G.Adj i k
      · by_cases h3 : G.Adj j k
        · have hL := local_bound (mkLH G φ hφ huv hneg hi hj hk h1 h2 h3)
          unfold aW
          rw [if_pos ⟨hi, hj, h1⟩, if_pos ⟨hi, hk, h2⟩, if_pos ⟨hj, hk, h3⟩]
          unfold VE
          unfold ValT at hL
          rw [← add_div, ← add_div, div_le_iff₀ (by linarith)]
          linarith
        · have : aW G φ u v j k = 0 := by unfold aW; rw [if_neg (fun h => h3 h.2.2)]
          linarith
      · have : aW G φ u v i k = 0 := by unfold aW; rw [if_neg (fun h => h2 h.2.2)]
        linarith
    · have : aW G φ u v i j = 0 := by unfold aW; rw [if_neg (fun h => h1 h.2.2)]
      linarith
  clique := clique_le_four G φ hφ huv hneg

/-- The bound on `ch''_F(f)` (proof of Conjecture 4.22 from Lemmas 4.29 and 4.31). -/
lemma inner_value_bound (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v)
    (hneg : φ s(u, v) < 0) :
    ∑ w ∈ cn G u v, ∑ y ∈ cn G u v, (if G.Adj w y then valW φ u v w y else 0) ≤
      (-φ s(u, v)) * ((cn G u v).card : ℝ) ^ 2 / 2 := by
  set C := cn G u v
  set F := -φ s(u, v) with hF
  have hF0 : 0 < F := by linarith
  have hv := value_lemma C (aW G φ u v) (thin_aW G φ hφ huv hneg) (fun _ => 1)
    (fun _ => zero_le_one)
  simp only [quadF, mul_one, sum_const, nsmul_eq_mul] at hv
  set X := ∑ w ∈ C, ∑ y ∈ C, (if G.Adj w y then valW φ u v w y else 0)
  have hY : ∑ w ∈ C, ∑ y ∈ C, (if G.Adj w y then valW φ u v y w else 0) = X := by
    rw [sum_comm]
    refine sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_
    by_cases h : G.Adj y w
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hA : ∑ w ∈ C, ∑ y ∈ C, aW G φ u v w y = (X + ∑ w ∈ C, ∑ y ∈ C,
      (if G.Adj w y then valW φ u v y w else 0)) / (2 * F) := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun w hw => ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun y hy => ?_
    unfold aW
    by_cases h : G.Adj w y
    · rw [if_pos ⟨hw, hy, h⟩, VE_eq]; simp only [h, if_true, hF]
    · rw [if_neg (fun h' => h h'.2.2)]; simp [h]
  rw [hA, hY] at hv
  rw [div_le_iff₀ (by linarith)] at hv
  nlinarith

omit [DecidableEq V] in
lemma dem_pair_sum (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v)
    (hneg : φ s(u, v) < 0) {w : V} (hw : w ∈ cn G u v) :
    dem φ u w v + dem φ v w u = -φ s(u, v) := by
  rw [mem_cn] at hw
  unfold dem
  rw [show s(w, v) = s(v, w) from Sym2.eq_swap, show s(v, u) = s(u, v) from Sym2.eq_swap,
    show s(w, u) = s(u, w) from Sym2.eq_swap]
  exact demF_pair hneg (hφ.nz _) (hφ.nz _) (hφ.inj.ne (ne_sym2 huv.ne))
    (hφ.cov u v w huv hw.1 hw.2)

/-- The cleaning bound of Lemma 4.21 for one side. -/
lemma side_bound (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hφ : GoodWeighting G φ)
    {u v w : V} (hw : w ∈ cn G u v) :
    dem φ u w v * Dtot G φ u w / φ s(u, w) ≤
      ∑ y ∈ cn G u v, (if G.Adj w y then
        dem φ u w v * normT (φ s(u, w)) (φ s(u, y)) (φ s(w, y)) else 0) +
      dem φ u w v * (Fintype.card V / 4) := by
  have huw := ((mem_cn G).1 hw).1
  rw [dem_mul_Dtot_div, ← sum_filter_add_sum_filter_not (cn G u w) (fun y => y ∈ cn G u v)]
  have hset : (cn G u w).filter (fun y => y ∈ cn G u v) = (cn G u v).filter (G.Adj w) := by
    ext y; simp only [mem_filter, mem_cn]; tauto
  rw [hset, ← sum_filter]
  have := outer_bound G φ hδ hφ (b := v) huw
  linarith

/-- Per-vertex form of Proposition 4.15 and Lemma 4.21. -/
lemma per_w (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hφ : GoodWeighting G φ)
    {n : ℝ} (hn : 0 < n) (hnV : n = Fintype.card V) {u v : V} (huv : G.Adj u v)
    {w : V} (hw : w ∈ cn G u v) :
    4 / n * (dem φ u w v + dem φ v w u) - 4 / n ^ 2 * ((dem φ u w v + dem φ v w u) * (n / 4) +
      ∑ y ∈ cn G u v, (if G.Adj w y then valW φ u v w y else 0)) ≤
      trans G φ u w v + trans G φ v w u := by
  have hw' := (mem_cn G).1 hw
  have t1 := trans_lb G φ hn hw'.1 huv hw'.2.symm
  have t2 := trans_lb G φ hn hw'.2 huv.symm hw'.1.symm
  have s1 := side_bound G φ hδ hφ hw
  have s2 := side_bound G φ hδ hφ (u := v) (v := u) (by rw [cn_comm]; exact hw)
  rw [cn_comm G v u, ← hnV] at s2
  rw [← hnV] at s1
  have hsplit : ∑ y ∈ cn G u v, (if G.Adj w y then valW φ u v w y else 0) =
      ∑ y ∈ cn G u v, (if G.Adj w y then
        dem φ u w v * normT (φ s(u, w)) (φ s(u, y)) (φ s(w, y)) else 0) +
      ∑ y ∈ cn G u v, (if G.Adj w y then
        dem φ v w u * normT (φ s(v, w)) (φ s(v, y)) (φ s(w, y)) else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    split_ifs
    · unfold valW vterm dem
      rw [show s(w, v) = s(v, w) from Sym2.eq_swap, show s(v, u) = s(u, v) from Sym2.eq_swap,
        show s(w, u) = s(u, w) from Sym2.eq_swap]
    · simp
  have hc : (0 : ℝ) ≤ 4 / n ^ 2 := by positivity
  have m1 := mul_le_mul_of_nonneg_left s1 hc
  have m2 := mul_le_mul_of_nonneg_left s2 hc
  rw [hsplit]
  nlinarith

/-- **Key lemma**: every negative edge ends with nonnegative charge. -/
lemma neg_le_sum_trans (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hφ : GoodWeighting G φ)
    {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0) :
    -φ s(u, v) ≤ ∑ w, (trans G φ u w v + trans G φ v w u) := by
  set n : ℝ := (Fintype.card V : ℝ) with hnV
  have hn : 0 < n := by
    rw [hnV]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  set C := cn G u v with hC
  set F := -φ s(u, v) with hF
  have hF0 : 0 < F := by linarith
  have hsub : ∑ w, (trans G φ u w v + trans G φ v w u) =
      ∑ w ∈ C, (trans G φ u w v + trans G φ v w u) := by
    refine (sum_subset (subset_univ C) fun w _ hw => ?_).symm
    rw [hC, mem_cn] at hw
    unfold trans
    rw [if_neg (fun h => hw ⟨h.1, h.2.2.symm⟩), if_neg (fun h => hw ⟨h.2.2.symm, h.1⟩)]
    ring
  rw [hsub]
  have hsum := sum_le_sum fun w (hw : w ∈ C) => per_w G φ hδ hφ hn hnV huv hw
  have hp : ∀ w ∈ C, dem φ u w v + dem φ v w u = F := fun w hw =>
    dem_pair_sum G φ hφ huv hneg hw
  rw [sum_congr rfl fun w hw => by rw [hp w hw]] at hsum
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul,
    ← sum_mul, sum_const, nsmul_eq_mul] at hsum
  have hI := inner_value_bound G φ hφ huv hneg
  have hc1 := card_cn_ge G hδ u v
  have hc2 := card_cn_le G u v
  rw [← hC, ← hnV] at hc1 hc2
  rw [← hC] at hI
  set c : ℝ := (C.card : ℝ)
  set I := ∑ w ∈ C, ∑ y ∈ C, (if G.Adj w y then valW φ u v w y else 0)
  have hfin : F ≤ 4 / n * (c * F) - 4 / n ^ 2 * (c * F * (n / 4) + F * c ^ 2 / 2) := by
    have e : 4 / n * (c * F) - 4 / n ^ 2 * (c * F * (n / 4) + F * c ^ 2 / 2) - F =
        F * (2 * c - n) * (n - c) / n ^ 2 := by
      field_simp; ring
    have : 0 ≤ F * (2 * c - n) * (n - c) / n ^ 2 := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg hF0.le (by linarith)) (by linarith)
    linarith
  have hc : (0 : ℝ) ≤ 4 / n ^ 2 := by positivity
  have m := mul_le_mul_of_nonneg_left hI hc
  nlinarith

end NashWilliams.Frac
