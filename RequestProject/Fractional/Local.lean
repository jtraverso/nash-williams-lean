/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.Fractional.Demand

/-!
# Local configurations on five vertices

We fix a negative edge `f = uv` and three common neighbours `w, x, y` of `u` and `v` forming a
triangle.  All quantities below are expressed in terms of the ten edge weights of the `K₅` on
`u, v, w, x, y`:

* `f = φ(uv)`,
* `aw = φ(uw)`, `bw = φ(vw)` (and similarly for `x`, `y`),
* `qwx = φ(wx)`, `qwy = φ(wy)`, `qxy = φ(xy)`.

`ValE f aw bw ax bx q` is the value `Val_f(wx)` of the edge `wx` (Definition 4.23) and
`ValT` is the value of the triangle `wxy` (Definition 4.30).
-/

namespace NashWilliams.Frac

/-- `dem_f(e, T)` for `e` of weight `pe`, where the triangle `e ∪ f` has third edge `po`
and the triangle `T` has the two further edges `p1, p2`. -/
noncomputable def vterm (f pe po p1 p2 : ℝ) : ℝ := demF pe f po * normT pe p1 p2

/-- The value `Val_f(wx)` of an edge `wx` in the common neighbourhood of the ends of `f`. -/
noncomputable def ValE (f aw bw ax bx q : ℝ) : ℝ :=
  vterm f aw bw ax q + vterm f bw aw bx q + vterm f ax bx aw q + vterm f bx ax bw q

/-- The value `Val_f(T)` of a triangle `T = wxy`. -/
noncomputable def ValT (f aw bw ax bx ay b_y qwx qwy qxy : ℝ) : ℝ :=
  ValE f aw bw ax bx qwx + ValE f aw bw ay b_y qwy + ValE f ax bx ay b_y qxy

/-- Hypotheses on the ten weights: `φ` is nonzero, untied and triangle-covered on the `K₅`,
and `f` is negative. -/
structure LH (f aw bw ax bx ay b_y qwx qwy qxy : ℝ) : Prop where
  hf : f < 0
  nd : [f, aw, bw, ax, bx, ay, b_y, qwx, qwy, qxy].Nodup
  nz : aw ≠ 0 ∧ bw ≠ 0 ∧ ax ≠ 0 ∧ bx ≠ 0 ∧ ay ≠ 0 ∧ b_y ≠ 0 ∧ qwx ≠ 0 ∧ qwy ≠ 0 ∧ qxy ≠ 0
  cw : 0 ≤ f + aw + bw
  cx : 0 ≤ f + ax + bx
  cy : 0 ≤ f + ay + b_y
  cuwx : 0 ≤ aw + ax + qwx
  cuwy : 0 ≤ aw + ay + qwy
  cuxy : 0 ≤ ax + ay + qxy
  cvwx : 0 ≤ bw + bx + qwx
  cvwy : 0 ≤ bw + b_y + qwy
  cvxy : 0 ≤ bx + b_y + qxy
  cwxy : 0 ≤ qwx + qwy + qxy

lemma vterm_nonneg (f pe po p1 p2 : ℝ) : 0 ≤ vterm f pe po p1 p2 :=
  mul_nonneg (demF_nonneg _ _ _) (normT_nonneg _ _ _)

lemma vterm_le (f pe po p1 p2 : ℝ) (hc : 0 ≤ pe + p1 + p2) :
    vterm f pe po p1 p2 ≤ demF pe f po :=
  mul_le_of_le_one_right (demF_nonneg _ _ _) (normT_le_one _ _ _ hc)

lemma ValE_nonneg (f aw bw ax bx q : ℝ) : 0 ≤ ValE f aw bw ax bx q := by
  unfold ValE
  have := vterm_nonneg f aw bw ax q
  have := vterm_nonneg f bw aw bx q
  have := vterm_nonneg f ax bx aw q
  have := vterm_nonneg f bx ax bw q
  linarith

/-- Proposition 4.27: `Val_f(g) ≤ 2 |φ(f)|`. -/
lemma ValE_le {f aw bw ax bx q : ℝ} (hf : f < 0) (haw : aw ≠ 0) (hbw : bw ≠ 0) (hw : aw ≠ bw)
    (hax : ax ≠ 0) (hbx : bx ≠ 0) (hx : ax ≠ bx) (cw : 0 ≤ f + aw + bw) (cx : 0 ≤ f + ax + bx)
    (cu : 0 ≤ aw + ax + q) (cv : 0 ≤ bw + bx + q) : ValE f aw bw ax bx q ≤ -2 * f := by
  unfold ValE
  have h1 := vterm_le f aw bw ax q cu
  have h2 := vterm_le f bw aw bx q cv
  have h3 := vterm_le f ax bx aw q (by linarith)
  have h4 := vterm_le f bx ax bw q (by linarith)
  have p1 := demF_pair hf haw hbw hw cw
  have p2 := demF_pair hf hax hbx hx cx
  linarith

/-- Proposition 4.26 (a convenient general form): if each of the four contributions vanishes
because either its edge is not positive or the relevant triangle has no negative edge, then
the value is `0`. -/
lemma ValE_eq_zero {f aw bw ax bx q : ℝ}
    (h1 : aw ≤ 0 ∨ (0 ≤ ax ∧ 0 ≤ q)) (h2 : bw ≤ 0 ∨ (0 ≤ bx ∧ 0 ≤ q))
    (h3 : ax ≤ 0 ∨ (0 ≤ aw ∧ 0 ≤ q)) (h4 : bx ≤ 0 ∨ (0 ≤ bw ∧ 0 ≤ q)) :
    ValE f aw bw ax bx q = 0 := by
  have z : ∀ pe po p1 p2 : ℝ, (pe ≤ 0 ∨ (0 ≤ p1 ∧ 0 ≤ p2)) → vterm f pe po p1 p2 = 0 := by
    intro pe po p1 p2 h
    unfold vterm
    rcases h with h | ⟨h1, h2⟩
    · rw [demF_of_nonpos h]; simp
    · rw [normT_of_nonneg h1 h2]; simp
  unfold ValE
  rw [z _ _ _ _ h1, z _ _ _ _ h2, z _ _ _ _ h3, z _ _ _ _ h4]; simp

/-- Each common neighbour is of one of three types. -/
lemma type_cases {f a b : ℝ} (hf : f < 0) (c : 0 ≤ f + a + b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b) ∨ (0 < a ∧ 0 < b) := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · linarith
  · exact Or.inr (Or.inl ⟨ha, hb⟩)
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr (Or.inr ⟨ha, hb⟩)

lemma LH.ne_ab_w {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) : aw ≠ bw := by
  have := h.nd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil] at this; tauto

lemma LH.ne_ab_x {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) : ax ≠ bx := by
  have := h.nd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil] at this; tauto

lemma LH.ne_ab_y {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) : ay ≠ b_y := by
  have := h.nd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil] at this; tauto

lemma LH.ValE_wx_le {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) : ValE f aw bw ax bx qwx ≤ -2 * f := by
  obtain ⟨n1, n2, n3, n4, n5, n6, -, -, -⟩ := h.nz
  exact ValE_le h.hf n1 n2 h.ne_ab_w n3 n4 h.ne_ab_x h.cw h.cx h.cuwx h.cvwx

lemma LH.ValE_wy_le {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) : ValE f aw bw ay b_y qwy ≤ -2 * f := by
  obtain ⟨n1, n2, n3, n4, n5, n6, -, -, -⟩ := h.nz
  exact ValE_le h.hf n1 n2 h.ne_ab_w n5 n6 h.ne_ab_y h.cw h.cy h.cuwy h.cvwy

lemma LH.ValE_xy_le {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy) : ValE f ax bx ay b_y qxy ≤ -2 * f := by
  obtain ⟨n1, n2, n3, n4, n5, n6, -, -, -⟩ := h.nz
  exact ValE_le h.hf n3 n4 h.ne_ab_x n5 n6 h.ne_ab_y h.cx h.cy h.cuxy h.cvxy

/-- If one of the three edges of the triangle has value `0`, the triangle has value at most
`4 |φ(f)|`. -/
lemma LH.bound_of_zero {f aw bw ax bx ay b_y qwx qwy qxy : ℝ}
    (h : LH f aw bw ax bx ay b_y qwx qwy qxy)
    (hz : ValE f aw bw ax bx qwx = 0 ∨ ValE f aw bw ay b_y qwy = 0 ∨
      ValE f ax bx ay b_y qxy = 0) :
    ValT f aw bw ax bx ay b_y qwx qwy qxy ≤ -4 * f := by
  unfold ValT
  have := h.ValE_wx_le; have := h.ValE_wy_le; have := h.ValE_xy_le
  rcases hz with hz | hz | hz <;> linarith

end NashWilliams.Frac
