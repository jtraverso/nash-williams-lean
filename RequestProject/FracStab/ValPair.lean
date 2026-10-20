/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.Fractional.Local

/-!
# Value lemmas for a pair in the common neighbourhood (Lemmas 9.2 and 9.3)

Throughout, `f = φ(uv) < 0` and `x, y` are common neighbours of `u, v` with `xy` an edge;
`ax = φ(ux)`, `bx = φ(vx)`, `ay = φ(uy)`, `b_y = φ(vy)` and `q = φ(xy)`.  The value of `xy` with
respect to `f` is `ValE f ax bx ay b_y q`.  A common neighbour `x` is *`u`-obtuse* if `ax > 0 > bx`,
*`v`-obtuse* if `bx > 0 > ax`, and *acute* if `ax, bx > 0`.
-/

namespace NashWilliams.Frac

/-- Hypotheses: nonzero, untied and triangle-covered weights on `u, v, x, y`. -/
structure PairH (f ax bx ay b_y q : ℝ) : Prop where
  hf : f < 0
  nax : ax ≠ 0
  nbx : bx ≠ 0
  nay : ay ≠ 0
  nby : b_y ≠ 0
  nq : q ≠ 0
  cx : 0 ≤ f + ax + bx
  cy : 0 ≤ f + ay + b_y
  cuxy : 0 ≤ ax + ay + q
  cvxy : 0 ≤ bx + b_y + q
  dxy : ax ≠ ay
  dbxy : bx ≠ b_y
  dx : ax ≠ bx
  dy : ay ≠ b_y

lemma PairH.swap_xy {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) :
    PairH f ay b_y ax bx q :=
  ⟨H.hf, H.nay, H.nby, H.nax, H.nbx, H.nq, H.cy, H.cx, by linarith [H.cuxy],
    by linarith [H.cvxy], H.dxy.symm, H.dbxy.symm, H.dy, H.dx⟩

lemma PairH.swap_uv {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) :
    PairH f bx ax b_y ay q :=
  ⟨H.hf, H.nbx, H.nax, H.nby, H.nay, H.nq, by linarith [H.cx], by linarith [H.cy], H.cvxy,
    H.cuxy, H.dbxy, H.dxy, H.dx.symm, H.dy.symm⟩

lemma ValE_swap_xy (f ax bx ay b_y q : ℝ) : ValE f ax bx ay b_y q = ValE f ay b_y ax bx q := by
  unfold ValE; ring

lemma ValE_swap_uv (f ax bx ay b_y q : ℝ) : ValE f ax bx ay b_y q = ValE f bx ax b_y ay q := by
  unfold ValE; ring

lemma ValE_nonneg' (f ax bx ay b_y q : ℝ) : 0 ≤ ValE f ax bx ay b_y q := by
  unfold ValE
  linarith [vterm_nonneg f ax bx ay q, vterm_nonneg f bx ax b_y q, vterm_nonneg f ay b_y ax q,
    vterm_nonneg f b_y ay bx q]

/-- `vterm` vanishes on a nonpositive edge. -/
lemma vterm_of_nonpos {f pe po p1 p2 : ℝ} (h : pe ≤ 0) : vterm f pe po p1 p2 = 0 := by
  unfold vterm; rw [demF_of_nonpos h, zero_mul]

/-- `vterm` vanishes when both further edges are positive. -/
lemma vterm_of_pos {f pe po p1 p2 : ℝ} (h1 : 0 ≤ p1) (h2 : 0 ≤ p2) : vterm f pe po p1 p2 = 0 := by
  unfold vterm; rw [normT_of_nonneg h1 h2, mul_zero]

/-- `vterm` is at most the demand of `f`, in a covered triangle. -/
lemma vterm_le_dem {f pe po p1 p2 : ℝ} (hc : 0 ≤ pe + p1 + p2) :
    vterm f pe po p1 p2 ≤ demF pe f po := by
  unfold vterm
  have := normT_le_one pe p1 p2 hc
  have h0 := demF_nonneg pe f po
  nlinarith [normT_nonneg pe p1 p2]

/-- The demand of `f` on `ux` when `x` is `u`-obtuse is `|f|`. -/
lemma dem_uobt {f ax bx : ℝ} (hf : f < 0) (hax : 0 < ax) (hbx : bx < 0) : demF ax f bx = -f :=
  demF_obtuse hax hf hbx

/-- For an acute `y`, the two demands of `f` add up to (at most) `|f|`. -/
lemma dem_acute_sum {f ay b_y : ℝ} (hf : f < 0) (hay : 0 < ay) (hby : 0 < b_y) (hne : ay ≠ b_y)
    (hc : 0 ≤ f + ay + b_y) : demF ay f b_y + demF b_y f ay = -f :=
  demF_pair hf hay.ne' hby.ne' hne hc

/-! ### Lemma 9.2 -/

/-- **Lemma 9.2 (i)**: `x` `u`-obtuse, `y` acute, `xy` positive: `Val_f(xy) ≤ dem(vy, f)`. -/
lemma val_uobt_acute_pos {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) (hax : 0 < ax)
    (hbx : bx < 0) (hay : 0 < ay) (hq : 0 < q) :
    ValE f ax bx ay b_y q ≤ demF b_y f ay := by
  unfold ValE
  rw [vterm_of_pos hay.le hq.le, vterm_of_nonpos hbx.le, vterm_of_pos hax.le hq.le]
  have := vterm_le_dem (f := f) (pe := b_y) (po := ay) (p1 := bx) (p2 := q) (by linarith [H.cvxy])
  linarith

/-- **Lemma 9.2 (ii)**: `x` `u`-obtuse, `y` acute, `xy` negative:
`Val_f(xy) ≤ min(|φ(xy)|/φ(ux), 1) |f| + dem(vy, f)`. -/
lemma val_uobt_acute_neg {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) (hax : 0 < ax)
    (hbx : bx < 0) (hay : 0 < ay) (hq : q < 0) :
    ValE f ax bx ay b_y q ≤ (-f) * min (-q / ax) 1 + demF b_y f ay := by
  have hf := H.hf
  unfold ValE
  rw [vterm_of_nonpos (f := f) (po := ax) (p1 := b_y) (p2 := q) hbx.le]
  have h4 := vterm_le_dem (f := f) (pe := b_y) (po := ay) (p1 := bx) (p2 := q)
    (by linarith [H.cvxy])
  -- the two terms in the triangle `uxy`
  suffices h13 : vterm f ax bx ay q + vterm f ay b_y ax q ≤ (-f) * min (-q / ax) 1 by linarith
  unfold vterm normT
  rw [dem_uobt hf hax hbx, demF_of_nonneg_f hay.le, demF_of_nonneg_f hax.le, zero_add, zero_add]
  have hdu := demF_le ay f b_y hf
  have hdu0 := demF_nonneg ay f b_y
  have hF : -f < ax := by linarith [H.cx]
  rcases lt_or_gt_of_ne H.dxy with hlt | hlt
  · -- `ax < ay`
    by_cases hs : -q ≤ ay
    · rw [demF_nonsponsor hax hq hlt hs, demF_sponsor hay hq hax.le hlt hs]
      simp only [zero_div, mul_zero, zero_add]
      have h1 : -q / ay ≤ min (-q / ax) 1 := le_min
        (div_le_div_of_nonneg_left (by linarith) hax hlt.le) ((div_le_one hay).2 hs)
      have h2 : demF ay f b_y * (-q / ay) ≤ (-f) * (-q / ay) :=
        mul_le_mul_of_nonneg_right hdu (div_nonneg (by linarith) hay.le)
      calc demF ay f b_y * (-q / ay) ≤ (-f) * (-q / ay) := h2
        _ ≤ (-f) * min (-q / ax) 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
    · push_neg at hs
      -- unsponsored; then `vy` sponsors `uvy` and `dem(uy, f) = 0`
      have hby' : -q < b_y := by
        have := H.cvxy
        have hq' : -q ≤ b_y + bx := by linarith
        linarith
      have hduy : demF ay f b_y = 0 := demF_nonsponsor hay hf (by linarith) (by linarith)
      rw [hduy, demF_unsponsored hax hq hay.le (by linarith) hs]
      simp only [zero_mul, add_zero]
      have e : -q * ax / (ax + ay) / ax = -q / (ax + ay) := by
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      refine le_min (div_le_div_of_nonneg_left (by linarith) hax (by linarith)) ?_
      rw [div_le_one (by linarith)]; linarith [H.cuxy]
  · -- `ay < ax`
    by_cases hs : -q ≤ ax
    · rw [demF_sponsor hax hq hay.le hlt hs, demF_nonsponsor hay hq hlt hs]
      simp only [zero_div, mul_zero, add_zero]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact le_min le_rfl ((div_le_one hax).2 hs)
    · push_neg at hs
      have hby' : -q < b_y := by linarith [H.cvxy]
      have hduy : demF ay f b_y = 0 := demF_nonsponsor hay hf (by linarith) (by linarith)
      rw [hduy, demF_unsponsored hax hq hay.le hs (by linarith)]
      simp only [zero_mul, add_zero]
      have e : -q * ax / (ax + ay) / ax = -q / (ax + ay) := by
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      refine le_min (div_le_div_of_nonneg_left (by linarith) hax (by linarith)) ?_
      rw [div_le_one (by linarith)]; linarith [H.cuxy]

/-! ### Vanishing and the acute bound -/

/-- Two acute vertices joined by a positive edge have value `0`. -/
lemma val_acute_acute_pos {f ax bx ay b_y q : ℝ} (hax : 0 < ax) (hbx : 0 < bx) (hay : 0 < ay)
    (hby : 0 < b_y) (hq : 0 < q) : ValE f ax bx ay b_y q = 0 := by
  unfold ValE
  rw [vterm_of_pos hay.le hq.le, vterm_of_pos hby.le hq.le, vterm_of_pos hax.le hq.le,
    vterm_of_pos hbx.le hq.le]; ring

/-- Two `u`-obtuse vertices have value `0`. -/
lemma val_uobt_uobt {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) (hax : 0 < ax)
    (hbx : bx < 0) (hay : 0 < ay) (hby : b_y < 0) : ValE f ax bx ay b_y q = 0 := by
  have hq : 0 < q := by linarith [H.cvxy]
  unfold ValE
  rw [vterm_of_pos hay.le hq.le, vterm_of_nonpos hbx.le, vterm_of_pos hax.le hq.le,
    vterm_of_nonpos hby.le]; ring

/-- Two acute vertices: `Val_f(xy) ≤ 2 |φ(xy)|`. -/
lemma val_acute_acute_le {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) (hax : 0 < ax)
    (hbx : 0 < bx) (hay : 0 < ay) (hby : 0 < b_y) (hq : q < 0) :
    ValE f ax bx ay b_y q ≤ 2 * (-q) := by
  unfold ValE vterm normT
  rw [demF_of_nonneg_f hay.le, demF_of_nonneg_f hby.le, demF_of_nonneg_f hax.le,
    demF_of_nonneg_f hbx.le]
  simp only [zero_add]
  -- each `dem(e, f) ≤ φ(e)`, so each term is at most the corresponding demand of `xy`
  have key : ∀ {pe po p : ℝ}, 0 < pe → 0 ≤ pe + f + po → 0 ≤ p →
      demF pe f po * (demF pe q p / pe) ≤ demF pe q p := by
    intro pe po p hpe hc hp
    have h1 := demF_le_pe pe f po hc
    rw [max_eq_left hpe.le] at h1
    have h2 := demF_nonneg pe q p
    rw [mul_div_assoc', div_le_iff₀ hpe]
    nlinarith [demF_nonneg pe f po]
  have k1 := key (po := bx) hax (by linarith [H.cx]) hay.le
  have k2 := key (po := ax) hbx (by linarith [H.cx]) hby.le
  have k3 := key (po := b_y) hay (by linarith [H.cy]) hax.le
  have k4 := key (po := ay) hby (by linarith [H.cy]) hbx.le
  have p1 := demF_pair hq hax.ne' hay.ne' H.dxy (by linarith [H.cuxy])
  have p2 := demF_pair hq hbx.ne' hby.ne' H.dbxy (by linarith [H.cvxy])
  linarith

/-- A `u`-obtuse and a `v`-obtuse vertex: `Val_f(xy) = |f| (T(ux) + T(vy))`. -/
lemma val_uobt_vobt {f ax bx ay b_y q : ℝ} (H : PairH f ax bx ay b_y q) (hax : 0 < ax)
    (hbx : bx < 0) (hay : ay < 0) (hby : 0 < b_y) :
    ValE f ax bx ay b_y q = (-f) * (normT ax ay q + normT b_y bx q) := by
  unfold ValE
  rw [vterm_of_nonpos (f := f) hbx.le, vterm_of_nonpos (f := f) hay.le]
  unfold vterm
  rw [dem_uobt H.hf hax hbx, dem_uobt H.hf hby hay]; ring

/-! ### Lemma 9.3 -/

lemma alg_ext {F A B Q ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1/3)
    (h1 : (1-ε)*(F+B) ≤ A + Q) (h2 : (1-ε)*(F+A) ≤ B + Q) (hQ : Q < (1-3*ε)*F) :
    2*F ≤ A ∧ 2*F ≤ B := by
  have e1 : 2*ε*F + (1-ε)*B < A := by nlinarith
  have e2 : 2*ε*F + (1-ε)*A < B := by nlinarith
  have k : ε*(2-ε)*(A - 2*F) > 0 := by
    nlinarith [mul_le_mul_of_nonneg_left e2.le (by linarith : (0:ℝ) ≤ 1 - ε)]
  have k' : ε*(2-ε)*(B - 2*F) > 0 := by
    nlinarith [mul_le_mul_of_nonneg_left e1.le (by linarith : (0:ℝ) ≤ 1 - ε)]
  have hpos : 0 ≤ ε*(2-ε) := by nlinarith
  constructor
  · by_contra h; push_neg at h; nlinarith
  · by_contra h; push_neg at h; nlinarith

lemma alg_ext' {F A B ε : ℝ} (hF : 0 < F) (hA : 0 < A) (hB : 0 < B) (hε : ε ≤ 1/3)
    (h1 : (1-ε)*(F+B) ≤ A) (h2 : (1-ε)*(F+A) ≤ B) : 2*F ≤ A ∧ 2*F ≤ B := by
  have k : ε*(2-ε)*A ≥ (1-ε)*(2-ε)*F := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - ε)]
  have k' : ε*(2-ε)*B ≥ (1-ε)*(2-ε)*F := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - ε)]
  have hk : ε*A ≥ (1-ε)*F := by nlinarith
  have hk' : ε*B ≥ (1-ε)*F := by nlinarith
  constructor
  · by_contra h; push_neg at h; nlinarith
  · by_contra h; push_neg at h; nlinarith

/-- Lemma 9.3, case `x` `u`-obtuse and `y` acute. -/
lemma ext_uobt_acute {f ax bx ay b_y q ε : ℝ} (H : PairH f ax bx ay b_y q) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1/3)
    (hax : 0 < ax) (hbx : bx < 0) (hay : 0 < ay)
    (hV : (2 - ε) * (-f) ≤ ValE f ax bx ay b_y q) : q < 0 ∧ (1 - 3 * ε) * (-f) ≤ -q := by
  have hf := H.hf
  have hdv := demF_le b_y f ay hf
  rcases lt_or_gt_of_ne H.nq with hq | hq
  · refine ⟨hq, ?_⟩
    have h := val_uobt_acute_neg H hax hbx hay hq
    have hmin : (1 - ε) ≤ min (-q / ax) 1 := by
      by_contra hc; push_neg at hc
      have : (-f) * min (-q / ax) 1 < (-f) * (1 - ε) := mul_lt_mul_of_pos_left hc (by linarith)
      nlinarith
    have h1 : (1 - ε) ≤ -q / ax := le_trans hmin (min_le_left _ _)
    rw [le_div_iff₀ hax] at h1
    have hF : -f ≤ ax := by linarith [H.cx]
    nlinarith [mul_le_mul_of_nonneg_left hF (by linarith : (0:ℝ) ≤ 1 - ε)]
  · exfalso
    have h := val_uobt_acute_pos H hax hbx hay hq
    nlinarith

/-- Lemma 9.3, case both acute. -/
lemma ext_acute_acute {f ax bx ay b_y q ε : ℝ} (H : PairH f ax bx ay b_y q) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1/3)
    (hax : 0 < ax) (hbx : 0 < bx) (hay : 0 < ay) (hby : 0 < b_y)
    (hV : (2 - ε) * (-f) ≤ ValE f ax bx ay b_y q) : q < 0 ∧ (1 - 3 * ε) * (-f) ≤ -q := by
  have hf := H.hf
  rcases lt_or_gt_of_ne H.nq with hq | hq
  · have := val_acute_acute_le H hax hbx hay hby hq
    refine ⟨hq, by nlinarith⟩
  · rw [val_acute_acute_pos hax hbx hay hby hq] at hV
    exfalso; nlinarith

/-- Lemma 9.3, case `x` `u`-obtuse and `y` `v`-obtuse. -/
lemma ext_uobt_vobt {f ax bx ay b_y q ε : ℝ} (H : PairH f ax bx ay b_y q) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1/3) (hax : 0 < ax) (hbx : bx < 0) (hay : ay < 0) (hby : 0 < b_y)
    (hV : (2 - ε) * (-f) ≤ ValE f ax bx ay b_y q) :
    (2 * (-f) ≤ -bx ∧ 2 * (-f) ≤ -ay) ∨ (q < 0 ∧ (1 - 3 * ε) * (-f) ≤ -q) := by
  have hf := H.hf
  rw [val_uobt_vobt H hax hbx hay hby] at hV
  have hn1 := normT_le_one ax ay q H.cuxy
  have hn2 := normT_le_one b_y bx q (by linarith [H.cvxy])
  have hs : 2 - ε ≤ normT ax ay q + normT b_y bx q := by
    by_contra hc; push_neg at hc
    have := mul_lt_mul_of_pos_left hc (by linarith : (0:ℝ) < -f)
    linarith
  have hF1 : -f - bx ≤ ax := by linarith [H.cx]
  have hF2 : -f - ay ≤ b_y := by linarith [H.cy]
  rcases lt_or_gt_of_ne H.nq with hq | hq
  · by_cases hc : (1 - 3 * ε) * (-f) ≤ -q
    · exact Or.inr ⟨hq, hc⟩
    left
    push_neg at hc
    have e1 : normT ax ay q = (-ay + -q) / ax := by
      unfold normT; rw [demF_obtuse hax hay hq, demF_obtuse hax hq hay]
    have e2 : normT b_y bx q = (-bx + -q) / b_y := by
      unfold normT; rw [demF_obtuse hby hbx hq, demF_obtuse hby hq hbx]
    have r1 : (1 - ε) * ax ≤ -ay + -q := by
      have : 1 - ε ≤ normT ax ay q := by linarith
      rw [e1, le_div_iff₀ hax] at this; exact this
    have r2 : (1 - ε) * b_y ≤ -bx + -q := by
      have : 1 - ε ≤ normT b_y bx q := by linarith
      rw [e2, le_div_iff₀ hby] at this; exact this
    have h1 : (1 - ε) * (-f + -bx) ≤ -ay + -q :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) r1
    have h2 : (1 - ε) * (-f + -ay) ≤ -bx + -q :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) r2
    obtain ⟨k1, k2⟩ := alg_ext hε0 hε h1 h2 hc
    exact ⟨k2, k1⟩
  · left
    have b1 : normT ax ay q ≤ -ay / ax := by
      unfold normT; rw [demF_of_nonneg_f hq.le, add_zero]
      exact div_le_div_of_nonneg_right (demF_le ax ay q hay) hax.le
    have b2 : normT b_y bx q ≤ -bx / b_y := by
      unfold normT; rw [demF_of_nonneg_f hq.le, add_zero]
      exact div_le_div_of_nonneg_right (demF_le b_y bx q hbx) hby.le
    have r1 : (1 - ε) * ax ≤ -ay := by
      have : 1 - ε ≤ -ay / ax := by linarith
      rwa [le_div_iff₀ hax] at this
    have r2 : (1 - ε) * b_y ≤ -bx := by
      have : 1 - ε ≤ -bx / b_y := by linarith
      rwa [le_div_iff₀ hby] at this
    have h1 : (1 - ε) * (-f + -bx) ≤ -ay :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) r1
    have h2 : (1 - ε) * (-f + -ay) ≤ -bx :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) r2
    obtain ⟨k1, k2⟩ := alg_ext' (by linarith) (by linarith) (by linarith) hε h1 h2
    exact ⟨k2, k1⟩

/-- **Lemma 9.3 (Extremal Pair Value).**  If `Val_f(xy) ≥ (2 - ε)|f|` with `0 ≤ ε ≤ 1/3`, then
(a) `x` is `u`-obtuse, `y` is `v`-obtuse and `|φ(vx)|, |φ(uy)| ≥ 2|f|`, or (b) the same with
`u` and `v` exchanged, or (c) `xy` is negative with `|φ(xy)| ≥ (1 - 3ε)|f|`. -/
lemma val_extremal {f ax bx ay b_y q ε : ℝ} (H : PairH f ax bx ay b_y q) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1/3) (hV : (2 - ε) * (-f) ≤ ValE f ax bx ay b_y q) :
    (0 < ax ∧ bx < 0 ∧ ay < 0 ∧ 0 < b_y ∧ 2 * (-f) ≤ -bx ∧ 2 * (-f) ≤ -ay) ∨
    (ax < 0 ∧ 0 < bx ∧ 0 < ay ∧ b_y < 0 ∧ 2 * (-f) ≤ -ax ∧ 2 * (-f) ≤ -b_y) ∨
    (q < 0 ∧ (1 - 3 * ε) * (-f) ≤ -q) := by
  have hf := H.hf
  have hV1 := hV; have hV2 := hV; have hV3 := hV
  rw [ValE_swap_uv] at hV1
  rw [ValE_swap_xy] at hV2
  rw [ValE_swap_xy, ValE_swap_uv] at hV3
  have H1 := H.swap_uv
  have H2 := H.swap_xy
  have H3 := H.swap_xy.swap_uv
  rcases lt_or_gt_of_ne H.nax with hax | hax <;> rcases lt_or_gt_of_ne H.nbx with hbx | hbx <;>
    rcases lt_or_gt_of_ne H.nay with hay | hay <;> rcases lt_or_gt_of_ne H.nby with hby | hby
  all_goals first
    | (exfalso; linarith [H.cx])
    | (exfalso; linarith [H.cy])
    | skip
  -- `x` is `v`-obtuse
  · -- `y` `v`-obtuse: value zero
    exfalso; rw [val_uobt_uobt H1 hbx hax hby hay] at hV1; nlinarith
  · -- `y` `u`-obtuse: case (b) or (c)
    rcases ext_uobt_vobt H2 hε0 hε hay hby hax hbx hV2 with h | h
    · exact Or.inr (Or.inl ⟨hax, hbx, hay, hby, h.2, h.1⟩)
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr (ext_uobt_acute H1 hε0 hε hbx hax hby hV1))
  -- `x` is `u`-obtuse
  · rcases ext_uobt_vobt H hε0 hε hax hbx hay hby hV with h | h
    · exact Or.inl ⟨hax, hbx, hay, hby, h.1, h.2⟩
    · exact Or.inr (Or.inr h)
  · exfalso; rw [val_uobt_uobt H hax hbx hay hby] at hV; nlinarith
  · exact Or.inr (Or.inr (ext_uobt_acute H hε0 hε hax hbx hay hV))
  -- `x` is acute
  · exact Or.inr (Or.inr (ext_uobt_acute H3 hε0 hε hby hay hbx hV3))
  · exact Or.inr (Or.inr (ext_uobt_acute H2 hε0 hε hay hby hax hV2))
  · exact Or.inr (Or.inr (ext_acute_acute H hε0 hε hax hbx hay hby hV))

end NashWilliams.Frac
