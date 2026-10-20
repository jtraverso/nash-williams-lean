/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.BipAbs
public import RequestProject.FracStab.ValPair
public import RequestProject.Fractional.Key

@[expose] public section

/-!
# The local facts hold for a good weighting (Lemmas 9.2 and 9.3 in graph form)
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- Normalised weight of a negative edge (`0` for non-edges and positive edges). -/
noncomputable def gG (u v x y : V) : ℝ :=
  if G.Adj x y ∧ φ s(x, y) < 0 then -φ s(x, y) / (-φ s(u, v)) else 0

/-- `u`-obtuse common neighbours. -/
def UG (u v x : V) : Prop := 0 < φ s(u, x) ∧ φ s(v, x) < 0

/-- `v`-obtuse common neighbours. -/
def WG (u v x : V) : Prop := 0 < φ s(v, x) ∧ φ s(u, x) < 0

/-- Acute common neighbours. -/
def AG (u v x : V) : Prop := 0 < φ s(u, x) ∧ 0 < φ s(v, x)

/-- Normalised demand `dem(uy, f) / |φ(f)|`. -/
noncomputable def duG (u v y : V) : ℝ := dem φ u y v / (-φ s(u, v))

/-- Normalised demand `dem(vy, f) / |φ(f)|`. -/
noncomputable def dvG (u v y : V) : ℝ := dem φ v y u / (-φ s(u, v))

open Classical in
/-- `u`-obtuse common neighbours `x` with `|φ(vx)| ≥ 2 |φ(uv)|`. -/
noncomputable def SuG (u v : V) : Finset V :=
  (cn G u v).filter fun x => UG φ u v x ∧ 2 * (-φ s(u, v)) ≤ -φ s(v, x)

open Classical in
/-- `v`-obtuse common neighbours `y` with `|φ(uy)| ≥ 2 |φ(uv)|`. -/
noncomputable def SvG (u v : V) : Finset V :=
  (cn G u v).filter fun x => WG φ u v x ∧ 2 * (-φ s(u, v)) ≤ -φ s(u, x)

variable {G φ}

omit [DecidableEq V] in
lemma mkPairH (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v) (hneg : φ s(u, v) < 0)
    {x y : V} (hx : x ∈ cn G u v) (hy : y ∈ cn G u v) (hxy : G.Adj x y) :
    PairH (φ s(u, v)) (φ s(u, x)) (φ s(v, x)) (φ s(u, y)) (φ s(v, y)) (φ s(x, y)) := by
  rw [mem_cn] at hx hy
  have e1 : s(u, x) ≠ s(u, y) := by
    rw [Sym2.eq_swap (a := u), Sym2.eq_swap (a := u) (b := y)]; exact ne_sym2 hxy.ne
  have e2 : s(v, x) ≠ s(v, y) := by
    rw [Sym2.eq_swap (a := v), Sym2.eq_swap (a := v) (b := y)]; exact ne_sym2 hxy.ne
  exact ⟨hneg, hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _, hφ.nz _, hφ.cov u v x huv hx.1 hx.2,
    hφ.cov u v y huv hy.1 hy.2, hφ.cov u x y hx.1 hy.1 hxy, hφ.cov v x y hx.2 hy.2 hxy,
    hφ.inj.ne e1, hφ.inj.ne e2, hφ.inj.ne (ne_sym2 huv.ne), hφ.inj.ne (ne_sym2 huv.ne)⟩

lemma aW_eq {u v x y : V} (hx : x ∈ cn G u v) (hy : y ∈ cn G u v) (hxy : G.Adj x y) :
    aW G φ u v x y = ValE (φ s(u, v)) (φ s(u, x)) (φ s(v, x)) (φ s(u, y)) (φ s(v, y))
      (φ s(x, y)) / (2 * -φ s(u, v)) := by
  unfold aW; rw [if_pos ⟨hx, hy, hxy⟩]; rfl

lemma aW_of_not {u v x y : V} (h : ¬ (x ∈ cn G u v ∧ y ∈ cn G u v ∧ G.Adj x y)) :
    aW G φ u v x y = 0 := by
  unfold aW; rw [if_neg h]

omit [Fintype V] [DecidableEq V] in
lemma dem_v_eq (u v y : V) :
    dem φ v y u = demF (φ s(v, y)) (φ s(u, v)) (φ s(u, y)) := by
  unfold dem; rw [Sym2.eq_swap (a := v) (b := u), Sym2.eq_swap (a := y) (b := u)]

omit [Fintype V] [DecidableEq V] in
lemma dem_u_eq (u v y : V) :
    dem φ u y v = demF (φ s(u, y)) (φ s(u, v)) (φ s(v, y)) := by
  unfold dem; rw [Sym2.eq_swap (a := y) (b := v)]

omit [Fintype V] [DecidableEq V] in
lemma gG_pos {u v x y : V} (h : 0 < gG G φ u v x y) :
    G.Adj x y ∧ φ s(x, y) < 0 := by
  unfold gG at h; split_ifs at h with hc
  · exact hc
  · exact absurd h (lt_irrefl 0)

omit [Fintype V] [DecidableEq V] in
lemma gG_of {u v x y : V} (h : G.Adj x y ∧ φ s(x, y) < 0) :
    gG G φ u v x y = -φ s(x, y) / (-φ s(u, v)) := by
  unfold gG; rw [if_pos h]

omit [Fintype V] [DecidableEq V] in
lemma pos_of_gG_zero (hφ : GoodWeighting G φ) {u v x y : V} (hneg : φ s(u, v) < 0)
    (hxy : G.Adj x y) (h : gG G φ u v x y = 0) : 0 < φ s(x, y) := by
  rcases lt_or_gt_of_ne (hφ.nz s(x, y)) with hl | hl
  · exfalso
    rw [gG_of ⟨hxy, hl⟩] at h
    have : 0 < -φ s(x, y) / (-φ s(u, v)) := div_pos (by linarith) (by linarith)
    linarith
  · exact hl

/-- **The local facts hold for good weightings.** -/
theorem locFacts_of_graph (hφ : GoodWeighting G φ) {u v : V} (huv : G.Adj u v)
    (hneg : φ s(u, v) < 0) :
    LocFacts (cn G u v) (aW G φ u v) (gG G φ u v) (UG φ u v) (WG φ u v) (AG φ u v)
      (duG φ u v) (dvG φ u v) (SuG G φ u v) (SvG G φ u v) := by
  classical
  set F := -φ s(u, v) with hF
  have hF0 : 0 < F := by linarith
  have h2F : 0 < 2 * F := by linarith
  -- value of `aW` on edges
  have hval : ∀ {x y : V}, x ∈ cn G u v → y ∈ cn G u v → G.Adj x y →
      2 * aW G φ u v x y = ValE (φ s(u, v)) (φ s(u, x)) (φ s(v, x)) (φ s(u, y)) (φ s(v, y))
        (φ s(x, y)) / F := by
    intro x y hx hy hxy
    rw [aW_eq hx hy hxy, ← hF]; field_simp
  refine
    { thin := thin_aW G φ hφ huv hneg
      gsymm := ?_, g0 := ?_, cov := ?_, AU := ?_, AW := ?_, UW := ?_, SuU := ?_, SvW := ?_,
      UU := ?_, WW := ?_, AA := ?_, tri := ?_, du0 := ?_, dv0 := ?_, dsum := ?_, F4u := ?_,
      F4w := ?_, F5u := ?_, F5w := ?_, F6u := ?_, F6w := ?_, F7 := ?_ }
  · intro x y; unfold gG
    rw [Sym2.eq_swap (a := x) (b := y)]
    by_cases h : G.Adj x y ∧ φ s(y, x) < 0
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩)]
  · intro x y; unfold gG; split_ifs with h
    · exact div_nonneg (by linarith [h.2]) hF0.le
    · exact le_rfl
  · intro x hx
    rw [mem_cn] at hx
    have c := hφ.cov u v x huv hx.1 hx.2
    rcases lt_or_gt_of_ne (hφ.nz s(u, x)) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hφ.nz s(v, x)) with h2 | h2
    · exfalso; linarith
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · intro x h h'; exact absurd h'.2 (not_lt.2 h.2.le)
  · intro x h h'; exact absurd h'.2 (not_lt.2 h.1.le)
  · intro x h h'; exact absurd h'.2 (not_lt.2 h.1.le)
  · intro x hx; unfold SuG at hx; exact (mem_filter.1 hx).2.1
  · intro x hx; unfold SvG at hx; exact (mem_filter.1 hx).2.1
  · intro x hx y hy hUx hUy
    by_cases hxy : G.Adj x y
    · rw [aW_eq hx hy hxy, val_uobt_uobt (mkPairH hφ huv hneg hx hy hxy) hUx.1 hUx.2 hUy.1 hUy.2,
        zero_div]
    · exact aW_of_not fun h => hxy h.2.2
  · intro x hx y hy hWx hWy
    by_cases hxy : G.Adj x y
    · rw [aW_eq hx hy hxy, ValE_swap_uv, val_uobt_uobt (mkPairH hφ huv hneg hx hy hxy).swap_uv
        hWx.1 hWx.2 hWy.1 hWy.2, zero_div]
    · exact aW_of_not fun h => hxy h.2.2
  · intro x hx y hy hAx hAy hg
    by_cases hxy : G.Adj x y
    · rw [aW_eq hx hy hxy, val_acute_acute_pos hAx.1 hAx.2 hAy.1 hAy.2
        (pos_of_gG_zero hφ hneg hxy hg), zero_div]
    · exact aW_of_not fun h => hxy h.2.2
  · intro x y z h1 h2 h3
    obtain ⟨a1, b1⟩ := gG_pos h1
    obtain ⟨a2, b2⟩ := gG_pos h2
    obtain ⟨a3, b3⟩ := gG_pos h3
    have := hφ.cov x y z a1 a2 a3
    linarith
  · intro y; exact div_nonneg (dem_nonneg _ _ _ _) hF0.le
  · intro y; exact div_nonneg (dem_nonneg _ _ _ _) hF0.le
  · intro y hy
    unfold duG dvG
    rw [← add_div, dem_pair_sum G φ hφ huv hneg hy, div_self hF0.ne']
  · intro z hz y hy hUz hAy hg
    by_cases hzy : G.Adj z y
    · rw [hval hz hy hzy]
      unfold dvG; rw [dem_v_eq, ← hF]
      exact div_le_div_of_nonneg_right (val_uobt_acute_pos (mkPairH hφ huv hneg hz hy hzy)
        hUz.1 hUz.2 hAy.1 (pos_of_gG_zero hφ hneg hzy hg)) hF0.le
    · rw [aW_of_not fun h => hzy h.2.2, mul_zero]
      exact div_nonneg (dem_nonneg _ _ _ _) hF0.le
  · intro z hz y hy hWz hAy hg
    by_cases hzy : G.Adj z y
    · rw [hval hz hy hzy, ValE_swap_uv]
      unfold duG; rw [dem_u_eq, ← hF]
      exact div_le_div_of_nonneg_right (val_uobt_acute_pos
        (mkPairH hφ huv hneg hz hy hzy).swap_uv hWz.1 hWz.2 hAy.2
        (pos_of_gG_zero hφ hneg hzy hg)) hF0.le
    · rw [aW_of_not fun h => hzy h.2.2, mul_zero]
      exact div_nonneg (dem_nonneg _ _ _ _) hF0.le
  · intro z hz y hy hUz hAy
    have hd : 0 ≤ dvG φ u v y := div_nonneg (dem_nonneg _ _ _ _) hF0.le
    by_cases hzy : G.Adj z y
    · rw [hval hz hy hzy]
      have H := mkPairH hφ huv hneg hz hy hzy
      have key : ValE (φ s(u, v)) (φ s(u, z)) (φ s(v, z)) (φ s(u, y)) (φ s(v, y)) (φ s(z, y))
          ≤ F + dem φ v y u := by
        rw [dem_v_eq]
        rcases lt_or_gt_of_ne (hφ.nz s(z, y)) with hq | hq
        · have := val_uobt_acute_neg H hUz.1 hUz.2 hAy.1 hq
          have hm : F * min (-φ s(z, y) / φ s(u, z)) 1 ≤ F :=
            mul_le_of_le_one_right hF0.le (min_le_right _ _)
          linarith
        · have := val_uobt_acute_pos H hUz.1 hUz.2 hAy.1 hq
          have := demF_nonneg (φ s(v, y)) (φ s(u, v)) (φ s(u, y))
          linarith
      unfold dvG; rw [← hF, div_le_iff₀ hF0, add_mul, one_mul, div_mul_cancel₀ _ hF0.ne']
      exact key
    · rw [aW_of_not fun h => hzy h.2.2, mul_zero]; linarith
  · intro z hz y hy hWz hAy
    have hd : 0 ≤ duG φ u v y := div_nonneg (dem_nonneg _ _ _ _) hF0.le
    by_cases hzy : G.Adj z y
    · rw [hval hz hy hzy, ValE_swap_uv]
      have H := (mkPairH hφ huv hneg hz hy hzy).swap_uv
      have key : ValE (φ s(u, v)) (φ s(v, z)) (φ s(u, z)) (φ s(v, y)) (φ s(u, y)) (φ s(z, y))
          ≤ F + dem φ u y v := by
        rw [dem_u_eq]
        rcases lt_or_gt_of_ne (hφ.nz s(z, y)) with hq | hq
        · have := val_uobt_acute_neg H hWz.1 hWz.2 hAy.2 hq
          have hm : F * min (-φ s(z, y) / φ s(v, z)) 1 ≤ F :=
            mul_le_of_le_one_right hF0.le (min_le_right _ _)
          linarith
        · have := val_uobt_acute_pos H hWz.1 hWz.2 hAy.2 hq
          have := demF_nonneg (φ s(u, y)) (φ s(u, v)) (φ s(v, y))
          linarith
      unfold duG; rw [← hF, div_le_iff₀ hF0, add_mul, one_mul, div_mul_cancel₀ _ hF0.ne']
      exact key
    · rw [aW_of_not fun h => hzy h.2.2, mul_zero]; linarith
  · intro z hz y hy hUz hAy hg
    obtain ⟨hzy, hq⟩ := gG_pos hg
    rw [hval hz hy hzy, gG_of ⟨hzy, hq⟩]
    have H := mkPairH hφ huv hneg hz hy hzy
    have hv := val_uobt_acute_neg H hUz.1 hUz.2 hAy.1 hq
    have hcz := H.cx
    have haz : F ≤ φ s(u, z) := by linarith [hUz.2]
    have hm : F * min (-φ s(z, y) / φ s(u, z)) 1 ≤ -φ s(z, y) := by
      calc F * min (-φ s(z, y) / φ s(u, z)) 1 ≤ F * (-φ s(z, y) / φ s(u, z)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hF0.le
        _ ≤ φ s(u, z) * (-φ s(z, y) / φ s(u, z)) :=
            mul_le_mul_of_nonneg_right haz (div_nonneg (by linarith) hUz.1.le)
        _ = -φ s(z, y) := by field_simp [hUz.1.ne']
    unfold dvG; rw [dem_v_eq, ← hF, div_sub_div_same, div_le_div_iff_of_pos_right hF0]
    linarith
  · intro z hz y hy hWz hAy hg
    obtain ⟨hzy, hq⟩ := gG_pos hg
    rw [hval hz hy hzy, gG_of ⟨hzy, hq⟩, ValE_swap_uv]
    have H := (mkPairH hφ huv hneg hz hy hzy).swap_uv
    have hv := val_uobt_acute_neg H hWz.1 hWz.2 hAy.2 hq
    have hcz := H.cx
    have haz : F ≤ φ s(v, z) := by linarith [hWz.2]
    have hm : F * min (-φ s(z, y) / φ s(v, z)) 1 ≤ -φ s(z, y) := by
      calc F * min (-φ s(z, y) / φ s(v, z)) 1 ≤ F * (-φ s(z, y) / φ s(v, z)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hF0.le
        _ ≤ φ s(v, z) * (-φ s(z, y) / φ s(v, z)) :=
            mul_le_mul_of_nonneg_right haz (div_nonneg (by linarith) hWz.1.le)
        _ = -φ s(z, y) := by field_simp [hWz.1.ne']
    unfold duG; rw [dem_u_eq, ← hF, div_sub_div_same, div_le_div_iff_of_pos_right hF0]
    linarith
  · intro x hx y hy e he0 he1 ha
    have hpos : 0 < aW G φ u v x y := by linarith
    have hxy : G.Adj x y := by
      by_contra h; rw [aW_of_not fun h' => h h'.2.2] at hpos; exact lt_irrefl 0 hpos
    have H := mkPairH hφ huv hneg hx hy hxy
    have hV : (2 - 2 * e) * (-φ s(u, v)) ≤
        ValE (φ s(u, v)) (φ s(u, x)) (φ s(v, x)) (φ s(u, y)) (φ s(v, y)) (φ s(x, y)) := by
      have := hval hx hy hxy
      rw [eq_div_iff hF0.ne'] at this
      rw [← hF, ← this]; nlinarith
    rcases val_extremal H (by linarith) (by linarith) hV with h | h | h
    · left
      refine ⟨?_, ?_⟩
      · unfold SuG; rw [mem_filter]; exact ⟨hx, ⟨h.1, h.2.1⟩, h.2.2.2.2.1⟩
      · unfold SvG; rw [mem_filter]; exact ⟨hy, ⟨h.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2⟩
    · right; left
      refine ⟨?_, ?_⟩
      · unfold SvG; rw [mem_filter]; exact ⟨hx, ⟨h.2.1, h.1⟩, h.2.2.2.2.1⟩
      · unfold SuG; rw [mem_filter]; exact ⟨hy, ⟨h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.2⟩
    · right; right
      rw [gG_of ⟨hxy, h.1⟩, le_div_iff₀ hF0]
      linarith [h.2]

end NashWilliams.Frac
