/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.Vortex.ChildStep

@[expose] public section

/-!
# The 12.4 vortex level invariant and one sampling step

For a level `W` (all quantities are local to `W`):
* `nnb G v W` = number of non-neighbours of `v` in `W` (including `v` itself);
* `hiSet G W b` = vertices of `W` with at most `(1/4 - b)|W|` non-neighbours in `W`
  (i.e. of degree at least `(3/4 + b)|W|` in `G[W]`);
* `badTup W` = the `k`-tuples of `W` satisfying a FIXED predicate `f` (later: "the `k`-sample has
  a large cut").

`Inv124 G f a₀ b₀ c₀ ρ₀ W e` says, with one error parameter `e`:
* every `v ∈ W` has at most `(1/4 + a₀ + e)|W|` non-neighbours in `W`;
* at least `(c₀ - e)|W|` vertices of `W` lie in `hiSet G W (b₀ - e)`;
* at most `(ρ₀ + e)|W|^k` tuples of `W` are bad.

`inv_step` (proved): one random child `U ⊆ W` with `|U| ∈ [7q|W|/8, 9q|W|/8]` and
`Inv124 … U (e + D s)`, `s = |W|^{-1/4}`, `D = 4k/q + 4`, under explicit level-local numerical
conditions on `|W|` only.
-/

namespace NashWilliams18.Vortex124

open Finset
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Non-neighbours of `v` inside `W` (including `v`). -/
def nnb (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (W : Finset V) : ℕ :=
  (W.filter fun z => ¬ G.Adj v z).card

/-- High-degree vertices of `G[W]`. -/
noncomputable def hiSet (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (b : ℝ) :
    Finset V :=
  W.filter fun v => (nnb G v W : ℝ) ≤ (1 / 4 - b) * W.card

/-- The level invariant with a single error parameter `e`. -/
def Inv124 (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : (Fin k → V) → Prop)
    [DecidablePred f] (a₀ b₀ c₀ ρ₀ : ℝ) (W : Finset V) (e : ℝ) : Prop :=
  (∀ v ∈ W, (nnb G v W : ℝ) ≤ (1 / 4 + a₀ + e) * W.card) ∧
  (c₀ - e) * W.card ≤ ((hiSet G W (b₀ - e)).card : ℝ) ∧
  (((tup W k).filter f).card : ℝ) ≤ (ρ₀ + e) * (W.card : ℝ) ^ k

/-- Query sets of a level: the level, its high set, and the non-neighbourhoods. -/
noncomputable def qset (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (b : ℝ) :
    Option (Option V) → Finset V
  | none => W
  | some none => hiSet G W b
  | some (some v) => W.filter fun z => ¬ G.Adj v z

/-- Query indices of a level. -/
def qidx (W : Finset V) : Finset (Option (Option V)) :=
  insert none (insert (some none) (W.image fun v => some (some v)))

omit [Fintype V] in
lemma qidx_card (W : Finset V) : ((qidx W).card : ℝ) ≤ W.card + 2 := by
  have h1 := card_insert_le (none : Option (Option V))
    (insert (some none) (W.image fun v => some (some v)))
  have h2 := card_insert_le (some none : Option (Option V)) (W.image fun v => some (some v))
  have h3 := card_image_le (s := W) (f := fun v => (some (some v) : Option (Option V)))
  have : (qidx W).card ≤ W.card + 2 := by unfold qidx; omega
  exact_mod_cast this

omit [Fintype V] [DecidableEq V] in
lemma hiSet_subset (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (b : ℝ) :
    hiSet G W b ⊆ W := filter_subset _ _

lemma vx_deg_real {x y m u q s A : ℝ} (hm : 0 < m) (hq : 0 < q) (hs : 0 < s) (hsq : s ≤ q / 8)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 9 / 4) (hx : x < q * y + s * m) (hy : y ≤ A * m)
    (hu : (q - s) * m < u) : x ≤ (A + 4 * s / q) * u := by
  have hδ : 4 * s / q * q = 4 * s := by field_simp
  have hδs : 4 * s / q * s ≤ s / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq]; nlinarith
  have hδ0 : 0 ≤ 4 * s / q := by positivity
  have key : q * A + s ≤ (A + 4 * s / q) * (q - s) := by nlinarith
  have h1 : x ≤ (q * A + s) * m := by nlinarith
  have h2 : (q * A + s) * m ≤ (A + 4 * s / q) * ((q - s) * m) := by nlinarith
  have h3 : (A + 4 * s / q) * ((q - s) * m) ≤ (A + 4 * s / q) * u :=
    mul_le_mul_of_nonneg_left hu.le (by positivity)
  linarith

lemma vx_count_real {c c' h H m u q s : ℝ} (hm : 0 < m) (hq : 0 < q) (hs : 0 < s)
    (hc1 : c ≤ 1) (hc' : c' ≤ c - 4 * s / q) (hc'0 : 0 < c') (hu0 : 0 ≤ u)
    (hu : u < (q + s) * m) (hh : q * H - s * m < h) (hH : c * m ≤ H) : c' * u ≤ h := by
  have hδ : 4 * s / q * q = 4 * s := by field_simp
  have h1 : c' * u ≤ (c - 4 * s / q) * ((q + s) * m) :=
    mul_le_mul hc' hu.le hu0 (by linarith)
  have hδ0 : 0 ≤ 4 * s / q := by positivity
  have h2 : (c - 4 * s / q) * ((q + s) * m) ≤ q * (c * m) - s * m := by
    have : (c - 4 * s / q) * (q + s) ≤ q * c - s := by nlinarith
    nlinarith
  nlinarith

lemma vx_tup_real {B Bw N ρ qk mk uk s x : ℝ} (hqk : 0 < qk) (hmk : 0 < mk) (hs : 0 < s)
    (hs2 : s ≤ 1 / 2) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hB : B ≤ qk * Bw + N + s * (qk * mk)) (hN : N ≤ s * (qk * mk)) (hBw : Bw ≤ ρ * mk)
    (hUk : qk * mk * (1 - x) ≤ uk) : B ≤ (ρ + (4 * x + 4 * s)) * uk := by
  have h1 : B ≤ qk * mk * (ρ + 2 * s) := by
    have := mul_le_mul_of_nonneg_left hBw hqk.le
    nlinarith
  have hkey : ρ + 2 * s ≤ (ρ + (4 * x + 4 * s)) * (1 - x) := by nlinarith
  have hpos : 0 ≤ ρ + (4 * x + 4 * s) := by positivity
  calc B ≤ qk * mk * (ρ + 2 * s) := h1
    _ ≤ qk * mk * ((ρ + (4 * x + 4 * s)) * (1 - x)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (ρ + (4 * x + 4 * s)) * (qk * mk * (1 - x)) := by ring
    _ ≤ (ρ + (4 * x + 4 * s)) * uk := mul_le_mul_of_nonneg_left hUk hpos

lemma vx_tup_step {k : ℕ} (hk : 1 ≤ k) {BU BW E ρ q s m u : ℝ} (hq0 : 0 < q) (hm0 : 0 < m)
    (hs0 : 0 < s) (hsq : s ≤ q / 8) (hks : k * s / q ≤ 1 / 2) (hs2 : s ≤ 1 / 2)
    (hkm : (k : ℝ) ^ 2 / (q ^ k * m) ≤ s) (hρ0 : 0 ≤ ρ)
    (hcheb : BU ≤ E + s * q ^ k * m ^ k) (hexp : E ≤ q ^ k * BW + (k : ℝ) ^ 2 * m ^ (k - 1))
    (htup : BW ≤ ρ * m ^ k) (htriv : BU ≤ u ^ k) (hUlo : (q - s) * m < u) :
    BU ≤ (ρ + (4 * k / q + 4) * s) * u ^ k := by
  have hqk : 0 < q ^ k := by positivity
  have hmk : 0 < m ^ k := by positivity
  have hu0 : 0 ≤ u := le_trans (mul_nonneg (by linarith) hm0.le) hUlo.le
  have hm1 : m ^ (k - 1) * m = m ^ k := by
    rw [← pow_succ]; congr 1; omega
  have hnoninj : (k : ℝ) ^ 2 * m ^ (k - 1) ≤ s * (q ^ k * m ^ k) := by
    have h1 : (k : ℝ) ^ 2 ≤ s * (q ^ k * m) := by
      rwa [div_le_iff₀ (mul_pos hqk hm0)] at hkm
    calc (k : ℝ) ^ 2 * m ^ (k - 1) ≤ s * (q ^ k * m) * m ^ (k - 1) :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hm0.le _)
      _ = s * (q ^ k * m ^ k) := by rw [← hm1]; ring
  have hDs : 0 ≤ (4 * k / q + 4) * s := by positivity
  by_cases hρ1 : 1 ≤ ρ
  · exact htriv.trans (le_mul_of_one_le_left (pow_nonneg hu0 k) (by linarith))
  · push_neg at hρ1
    set x : ℝ := k * s / q with hx
    have hx0 : 0 ≤ x := by positivity
    have hsq' : s / q ≤ 1 / 8 := by rw [div_le_iff₀ hq0]; linarith
    have hbern : 1 - x ≤ (1 - s / q) ^ k := by
      have := one_add_mul_le_pow (a := -(s / q)) (by linarith) k
      have e1 : (1 + -(s / q)) = 1 - s / q := by ring
      rw [e1] at this
      have hx' : x = k * (s / q) := by rw [hx]; ring
      rw [hx']; linarith
    have hqsk : ((q - s) * m) ^ k = q ^ k * m ^ k * (1 - s / q) ^ k := by
      rw [show (q - s) * m = q * (1 - s / q) * m by field_simp, mul_pow, mul_pow]; ring
    have hUk : ((q - s) * m) ^ k ≤ u ^ k :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hm0.le) hUlo.le k
    have hUk' : q ^ k * m ^ k * (1 - x) ≤ u ^ k := by
      have := mul_le_mul_of_nonneg_left hbern (by positivity : (0 : ℝ) ≤ q ^ k * m ^ k)
      rw [hqsk] at hUk
      linarith
    have hB : BU ≤ q ^ k * BW + (k : ℝ) ^ 2 * m ^ (k - 1) + s * (q ^ k * m ^ k) := by
      linarith
    have h4 : (4 * k / q + 4) * s = 4 * x + 4 * s := by rw [hx]; ring
    rw [h4]
    exact vx_tup_real hqk hmk hs0 hs2 hx0 hks hρ0 hρ1 hB hnoninj htup hUk'

-- The extra parent-wide conjunct pushes the (unchanged) elaboration past the default budget.
set_option maxHeartbeats 400000 in
/-- **One sampling step of the 12.4 vortex** (proved).  The child `U` is controlled from every
vertex of the parent `W`: `nnb G v U` is bounded for all `v ∈ W`, not only for `v ∈ U`. -/
theorem inv_step (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (f : (Fin k → V) → Prop) [DecidablePred f] {a₀ b₀ c₀ ρ₀ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : a₀ ≤ 1) (hb₀ : 0 ≤ b₀) (hb₁ : b₀ ≤ 1 / 4) (hc₁ : c₀ ≤ 1)
    (hρ₀ : 0 ≤ ρ₀)
    {q : ℝ≥0} (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1 / 32)
    (W : Finset V) (hW : 0 < W.card) {e s : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hs0 : 0 < s)
    (hsq : s ≤ q / 8) (hks : k * s / q ≤ 1 / 2) (hs2 : s ≤ 1 / 2)
    (hkm : (k : ℝ) ^ 2 / ((q : ℝ) ^ k * W.card) ≤ s)
    (hfail : ((W.card : ℝ) + 2) * (2 * Real.exp (-2 * (s * W.card) ^ 2 / W.card)) +
      (k : ℝ) ^ 2 * (W.card : ℝ) ^ (2 * k - 1) / (s * (q : ℝ) ^ k * (W.card : ℝ) ^ k) ^ 2 < 1)
    (hinv : Inv124 G f a₀ b₀ c₀ ρ₀ W e) :
    ∃ U ⊆ W, 7 * q / 8 * (W.card : ℝ) ≤ U.card ∧ (U.card : ℝ) ≤ 9 * q / 8 * W.card ∧
      Inv124 G f a₀ b₀ c₀ ρ₀ U (e + (4 * k / q + 4) * s) ∧
      ∀ v ∈ W, (nnb G v U : ℝ) ≤ (1 / 4 + a₀ + (e + (4 * k / q + 4) * s)) * U.card := by
  classical
  set m : ℝ := (W.card : ℝ) with hm_def
  have hm0 : 0 < m := by rw [hm_def]; exact_mod_cast hW
  have hq1' : q ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_one]; linarith
  set b := b₀ - e with hb_def
  obtain ⟨hdeg, hhi, htup⟩ := hinv
  have hcpos : 0 < s * (q : ℝ) ^ k * m ^ k := by positivity
  obtain ⟨U, hUW, hdisc, hcheb⟩ := exists_child_discrepancy_tuple W q hq1' (qset G W b) (qidx W)
    (t := s * m) (by positivity) hW ((tup W k).filter f) (filter_subset _ _) hcpos (by
      refine lt_of_le_of_lt ?_ hfail
      gcongr
      exact qidx_card W)
  have hinterU : ∀ P : V → Prop, [DecidablePred P] → (W.filter P ∩ U) = U.filter P := by
    intro P _
    ext z; simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨-, h⟩, hz⟩; exact ⟨hz, h⟩
    · rintro ⟨hz, h⟩; exact ⟨⟨hUW hz, h⟩, hz⟩
  have hsize : |(U.card : ℝ) - q * m| < s * m := by
    have := hdisc none (mem_insert_self _ _)
    simp only [qset, inter_self, inter_eq_right.mpr hUW] at this
    exact this
  have hnn : ∀ v ∈ W, (nnb G v U : ℝ) < q * nnb G v W + s * m := by
    intro v hv
    have := hdisc (some (some v)) (mem_insert_of_mem (mem_insert_of_mem
      (mem_image.mpr ⟨v, hv, rfl⟩)))
    simp only [qset, hinterU, inter_eq_left.mpr (filter_subset _ W)] at this
    unfold nnb
    linarith [(abs_lt.mp this).2]
  have hhiU : q * (hiSet G W b).card - s * m < ((hiSet G W b ∩ U).card : ℝ) := by
    have := hdisc (some none) (mem_insert_of_mem (mem_insert_self _ _))
    simp only [qset] at this
    rw [inter_eq_left.mpr (hiSet_subset G W b)] at this
    linarith [(abs_lt.mp this).1]
  obtain ⟨hs1, hs2'⟩ := abs_lt.mp hsize
  have hUlo : (q - s) * m < U.card := by linarith
  have hUhi : (U.card : ℝ) < (q + s) * m := by linarith
  have hqs : 7 * q / 8 ≤ (q : ℝ) - s := by linarith
  have hU0 : (0 : ℝ) < U.card :=
    lt_of_le_of_lt (mul_nonneg (by linarith) hm0.le) hUlo
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : 4 * s / q ≤ (4 * k / q + 4) * s := by
    have : 4 * s / q ≤ 4 * k / q * s := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq0]; nlinarith
    nlinarith
  have hlo : 7 * q / 8 * m ≤ U.card :=
    (mul_le_mul_of_nonneg_right hqs hm0.le).trans hUlo.le
  have hhi' : (U.card : ℝ) ≤ 9 * q / 8 * m :=
    hUhi.le.trans (mul_le_mul_of_nonneg_right (by linarith) hm0.le)
  refine ⟨U, hUW, hlo, hhi', ⟨?_, ?_, ?_⟩, ?_⟩
  · -- degree invariant
    intro v hv
    have h := vx_deg_real hm0 hq0 hs0 hsq (by positivity) (by linarith) (hnn v (hUW hv))
      (hdeg v (hUW hv)) hUlo
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hU0.le)
    linarith
  · -- high-degree invariant
    have hsub : hiSet G W b ∩ U ⊆ hiSet G U (b₀ - (e + (4 * k / q + 4) * s)) := by
      intro v hv
      rw [mem_inter] at hv
      obtain ⟨hvW, hvU⟩ := hv
      have hvW' := hvW
      unfold hiSet at hvW' ⊢
      rw [mem_filter] at hvW' ⊢
      refine ⟨hvU, ?_⟩
      have h := vx_deg_real hm0 hq0 hs0 hsq (A := 1 / 4 - b) (by rw [hb_def]; linarith)
        (by rw [hb_def]; linarith) (hnn v hvW'.1) hvW'.2 hUlo
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hU0.le)
      rw [hb_def]; linarith
    have hcard : ((hiSet G W b ∩ U).card : ℝ) ≤
        (hiSet G U (b₀ - (e + (4 * k / q + 4) * s))).card := by
      exact_mod_cast card_le_card hsub
    by_cases hc : (c₀ - (e + (4 * k / q + 4) * s)) ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hc hU0.le).trans (Nat.cast_nonneg _)
    · push_neg at hc
      exact (vx_count_real hm0 hq0 hs0 (by linarith) (by linarith) hc hU0.le hUhi hhiU
        hhi).trans hcard
  · -- tuple invariant
    have htupU : ((tup U k).filter f) = ((tup W k).filter f).filter (fun s => ∀ l, s l ∈ U) := by
      ext t
      simp only [mem_filter, mem_tup]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨fun l => hUW (h1 l), h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
    have hexp := sum_pow_image_le W ((tup W k).filter f) (filter_subset _ _) q hq0.le
      (by exact_mod_cast hq1')
    rw [← htupU] at hcheb
    have htriv : (((tup U k).filter f).card : ℝ) ≤ (U.card : ℝ) ^ k := by
      have := (card_filter_le (tup U k) f).trans (card_tup U k).le
      exact_mod_cast this
    exact le_of_le_of_eq
      (vx_tup_step hk hq0 hm0 hs0 hsq hks hs2 hkm (by linarith) hcheb hexp htup htriv hUlo)
      (by ring)
  · -- parent-wide degree control: every vertex of the parent `W`, not only of the child
    intro v hv
    have h := vx_deg_real hm0 hq0 hs0 hsq (by positivity) (by linarith) (hnn v hv)
      (hdeg v hv) hUlo
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hU0.le)
    linarith

end NashWilliams18.Vortex124
