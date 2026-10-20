/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.LevelCoverF1

@[expose] public section

/-!
# The protected `F₁` level, part 4: the numerical inputs of the spread cover-down

Each lemma derives one rounded (natural-number) input of `F1_spread_level_cover_down` for the
actual cross graph `Q = R ∪ E` from the physical counts of `LevelCountsF1.lean` and explicit
scalar inequalities: link margins, link defect, overlaps, visits, the logarithmic budget and the
apex supply.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen ApexF1
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The logarithmic budget of the spread lemma, with explicit ceilings. -/
theorem spread_log_budget (n ωc Lc b S : ℝ) (ω L K B : ℕ) (hb : 0 < b) (hωc : 0 ≤ ωc)
    (hLc : 0 ≤ Lc) (hn : 1 ≤ n) (hω : (ω : ℝ) ≤ ωc * n + 1) (hL : (L : ℝ) ≤ Lc * n)
    (hK : b * n ≤ K) (hS0 : 0 ≤ S) (hS : S ≤ n ^ 2)
    (hover : 2 * ωc * Lc / b ≤ b / 2) (hN : 8 * Lc / b ^ 2 + 256 / b ^ 2 ≤ n)
    (hB : b * n ≤ B) :
    (Real.exp 1 - 1) * ω * L / K + Real.log S ≤ B := by
  have he1 : Real.exp 1 - 1 ≤ 2 := by
    have := Real.exp_one_lt_d9; linarith
  have he0 : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1; linarith
  have hn0 : 0 < n := by linarith
  have hbn : 0 < b * n := by positivity
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le hbn hK
  have hω0 : (0 : ℝ) ≤ ω := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  -- the potential term
  have hnum : (Real.exp 1 - 1) * ω * L ≤ 2 * (ωc * n + 1) * (Lc * n) := by
    have h1 : (Real.exp 1 - 1) * ω ≤ 2 * (ωc * n + 1) :=
      mul_le_mul he1 hω hω0 (by norm_num)
    exact mul_le_mul h1 hL hL0 (by positivity)
  have hT : (Real.exp 1 - 1) * ω * L / K ≤ 2 * (ωc * n + 1) * (Lc * n) / (b * n) := by
    calc (Real.exp 1 - 1) * ω * L / K ≤ 2 * (ωc * n + 1) * (Lc * n) / K :=
          div_le_div_of_nonneg_right hnum hK0.le
      _ ≤ 2 * (ωc * n + 1) * (Lc * n) / (b * n) :=
          div_le_div_of_nonneg_left (by positivity) hbn hK
  have hT' : 2 * (ωc * n + 1) * (Lc * n) / (b * n) = (2 * ωc * Lc / b) * n + 2 * Lc / b := by
    field_simp
  have h2L : 2 * Lc / b ≤ b / 4 * n := by
    have h8 : 8 * Lc / b ^ 2 ≤ n := le_trans (le_add_of_nonneg_right (by positivity)) hN
    rw [div_le_iff₀ (by positivity)] at h8
    rw [div_le_iff₀ hb]; nlinarith
  have hpot : (Real.exp 1 - 1) * ω * L / K ≤ b / 2 * n + b / 4 * n := by
    rw [hT'] at hT
    nlinarith [mul_le_mul_of_nonneg_right hover hn0.le]
  -- the logarithm
  have hlog : Real.log S ≤ b / 4 * n := by
    rcases le_or_gt S 1 with hS1 | hS1
    · have := Real.log_nonpos hS0 hS1
      have : 0 ≤ b / 4 * n := by positivity
      linarith
    · have hl1 : Real.log S ≤ Real.log (n ^ 2) := Real.log_le_log (by linarith) hS
      rw [Real.log_pow] at hl1
      have hsq := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
      rw [Real.log_sqrt hn0.le] at hsq
      have hs0 := Real.sqrt_nonneg n
      have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      have h256 : 256 / b ^ 2 ≤ n := le_trans (le_add_of_nonneg_left (by positivity)) hN
      have hsqb : 16 / b ≤ Real.sqrt n := by
        rw [show (16 : ℝ) / b = Real.sqrt (256 / b ^ 2) by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hb.le]
          norm_num]
        exact Real.sqrt_le_sqrt h256
      have h4 : 4 * Real.sqrt n ≤ b / 4 * n := by
        have := mul_le_mul_of_nonneg_left hsqb (show 0 ≤ b / 4 * Real.sqrt n by positivity)
        have e1 : b / 4 * Real.sqrt n * (16 / b) = 4 * Real.sqrt n := by field_simp; ring
        nlinarith
      push_cast at hl1
      linarith
  linarith

omit [Fintype V] [DecidableEq V] in
/-- Four link margins from one upper and one lower physical class count. -/
theorem margins_of_bounds (p : V → Fin 4) (c : Fin 4) (T : Finset V) (Γ γ : ℕ) (Up Lo : ℝ)
    (ho : ((T.filter fun y => p y = c).card : ℝ) ≤ Up)
    (h0 : Lo ≤ ((T.filter fun y => p y = c).card : ℝ))
    (h1 : Lo ≤ ((T.filter fun y => p y = partner1 c).card : ℝ))
    (h2 : Lo ≤ ((T.filter fun y => p y = partner2 c).card : ℝ))
    (hcond : (8 * Γ + 1 + 2 * γ : ℝ) + (Up - Lo) ≤ Lo) : MarginsSlack p c T Γ γ := by
  have hΓ : (0 : ℝ) ≤ Γ := Nat.cast_nonneg _
  have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (4 * Γ + 1 + γ : ℝ) ≤ (T.filter fun y => p y = c).card := by linarith
    exact_mod_cast this
  · have : (6 * Γ + 1 + γ : ℝ) ≤ (T.filter fun y => p y = partner1 c).card := by linarith
    exact_mod_cast this
  · have : (6 * Γ + 1 + γ : ℝ) ≤ (T.filter fun y => p y = partner2 c).card := by linarith
    exact_mod_cast this
  · have : ((T.filter fun y => p y = c).card : ℝ) + 8 * Γ + 1 + 2 * γ ≤
        (T.filter fun y => p y = partner1 c).card + (T.filter fun y => p y = partner2 c).card := by
      linarith
    exact_mod_cast this

/-- Allowed partner classes of a root class. -/
theorem allowed_own_partners : ∀ c : Fin 4, AllowedT F1 c c ∧ AllowedT F1 c (partner1 c) ∧
    AllowedT F1 c (partner2 c) := by decide


section Fields

variable {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
  {W U U' : Finset V} {β κ ξ ζ : ℝ}

/-- **The four link margins** of an actual cross neighbourhood, with
`Γ = ⌈g|W|⌉ + 1 + (⌈b|W|⌉ + ⌈b|W|⌉)` and slack `⌈η'|W|⌉`. -/
theorem field_margins (h : ProtLevel p G H W U U' β κ ξ ζ) {R E : Finset (Sym2 V)}
    {ρ ε θ g b η' : ℝ} (hR : CrossResGood p H W U R ρ (3 * ε)) (hρ : 0 < ρ)
    (hE : ∀ v, ((E.filter fun e => v ∈ e).card : ℝ) ≤ θ * W.card) {r : V} (hr : r ∈ W)
    (hrU : r ∉ U) (hκ : 0 ≤ κ) (hg : 0 ≤ g) (hb : 0 ≤ b) (hη' : 0 ≤ η')
    (hkey : (8 * g + 16 * b + 2 * η') * W.card + 35 +
      (ρ * (3 * κ + 2 * ξ + 2 * ζ) + 9 * ε + θ) * W.card ≤ ρ * (U.card / 4)) :
    MarginsSlack p (p r) (tgt U (R ∪ E) r) ((⌈g * W.card⌉₊ + 1) + (⌈b * W.card⌉₊ + ⌈b * W.card⌉₊))
      ⌈η' * W.card⌉₊ := by
  set n : ℝ := (W.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hown : ∀ c : Fin 4, (((tgt U (R ∪ E) r).filter fun z => p z = c).card : ℝ) ≤
      ρ * (U.card / 4 + κ * n) + 3 * ε * n + θ * n := by
    intro c
    have h1 := tgt_cls_upper hR hρ.le E hr hrU c
    have h2 := (abs_le.mp (h.hin c)).2
    unfold uOf at h2
    have h3 := hE r
    have := mul_le_mul_of_nonneg_left h2 hρ.le
    linarith
  have hpart : ∀ c : Fin 4, AllowedT F1 (p r) c →
      ρ * (U.card / 4 - κ * n - (ξ + ζ) * n) - 3 * ε * n ≤
        (((tgt U (R ∪ E) r).filter fun z => p z = c).card : ℝ) := by
    intro c hc
    have h1 := tgt_cls_lower h hR hρ.le E hr hrU hc
    have h2 := (abs_le.mp (h.hin c)).1
    unfold uOf at h2
    have := mul_le_mul_of_nonneg_left h2 hρ.le
    linarith
  have hγ₀ : ((⌈g * n⌉₊ + 1 : ℕ) : ℝ) < g * n + 2 := by
    push_cast; linarith [Nat.ceil_lt_add_one (show 0 ≤ g * n by positivity)]
  have hK : ((⌈b * n⌉₊ : ℕ) : ℝ) < b * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hγ : ((⌈η' * n⌉₊ : ℕ) : ℝ) < η' * n + 1 := Nat.ceil_lt_add_one (by positivity)
  obtain ⟨ha0, ha1, ha2⟩ := allowed_own_partners (p r)
  refine margins_of_bounds p (p r) (tgt U (R ∪ E) r) _ _
    (ρ * (U.card / 4 + κ * n) + 3 * ε * n + θ * n)
    (ρ * (U.card / 4 - κ * n - (ξ + ζ) * n) - 3 * ε * n)
    (hown _) (hpart _ ha0) (hpart _ ha1) (hpart _ ha2) ?_
  have : 0 ≤ ρ * κ * n := by positivity
  push_cast at hγ₀ ⊢
  linarith

/-- **Link defect** bound by `⌈g|W|⌉ + 1`, `g = ρ(β² + ξ) + ε + θ`. -/
theorem field_defect (h : ProtLevel p G H W U U' β κ ξ ζ) {R E : Finset (Sym2 V)}
    {ρ ε θ : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hbad : ∀ x ∈ W, ∀ v ∈ W, ∀ c : Fin 4,
      ((U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(x, z) ∈ R).card : ℝ) ≤
        ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ H.Adj v z).card) + ε * W.card)
    (hE : ∀ v, ((E.filter fun e => v ∈ e).card : ℝ) ≤ θ * W.card) {r v : V} (hr : r ∈ W)
    (hv : v ∈ U) {c : Fin 4} (hc : AllowedT F1 (p v) c) :
    ((tgt U (R ∪ E) r).filter fun z => p z = c ∧
        ¬ (z ≠ v ∧ s(v, z) ∈ edgesIn H U \ edgesIn H U')).card ≤
      ⌈(ρ * (β ^ 2 + ξ) + ε + θ) * W.card⌉₊ + 1 := by
  have h1 := tgt_defect h hρ hbad E hr hv hc
  have h2 := hE r
  have hU' : (U'.card : ℝ) ≤ β ^ 2 * W.card := by
    have := h.hU'hi
    have := mul_le_mul_of_nonneg_left h.hUhi hβ
    linarith
  have h3 := mul_le_mul_of_nonneg_left hU' hρ
  have h4 := Nat.le_ceil ((ρ * (β ^ 2 + ξ) + ε + θ) * W.card)
  have : (((tgt U (R ∪ E) r).filter fun z => p z = c ∧
        ¬ (z ≠ v ∧ s(v, z) ∈ edgesIn H U \ edgesIn H U')).card : ℝ) ≤
      ((⌈(ρ * (β ^ 2 + ξ) + ε + θ) * W.card⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

/-- **Pairwise overlap** bound by `⌈(ρ²β + 12ε + 2θ)|W|⌉`. -/
theorem field_overlap (h : ProtLevel p G H W U U' β κ ξ ζ) {R E : Finset (Sym2 V)}
    {ρ ε θ : ℝ} (hR : CrossResGood p H W U R ρ (3 * ε))
    (hE : ∀ v, ((E.filter fun e => v ∈ e).card : ℝ) ≤ θ * W.card) {a b : V}
    (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U) :
    (tgt U (R ∪ E) a ∩ tgt U (R ∪ E) b).card ≤ ⌈(ρ ^ 2 * β + 12 * ε + 2 * θ) * W.card⌉₊ := by
  have h1 := tgt_overlap hR E ha hb hab haU hbU
  have h2 := hE a
  have h3 := hE b
  have h4 := mul_le_mul_of_nonneg_left h.hUhi (sq_nonneg ρ)
  have h5 := Nat.le_ceil ((ρ ^ 2 * β + 12 * ε + 2 * θ) * W.card)
  have : ((tgt U (R ∪ E) a ∩ tgt U (R ∪ E) b).card : ℝ) ≤
      ((⌈(ρ ^ 2 * β + 12 * ε + 2 * θ) * W.card⌉₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- **Apex supply** `⌊(ρ²(β/8 - κ - 2ξ - 2ζ) - 3ε)|W|⌋` for an outer pair. -/
theorem field_apex (h : ProtLevel p G H W U U' β κ ξ ζ) {R Q : Finset (Sym2 V)} {ρ ε : ℝ}
    (hW : 0 < W.card) (hβ1 : β ≤ 1 / 2) (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (hR : CrossResGood p H W U R ρ (3 * ε)) (hRQ : R ⊆ Q)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hxU : x ∉ U) (hyU : y ∉ U)
    (hall : AllowedT F1 (p x) (p y)) :
    ⌊(ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε) * W.card⌋₊ ≤
      (U.filter fun z => s(x, z) ∈ Q ∧ s(y, z) ∈ Q ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card := by
  have hlow := apex_count_lower (Q := Q) h hW hβ1 hκ hξ hζ hR hRQ hx hy hxy hxU hyU hall
  have hXn : (ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε) * W.card ≤
      ((U.filter fun z => s(x, z) ∈ Q ∧ s(y, z) ∈ Q ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card : ℝ) := by
    refine le_trans ?_ hlow
    unfold uOf
    have := mul_le_mul_of_nonneg_left h.hUlo (sq_nonneg ρ)
    linarith
  exact (Nat.floor_le_floor hXn).trans (Nat.floor_natCast _).le

end Fields

/-- **Visit load** bound by `⌊(ρ + ε + θ) n⌋`. -/
theorem field_visits (U : Finset V) (R E : Finset (Sym2 V)) (kr : ℕ) (r : ℕ → V)
    (hr : ∀ i < kr, ∀ j < kr, r i = r j → i = j) {ρ ε θ n : ℝ}
    (hR : ∀ v, ((R.filter fun e => v ∈ e).card : ℝ) ≤ (ρ + ε) * n)
    (hE : ∀ v, ((E.filter fun e => v ∈ e).card : ℝ) ≤ θ * n) (v : V) :
    visits (fun j => tgt U (R ∪ E) (r j)) kr v ≤ ⌊(ρ + ε + θ) * n⌋₊ := by
  have h1 := visits_le U (R ∪ E) kr r hr v
  have h2 : ((R ∪ E).filter fun e => v ∈ e).card ≤ (R.filter fun e => v ∈ e).card +
      (E.filter fun e => v ∈ e).card := by
    rw [filter_union]; exact card_union_le _ _
  have h3 : ((visits (fun j => tgt U (R ∪ E) (r j)) kr v : ℕ) : ℝ) ≤ (ρ + ε + θ) * n := by
    have h' : ((visits (fun j => tgt U (R ∪ E) (r j)) kr v : ℕ) : ℝ) ≤
        (R.filter fun e => v ∈ e).card + (E.filter fun e => v ∈ e).card := by
      exact_mod_cast h1.trans h2
    have := hR v
    have := hE v
    linarith
  exact Nat.le_floor h3

omit [Fintype V] in
/-- **Total target size** at most `|W|²`. -/
theorem field_total (W U : Finset V) (Q : Finset (Sym2 V)) (hUW : U ⊆ W) (kr : ℕ) (r : ℕ → V)
    (hkr : kr ≤ W.card) :
    ∑ j ∈ range kr, ((tgt U Q (r j)).card : ℝ) ≤ (W.card : ℝ) ^ 2 := by
  have h1 : ∀ j ∈ range kr, ((tgt U Q (r j)).card : ℝ) ≤ W.card := by
    intro j _
    exact_mod_cast (card_le_card (filter_subset _ _)).trans (card_le_card hUW)
  refine (sum_le_sum h1).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have : (kr : ℝ) ≤ W.card := by exact_mod_cast hkr
  have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (α := ℝ) W.card)
  nlinarith

/-- Apex budget in natural numbers. -/
theorem field_apex_budget (k n γ sN : ℕ) (hk : k ≤ n * γ) (h3 : 3 * γ < sN) :
    2 * γ + k / n < sN := by
  have : k / n ≤ γ := Nat.div_le_of_le_mul hk
  omega

/-- Rounding of the apex supply against the leftover degree. -/
theorem field_three (η X n : ℝ) (hη : 0 ≤ η) (hn : 0 ≤ n) (h : 5 ≤ (X - 3 * η) * n) :
    3 * ⌈η * n⌉₊ < ⌊X * n⌋₊ := by
  have h1 : ((⌈η * n⌉₊ : ℕ) : ℝ) < η * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : X * n - 1 < ((⌊X * n⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (X * n); linarith
  have : ((3 * ⌈η * n⌉₊ : ℕ) : ℝ) < ((⌊X * n⌋₊ : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

end NashWilliams18.SpreadF1
