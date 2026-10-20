/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.L3F0VertexSample
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The strengthened one-step sampling lemma for the `F₁` vortex

`VInv p G A W a` is the level invariant: every class of `W` is within `a |W|` of `|W| / 4`,
and every `v ∈ W` misses at most `a |W|` vertices of `W` in every class `j` with `A (p v) j`
(`A` is the allowed-pair relation; it is instantiated with `AllowedT F1` downstream).

`vortex_sampling_step` (proved) samples `U ⊆ W` at rate `q = 3β/4` (strictly between `β/2`
and `β`) with the ported finite-query discrepancy lemma
`PartitionedTriangleAbsorption.L3F0.exists_subset_discrepancy`, tested ONLY on the
`4 |W| + 5` query sets of the current level (the level itself, its four classes and the actual
non-neighbour sets `{z ∈ W : p z = j, z ≁ v}` for `v ∈ W`).  So the union bound involves the
level size `|W|`, never the ambient vertex count.  With tolerance `t = s |W|` it gives

* `β|W|/2 ≤ |U| ≤ β|W|`;
* class deviation of `U` at most `(β a + 2 s) |W|` (absolute, parent units);
* `VInv p G A U (a + 6 s / β)` (relative to the child).

`sampling_union_bound` (proved) checks the failure budget for `s = |W|^{-1/4}`:
`(4m+5) · 2 exp(-2 (s m)^2 / m) < 1` once `m^{1/4} ≥ 3`.
-/

namespace NashWilliams18.SpreadF1

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vortex level invariant with relative error `a`. -/
def VInv (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Fin 4 → Fin 4 → Prop) (W : Finset V) (a : ℝ) : Prop :=
  (∀ j : Fin 4, |((W.filter fun z => p z = j).card : ℝ) - W.card / 4| ≤ a * W.card) ∧
  (∀ v ∈ W, ∀ j : Fin 4, A (p v) j →
    ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ a * W.card)

omit [Fintype V] [DecidableEq V] in
theorem VInv.mono {p : V → Fin 4} {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Fin 4 → Fin 4 → Prop} {W : Finset V} {a b : ℝ} (h : VInv p G A W a) (hab : a ≤ b) :
    VInv p G A W b := by
  have hW : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  refine ⟨fun j => (h.1 j).trans (by nlinarith), fun v hv j hj => (h.2 v hv j hj).trans
    (by nlinarith)⟩

/-- Query indices of a level: the level itself, its classes, the non-neighbour sets. -/
abbrev VQuery (V : Type) := Option (Fin 4 ⊕ (V × Fin 4))

/-- Query sets of a level `W`. -/
def vQuerySet (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    VQuery V → Finset V
  | none => W
  | some (Sum.inl j) => W.filter fun z => p z = j
  | some (Sum.inr (v, j)) => W.filter fun z => p z = j ∧ ¬ G.Adj v z

/-- The `4|W| + 5`-element family of queries actually tested at level `W`. -/
def vQueryIdx (W : Finset V) : Finset (VQuery V) :=
  insert none (((univ : Finset (Fin 4)).image fun j => some (Sum.inl j)) ∪
    ((W ×ˢ (univ : Finset (Fin 4))).image fun x => some (Sum.inr x)))

omit [Fintype V] in
theorem vQueryIdx_card (W : Finset V) : ((vQueryIdx W).card : ℝ) ≤ 4 * W.card + 5 := by
  have h1 := card_insert_le none (((univ : Finset (Fin 4)).image fun j => some (Sum.inl j)) ∪
    ((W ×ˢ (univ : Finset (Fin 4))).image fun x => (some (Sum.inr x) : VQuery V)))
  have h2 := card_union_le (((univ : Finset (Fin 4)).image fun j => (some (Sum.inl j) :
    VQuery V))) ((W ×ˢ (univ : Finset (Fin 4))).image fun x => (some (Sum.inr x) : VQuery V))
  have h3 := card_image_le (s := (univ : Finset (Fin 4)))
    (f := fun j => (some (Sum.inl j) : VQuery V))
  have h4 := card_image_le (s := W ×ˢ (univ : Finset (Fin 4)))
    (f := fun x => (some (Sum.inr x) : VQuery V))
  rw [card_product, card_univ, Fintype.card_fin] at h4
  rw [card_univ, Fintype.card_fin] at h3
  have : (vQueryIdx W).card ≤ 4 * W.card + 5 := by unfold vQueryIdx; omega
  exact_mod_cast this

/-- **The strengthened one-step sampling lemma** (proved).  From a level `W` with invariant
`a ≤ 1`, a rate `q = 3β/4` and a tolerance `s ≤ β/8` whose level-local failure budget is
`< 1`, there is a child `U ⊆ W` with the size window `[β|W|/2, β|W|]`, class deviation at most
`(βa + 2s)|W|`, and invariant `a + 6s/β` on `U`. -/
theorem vortex_sampling_step (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Fin 4 → Fin 4 → Prop) {β a s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hs0 : 0 < s) (hsβ : s ≤ β / 8) (W : Finset V) (hW : 0 < W.card)
    (hsmall : (4 * (W.card : ℝ) + 5) * (2 * Real.exp (-2 * (s * W.card) ^ 2 / W.card)) < 1)
    (hinv : VInv p G A W a) :
    ∃ U ⊆ W, β * W.card / 2 ≤ U.card ∧ (U.card : ℝ) ≤ β * W.card ∧
      (∀ j : Fin 4, |((U.filter fun z => p z = j).card : ℝ) - U.card / 4| ≤
        (β * a + 2 * s) * W.card) ∧
      VInv p G A U (a + 6 * s / β) := by
  set m : ℝ := (W.card : ℝ) with hm
  have hm0 : 0 < m := Nat.cast_pos.mpr hW
  set q : NNReal := ⟨3 * β / 4, by positivity⟩ with hq
  have hqv : ((q : NNReal) : ℝ) = 3 * β / 4 := rfl
  have hq1 : q ≤ 1 := by
    rw [← NNReal.coe_le_coe, hqv, NNReal.coe_one]; linarith
  have ht : 0 < s * m := by positivity
  have hsm : ((vQueryIdx W).card : ℝ) * (2 * Real.exp (-2 * (s * m) ^ 2 / W.card)) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (vQueryIdx_card W) (by positivity)) hsmall
  obtain ⟨U, hUW, hdisc⟩ := PartitionedTriangleAbsorption.L3F0.exists_subset_discrepancy W q
    hq1 (vQuerySet p G W) (vQueryIdx W) ht hW hsm
  -- unpacking the queries
  have hinterW : ∀ P : V → Prop, [DecidablePred P] →
      (W.filter P ∩ W) = W.filter P := fun P _ => inter_eq_left.mpr (filter_subset _ _)
  have hinterU : ∀ P : V → Prop, [DecidablePred P] →
      (W.filter P ∩ U) = U.filter P := fun P _ => by
    ext z; simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨-, h⟩, hz⟩; exact ⟨hz, h⟩
    · rintro ⟨hz, h⟩; exact ⟨⟨hUW hz, h⟩, hz⟩
  have hsize : |(U.card : ℝ) - 3 * β / 4 * m| < s * m := by
    have := hdisc none (mem_insert_self _ _)
    simp only [vQuerySet, inter_self, inter_eq_right.mpr hUW, hqv] at this
    exact this
  have hcls : ∀ j : Fin 4, |((U.filter fun z => p z = j).card : ℝ) -
      3 * β / 4 * (W.filter fun z => p z = j).card| < s * m := by
    intro j
    have := hdisc (some (Sum.inl j)) (mem_insert_of_mem (mem_union_left _
      (mem_image.mpr ⟨j, mem_univ _, rfl⟩)))
    simp only [vQuerySet, hinterW, hinterU, hqv] at this
    exact this
  have hnn : ∀ v ∈ W, ∀ j : Fin 4,
      ((U.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) <
      3 * β / 4 * (W.filter fun z => p z = j ∧ ¬ G.Adj v z).card + s * m := by
    intro v hv j
    have := hdisc (some (Sum.inr (v, j))) (mem_insert_of_mem (mem_union_right _
      (mem_image.mpr ⟨(v, j), mem_product.mpr ⟨hv, mem_univ _⟩, rfl⟩)))
    simp only [vQuerySet, hinterW, hinterU, hqv] at this
    linarith [(abs_lt.mp this).2]
  obtain ⟨hs1, hs2⟩ := abs_lt.mp hsize
  have hβs : 6 * s / β ≤ 3 / 4 := by
    rw [div_le_iff₀ hβ0]; linarith
  have hUpos : 3 * β / 4 * m - s * m ≤ U.card := by linarith
  -- class deviation in parent units
  have hclsdev : ∀ j : Fin 4, |((U.filter fun z => p z = j).card : ℝ) - U.card / 4| ≤
      3 * β / 4 * a * m + 5 / 4 * (s * m) := by
    intro j
    obtain ⟨c1, c2⟩ := abs_lt.mp (hcls j)
    obtain ⟨w1, w2⟩ := abs_le.mp (hinv.1 j)
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨U, hUW, by nlinarith, by nlinarith, fun j => (hclsdev j).trans (by nlinarith), ?_, ?_⟩
  · intro j
    refine (hclsdev j).trans ?_
    -- `(a + 6s/β) |U| ≥ (a + 6s/β)(qm - sm)`
    have hk : 0 ≤ a + 6 * s / β := by positivity
    have h6 : 6 * s / β * β = 6 * s := by field_simp
    have := mul_le_mul_of_nonneg_left hUpos hk
    nlinarith
  · intro v hv j hj
    have h1 := hnn v (hUW hv) j
    have h2 := hinv.2 v (hUW hv) j hj
    have hk : 0 ≤ a + 6 * s / β := by positivity
    have h6 : 6 * s / β * β = 6 * s := by field_simp
    have := mul_le_mul_of_nonneg_left hUpos hk
    nlinarith

/-- The level-local failure budget for `s = m^{-1/4}` (proved): if `m^{1/4} ≥ 3` then
`(4m+5) · 2 exp(-2 (s m)^2 / m) < 1`. -/
theorem sampling_union_bound (m : ℝ) (hm : 3 ≤ Real.sqrt (Real.sqrt m)) :
    (4 * m + 5) * (2 * Real.exp (-2 * ((1 / Real.sqrt (Real.sqrt m)) * m) ^ 2 / m)) < 1 := by
  set x := Real.sqrt (Real.sqrt m) with hx
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < m := by
    by_contra h
    push_neg at h
    have : Real.sqrt m = 0 := Real.sqrt_eq_zero'.mpr h
    rw [hx, this, Real.sqrt_zero] at hm; linarith
  have hy : Real.sqrt m = x ^ 2 := by
    rw [hx, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hmx : m = x ^ 4 := by
    have := Real.sq_sqrt hm0.le
    rw [hy] at this; rw [← this]; ring
  have hexp : -2 * ((1 / x) * m) ^ 2 / m = -(2 * x ^ 2) := by
    rw [hmx]; field_simp
  rw [hexp]
  have hE := Real.pow_div_factorial_le_exp (x := 2 * x ^ 2) (by positivity) 4
  norm_num [Nat.factorial] at hE
  have hpos := Real.exp_pos (2 * x ^ 2)
  rw [Real.exp_neg]
  rw [hmx]
  have hx3 : 9 ≤ x ^ 2 := by nlinarith
  rw [← div_eq_mul_inv, mul_div_assoc', div_lt_one hpos]
  set y := x ^ 2 with hydef
  have hx4 : x ^ 4 = y ^ 2 := by rw [hydef]; ring
  have hE' : (2 * y) ^ 4 / 24 ≤ Real.exp (2 * y) := hE
  rw [hx4]
  have h1 : (4 * y ^ 2 + 5) * 2 < (2 * y) ^ 4 / 24 := by
    have h81 : 81 ≤ y ^ 2 := by nlinarith
    nlinarith [mul_le_mul h81 h81 (by norm_num) (by positivity)]
  linarith

end NashWilliams18.SpreadF1
