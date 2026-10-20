/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.Linear
public import PartitionedTriangleAbsorption.Nibble.Geometry

/-! # Tail estimates for the star statistics of one round

All events live in the single product space `cubeMean (qv γ w)`, where triangle
`i` is retained with probability `γ * w i`. For a vertex `v` with star degree
`d = |star B v|` we bound the probability that

* few triangles through `v` are retained (`R`);
* the outside blockage mass `Y` is large;
* `Y` is moderate but many retained triangles are blocked (`Z`), using the
  conditional product law of the inside coins;
* a link degree reaches the truncation level `K`;
* the truncated conflict count `F̂` is large.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The hypotheses of one near-unit-load round. -/
structure RoundHyp (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (β δ γ : ℝ) : Prop where
  hB : ∀ i, triEdges (S.tri i) ⊆ B
  w0 : ∀ i, 0 ≤ w i
  wβ : ∀ i, w i ≤ β
  β0 : 0 < β
  load_lo : ∀ e ∈ B, 1 - δ ≤ S.load w e
  load_hi : ∀ e ∈ B, S.load w e ≤ 1 + δ
  δ0 : 0 ≤ δ
  δ1 : δ ≤ 1 / 4
  γ0 : 0 < γ
  γ1 : γ ≤ 1 / 128
  γβ : γ * β ≤ 1 / 4

/-- Retention probabilities `γ w`. -/
def qv (γ : ℝ) (w : Fin m → ℝ) : Fin m → ℝ := fun i => γ * w i

namespace RoundHyp

variable {S : TriSystem V m} {B : Finset (Sym2 V)} {w : Fin m → ℝ} {β δ γ : ℝ}
variable (H : RoundHyp S B w β δ γ)
include H

theorem hq : ∀ i, 0 ≤ qv γ w i ∧ qv γ w i ≤ 1 := by
  intro i
  have := H.w0 i; have := H.wβ i; have := H.γ0; have := H.γβ
  constructor
  · exact mul_nonneg H.γ0.le (H.w0 i)
  · unfold qv; nlinarith

theorem load_le (e : Sym2 V) : S.load w e ≤ 1 + δ := by
  by_cases he : e ∈ B
  · exact H.load_hi e he
  · have : S.edgeTris e = ∅ := by
      ext i
      simp only [S.mem_edgeTris, notMem_empty, iff_false]
      exact fun h => he (H.hB i h)
    rw [TriSystem.load, this, sum_empty]
    linarith [H.δ0]

theorem load_nonneg (e : Sym2 V) : 0 ≤ S.load w e :=
  sum_nonneg fun i _ => H.w0 i

theorem sum_through_le (v : V) :
    ∑ i ∈ S.through v, w i ≤ (1 + δ) * (star B v).card / 2 := by
  have h := S.sum_star_load B H.hB w v
  have : ∑ e ∈ star B v, S.load w e ≤ ∑ _e ∈ star B v, (1 + δ) :=
    sum_le_sum fun e _ => H.load_le e
  rw [sum_const, nsmul_eq_mul] at this
  linarith

theorem le_sum_through (v : V) :
    (1 - δ) * (star B v).card / 2 ≤ ∑ i ∈ S.through v, w i := by
  have h := S.sum_star_load B H.hB w v
  have : ∑ _e ∈ star B v, (1 - δ) ≤ ∑ e ∈ star B v, S.load w e :=
    sum_le_sum fun e he => H.load_lo e (filter_subset _ _ he)
  rw [sum_const, nsmul_eq_mul] at this
  linarith

theorem sum_through_le_d (v : V) : ∑ i ∈ S.through v, w i ≤ (star B v).card := by
  have := H.sum_through_le v
  have hd : (0 : ℝ) ≤ (star B v).card := Nat.cast_nonneg _
  have := H.δ1
  nlinarith

/-! ## Retained triangles through `v` -/

omit H in
theorem retained_card_eq (v : V) (ω : Fin m → Bool) :
    ((S.retainedThrough ω v).card : ℝ) = lin (S.through v) (fun _ => 1) ω :=
  card_filter_eq_lin _ ω

/-- Few retained triangles through `v`. -/
theorem R_tail (v : V) (hd : 0 < (star B v).card) :
    cubeProb (qv γ w) (fun ω => ((S.retainedThrough ω v).card : ℝ) < γ * (star B v).card / 4) ≤
      Real.exp (-(γ * (star B v).card / 64)) := by
  have hd0 : (0 : ℝ) < (star B v).card := by exact_mod_cast hd
  have hγ := H.γ0
  have hlo := H.le_sum_through v
  have hδ := H.δ1
  have hμeq : ∑ i ∈ S.through v, qv γ w i * 1 = γ * ∑ i ∈ S.through v, w i := by
    rw [mul_sum]; simp [qv]
  set μ := ∑ i ∈ S.through v, qv γ w i * 1 with hμ
  set a := γ * ((star B v).card : ℝ) / 4 with ha_def
  have ha : 0 < a := div_pos (mul_pos hγ hd0) (by norm_num)
  have hμlo : 3 * a / 2 ≤ μ := by
    rw [hμeq, ha_def]
    have : (1 - δ) * ((star B v).card : ℝ) / 2 * γ ≤ (∑ i ∈ S.through v, w i) * γ :=
      mul_le_mul_of_nonneg_right hlo hγ.le
    nlinarith
  have ht : 0 < μ - a := by linarith
  have h := lin_lower_tail (qv γ w) H.hq (S.through v) (fun _ => 1) 1 μ one_pos
    (fun i _ => ⟨zero_le_one, le_rfl⟩) (by rw [hμ]; simp) (μ - a) ht
  refine le_trans (cubeProb_mono _ H.hq ?_) (h.trans ?_)
  · intro ω hω
    rw [retained_card_eq] at hω
    rw [← hμ]
    linarith
  · apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have h2s : a ≤ 2 * (μ - a) := by linarith
    have hden : 0 < 2 * (μ + 1 * (μ - a)) := by linarith
    rw [le_div_iff₀ hden]
    have : γ * ((star B v).card : ℝ) / 64 = a / 16 := by rw [ha_def]; ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2s) (sub_nonneg.mpr h2s),
      mul_nonneg ha.le (sub_nonneg.mpr h2s)]

/-! ## Outside blockage -/

/-- Blockage weight of an outside triangle `U` at `v`. -/
def blockW (S : TriSystem V m) (w : Fin m → ℝ) (v : V) (U : Fin m) : ℝ :=
  ∑ i ∈ (S.through v).filter (fun i => S.Shares i U), w i

/-- Outside triangles at `v`. -/
def outside (S : TriSystem V m) (v : V) : Finset (Fin m) := univ.filter (fun U => v ∉ S.tri U)

/-- The outside blockage mass `Y_v`. -/
def Yv (S : TriSystem V m) (w : Fin m → ℝ) (v : V) (ω : Fin m → Bool) : ℝ :=
  lin (outside S v) (blockW S w v) ω

theorem blockW_nonneg (v : V) (U : Fin m) : 0 ≤ blockW S w v U :=
  sum_nonneg fun i _ => H.w0 i

theorem blockW_le (v : V) {U : Fin m} (hU : U ∈ outside S v) : blockW S w v U ≤ 3 * β := by
  have hvU : v ∉ S.tri U := by simpa [outside] using hU
  unfold blockW
  calc _ ≤ ∑ _i ∈ (S.through v).filter (fun i => S.Shares i U), β :=
        sum_le_sum fun i _ => H.wβ i
    _ = ((S.through v).filter (fun i => S.Shares i U)).card * β := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 3 * β := by
        have := S.card_through_shares_le hvU
        have hβ := H.β0
        have : (((S.through v).filter (fun i => S.Shares i U)).card : ℝ) ≤ 3 := by
          exact_mod_cast this
        nlinarith

omit H in
theorem through_outside_disjoint (v : V) : Disjoint (S.through v) (outside S v) := by
  rw [Finset.disjoint_left]
  intro i hi ho
  simp only [TriSystem.through, outside, mem_filter, mem_univ, true_and] at hi ho
  exact ho hi

/-- The mean outside blockage. -/
theorem Yv_mean_le (v : V) :
    ∑ U ∈ outside S v, qv γ w U * blockW S w v U ≤ γ * (star B v).card := by
  have hswap : ∑ U ∈ outside S v, qv γ w U * blockW S w v U =
      γ * ∑ i ∈ S.through v, w i *
        ∑ U ∈ univ.filter (fun U => v ∉ S.tri U ∧ S.Shares i U), w U := by
    have e1 : ∀ i, univ.filter (fun U => v ∉ S.tri U ∧ S.Shares i U) =
        (outside S v).filter (fun U => S.Shares i U) := by
      intro i; ext U; simp [outside]
    simp only [e1, qv, blockW, sum_filter, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro U _
    split_ifs <;> ring
  rw [hswap]
  have hinner : ∀ i ∈ S.through v,
      w i * ∑ U ∈ univ.filter (fun U => v ∉ S.tri U ∧ S.Shares i U), w U ≤ w i * (1 + δ) := by
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (H.w0 i)
    exact S.sum_outside_shares_le w H.w0 (by simpa [TriSystem.through] using hi) (1 + δ)
      (fun e _ => H.load_le e) (by linarith [H.δ0])
  have h1 := sum_le_sum hinner
  rw [← sum_mul] at h1
  have h2 := H.sum_through_le v
  have hd : (0 : ℝ) ≤ (star B v).card := Nat.cast_nonneg _
  have hs : 0 ≤ ∑ i ∈ S.through v, w i := sum_nonneg fun i _ => H.w0 i
  have := H.δ1; have := H.δ0; have hγ := H.γ0
  have h3 : (∑ i ∈ S.through v, w i) * (1 + δ) ≤ (star B v).card := by nlinarith
  nlinarith

/-- Upper tail of the outside blockage. -/
theorem Y_tail (v : V) (y0 t0 : ℝ) (ht0 : 0 < t0) (hy : γ * (star B v).card + t0 ≤ y0) :
    cubeProb (qv γ w) (fun ω => y0 ≤ Yv S w v ω) ≤
      Real.exp (-(t0 ^ 2 / (2 * (3 * β * (γ * (star B v).card) + 3 * β * t0)))) := by
  have hmean := H.Yv_mean_le v
  have hV : ∑ U ∈ outside S v, qv γ w U * blockW S w v U ^ 2 ≤
      3 * β * (γ * (star B v).card) := by
    calc _ ≤ ∑ U ∈ outside S v, 3 * β * (qv γ w U * blockW S w v U) := by
          apply sum_le_sum
          intro U hU
          have h0 := H.blockW_nonneg v U
          have h1 := H.blockW_le v hU
          have hq0 := (H.hq U).1
          rw [sq]
          nlinarith [mul_nonneg hq0 h0]
      _ = 3 * β * ∑ U ∈ outside S v, qv γ w U * blockW S w v U := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (by linarith [H.β0])
  have h := lin_upper_tail (qv γ w) H.hq (outside S v) (blockW S w v) (3 * β) _
    (by linarith [H.β0]) (fun U hU => ⟨H.blockW_nonneg v U, H.blockW_le v hU⟩) hV t0 ht0
  refine le_trans (cubeProb_mono _ H.hq ?_) h
  intro ω hω
  unfold Yv at hω
  linarith

end RoundHyp

end PartitionedTriangleAbsorption.Nibble
