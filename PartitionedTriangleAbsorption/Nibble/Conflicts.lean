/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.StarTails
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Blocked retained triangles, link degrees and truncated conflicts

* `Z_tail`: on the event `Y ≤ y0`, many blocked retained triangles are unlikely.
  The proof integrates out the inside coins (`cond_mgf_le`); the blocking
  indicators depend only on outside coins. No global event is conditioned on.
* `linkDeg_tail`: a link degree reaches `K` with probability at most `e^{-K/8}`.
* `Fhat_tail`: the truncated conflict count `F̂ = ∑ C(min(D_a,K),2)` has
  bounded differences `2K` on inside coins only, and concentrates.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- Indicator that triangle `i` is blocked from outside `v`. -/
noncomputable def blockInd (S : TriSystem V m) (v : V) (i : Fin m) (ω : Fin m → Bool) : ℝ :=
  if S.Blocked ω v i then 1 else 0

theorem exp_half_le : Real.exp (1 / 2) ≤ 7 / 4 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-! ## Truncation -/

/-- `C(min(d,K), 2)` as a real number. -/
noncomputable def clip (K d : ℕ) : ℝ := ((min d K).choose 2 : ℕ)

theorem clip_succ (K d : ℕ) : 0 ≤ clip K (d + 1) - clip K d ∧ clip K (d + 1) - clip K d ≤ K := by
  unfold clip
  by_cases h : d < K
  · rw [Nat.min_eq_left h.le, Nat.min_eq_left h, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    constructor
    · linarith [Nat.cast_nonneg (α := ℝ) d]
    · have : (d : ℝ) ≤ K := by exact_mod_cast h.le
      linarith
  · push Not at h
    rw [Nat.min_eq_right h, Nat.min_eq_right (h.trans (Nat.le_succ d))]
    simp

theorem clip_le_choose (K d : ℕ) : clip K d ≤ (d.choose 2 : ℕ) := by
  unfold clip
  exact_mod_cast Nat.choose_le_choose 2 (min_le_left d K)

namespace RoundHyp

variable {S : TriSystem V m} {B : Finset (Sym2 V)} {w : Fin m → ℝ} {β δ γ : ℝ}
variable (H : RoundHyp S B w β δ γ)
include H

omit H in
theorem Z_eq (v : V) (ω : Fin m → Bool) :
    ((S.blockedRetained ω v).card : ℝ) =
      ∑ i ∈ S.through v, (if ω i then blockInd S v i ω else 0) := by
  unfold TriSystem.blockedRetained TriSystem.retainedThrough blockInd
  rw [filter_filter, card_filter]
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases h1 : ω i = true <;> by_cases h2 : S.Blocked ω v i <;> simp [h1, h2]

omit H in
theorem blockInd_indepOf (v : V) (i : Fin m) : IndepOf (S.through v) (blockInd S v i) := by
  intro ω k b hk
  unfold blockInd TriSystem.Blocked
  have hvk : v ∈ S.tri k := by simpa [TriSystem.through] using hk
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hvj, hωj, hsh⟩
    have hjk : j ≠ k := fun h => hvj (h ▸ hvk)
    exact ⟨j, hvj, by rwa [Function.update_of_ne hjk] at hωj, hsh⟩
  · rintro ⟨j, hvj, hωj, hsh⟩
    have hjk : j ≠ k := fun h => hvj (h ▸ hvk)
    exact ⟨j, hvj, by rwa [Function.update_of_ne hjk], hsh⟩

/-- The blocked weight is at most the outside blockage mass. -/
theorem blocked_weight_le (v : V) (ω : Fin m → Bool) :
    ∑ i ∈ S.through v, qv γ w i * blockInd S v i ω ≤ γ * Yv S w v ω := by
  have hY : Yv S w v ω = ∑ i ∈ S.through v, ∑ U ∈ outside S v,
      (if ω U = true ∧ S.Shares i U then w i else 0) := by
    unfold Yv lin blockW
    rw [sum_comm]
    apply sum_congr rfl
    intro U _
    rw [sum_filter]
    by_cases hU : ω U = true
    · simp [hU]
    · simp [hU]
  rw [hY, mul_sum]
  apply sum_le_sum
  intro i _
  unfold blockInd qv
  split_ifs with hb
  · obtain ⟨U, hvU, hωU, hsh⟩ := hb
    have hUo : U ∈ outside S v := by simp [outside, hvU]
    have := single_le_sum (f := fun U => if ω U = true ∧ S.Shares i U then w i else 0)
      (fun U _ => by split_ifs; exacts [H.w0 i, le_rfl]) hUo
    simp only [hωU, hsh, and_self, ite_true] at this
    nlinarith [H.γ0]
  · have : 0 ≤ ∑ U ∈ outside S v, (if ω U = true ∧ S.Shares i U then w i else 0) :=
      sum_nonneg fun U _ => by split_ifs; exacts [H.w0 i, le_rfl]
    nlinarith [H.γ0]

/-- Blocked retained triangles, on the event of moderate outside blockage. -/
theorem Z_tail (v : V) (y0 z0 : ℝ) :
    cubeProb (qv γ w) (fun ω => Yv S w v ω ≤ y0 ∧ z0 ≤ (S.blockedRetained ω v).card) ≤
      Real.exp (-(z0 / 2) + 3 / 4 * (γ * y0)) := by
  classical
  set φ : (Fin m → Bool) → ℝ := fun ω => if Yv S w v ω ≤ y0 then 1 else 0 with hφ
  have hφ0 : ∀ ω, 0 ≤ φ ω := fun ω => by simp only [hφ]; split_ifs <;> norm_num
  have hφI : IndepOf (S.through v) φ := by
    intro ω k b hk
    simp only [hφ]
    rw [show Yv S w v (Function.update ω k b) = Yv S w v ω from
      lin_indepOf _ _ _ (through_outside_disjoint v) ω k b hk]
  have ha : ∀ i ∈ S.through v, IndepOf (S.through v) (blockInd S v i) :=
    fun i _ => blockInd_indepOf v i
  have ha01 : ∀ i ∈ S.through v, ∀ ω, 0 ≤ blockInd S v i ω ∧ blockInd S v i ω ≤ 1 := by
    intro i _ ω; unfold blockInd; split_ifs <;> norm_num
  have hmgf := cond_mgf_le (qv γ w) H.hq (1 / 2) (S.through v) (blockInd S v) ha ha01 φ hφ0 hφI
  have hpt : ∀ ω, (if Yv S w v ω ≤ y0 ∧ z0 ≤ ((S.blockedRetained ω v).card : ℝ) then (1 : ℝ)
      else 0) ≤ Real.exp (-(z0 / 2)) * (φ ω * Real.exp (1 / 2 *
        ∑ i ∈ S.through v, (if ω i then blockInd S v i ω else 0))) := by
    intro ω
    split_ifs with h
    · simp only [hφ, ite_eq_left h.1, one_mul]
      rw [← Real.exp_add, ← Z_eq]
      apply Real.one_le_exp
      linarith [h.2]
    · positivity
  have hpt2 : ∀ ω, φ ω * Real.exp ((Real.exp (1 / 2) - 1) *
      ∑ i ∈ S.through v, qv γ w i * blockInd S v i ω) ≤ Real.exp (3 / 4 * (γ * y0)) := by
    intro ω
    simp only [hφ]
    split_ifs with h
    · rw [one_mul]
      apply Real.exp_le_exp.mpr
      have h1 := H.blocked_weight_le v ω
      have h2 : 0 ≤ ∑ i ∈ S.through v, qv γ w i * blockInd S v i ω :=
        sum_nonneg fun i hi => mul_nonneg (H.hq i).1 (ha01 i hi ω).1
      have h3 := exp_half_le
      have h4 : 0 ≤ Real.exp (1 / 2) - 1 := by
        have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
      have hγ := H.γ0
      calc (Real.exp (1 / 2) - 1) * ∑ i ∈ S.through v, qv γ w i * blockInd S v i ω
          ≤ 3 / 4 * ∑ i ∈ S.through v, qv γ w i * blockInd S v i ω :=
            mul_le_mul_of_nonneg_right (by linarith) h2
        _ ≤ 3 / 4 * (γ * y0) := by nlinarith
    · rw [zero_mul]; positivity
  rw [cubeProb_def]
  calc _ ≤ cubeMean (qv γ w) (fun ω => Real.exp (-(z0 / 2)) * (φ ω * Real.exp (1 / 2 *
          ∑ i ∈ S.through v, (if ω i then blockInd S v i ω else 0)))) :=
        cubeMean_mono _ H.hq _ _ hpt
    _ = Real.exp (-(z0 / 2)) * cubeMean (qv γ w) (fun ω => φ ω * Real.exp (1 / 2 *
          ∑ i ∈ S.through v, (if ω i then blockInd S v i ω else 0))) := cubeMean_const_mul _ _ _
    _ ≤ Real.exp (-(z0 / 2)) * cubeMean (qv γ w) (fun ω => Real.exp (3 / 4 * (γ * y0))) := by
        gcongr
        exact hmgf.trans (cubeMean_mono _ H.hq _ _ hpt2)
    _ = _ := by rw [cubeMean_const, ← Real.exp_add]

/-! ## Link degrees -/

omit H in
theorem linkDeg_eq (v a : V) (hav : a ≠ v) (ω : Fin m → Bool) :
    (S.linkDeg ω v a : ℝ) = lin (S.edgeTris s(v, a)) (fun _ => 1) ω := by
  unfold TriSystem.linkDeg TriSystem.retainedThrough
  rw [filter_comm, S.through_filter_eq_edgeTris hav]
  exact card_filter_eq_lin _ ω

theorem linkDeg_mean_le (v a : V) :
    ∑ i ∈ S.edgeTris s(v, a), qv γ w i * 1 ≤ γ * (1 + δ) := by
  have : ∑ i ∈ S.edgeTris s(v, a), qv γ w i * 1 = γ * S.load w s(v, a) := by
    simp [qv, TriSystem.load, mul_sum]
  rw [this]
  exact mul_le_mul_of_nonneg_left (H.load_le _) H.γ0.le

/-- A link degree reaching the truncation level. -/
theorem linkDeg_tail (v a : V) (hav : a ≠ v) (K : ℕ) (hK : 1 ≤ K) :
    cubeProb (qv γ w) (fun ω => (K : ℝ) ≤ S.linkDeg ω v a) ≤ Real.exp (-((K : ℝ) / 8)) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set μ := ∑ i ∈ S.edgeTris s(v, a), qv γ w i * 1 with hμ
  have hμ0 : 0 ≤ μ := sum_nonneg fun i _ => by rw [mul_one]; exact (H.hq i).1
  have hμ1 : μ ≤ 1 / 2 := by
    have := H.linkDeg_mean_le v a
    have := H.γ1; have := H.δ1; have := H.γ0
    nlinarith
  have ht : 0 < (K : ℝ) - μ := by linarith
  have h := lin_upper_tail (qv γ w) H.hq (S.edgeTris s(v, a)) (fun _ => 1) 1 μ one_pos
    (fun i _ => ⟨zero_le_one, le_rfl⟩) (by rw [hμ]; simp) ((K : ℝ) - μ) ht
  refine le_trans (cubeProb_mono _ H.hq ?_) (h.trans ?_)
  · intro ω hω
    rw [linkDeg_eq v a hav] at hω
    rw [← hμ]; linarith
  · apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith

/-! ## Truncated conflicts -/

/-- The truncated conflict count `F̂_v`. -/
noncomputable def Fhat [Fintype V] (S : TriSystem V m) (v : V) (K : ℕ) (ω : Fin m → Bool) : ℝ :=
  ∑ a ∈ univ.erase v, clip K (S.linkDeg ω v a)

omit H in
theorem linkDeg_update (v a : V) (i : Fin m) (ω : Fin m → Bool) :
    S.linkDeg (Function.update ω i true) v a =
      S.linkDeg (Function.update ω i false) v a +
        (if i ∈ S.through v ∧ a ∈ S.tri i then 1 else 0) := by
  have key : ∀ ω' : Fin m → Bool, (S.linkDeg ω' v a : ℝ) =
      lin ((S.through v).filter (fun k => a ∈ S.tri k)) (fun _ => 1) ω' := by
    intro ω'
    unfold TriSystem.linkDeg TriSystem.retainedThrough
    rw [filter_comm]
    exact card_filter_eq_lin _ ω'
  have h := lin_update_sub ((S.through v).filter (fun k => a ∈ S.tri k)) (fun _ => 1) i ω
  rw [← key, ← key] at h
  have h' : (S.linkDeg (Function.update ω i true) v a : ℝ) =
      (S.linkDeg (Function.update ω i false) v a : ℝ) +
        ((if i ∈ S.through v ∧ a ∈ S.tri i then 1 else 0 : ℕ) : ℝ) := by
    rw [← sub_eq_iff_eq_add', h]
    simp only [mem_filter]
    split_ifs <;> simp
  exact_mod_cast h'

omit H in
theorem Fhat_coordBounded [Fintype V] (v : V) (K : ℕ) :
    CoordBounded (Fhat S v K) (fun i => if i ∈ S.through v then 2 * (K : ℝ) else 0) := by
  intro i ω
  unfold Fhat
  rw [← sum_sub_distrib]
  have hterm : ∀ a ∈ univ.erase v,
      0 ≤ clip K (S.linkDeg (Function.update ω i true) v a) -
        clip K (S.linkDeg (Function.update ω i false) v a) ∧
      clip K (S.linkDeg (Function.update ω i true) v a) -
        clip K (S.linkDeg (Function.update ω i false) v a) ≤
        if i ∈ S.through v ∧ a ∈ S.tri i then (K : ℝ) else 0 := by
    intro a _
    rw [linkDeg_update]
    split_ifs with h
    · exact clip_succ K _
    · simp
  have hsum0 : 0 ≤ ∑ a ∈ univ.erase v, (clip K (S.linkDeg (Function.update ω i true) v a) -
      clip K (S.linkDeg (Function.update ω i false) v a)) :=
    sum_nonneg fun a ha => (hterm a ha).1
  have hsum1 := sum_le_sum fun a ha => (hterm a ha).2
  rw [abs_of_nonneg hsum0]
  refine hsum1.trans ?_
  dsimp only
  split_ifs with hi
  · rw [← sum_filter]
    have : (univ.erase v).filter (fun a => i ∈ S.through v ∧ a ∈ S.tri i) = (S.tri i).erase v := by
      ext a; simp [hi, and_comm]
    rw [this, sum_const, nsmul_eq_mul, card_erase_of_mem (by simpa [TriSystem.through] using hi),
      S.card_tri]
    norm_num
  · apply le_of_eq
    apply sum_eq_zero
    intro a _
    simp [hi]

theorem conflicts_mean_le [Fintype V] (v : V) :
    cubeMean (qv γ w) (fun ω => (S.conflicts ω v : ℝ)) ≤ γ ^ 2 * (star B v).card := by
  unfold TriSystem.conflicts
  push_cast
  rw [cubeMean_sum]
  have hterm : ∀ a ∈ univ.erase v, cubeMean (qv γ w) (fun ω => ((S.linkDeg ω v a).choose 2 : ℝ)) ≤
      γ * (1 + δ) / 2 * ∑ i ∈ S.edgeTris s(v, a), qv γ w i := by
    intro a ha
    have hav : a ≠ v := (mem_erase.mp ha).1
    rw [cubeMean_congr _ (g := fun ω => lin (S.edgeTris s(v, a)) (fun _ => 1) ω *
      (lin (S.edgeTris s(v, a)) (fun _ => 1) ω - 1) / 2) (fun ω => by
        rw [Nat.cast_choose_two, linkDeg_eq v a hav])]
    rw [cubeMean_congr _ (g := fun ω => (1 / 2) * (lin (S.edgeTris s(v, a)) (fun _ => 1) ω *
      (lin (S.edgeTris s(v, a)) (fun _ => 1) ω - 1))) (fun ω => by ring), cubeMean_const_mul]
    have h1 := cubeMean_count_pairs_le (qv γ w) H.hq (S.edgeTris s(v, a))
    have h2 := H.linkDeg_mean_le v a
    simp only [mul_one] at h2
    have h3 : 0 ≤ ∑ i ∈ S.edgeTris s(v, a), qv γ w i := sum_nonneg fun i _ => (H.hq i).1
    nlinarith
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hlink : ∑ a ∈ univ.erase v, ∑ i ∈ S.edgeTris s(v, a), qv γ w i =
      γ * (2 * ∑ i ∈ S.through v, w i) := by
    rw [← S.sum_link_weights w v, mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [← S.through_filter_eq_edgeTris (mem_erase.mp ha).1, mul_sum]
    rfl
  rw [hlink]
  have h4 := H.sum_through_le v
  have h5 : 0 ≤ ∑ i ∈ S.through v, w i := sum_nonneg fun i _ => H.w0 i
  have hd : (0 : ℝ) ≤ (star B v).card := Nat.cast_nonneg _
  have := H.δ0; have := H.δ1; have hγ := H.γ0
  have h6 : (1 + δ) * (∑ i ∈ S.through v, w i) ≤ (star B v).card := by nlinarith
  have h7 : 0 ≤ γ ^ 2 := sq_nonneg γ
  nlinarith [mul_le_mul_of_nonneg_left h6 h7]

omit H in
theorem Fhat_le_conflicts [Fintype V] (v : V) (K : ℕ) (ω : Fin m → Bool) :
    Fhat S v K ω ≤ S.conflicts ω v := by
  unfold Fhat TriSystem.conflicts
  push_cast
  exact sum_le_sum fun a _ => clip_le_choose K _

/-- Upper tail of the truncated conflict count. -/
theorem Fhat_tail [Fintype V] (v : V) (K : ℕ) (hK : 1 ≤ K) (f0 t0 : ℝ) (ht0 : 0 < t0)
    (hf : γ ^ 2 * (star B v).card + t0 ≤ f0) :
    cubeProb (qv γ w) (fun ω => f0 ≤ Fhat S v K ω) ≤
      Real.exp (-(t0 ^ 2 / (2 * (4 * (K : ℝ) ^ 2 * (γ * (star B v).card) +
        2 * (K : ℝ) * t0)))) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL : 0 < 2 * (K : ℝ) := by linarith
  have h := cube_upper_tail (qv γ w) H.hq (Fhat S v K)
    (fun i => if i ∈ S.through v then 2 * (K : ℝ) else 0) (2 * K) hL
    (fun i => by split_ifs; exacts [⟨hL.le, le_rfl⟩, ⟨le_rfl, hL.le⟩])
    (Fhat_coordBounded v K) t0 ht0
  rw [sum_ite_sq] at h
  have hV : ∑ i ∈ S.through v, qv γ w i * (2 * (K : ℝ)) ^ 2 ≤
      4 * (K : ℝ) ^ 2 * (γ * (star B v).card) := by
    rw [← sum_mul]
    have : ∑ i ∈ S.through v, qv γ w i = γ * ∑ i ∈ S.through v, w i := by
      simp [qv, mul_sum]
    rw [this]
    have h1 := H.sum_through_le_d v
    have hγ := H.γ0
    nlinarith [sq_nonneg (K : ℝ), mul_le_mul_of_nonneg_left h1 hγ.le]
  have hmean : cubeMean (qv γ w) (Fhat S v K) ≤ γ ^ 2 * (star B v).card :=
    (cubeMean_mono _ H.hq _ _ (Fhat_le_conflicts v K)).trans (H.conflicts_mean_le v)
  refine le_trans (cubeProb_mono _ H.hq ?_) (h.trans (bernstein_mono _ _ _ _ hL ht0
    (sum_nonneg fun i _ => mul_nonneg (H.hq i).1 (sq_nonneg _)) hV))
  intro ω hω
  linarith

end RoundHyp

end PartitionedTriangleAbsorption.Nibble
