/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.NearLoadRound

/-! # Restricting a triangle system to surviving triangles, and the schedule

`reindex S s` is the triangle system of the triangles in `s`, indexed by
`Fin s.card`; `reidx s k` is the original index. Each round of the iteration
uses a fresh product space on the current surviving system.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The original index of the `k`-th element of `s`. -/
noncomputable def reidx (s : Finset (Fin m)) (k : Fin s.card) : Fin m := (s.equivFin.symm k : Fin m)

theorem reidx_mem (s : Finset (Fin m)) (k : Fin s.card) : reidx s k ∈ s :=
  (s.equivFin.symm k).2

theorem reidx_injective (s : Finset (Fin m)) : Function.Injective (reidx s) :=
  fun _ _ h => s.equivFin.symm.injective (Subtype.ext h)

/-- The triangle system restricted to `s`. -/
noncomputable def TriSystem.reindex (S : TriSystem V m) (s : Finset (Fin m)) :
    TriSystem V s.card where
  tri k := S.tri (reidx s k)
  card_tri _ := S.card_tri _
  tri_inj := fun _ _ h => reidx_injective s (S.tri_inj h)

theorem sum_reidx (s : Finset (Fin m)) (f : Fin m → ℝ) :
    ∑ k : Fin s.card, f (reidx s k) = ∑ i ∈ s, f i := by
  rw [← Finset.sum_coe_sort s f]
  exact Equiv.sum_comp s.equivFin.symm (fun x => f x)

theorem sum_reidx_filter (s : Finset (Fin m)) (p : Fin m → Prop) [DecidablePred p]
    (f : Fin m → ℝ) :
    ∑ k ∈ univ.filter (fun k => p (reidx s k)), f (reidx s k) = ∑ i ∈ s.filter p, f i := by
  rw [sum_filter, sum_filter]
  exact sum_reidx s (fun i => if p i then f i else 0)

theorem reindex_load (S : TriSystem V m) (s : Finset (Fin m)) (w : Fin m → ℝ) (e : Sym2 V) :
    (S.reindex s).load (fun k => w (reidx s k)) e =
      ∑ i ∈ s.filter (fun i => e ∈ triEdges (S.tri i)), w i := by
  unfold TriSystem.load TriSystem.edgeTris
  exact sum_reidx_filter s (fun i => e ∈ triEdges (S.tri i)) w

theorem reindex_availLoad (S : TriSystem V m) (s : Finset (Fin m)) (B : Finset (Sym2 V))
    (w : Fin m → ℝ) (e : Sym2 V) (ω : Fin s.card → Bool) :
    availLoad (S.reindex s) B (fun k => w (reidx s k)) e ω =
      ∑ i ∈ s.filter (fun i => e ∈ triEdges (S.tri i) ∧
        triEdges (S.tri i) ⊆ (S.reindex s).untouched B ω), w i := by
  unfold availLoad TriSystem.edgeTris
  rw [filter_filter]
  exact sum_reidx_filter s (fun i => e ∈ triEdges (S.tri i) ∧
    triEdges (S.tri i) ⊆ (S.reindex s).untouched B ω) w

theorem reindex_packEdges (S : TriSystem V m) (s : Finset (Fin m)) (ω : Fin s.card → Bool) :
    (S.reindex s).packEdges ω =
      (((S.reindex s).packing ω).image (reidx s)).biUnion (fun i => triEdges (S.tri i)) := by
  unfold TriSystem.packEdges
  rw [image_biUnion]
  rfl

/-! ## The schedule -/

/-- Parameters of the finite schedule, fixed before the graph order. -/
theorem schedule_params (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ γ : ℝ, ∃ r : ℕ, 0 < γ ∧ γ ≤ 1 / 128 ∧ 1 ≤ r ∧
      (1 - γ / 8) ^ r ≤ η / 2 ∧ 24 * (r : ℝ) * γ ^ 2 ≤ η / 4 := by
  set L := Real.log (2 / η) with hL
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hη0]; linarith)
  set γ := min (1 / 128) (η / (768 * (L + 1))) with hγ
  have hγ0 : 0 < γ := lt_min (by norm_num) (by positivity)
  have hγ1 : γ ≤ 1 / 128 := min_le_left _ _
  have hγ2 : γ ≤ η / (768 * (L + 1)) := min_le_right _ _
  set r := ⌈8 * L / γ⌉₊ with hr
  have hr1 : 8 * L / γ ≤ r := Nat.le_ceil _
  have hr2 : (r : ℝ) < 8 * L / γ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hr0 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr1
    exact_mod_cast this
  refine ⟨γ, r, hγ0, hγ1, hr0, ?_, ?_⟩
  · have h1 : 1 - γ / 8 ≤ Real.exp (-(γ / 8)) := by
      have := Real.add_one_le_exp (-(γ / 8)); linarith
    have h2 : (1 - γ / 8) ^ r ≤ Real.exp (-(γ / 8)) ^ r :=
      pow_le_pow_left₀ (by linarith) h1 r
    rw [← Real.exp_nat_mul] at h2
    have h3 : L ≤ r * (γ / 8) := by
      rw [div_le_iff₀ hγ0] at hr1; nlinarith
    have h4 : Real.exp (-L) = η / 2 := by
      rw [hL, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    calc (1 - γ / 8) ^ r ≤ Real.exp (r * -(γ / 8)) := h2
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = η / 2 := h4
  · have h1 : (r : ℝ) * γ ≤ 8 * L + γ := by
      have := mul_lt_mul_of_pos_right hr2 hγ0
      rw [add_mul, div_mul_cancel₀ _ hγ0.ne'] at this; linarith
    have h2 : 768 * γ * (L + 1) ≤ η := by
      rw [le_div_iff₀ (by positivity)] at hγ2; linarith
    have h3 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 24 * γ by positivity)
    nlinarith

end PartitionedTriangleAbsorption.Nibble
