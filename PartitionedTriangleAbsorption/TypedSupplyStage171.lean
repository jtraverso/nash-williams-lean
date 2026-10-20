/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.NearConsumer

/-! # Type supply in the first physical nibble round

The input consists of fractional weights, not a packing already having many
copies of each type. A collision is counted using two distinct independent
coins. The resulting supply event can be intersected with any good-round event;
no independence between those events is asserted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedSupplyStage171

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {V : Type*} [DecidableEq V] {m : ℕ}

def neighbors (S : TriSystem V m) (i : Fin m) : Finset (Fin m) :=
  univ.filter (fun j => j ≠ i ∧ S.Shares i j)

def lost (S : TriSystem V m) (J : Finset (Fin m)) (ω : Fin m → Bool) : Finset (Fin m) :=
  (J.filter fun i => ω i = true) \ S.packing ω

def pairs (S : TriSystem V m) (J : Finset (Fin m)) (ω : Fin m → Bool) : ℝ :=
  ∑ i ∈ J, (if ω i then (1 : ℝ) else 0) * lin (neighbors S i) (fun _ => 1) ω

/-- The shared-edge neighborhood has weight at most the sum of three edge loads. -/
theorem neighbor_weight_le (S : TriSystem V m) (w : Fin m → ℝ) (L : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hload : ∀ e ∈ (univ.biUnion fun i => Nibble.triEdges (S.tri i)), S.load w e ≤ L)
    (i : Fin m) : ∑ j ∈ neighbors S i, w j ≤ 3 * L := by
  have hpt : ∀ j ∈ neighbors S i,
      w j ≤ ∑ e ∈ Nibble.triEdges (S.tri i), if e ∈ Nibble.triEdges (S.tri j) then w j else 0 := by
    intro j hj
    obtain ⟨e, hei, hej⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2.2
    simpa [hej] using (single_le_sum
      (f := fun e => if e ∈ Nibble.triEdges (S.tri j) then w j else 0)
      (fun e _ => ite_nonneg (hw j) le_rfl) hei)
  calc ∑ j ∈ neighbors S i, w j
      ≤ ∑ j ∈ neighbors S i, ∑ e ∈ Nibble.triEdges (S.tri i),
          if e ∈ Nibble.triEdges (S.tri j) then w j else 0 := sum_le_sum hpt
    _ = ∑ e ∈ Nibble.triEdges (S.tri i), ∑ j ∈ neighbors S i,
          if e ∈ Nibble.triEdges (S.tri j) then w j else 0 := sum_comm
    _ ≤ ∑ e ∈ Nibble.triEdges (S.tri i), S.load w e := by
      apply sum_le_sum
      intro e _
      unfold TriSystem.load TriSystem.edgeTris
      rw [sum_filter]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => by
        split_ifs; exacts [hw j, le_rfl])
    _ ≤ ∑ _e ∈ Nibble.triEdges (S.tri i), L := by
      apply sum_le_sum
      intro e he
      exact hload e (mem_biUnion.mpr ⟨i, mem_univ i, he⟩)
    _ = 3 * L := by rw [sum_const, card_triEdges (S.card_tri i)]; simp

/-- Every non-isolated retained copy has at least one distinct retained neighbor. -/
theorem lost_card_le_pairs (S : TriSystem V m) (J : Finset (Fin m)) (ω : Fin m → Bool) :
    ((lost S J ω).card : ℝ) ≤ pairs S J ω := by
  classical
  unfold lost pairs
  rw [card_sdiff, card_filter]
  have heq : (S.packing ω ∩ (J.filter fun i => ω i = true)).card =
      (J.filter fun i => S.Isolated ω i).card := by
    congr 1
    ext i
    simp only [mem_inter, mem_filter, TriSystem.packing, mem_univ, true_and]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, ⟨h.1, h.2.1⟩⟩⟩
  rw [heq, card_filter]
  have hc : (∑ i ∈ J, if S.Isolated ω i then 1 else 0) ≤
      ∑ i ∈ J, if ω i = true then 1 else 0 := by
    apply sum_le_sum
    intro i _
    split_ifs with h1 h2 <;> simp_all [TriSystem.Isolated]
  rw [Nat.cast_sub hc]
  push_cast
  rw [← sum_sub_distrib]
  apply sum_le_sum
  intro i _
  by_cases hi : ω i = true
  · by_cases his : S.Isolated ω i
    · simp [hi, his, lin_nonneg (neighbors S i) (fun _ => 1) (by intros; norm_num) ω]
    · have hb : ∃ j, j ≠ i ∧ ω j = true ∧ S.Shares i j := by
        by_contra h
        apply his
        refine ⟨hi, fun j hji hj => ?_⟩
        exact fun hsh => h ⟨j, hji, hj, hsh⟩
      obtain ⟨j, hji, hj, hsh⟩ := hb
      have hjn : j ∈ neighbors S i := by simp [neighbors, hji, hsh]
      have hlin : 1 ≤ lin (neighbors S i) (fun _ => 1) ω := by
        unfold lin
        simpa [hj] using single_le_sum
          (f := fun j => if ω j then (1 : ℝ) else 0)
          (fun j _ => ite_nonneg zero_le_one le_rfl) hjn
      simpa [hi, his] using hlin
  · have his : ¬ S.Isolated ω i := fun h => hi h.1
    simp [hi, his]

/-- The expected collision loss is O(gamma) times the retained type mass. -/
theorem mean_lost_le (S : TriSystem V m) (J : Finset (Fin m))
    (w : Fin m → ℝ) (γ L : ℝ) (hγ : 0 ≤ γ) (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i, 0 ≤ γ * w i ∧ γ * w i ≤ 1)
    (hload : ∀ e ∈ (univ.biUnion fun i => Nibble.triEdges (S.tri i)), S.load w e ≤ L) :
    cubeMean (fun i => γ * w i) (fun ω => ((lost S J ω).card : ℝ)) ≤
      3 * γ * L * ∑ i ∈ J, γ * w i := by
  refine (cubeMean_mono _ hq _ _ (lost_card_le_pairs S J)).trans ?_
  unfold pairs
  rw [cubeMean_sum]
  have hi : ∀ i, IndepOf {i} (lin (neighbors S i) (fun _ => 1)) := by
    intro i
    apply lin_indepOf
    simp [neighbors]
  simp only [cubeMean_coord_mul _ _ _ (hi _), cubeMean_lin, mul_one]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (neighbor_weight_le S w L hw hload i) hγ
  rw [mul_sum] at h
  calc (γ * w i) * ∑ j ∈ neighbors S i, γ * w j
      ≤ (γ * w i) * (γ * (3 * L)) :=
        mul_le_mul_of_nonneg_left h (hq i).1
    _ = 3 * γ * L * (γ * w i) := by ring

/-- Markov on the finite product measure, without conditioning on a good event. -/
theorem count_markov {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (t : ℝ) :
    t * cubeProb q (fun ω => t ≤ f ω) ≤ cubeMean q f := by
  classical
  rw [cubeProb_def, ← cubeMean_const_mul]
  apply cubeMean_mono _ hq
  intro ω
  split_ifs with h
  · simpa using h
  · simpa using hf ω

theorem collision_probability_le (S : TriSystem V m) (J : Finset (Fin m))
    (w : Fin m → ℝ) (γ L : ℝ) (hγ : 0 ≤ γ) (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i, 0 ≤ γ * w i ∧ γ * w i ≤ 1)
    (hload : ∀ e ∈ (univ.biUnion fun i => Nibble.triEdges (S.tri i)), S.load w e ≤ L)
    (hμ : 0 < ∑ i ∈ J, γ * w i) :
    cubeProb (fun i => γ * w i)
      (fun ω => (∑ i ∈ J, γ * w i) / 4 ≤ ((lost S J ω).card : ℝ)) ≤ 12 * γ * L := by
  have hm := count_markov (fun i => γ * w i) hq
    (fun ω => ((lost S J ω).card : ℝ)) (fun ω => Nat.cast_nonneg _)
    ((∑ i ∈ J, γ * w i) / 4)
  have he := mean_lost_le S J w γ L hγ hw hq hload
  nlinarith

theorem retained_lower_probability (q : Fin m → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (J : Finset (Fin m)) (hμ : 0 < ∑ i ∈ J, q i) :
    cubeProb q (fun ω => ((J.filter fun i => ω i = true).card : ℝ) ≤
      (∑ i ∈ J, q i) / 2) ≤ Real.exp (-(∑ i ∈ J, q i) / 12) := by
  have h := lin_lower_tail q hq J (fun _ => 1) 1 (∑ i ∈ J, q i)
    (by norm_num) (by intros; norm_num) (by simp) ((∑ i ∈ J, q i) / 2)
    (div_pos hμ (by norm_num))
  have hb := cubeProb_mono q hq
    (P := fun ω => ((J.filter fun i => ω i = true).card : ℝ) ≤ (∑ i ∈ J, q i) / 2)
    (Q := fun ω => lin J (fun _ => 1) ω + (∑ i ∈ J, q i) / 2 ≤
      ∑ i ∈ J, q i) (fun ω hω => by
        simp (config := { failIfUnchanged := false }) only at hω ⊢
        rw [← card_filter_eq_lin]
        linarith)
  simp only [mul_one, one_mul] at h
  have heq : -(((∑ i ∈ J, q i) / 2) ^ 2 /
      (2 * ((∑ i ∈ J, q i) + ((∑ i ∈ J, q i) / 2)))) =
      -(∑ i ∈ J, q i) / 12 := by field_simp; ring
  rw [heq] at h
  exact hb.trans h

/-- A finite union bound retains type supply and an arbitrary round invariant. -/
theorem exists_supply_and_good {ι : Type*} [Fintype ι]
    (S : TriSystem V m) (J : ι → Finset (Fin m)) (w : Fin m → ℝ)
    (γ L : ℝ) (hγ : 0 ≤ γ) (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i, 0 ≤ γ * w i ∧ γ * w i ≤ 1)
    (hload : ∀ e ∈ (univ.biUnion fun i => Nibble.triEdges (S.tri i)), S.load w e ≤ L)
    (hμ : ∀ t, 0 < ∑ i ∈ J t, γ * w i)
    (Good : (Fin m → Bool) → Prop)
    (hbudget : cubeProb (fun i => γ * w i) (fun ω => ¬ Good ω) +
      ∑ t, (Real.exp (-(∑ i ∈ J t, γ * w i) / 12) + 12 * γ * L) < 1) :
    ∃ ω, Good ω ∧ ∀ t,
      (∑ i ∈ J t, γ * w i) / 4 ≤ ((J t ∩ S.packing ω).card : ℝ) := by
  classical
  let Bad : ι → (Fin m → Bool) → Prop := fun t ω =>
    ((J t).filter fun i => ω i = true).card ≤ (∑ i ∈ J t, γ * w i) / 2 ∨
      (∑ i ∈ J t, γ * w i) / 4 ≤ ((lost S (J t) ω).card : ℝ)
  have hp : ∀ t, cubeProb (fun i => γ * w i) (Bad t) ≤
      Real.exp (-(∑ i ∈ J t, γ * w i) / 12) + 12 * γ * L := by
    intro t
    exact (cubeProb_or_le _ hq _ _).trans (add_le_add
      (retained_lower_probability _ hq (J t) (hμ t))
      (collision_probability_le S (J t) w γ L hγ hw hq hload (hμ t)))
  have hb := cubeProb_or_le (fun i => γ * w i) hq (fun ω => ¬ Good ω)
    (fun ω => ∃ t ∈ (univ : Finset ι), Bad t ω)
  have hu := cubeProb_exists_le (fun i => γ * w i) hq univ Bad
  have htotal : cubeProb (fun i => γ * w i)
      (fun ω => ¬ Good ω ∨ ∃ t ∈ (univ : Finset ι), Bad t ω) < 1 := by
    exact lt_of_le_of_lt (hb.trans (add_le_add_right
      (hu.trans (sum_le_sum fun t _ => hp t)) _)) hbudget
  obtain ⟨ω, hω⟩ := exists_not_of_cubeProb_lt_one _ _ htotal
  refine ⟨ω, by tauto, fun t => ?_⟩
  have hnot : ¬ Bad t ω := fun h => hω (Or.inr ⟨t, mem_univ t, h⟩)
  have hret : (∑ i ∈ J t, γ * w i) / 2 <
      (((J t).filter fun i => ω i = true).card : ℝ) := by
    exact lt_of_not_ge (fun h => hnot (Or.inl h))
  have hlost : ((lost S (J t) ω).card : ℝ) < (∑ i ∈ J t, γ * w i) / 4 := by
    exact lt_of_not_ge (fun h => hnot (Or.inr h))
  have hsub : J t ∩ S.packing ω ⊆ (J t).filter fun i => ω i = true := by
    intro i hi
    have his : S.Isolated ω i := by simpa [TriSystem.packing] using (mem_inter.mp hi).2
    exact mem_filter.mpr ⟨(mem_inter.mp hi).1, his.1⟩
  have hid : lost S (J t) ω = ((J t).filter fun i => ω i = true) \ (J t ∩ S.packing ω) := by
    ext i
    simp [lost]
    tauto
  have hcard := card_sdiff_add_card_eq_card hsub
  rw [← hid] at hcard
  have hcardR : ((lost S (J t) ω).card : ℝ) + (J t ∩ S.packing ω).card =
      ((J t).filter fun i => ω i = true).card := by exact_mod_cast hcard
  linarith

end PartitionedTriangleAbsorption.TypedSupplyStage171

