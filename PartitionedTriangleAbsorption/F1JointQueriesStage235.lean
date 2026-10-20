/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1GraphReserveStage234

/-! # One physical reserve for unary and pair queries

The same sampled edge set can control balance, degrees, common neighbours,
and the neighbours obstructed by a protected grandchild. Queries may overlap
each other; disjointness is required only between the blocks of one query.
This is a sampling lemma, not the full vortex-level producer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1JointQueriesStage235

open Finset MeasureTheory ProbabilityTheory L3F0
open scoped NNReal ENNReal

/-- Simultaneous counts of fully reserved blocks, with no independence
requirement BETWEEN queries. All blocks are actual subsets of the host. -/
theorem exists_joint_block_reserve {E K J : Type*} [Finite E] [DecidableEq E]
    (host : Finset E) (p : ℝ≥0) (hp : p ≤ 1)
    (I : Finset K) (Y : K → Finset J) (B : K → J → Finset E)
    (d : K → ℕ) (t m : K → ℝ)
    (hsub : ∀ k ∈ I, ∀ y ∈ Y k, B k y ⊆ host)
    (hcard : ∀ k ∈ I, ∀ y ∈ Y k, (B k y).card = d k)
    (hdis : ∀ k ∈ I, ∀ y ∈ Y k, ∀ z ∈ Y k,
      y ≠ z → Disjoint (B k y) (B k z))
    (ht : ∀ k ∈ I, 0 < t k) (hm : ∀ k ∈ I, 0 < m k)
    (hYm : ∀ k ∈ I, ((Y k).card : ℝ) ≤ m k)
    (htail : ∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k) < 1) :
    ∃ R ⊆ host, ∀ k ∈ I,
      |(((Y k).filter fun y => B k y ⊆ R).card : ℝ) -
        (p : ℝ) ^ d k * (Y k).card| < t k := by
  classical
  let := Fintype.ofFinite E
  let w : E → ℝ≥0 := fun _ => p
  have hw : ∀ e, w e ≤ 1 := fun _ => hp
  let μ := bernPi w hw
  let bad : K → Set (E → Bool) := fun k => {ω | t k ≤
    |∑ y ∈ Y k, blockInd (B k y) ω - ∑ y ∈ Y k, ∏ e ∈ B k y, (w e : ℝ)|}
  have hb : ∀ k ∈ I, μ.real (bad k) ≤ 2 * Real.exp (-2 * t k ^ 2 / m k) := by
    intro k hk
    exact tail_blocks w hw (B k) (Y k) (hdis k hk) (ht k hk) (hm k hk) (hYm k hk)
  have hsum : μ.real (⋃ k ∈ I, bad k) < 1 := by
    calc
      _ ≤ ∑ k ∈ I, μ.real (bad k) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k) := sum_le_sum hb
      _ < 1 := htail
  have hne : (⋃ k ∈ I, bad k) ≠ Set.univ := by
    intro h
    rw [h, measureReal_def, measure_univ, ENNReal.toReal_one] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  let R := host.filter fun e => ω e = true
  refine ⟨R, filter_subset _ _, ?_⟩
  intro k hk
  have hnot : ¬ t k ≤ |∑ y ∈ Y k, blockInd (B k y) ω -
      ∑ y ∈ Y k, ∏ e ∈ B k y, (w e : ℝ)| := by
    intro h
    exact hω (Set.mem_biUnion hk h)
  have hcount : (∑ y ∈ Y k, blockInd (B k y) ω) =
      (((Y k).filter fun y => B k y ⊆ R).card : ℝ) := by
    rw [card_filter, Nat.cast_sum]
    apply sum_congr rfl
    intro y hy
    have he : B k y ⊆ R ↔ ∀ e ∈ B k y, ω e = true := by
      constructor
      · intro h e he
        exact (mem_filter.mp (h he)).2
      · intro h e he
        exact mem_filter.mpr ⟨hsub k hk y hy he, h e he⟩
    simp only [blockInd, he, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hexp : (∑ y ∈ Y k, ∏ e ∈ B k y, (w e : ℝ)) =
      (p : ℝ) ^ d k * (Y k).card := by
    calc
      _ = ∑ y ∈ Y k, (p : ℝ) ^ d k := by
        apply sum_congr rfl
        intro y hy
        simp only [w, prod_const, hcard k hk y hy]
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
  rw [hcount, hexp] at hnot
  exact lt_of_not_ge hnot

variable {V : Type*} [DecidableEq V]

/-- Two-root queries really are disjoint blocks of physical unordered edges,
provided the query vertices avoid the roots. -/
theorem star_pair_disjoint (U : Finset V) (x y : V) (hx : x ∉ U) (hy : y ∉ U)
    {u v : V} (hu : u ∈ U) (huv : u ≠ v) :
    Disjoint ({s(x,u), s(y,u)} : Finset (Sym2 V)) {s(x,v), s(y,v)} := by
  rw [disjoint_left]
  intro e he hf
  simp only [mem_insert, mem_singleton] at he hf
  have hcross (a b : V) (hb : b ∉ U)
      (h : s(a,u) = s(b,v)) : False := by
    rcases Sym2.eq_iff.mp h with h | h
    · exact huv h.2
    · exact hb (h.2 ▸ hu)
  rcases he with rfl | rfl <;> rcases hf with hf | hf
  · exact hcross x x hx hf
  · exact hcross x y hy hf
  · exact hcross y x hx hf
  · exact hcross y y hy hf

/-- Complement pair tests follow from the three reserved tests. -/
theorem complement_pair_count (U A B : Finset V) :
    (U \ (A ∪ B)).card + (U ∩ A).card + (U ∩ B).card =
      U.card + (U ∩ A ∩ B).card := by
  have hc := card_union_add_card_inter (U ∩ A) (U ∩ B)
  have hu : (U ∩ A) ∪ (U ∩ B) = U ∩ (A ∪ B) := by
    ext v; simp only [mem_union, mem_inter]; tauto
  have hi : (U ∩ A) ∩ (U ∩ B) = U ∩ A ∩ B := by
    ext v; simp only [mem_inter]; tauto
  have hs := card_sdiff_add_card_inter U (A ∪ B)
  rw [hu, hi] at hc
  omega

/-- Corrected reserve plus nibble leftover: test only the genuinely sampled
bad vertices, not the entire protected grandchild. -/
theorem sampled_defect_after_correction (U Bad : Finset V)
    (R C Q : Finset (Sym2 V)) (x : V) :
    ((U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R ∪ C ∪ Q).card) ≤
      (U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R).card +
      (C.filter fun e => x ∈ e).card + (Q.filter fun e => x ∈ e).card := by
  have h := F1ReserveCorrectionStage231.corrected_target_growth U R (C ∪ Q) x
    (fun z => z ∈ Bad)
  have he : R ∪ (C ∪ Q) = R ∪ C ∪ Q := (union_assoc _ _ _).symm
  rw [he, filter_union] at h
  have hd := card_union_le (C.filter fun e => x ∈ e) (Q.filter fun e => x ∈ e)
  have hg := card_le_card (show (U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R ∪ C ∪ Q) ⊆
      ((U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R ∪ C ∪ Q) \
        (U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R)) ∪
        (U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R) from by
          intro z hz
          by_cases hr : z ∈ U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R
          · exact mem_union_right _ hr
          · exact mem_union_left _ (mem_sdiff.mpr ⟨hz, hr⟩))
  have hc := card_union_le
    ((U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R ∪ C ∪ Q) \
      (U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R))
    (U.filter fun z => z ∈ Bad ∧ s(x,z) ∈ R)
  omega

/-- The actual link obstruction is a sampled bad set. The internal reserve
contains every host edge in U except edges wholly inside the protected U'.
This converts its graph geometry to the defect used by the cover-down. -/
theorem physical_link_defect (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (U U' : Finset V) (R C Q I : Finset (Sym2 V))
    (x v : V) (c : Fin 4) (ρ ε : ℝ) (hρ : 0 ≤ ρ)
    (hI : ∀ z ∈ U, G.Adj v z → z ∉ U' → s(v, z) ∈ I)
    (hquery :
      |((U.filter fun z => (p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z)) ∧
          s(x, z) ∈ R).card : ℝ) -
        ρ * (U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z)).card| ≤ ε) :
    ((U.filter fun z => p z = c ∧ s(x,z) ∈ R ∪ C ∪ Q ∧
        ¬ (z ≠ v ∧ s(v,z) ∈ I)).card : ℝ) ≤
      ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ G.Adj v z).card) + ε +
        (C.filter fun e => x ∈ e).card + (Q.filter fun e => x ∈ e).card := by
  let Bad := U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z)
  have hsub : (U.filter fun z => p z = c ∧ s(x,z) ∈ R ∪ C ∪ Q ∧
        ¬ (z ≠ v ∧ s(v,z) ∈ I)) ⊆
      U.filter (fun z => z ∈ Bad ∧ s(x,z) ∈ R ∪ C ∪ Q) := by
    intro z hz
    obtain ⟨hzU, hzc, hzR, hn⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨hzU, mem_filter.mpr ⟨hzU, hzc, ?_⟩, hzR⟩
    by_cases hz : z ∈ U'
    · exact Or.inl hz
    · refine Or.inr ?_
      intro hadj
      exact hn ⟨hadj.ne.symm, hI z hzU hadj hz⟩
  have hb : Bad.card ≤ U'.card + (U.filter fun z => p z = c ∧ ¬ G.Adj v z).card := by
    apply (card_le_card (show Bad ⊆ U' ∪
      (U.filter fun z => p z = c ∧ ¬ G.Adj v z) from ?_)).trans (card_union_le _ _)
    intro z hz
    obtain ⟨hzU, hzc, hz | hz⟩ := mem_filter.mp hz
    · exact mem_union_left _ hz
    · exact mem_union_right _ (mem_filter.mpr ⟨hzU, hzc, hz⟩)
  have hs := (card_le_card hsub).trans (sampled_defect_after_correction U Bad R C Q x)
  have hc : U.filter (fun z => z ∈ Bad ∧ s(x,z) ∈ R) =
      U.filter (fun z => (p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z)) ∧ s(x,z) ∈ R) := by
    ext z
    simp only [Bad, mem_filter]
    tauto
  rw [hc] at hs
  have hsR : ((U.filter fun z => p z = c ∧ s(x,z) ∈ R ∪ C ∪ Q ∧
      ¬ (z ≠ v ∧ s(v,z) ∈ I)).card : ℝ) ≤
      (U.filter fun z => (p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z)) ∧ s(x,z) ∈ R).card +
      (C.filter fun e => x ∈ e).card + (Q.filter fun e => x ∈ e).card := by
    exact_mod_cast hs
  have hbR : (Bad.card : ℝ) ≤
      U'.card + (U.filter fun z => p z = c ∧ ¬ G.Adj v z).card := by exact_mod_cast hb
  have hmul := mul_le_mul_of_nonneg_left hbR hρ
  have hupper := (abs_le.mp hquery).2
  change _ - ρ * Bad.card ≤ ε at hupper
  linarith

end PartitionedTriangleAbsorption.F1JointQueriesStage235
