/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveTwoBlockTrialsStage198
public import PartitionedTriangleAbsorption.FiniteBernoulliTail
public import PartitionedTriangleAbsorption.PhysicalStarTail

/-! # Probability bounds for sampled packing-triangle coordinates

The coordinates in this module may be triangles, not individual physical
edges. All bounds use one actual measure and its independent coordinates.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveBlockTailsStage199

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks

noncomputable def successes {E I : Type*} (C : Finset I) (blocks : I → Finset E)
    (ω : E → Bool) : Finset I := C.filter fun i => ∀ e ∈ blocks i, ω e = true

theorem successes_card_eq_sum {E I : Type*} (C : Finset I) (blocks : I → Finset E)
    (ω : E → Bool) :
    ((successes C blocks ω).card : ℝ) =
      ∑ i : C, (blockEvent (fun e => {ω : E → Bool | ω e = true})
        (blocks i.val)).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  simp only [Set.indicator_apply, blockEvent, Set.mem_iInter, Set.mem_setOf_eq]
  rw [Finset.sum_coe_sort C (fun i : I => if ∀ e ∈ blocks i, ω e = true then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  rfl

theorem two_block_lower_tail {E I : Type*}
    (μ : Measure (E → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ)
    (C : Finset I) (hC : C.Nonempty) (blocks : I → Finset E)
    (hcard : ∀ i ∈ C, (blocks i).card = 2)
    (hdis : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (blocks i) (blocks j)) :
    μ.real {ω | ((successes C blocks ω).card : ℝ) ≤ ρ ^ 2 * C.card / 2} ≤
      Real.exp (-ρ ^ 4 * C.card / 2) := by
  classical
  have : Nonempty C := hC.to_subtype
  let A := fun i : C => blockEvent (fun e => {ω : E → Bool | ω e = true}) (blocks i.val)
  have hpair : Pairwise (fun i j : C => Disjoint (blocks i.val) (blocks j.val)) := by
    intro i j hij
    exact hdis i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have hblocks : iIndepSet A μ := independent_blocks _ μ
    (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) hind _ hpair
  have hreal : ∀ i : C, μ.real (A i) = ρ ^ 2 := by
    intro i
    rw [measureReal_def, block_probability _ μ hind _ hmarg, hcard i.val i.property,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ]
  have hb := FiniteBernoulliTail.lower_half_mean μ A
    (fun i => blockEvent_measurable _
      (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) _) hblocks
    (ρ ^ 2) (sq_nonneg ρ) hreal
  have hc : (Fintype.card C : ℝ) = C.card := by simp
  rw [hc, ← pow_mul] at hb
  norm_num only at hb
  refine le_trans (measureReal_mono ?_) hb
  intro ω hω
  change ((successes C blocks ω).card : ℝ) ≤ _ at hω
  rw [successes_card_eq_sum] at hω
  exact hω

theorem triangle_block_count_upper_tail {E : Type*}
    (μ : Measure (E → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ)
    (B : Finset E) (n : ℝ) (hn : 0 < n) (hcard : 2 * (B.card : ℝ) ≤ n) :
    μ.real {ω | 2 * ρ * n ≤ 2 * ((B.filter (fun e => ω e = true)).card : ℝ)} ≤
      Real.exp (-ρ ^ 2 * n) := by
  have hb := PhysicalStarTail.retained_count_upper_tail μ hind ρ hρ hmarg B
    (n / 2) (by positivity) (by linarith)
  have heq : {ω : E → Bool | 2 * ρ * n ≤ 2 * ((B.filter (fun e => ω e = true)).card : ℝ)} =
      {ω : E → Bool | 2 * ρ * (n / 2) ≤ ((B.filter (fun e => ω e = true)).card : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [heq]
  have hexp : -(2 * ρ ^ 2 * (n / 2)) = -ρ ^ 2 * n := by ring
  rw [hexp] at hb
  exact hb


end PartitionedTriangleAbsorption.ReserveBlockTailsStage199
