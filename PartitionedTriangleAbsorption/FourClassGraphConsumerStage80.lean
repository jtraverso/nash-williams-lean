/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassSeedStage80

/-! # Four-class decomposition from graph data alone

The uniform seed is constructed on the complete host and restricted to its
sparse deletion. The original integral divisibility remains explicit. No
fractional weights or geometric intermediates appear in the public input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassGraphConsumerStage80

open Finset ClassRepresentativesStage65 TypedApplicationLinks FourClassSeedStage80

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem class_lower_bound (p : V → Fin 4) (s : ℕ) (eta : ℝ)
    (heta : eta ≤ 1 / 2)
    (hsize : ∀ i, (1 - eta) * s ≤ ((classSet p i).card : ℝ) ∧
      ((classSet p i).card : ℝ) ≤ s) :
    ∀ i, (1 / 8 : ℝ) * Fintype.card V ≤ ((classSet p i).card : ℝ) := by
  classical
  have htotal : ∑ i : Fin 4, ((classSet p i).card : ℝ) = Fintype.card V := by
    exact_mod_cast sum_class_card p
  have h := sum_le_sum (s := (univ : Finset (Fin 4)))
    (f := fun i => ((classSet p i).card : ℝ)) (g := fun _ => (s : ℝ))
    (fun i _ => (hsize i).2)
  rw [htotal] at h
  have hnhi : (Fintype.card V : ℝ) ≤ 4 * s := by simpa using h
  intro i
  have hi := (hsize i).1
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith

theorem nearly_equal_decomposition :
    ∃ eta delta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧ 0 < delta ∧ ∃ N : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
        ∀ (p : W → Fin 4) (G0 : SimpleGraph W) [DecidableRel G0.Adj]
          (F : Finset (Sym2 W)) (s : ℕ), 0 < s →
          (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
          (∀ i, (1 - eta) * s ≤ ((classSet p i).card : ℝ) ∧
            ((classSet p i).card : ℝ) ≤ s) →
          F ⊆ G0.edgeFinset → DegBounded F (delta * Fintype.card W) →
          IsIntDiv p F3 (G0.deleteEdges (F : Set (Sym2 W))).edgeFinset →
          HasDecomp p F3 (G0.deleteEdges (F : Set (Sym2 W))).edgeFinset := by
  obtain ⟨delta0,eps,hd0,heps,N0,hN0⟩ :=
    FourClassUnconditionalStage79.four_class_decomposition (1 / 8) 2
      (by norm_num) (by norm_num) (by norm_num)
  let eta := min (1 / 2) (eps / 2)
  let delta := min delta0 (eps / 8)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta1 : eta ≤ 1 / 2 := min_le_left _ _
  have hd : 0 < delta := lt_min hd0 (by positivity)
  have hetaeps : eta ≤ eps / 2 := min_le_right _ _
  have hdeps : delta ≤ eps / 8 := min_le_right _ _
  refine ⟨eta,delta,heta,heta1,hd,max N0 1,?_⟩
  intro W _ _ hW p G0 _ F s hs hG0 hsize hF hFd hdiv
  classical
  have hn : 0 < Fintype.card W := by
    have h := le_of_max_le_right hW
    omega
  have hnR : (0 : ℝ) < Fintype.card W := by exact_mod_cast hn
  have hseed := uniform_seed p G0 hG0 s hs eta heta1 hsize
  have hdel := PackingRestriction.regularAlmostPacking_deleteEdges F
    (by norm_num : (0 : ℝ) < 2) hn hFd hseed
  have herr : eta + 2 * 2 * (delta * Fintype.card W) / Fintype.card W ≤ eps := by
    have hterm : 2 * 2 * (delta * Fintype.card W) / Fintype.card W = 4 * delta := by
      field_simp
      ring
    rw [hterm]
    linarith
  have hseed' : IsRegularAlmostPacking p F3
      (G0.deleteEdges (F : Set (Sym2 W))) 2 eps (fun _ => 1 / (2 * (s : ℝ))) := by
    refine ⟨hdel.1,?_⟩
    intro e he
    have hh := hdel.2 e he
    exact ⟨by linarith [hh.1],hh.2⟩
  have hFd0 : DegBounded F (delta0 * Fintype.card W) := fun v =>
    (hFd v).trans (mul_le_mul_of_nonneg_right (min_le_left delta0 (eps / 8))
      (Nat.cast_nonneg (Fintype.card W)))
  exact hN0 W (le_of_max_le_left hW) p G0 F (fun _ => 1 / (2 * (s : ℝ)))
    hG0 (class_lower_bound p s eta heta1 hsize) hF hFd0 hdiv hseed'

end PartitionedTriangleAbsorption.FourClassGraphConsumerStage80
