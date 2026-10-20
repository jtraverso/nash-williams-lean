/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.Marginals
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalChains
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.GadgetPlacements

/-!
# Distributions of a third vertex over a fixed physical edge

The old edge need not belong to the host. Both new edges do belong to the
host, and the third vertex has one fixed completing class. An unpaired
distribution is therefore a host triangle precisely when the old edge is
available. Opposite distributions can instead be coupled by a prism.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer

namespace FiniteDistribution

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]

theorem boundary_average (μ : FiniteDistribution W) (z : W → TriangleChain V) (e : Sym2 V) :
    boundary (fun Q => μ.average (fun w => z w Q)) e = μ.average (fun w => boundary (z w) e) := by
  simp only [average, boundary_sum, boundary_smul]

omit [Fintype V] [DecidableEq V] in
theorem copySupported_average {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (μ : FiniteDistribution W) (z : W → TriangleChain V)
    (hz : ∀ w, μ.mass w ≠ 0 → CopySupported p F G (z w)) :
    CopySupported p F G (fun Q => μ.average (fun w => z w Q)) := by
  intro Q hQ
  apply sum_eq_zero
  intro w hw
  change μ.mass w * z w Q = 0
  by_cases hm : μ.mass w = 0
  · simp only [hm, zero_mul]
  · rw [hz w hm Q hQ, mul_zero]

end FiniteDistribution

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

structure ThirdDistribution (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (a b : V) (s : ℝ) where
  law : FiniteDistribution V
  completion : Fin t
  typed : Link F (p a) (p b) completion
  support : ∀ c, law.mass c ≠ 0 → p c = completion ∧ G.Adj a c ∧ G.Adj b c
  cap : ∀ c, law.mass c ≤ 1 / s

namespace ThirdDistribution

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {a b : V} {s : ℝ}

noncomputable def chain (μ : ThirdDistribution p F G a b s) : TriangleChain V :=
  fun Q => μ.law.average (fun c => triangleBasis {a, b, c} Q)

theorem chain_nonneg (μ : ThirdDistribution p F G a b s) (Q : Finset V) : 0 ≤ μ.chain Q :=
  μ.law.average_nonneg _ fun _c _ => triangleBasis_nonneg _ _

theorem chain_supported (μ : ThirdDistribution p F G a b s) (hab : G.Adj a b) :
    CopySupported p F G μ.chain := by
  apply μ.law.copySupported_average
  intro c hc
  obtain ⟨ht, hac, hbc⟩ := μ.support c hc
  apply triangleBasis_supported
  exact isCopy_of_three_adj p G F hab hac hbc (by simpa only [ht] using μ.typed)

theorem chain_boundary (μ : ThirdDistribution p F G a b s) (e : Sym2 V) :
    boundary μ.chain e = μ.law.average (fun c => boundary (triangleBasis {a, b, c}) e) :=
  μ.law.boundary_average _ e

theorem chain_zero_of_edge_missing (μ : ThirdDistribution p F G a b s)
    (hab : a ≠ b) (Q : Finset V) (hQ : s(a, b) ∉ triEdges Q) : μ.chain Q = 0 := by
  unfold chain
  rw [← μ.law.average_const 0]
  apply μ.law.average_congr
  intro c hc
  apply triangleBasis_eq_zero
  intro h
  apply hQ
  rw [h]
  exact PaddedNibble.TypedNibble.mem_triEdges_iff.mpr ⟨by simp, by simp, hab⟩

theorem chain_le_window (μ : ThirdDistribution p F G a b s) (hs : 0 < s) (Q : Finset V) :
    μ.chain Q ≤ Q.card / s := by
  calc
    _ ≤ μ.law.average (fun c => if c ∈ Q then 1 else 0) := by
      apply μ.law.average_mono
      intro c hc
      unfold triangleBasis
      by_cases h : Q = ({a, b, c} : Finset V)
      · simp [h]
      · simp only [h, ite_false]
        split_ifs <;> norm_num
    _ ≤ _ := μ.law.average_window Q s hs μ.cap

end ThirdDistribution

#print axioms FiniteDistribution.boundary_average
#print axioms FiniteDistribution.copySupported_average
#print axioms ThirdDistribution.chain_supported
#print axioms ThirdDistribution.chain_zero_of_edge_missing
#print axioms ThirdDistribution.chain_le_window

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
