/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourColourStabilityStage84

/-! # Common neighbours for cleaning a sparse internal partition

The partition is not assumed to be a proper colouring. A three-quarter
minimum degree and a small internal degree give the required supply for
each requested internal edge and each different destination class.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupSupplyStage140

open Finset ClassRepresentativesStage65 FourClassSeedStage80

variable {V : Type*} [Fintype V] [DecidableEq V]

def internalNeighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) : Finset V :=
  G.neighborFinset v ∩ classSet p (p v)

def missingOutside (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) : Finset V :=
  (classSet p (p v))ᶜ \ G.neighborFinset v

def candidates (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (j : Fin 4) : Finset V :=
  classSet p j ∩ G.neighborFinset u ∩ G.neighborFinset v

theorem degree_class_account (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) :
    (missingOutside G p v).card + G.degree v + (classSet p (p v)).card =
      Fintype.card V + (internalNeighbours G p v).card := by
  classical
  have hm : missingOutside G p v = (G.neighborFinset v ∪ classSet p (p v))ᶜ := by
    ext w
    simp [missingOutside, and_comm]
  have hc := card_union_add_card_inter (G.neighborFinset v) (classSet p (p v))
  have hs := card_le_card (subset_univ (G.neighborFinset v ∪ classSet p (p v)))
  simp only [card_univ] at hs
  rw [hm, card_compl]
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  change _ + G.degree v + _ = _ + (G.neighborFinset v ∩ classSet p (p v)).card
  omega

theorem class_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hint : ∀ v, ((internalNeighbours G p v).card : ℝ) ≤ eps * Fintype.card V)
    (i : Fin 4) :
    ((classSet p i).card : ℝ) ≤ (1 / 4 + eps) * Fintype.card V := by
  classical
  by_cases hi : (classSet p i).Nonempty
  · obtain ⟨v, hv⟩ := hi
    have hp : p v = i := (mem_filter.mp hv).2
    have hc : G.degree v + (classSet p (p v)).card ≤
        Fintype.card V + (internalNeighbours G p v).card := by
      have := degree_class_account G p v
      omega
    have hcR : (G.degree v : ℝ) + (classSet p (p v)).card ≤
        Fintype.card V + (internalNeighbours G p v).card := by exact_mod_cast hc
    rw [hp] at hcR
    nlinarith [hdeg v, hint v]
  · have hz := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hi)
    rw [hz, Nat.cast_zero]
    positivity

theorem class_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hint : ∀ v, ((internalNeighbours G p v).card : ℝ) ≤ eps * Fintype.card V)
    (i : Fin 4) :
    (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet p i).card : ℝ) := by
  have h0 := class_upper G p eps heps hdeg hint 0
  have h1 := class_upper G p eps heps hdeg hint 1
  have h2 := class_upper G p eps heps hdeg hint 2
  have h3 := class_upper G p eps heps hdeg hint 3
  have ht : ∑ j : Fin 4, ((classSet p j).card : ℝ) = Fintype.card V :=
    by exact_mod_cast sum_class_card p
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ht
  change (classSet p 0).card + ((classSet p 1).card +
    ((classSet p 2).card + ((classSet p 3).card + (0 : ℝ)))) = Fintype.card V at ht
  fin_cases i
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet p 0).card : ℝ)
    nlinarith
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet p 1).card : ℝ)
    nlinarith
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet p 2).card : ℝ)
    nlinarith
  · change (1 / 4 - 3 * eps) * Fintype.card V ≤ ((classSet p 3).card : ℝ)
    nlinarith

theorem missingOutside_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hint : ∀ v, ((internalNeighbours G p v).card : ℝ) ≤ eps * Fintype.card V)
    (v : V) :
    ((missingOutside G p v).card : ℝ) ≤ 4 * eps * Fintype.card V := by
  have hc : ((missingOutside G p v).card : ℝ) + G.degree v +
      (classSet p (p v)).card = Fintype.card V + (internalNeighbours G p v).card :=
    by exact_mod_cast degree_class_account G p v
  have hl := class_lower G p eps heps hdeg hint (p v)
  nlinarith [hdeg v, hint v]

theorem candidates_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (j : Fin 4)
    (hju : j ≠ p u) (hjv : j ≠ p v) :
    (classSet p j).card ≤ (candidates G p u v j).card +
      (missingOutside G p u).card + (missingOutside G p v).card := by
  classical
  have hs : classSet p j ⊆ candidates G p u v j ∪
      missingOutside G p u ∪ missingOutside G p v := by
    intro w hw
    have hp : p w = j := (mem_filter.mp hw).2
    by_cases hu : w ∈ G.neighborFinset u
    · by_cases hv : w ∈ G.neighborFinset v
      · exact mem_union_left _ (mem_union_left _
          (mem_inter.mpr ⟨mem_inter.mpr ⟨hw, hu⟩, hv⟩))
      · apply mem_union_right
        apply mem_sdiff.mpr
        refine ⟨?_, hv⟩
        simp only [mem_compl, classSet, mem_filter, mem_univ, true_and, hp]
        exact hjv
    · apply mem_union_left
      apply mem_union_right
      apply mem_sdiff.mpr
      refine ⟨?_, hu⟩
      simp only [mem_compl, classSet, mem_filter, mem_univ, true_and, hp]
      exact hju
  exact (card_le_card hs).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))

theorem candidates_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hint : ∀ v, ((internalNeighbours G p v).card : ℝ) ≤ eps * Fintype.card V)
    (u v : V) (j : Fin 4) (hju : j ≠ p u) (hjv : j ≠ p v) :
    (1 / 4 - 11 * eps) * Fintype.card V ≤ (candidates G p u v j).card := by
  have hb : ((classSet p j).card : ℝ) ≤ (candidates G p u v j).card +
      (missingOutside G p u).card + (missingOutside G p v).card :=
    by exact_mod_cast candidates_budget G p u v j hju hjv
  have hl := class_lower G p eps heps hdeg hint j
  have hu := missingOutside_bound G p eps heps hdeg hint u
  have hv := missingOutside_bound G p eps heps hdeg hint v
  nlinarith

end PartitionedTriangleAbsorption.CleanupSupplyStage140

