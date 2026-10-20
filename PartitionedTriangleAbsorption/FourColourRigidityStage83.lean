/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassSeedStage80
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! # The exact four-colour case at the three-quarter degree threshold

The colour classes and the complete host are proved, not supplied. This does
not provide a colouring or handle an approximate independent partition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourColourRigidityStage83

open Finset ClassRepresentativesStage65 FourClassSeedStage80

variable {V : Type*} [Fintype V]

theorem degree_add_class_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4)) (v : V) :
    G.degree v + (classSet c (c v)).card ≤ Fintype.card V := by
  classical
  have hd : Disjoint (G.neighborFinset v) (classSet c (c v)) := by
    apply disjoint_left.mpr
    intro w hw hc
    have hwc : c w = c v := (mem_filter.mp hc).2
    exact c.valid ((G.mem_neighborFinset v w).mp hw) hwc.symm
  have hh := card_le_card (subset_univ
    (G.neighborFinset v ∪ classSet c (c v)))
  rw [card_union_of_disjoint hd, card_univ,
    SimpleGraph.card_neighborFinset_eq_degree] at hh
  exact hh

theorem class_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4))
    (hdeg : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v) (i : Fin 4) :
    4 * (classSet c i).card ≤ Fintype.card V := by
  classical
  by_cases hi : (classSet c i).Nonempty
  · obtain ⟨v, hv⟩ := hi
    have hvcol : c v = i := (mem_filter.mp hv).2
    have hb := degree_add_class_le G c v
    rw [hvcol] at hb
    have hd := hdeg v
    omega
  · have hz : (classSet c i).card = 0 :=
      card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hi)
    rw [hz]
    omega

theorem four_mul_class_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4))
    (hdeg : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v) (i : Fin 4) :
    4 * (classSet c i).card = Fintype.card V := by
  have h0 := class_card_bound G c hdeg 0
  have h1 := class_card_bound G c hdeg 1
  have h2 := class_card_bound G c hdeg 2
  have h3 := class_card_bound G c hdeg 3
  have ht := sum_class_card (c : V → Fin 4)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ht
  change (classSet c 0).card + ((classSet c 1).card +
    ((classSet c 2).card + ((classSet c 3).card + 0))) = Fintype.card V at ht
  fin_cases i
  · change 4 * (classSet c 0).card = Fintype.card V
    omega
  · change 4 * (classSet c 1).card = Fintype.card V
    omega
  · change 4 * (classSet c 2).card = Fintype.card V
    omega
  · change 4 * (classSet c 3).card = Fintype.card V
    omega

theorem equal_classes (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4))
    (hdeg : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v) (i : Fin 4) :
    (classSet c i).card = (classSet c 0).card := by
  have hi := four_mul_class_card G c hdeg i
  have h0 := four_mul_class_card G c hdeg 0
  omega

theorem complete_host (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4))
    (hdeg : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v) :
    ∀ u v, G.Adj u v ↔ c u ≠ c v := by
  classical
  intro u v
  have hsub : G.neighborFinset u ⊆ (classSet c (c u))ᶜ := by
    intro w hw
    simp only [mem_compl, classSet, mem_filter, mem_univ, true_and]
    exact (c.valid ((G.mem_neighborFinset u w).mp hw)).symm
  have hb := degree_add_class_le G c u
  have hd := hdeg u
  have hc := four_mul_class_card G c hdeg (c u)
  have hcard : ((classSet c (c u))ᶜ).card ≤ (G.neighborFinset u).card := by
    rw [card_compl, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have heq := eq_of_subset_of_card_le hsub hcard
  constructor
  · exact fun h => c.valid h
  · intro h
    apply (G.mem_neighborFinset u v).mp
    rw [heq]
    simp only [mem_compl, classSet, mem_filter, mem_univ, true_and]
    exact h.symm

theorem degree_eq_three_mul_class (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4))
    (hdeg : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v) (v : V) :
    G.degree v = 3 * (classSet c 0).card := by
  have hb := degree_add_class_le G c v
  rw [equal_classes G c hdeg (c v)] at hb
  have hd := hdeg v
  have hc := four_mul_class_card G c hdeg 0
  omega

theorem even_class_size (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 4)) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v)
    (heven : ∀ v, Even (G.degree v)) : Even (classSet c 0).card := by
  have hp : 0 < (classSet c 0).card := by
    have hc := four_mul_class_card G c hdeg 0
    omega
  obtain ⟨v, _⟩ := card_pos.mp hp
  have hv := heven v
  rw [degree_eq_three_mul_class G c hdeg v] at hv
  rw [Nat.even_iff] at hv ⊢
  omega

end PartitionedTriangleAbsorption.FourColourRigidityStage83
