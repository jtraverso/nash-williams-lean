/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassUnconditionalStage79
public import PartitionedTriangleAbsorption.TypedLoadCounterexample

/-! # A constructed regular seed for nearly equal four-class hosts

Each copy through an edge is counted once by its third vertex. Constant
weights construct the original almost packing; sparse deletion uses the
accepted physical restriction lemma. No fractional seed is supplied.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassSeedStage80

open Finset ClassRepresentativesStage65 TypedApplicationLinks TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem sum_class_card (p : V → Fin 4) :
    ∑ i : Fin 4, (classSet p i).card = Fintype.card V := by
  classical
  simp only [classSet, card_eq_sum_ones]
  simp only [sum_filter]
  rw [sum_comm]
  simp

theorem third_labels {i j k : Fin 4} (hij : i ≠ j) :
    ({i,j,k} : Multiset (Fin 4)) ∈ F3 ↔ k ≠ i ∧ k ≠ j := by
  revert i j k
  decide

theorem complete_copy_count (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    {u v : V} (huv : G.Adj u v) :
    ((copies p F3 G).filter (fun S => s(u,v) ∈ triEdges S)).card =
      ∑ i ∈ univ.filter (fun i => i ≠ p u ∧ i ≠ p v), (classSet p i).card := by
  classical
  rw [TypedLoadCounterexample.card_edgeCopies p F3 G huv]
  have hne : p u ≠ p v := (hG u v).mp huv
  have hpred : ∀ z, G.Adj u z ∧ G.Adj v z ∧
      ({p u,p v,p z} : Multiset (Fin 4)) ∈ F3 ↔ p z ≠ p u ∧ p z ≠ p v := by
    intro z
    rw [hG, hG, third_labels hne]
    tauto
  simp_rw [hpred]
  simp only [classSet, card_eq_sum_ones, sum_filter]
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp only [← ite_and]
  have hswap : ∀ i : Fin 4, (i ≠ p u ∧ i ≠ p v) ∧ p z = i ↔
      p z = i ∧ (p z ≠ p u ∧ p z ≠ p v) := by
    intro i
    constructor
    · rintro ⟨hi,hzi⟩
      subst i
      exact ⟨rfl,hi⟩
    · rintro ⟨hzi,hz⟩
      subst i
      exact ⟨hz,rfl⟩
  simp_rw [hswap, ite_and]
  simp

theorem two_other_labels {i j : Fin 4} (hij : i ≠ j) :
    (univ.filter (fun k : Fin 4 => k ≠ i ∧ k ≠ j)).card = 2 := by
  revert i j
  decide

theorem uniform_seed (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (s : ℕ) (hs : 0 < s) (eta : ℝ) (heta1 : eta ≤ 1 / 2)
    (hsize : ∀ i, (1 - eta) * s ≤ ((classSet p i).card : ℝ) ∧
      ((classSet p i).card : ℝ) ≤ s) :
    IsRegularAlmostPacking p F3 G 2 eta (fun _ => 1 / (2 * (s : ℝ))) := by
  classical
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htotal : ∑ i : Fin 4, ((classSet p i).card : ℝ) = Fintype.card V := by
    exact_mod_cast sum_class_card p
  have hnlo : 2 * (s : ℝ) ≤ Fintype.card V := by
    have h := sum_le_sum (s := (univ : Finset (Fin 4)))
      (f := fun _ => (s : ℝ) / 2) (g := fun i => ((classSet p i).card : ℝ))
      (fun i _ => by have hi := (hsize i).1; nlinarith)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [htotal] at h
    linarith
  have hnhi : (Fintype.card V : ℝ) ≤ 4 * s := by
    have h := sum_le_sum (s := (univ : Finset (Fin 4)))
      (f := fun i => ((classSet p i).card : ℝ)) (g := fun _ => (s : ℝ))
      (fun i _ => (hsize i).2)
    rw [htotal] at h
    simpa using h
  have hn : (0 : ℝ) < Fintype.card V := by linarith
  refine ⟨?_,?_⟩
  · intro S _
    constructor
    · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card V)
        (by positivity : (0 : ℝ) < 2 * s)).mpr
      nlinarith
    · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s) hn).mpr
      nlinarith
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have hne := (hG u v).mp huv
      let I := univ.filter (fun i : Fin 4 => i ≠ p u ∧ i ≠ p v)
      have hI : I.card = 2 := two_other_labels hne
      have hcount := complete_copy_count p G hG huv
      have hlo : 2 * ((1 - eta) * (s : ℝ)) ≤
          (((copies p F3 G).filter (fun S => s(u,v) ∈ triEdges S)).card : ℝ) := by
        rw [hcount, Nat.cast_sum]
        have h := sum_le_sum (s := I) (f := fun _ => (1 - eta) * (s : ℝ))
          (g := fun i => ((classSet p i).card : ℝ)) (fun i _ => (hsize i).1)
        simpa [hI] using h
      have hhi : (((copies p F3 G).filter (fun S => s(u,v) ∈ triEdges S)).card : ℝ)
          ≤ 2 * (s : ℝ) := by
        rw [hcount, Nat.cast_sum]
        have h := sum_le_sum (s := I) (f := fun i => ((classSet p i).card : ℝ))
          (g := fun _ => (s : ℝ)) (fun i _ => (hsize i).2)
        simpa [hI] using h
      simp only [sum_const, nsmul_eq_mul, mul_one_div]
      constructor
      · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mpr
        nlinarith
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mpr
        nlinarith

end PartitionedTriangleAbsorption.FourClassSeedStage80
