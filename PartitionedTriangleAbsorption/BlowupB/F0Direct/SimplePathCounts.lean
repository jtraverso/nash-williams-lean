/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkSupply
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Many simple paths of lengths three and four

For length four we first choose its first internal vertex, then count a
three-edge path whose two internal vertices avoid all three fixed vertices.
This gives the convenient lower bound `θ m^3 / 16` and enforces injectivity
of the whole five-vertex path.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.SimplePathCounts

open Finset WalkSupply

variable {V : Type*} [Fintype V] [DecidableEq V]

def avoidingPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (Q : Finset V) : Finset (V × V) :=
  ((neighbors G (S \ Q) u) ×ˢ (neighbors G (S \ Q) v)).filter fun ab => G.Adj ab.1 ab.2

theorem avoidingPairs_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (Q : Finset V) :
    ((avoidingPairs G S u v Q).card : ℝ) =
      arcs G (neighbors G (S \ Q) u) (neighbors G (S \ Q) v) := by
  rw [arcs_eq_card_pairs]
  rfl

theorem avoidingPairs_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (Q : Finset V) (ab : V × V) :
    ab ∈ avoidingPairs G S u v Q ↔
      ab.1 ∈ S ∧ ab.1 ∉ Q ∧ ab.2 ∈ S ∧ ab.2 ∉ Q ∧
        G.Adj u ab.1 ∧ G.Adj ab.1 ab.2 ∧ G.Adj ab.2 v := by
  simp only [avoidingPairs, mem_filter, mem_product, mem_neighbors, mem_sdiff]
  constructor
  · rintro ⟨⟨⟨⟨haS, haQ⟩, hua⟩, ⟨⟨hbS, hbQ⟩, hvb⟩⟩, hab⟩
    exact ⟨haS, haQ, hbS, hbQ, hua, hab, hvb.symm⟩
  · rintro ⟨haS, haQ, hbS, hbQ, hua, hab, hbv⟩
    exact ⟨⟨⟨⟨haS, haQ⟩, hua⟩, ⟨⟨hbS, hbQ⟩, hbv.symm⟩⟩, hab⟩

theorem arcs_remove_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Q : Finset V) (u v : V) :
    arcs G (neighbors G S u) (neighbors G S v) ≤
      (avoidingPairs G S u v Q).card + 2 * (Q.card : ℝ) * S.card := by
  have hperturb := arcs_perturb G (neighbors_subset G S u) (neighbors_subset G S v)
    ((neighbors_subset G (S \ Q) u).trans sdiff_subset)
    ((neighbors_subset G (S \ Q) v).trans sdiff_subset)
  have hsub (w : V) : neighbors G S w \ neighbors G (S \ Q) w ⊆ Q := by
    have h := neighbors_sdiff_subset G S (S \ Q) w
    rw [sdiff_sdiff_self_left] at h
    exact h.trans inter_subset_right
  have hu : ((neighbors G S u \ neighbors G (S \ Q) u).card : ℝ) ≤ Q.card :=
    Nat.cast_le.mpr (card_le_card (hsub u))
  have hv : ((neighbors G S v \ neighbors G (S \ Q) v).card : ℝ) ≤ Q.card :=
    Nat.cast_le.mpr (card_le_card (hsub v))
  have htotal : ((neighbors G S u \ neighbors G (S \ Q) u).card : ℝ) +
      (neighbors G S v \ neighbors G (S \ Q) v).card ≤ 2 * Q.card := by linarith
  have hmul := mul_le_mul_of_nonneg_right htotal (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  rw [avoidingPairs_card]
  nlinarith only [hperturb, hmul]

theorem avoidingPairs_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (Q : Finset V) (m θ : ℝ)
    (hm : 0 ≤ m) (hS : (S.card : ℝ) ≤ m) (hQ : Q.card ≤ 3)
    (hsize : 24 ≤ θ * m)
    (hwalk : θ * m^2 / 2 < arcs G (neighbors G S u) (neighbors G S v)) :
    θ * m^2 / 4 ≤ ((avoidingPairs G S u v Q).card : ℝ) := by
  have h := arcs_remove_bound G S Q u v
  have hQr : (Q.card : ℝ) ≤ 3 := by exact_mod_cast hQ
  have hprod := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ 2 * Q.card by positivity)
  have hprod' := mul_le_mul_of_nonneg_right hQr hm
  have hsize' := mul_le_mul_of_nonneg_right hsize hm
  nlinarith only [h, hwalk, hprod, hprod', hsize']

def threeCandidates (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) : Finset (V × V) := avoidingPairs G S u v {u, v}

def threeMap (u v : V) (ab : V × V) : Fin 4 → V := ![u, ab.1, ab.2, v]

theorem threeMap_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {u v : V} (huv : u ≠ v) {ab : V × V}
    (hab : ab ∈ threeCandidates G S u v) : Function.Injective (threeMap u v ab) := by
  obtain ⟨haS, haQ, hbS, hbQ, hua, hab, hbv⟩ :=
    (avoidingPairs_mem G S u v {u, v} ab).mp hab
  simp only [mem_insert, mem_singleton, not_or] at haQ hbQ
  have hadj := G.ne_of_adj hab
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [threeMap, eq_comm]

theorem threeCandidates_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (m θ : ℝ) (hm : 0 ≤ m) (hS : (S.card : ℝ) ≤ m)
    (hsize : 24 ≤ θ * m)
    (hwalk : θ * m^2 / 2 < arcs G (neighbors G S u) (neighbors G S v)) :
    θ * m^2 / 4 ≤ ((threeCandidates G S u v).card : ℝ) := by
  exact avoidingPairs_lower G S u v {u, v} m θ hm hS
    (card_le_two.trans (by decide)) hsize hwalk

def firstCandidates (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) : Finset V := neighbors G S u \ {v}

def fourCandidates (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) : Finset (Σ _c : V, V × V) :=
  (firstCandidates G S u v).sigma (fun c => avoidingPairs G S c v {u, c, v})

def fourMap (u v : V) (q : Σ _c : V, V × V) : Fin 5 → V :=
  ![u, q.1, q.2.1, q.2.2, v]

theorem fourCandidates_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (q : Σ _c : V, V × V) :
    q ∈ fourCandidates G S u v ↔
      q.1 ∈ S ∧ G.Adj u q.1 ∧ q.1 ≠ v ∧
        q.2 ∈ avoidingPairs G S q.1 v {u, q.1, v} := by
  simp only [fourCandidates, firstCandidates, mem_sigma, mem_sdiff,
    mem_neighbors, mem_singleton]
  tauto

theorem fourMap_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {u v : V} (huv : u ≠ v) {q : Σ _c : V, V × V}
    (hq : q ∈ fourCandidates G S u v) : Function.Injective (fourMap u v q) := by
  obtain ⟨hcS, huc, hcv, hp⟩ := (fourCandidates_mem G S u v q).mp hq
  obtain ⟨haS, haQ, hbS, hbQ, hca, hab, hbv⟩ :=
    (avoidingPairs_mem G S q.1 v {u, q.1, v} q.2).mp hp
  simp only [mem_insert, mem_singleton, not_or] at haQ hbQ
  have huc' := G.ne_of_adj huc
  have hab' := G.ne_of_adj hab
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fourMap, eq_comm]

theorem fourCandidates_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (m θ : ℝ) (hθ : 0 ≤ θ) (hm : 12 ≤ m)
    (hS : (S.card : ℝ) ≤ m) (hv : v ∈ S)
    (hsize : 24 ≤ θ * m)
    (hdeg : m / 3 ≤ ((neighbors G S u).card : ℝ))
    (hwalk : ∀ c ∈ S, θ * m^2 / 2 < arcs G (neighbors G S c) (neighbors G S v)) :
    θ * m^3 / 16 ≤ ((fourCandidates G S u v).card : ℝ) := by
  have hm0 : 0 ≤ m := by linarith
  have hfirst : m / 4 ≤ ((firstCandidates G S u v).card : ℝ) := by
    have h := card_le_card_sdiff_add_card (s := neighbors G S u) (t := {v})
    have hr := (Nat.cast_le (α := ℝ)).mpr h
    simp only [card_singleton, Nat.cast_add, Nat.cast_one] at hr
    change ((neighbors G S u).card : ℝ) ≤ (firstCandidates G S u v).card + 1 at hr
    linarith
  have hper : ∀ c ∈ firstCandidates G S u v,
      θ * m^2 / 4 ≤ ((avoidingPairs G S c v {u, c, v}).card : ℝ) := by
    intro c hc
    have hcS := (mem_neighbors G S u c).mp (mem_sdiff.mp hc).1
    exact avoidingPairs_lower G S c v {u, c, v} m θ hm0 hS card_le_three hsize (hwalk c hcS.1)
  have hsum := sum_le_sum hper
  simp only [sum_const, nsmul_eq_mul] at hsum
  have htotal : ((fourCandidates G S u v).card : ℝ) =
      ∑ c ∈ firstCandidates G S u v, ((avoidingPairs G S c v {u, c, v}).card : ℝ) := by
    simp only [fourCandidates, card_sigma, Nat.cast_sum]
  have hmul := mul_le_mul_of_nonneg_right hfirst
    (show 0 ≤ θ * m^2 / 4 by positivity)
  nlinarith only [hmul, hsum, htotal]

#print axioms threeCandidates_lower
#print axioms fourCandidates_lower
#print axioms threeMap_injective
#print axioms fourMap_injective

end PartitionedTriangleAbsorption.BlowupB.F0Direct.SimplePathCounts
