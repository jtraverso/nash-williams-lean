/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.NeighbourStarAdapterStage146
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Graph-derived supply for the exceptional star matchings

The independent exceptional set belongs to the same graph that satisfies the
minimum-degree assumption. This file does not infer that assumption after
the exceptional pre-cleaning packing. It constructs one star at a time against
a common sparse forbidden relation; joint edge-disjointness remains separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.GeometricStarMarginStage146

open Finset MatchedQuotaStage140 GraphStarInventoryStage144
open CleanupSupplyStage140 ExceptionalGeometryStage141 ClassRepresentativesStage65
open NeighbourStarAdapterStage146 StarPairProfileStage145

/-- Integer rounding is paid before using the local matching constructor. -/
theorem rounded_margin (n d U : ℕ) (rho tau : ℝ)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hdegree : (3 / 4 : ℝ) * n ≤ d)
    (hbudget : 8 + (112 * rho + 4 * tau) * n + 4 * U < (n : ℝ) / 4) :
    2 * ⌈(1 / 4 + 8 * rho) * (n : ℝ)⌉₊ +
      4 * (⌈(24 * rho + tau) * (n : ℝ)⌉₊ + U) + 2 < d := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hL := Nat.ceil_lt_add_one
    (show 0 ≤ (1 / 4 + 8 * rho) * (n : ℝ) by positivity)
  have hD := Nat.ceil_lt_add_one
    (show 0 ≤ (24 * rho + tau) * (n : ℝ) by positivity)
  have hh : (2 : ℝ) * ⌈(1 / 4 + 8 * rho) * (n : ℝ)⌉₊ +
      4 * (⌈(24 * rho + tau) * (n : ℝ)⌉₊ + U) + 2 < d := by
    nlinarith
  exact_mod_cast hh

/-- An explicit uniform hierarchy pays for at most one old base per centre. -/
theorem hierarchy_budget (n U : ℕ) (rho tau : ℝ)
    (hn : 128 ≤ n) (htau : 0 < tau)
    (htsmall : tau ≤ 1 / 1024) (hrsmall : rho ≤ tau / 1024)
    (hused : tau * U ≤ 2 * rho * n) :
    8 + (112 * rho + 4 * tau) * n + 4 * U < (n : ℝ) / 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnR : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : rho ≤ 1 / 1048576 := by linarith
  have hU : (U : ℝ) ≤ (n : ℝ) / 512 := by
    apply (mul_le_mul_iff_left₀ htau).mp
    have hh := mul_le_mul_of_nonneg_right hrsmall hn0
    nlinarith
  have hc : 112 * rho + 4 * tau ≤ (1 / 32 : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_right hc hn0
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every neighbour of an independent exceptional centre is typical. -/
theorem neighbours_typical (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (tau : ℝ)
    (hS : ∀ u ∈ exceptional G p tau, ∀ w ∈ exceptional G p tau, ¬ G.Adj u w)
    (v : exceptional G p tau) (w : Neighbours G v) :
    (w : V) ∉ exceptional G p tau := by
  intro hw
  exact hS v v.property w hw ((G.mem_neighborFinset v w).mp w.property)

/-- The graph's average internal error pays the whole star matching margin. -/
theorem graph_star_margin (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hn : 128 ≤ Fintype.card V)
    (hrho : 0 ≤ rho) (htau : 0 < tau)
    (htsmall : tau ≤ 1 / 1024) (hrsmall : rho ≤ tau / 1024)
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (v : V) :
    2 * ⌈(1 / 4 + 8 * rho) * (Fintype.card V : ℝ)⌉₊ +
      4 * (⌈(24 * rho + tau) * (Fintype.card V : ℝ)⌉₊ +
        (exceptional G p tau).card) + 2 < G.degree v := by
  have hnpos : 0 < Fintype.card V := by omega
  exact rounded_margin _ _ _ rho tau hrho htau.le (hdegree v)
    (hierarchy_budget _ _ rho tau hn htau htsmall hrsmall
      (exceptional_card_average G p rho tau hnpos herr))

/-- Construct the pairing for any allocated exceptional row from graph data. -/
theorem exists_geometric_star_pairing (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hn : 128 ≤ Fintype.card V)
    (hrho : 0 ≤ rho) (htau : 0 < tau)
    (htsmall : tau ≤ 1 / 1024) (hrsmall : rho ≤ tau / 1024)
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (hS : ∀ u ∈ exceptional G p tau, ∀ w ∈ exceptional G p tau, ¬ G.Adj u w)
    (B : V → V → Prop) [DecidableRel B]
    (hB : ∀ u w, B u w → B w u)
    (hused : ∀ w, (univ.filter fun z => B w z).card ≤ (exceptional G p tau).card)
    (v : exceptional G p tau) (x : Fin 3 → ℕ)
    (heven : G.degree v = 2 * (G.degree v / 2))
    (ha : classLoad p G v (p v) ≤ G.degree v / 2)
    (hrow : ∑ i, x i = classLoad p G v (p v))
    (hx : ∀ i,
      classLoad p G v (p v) + classLoad p G v (partner i (p v)) -
        G.degree v / 2 ≤ x i ∧ x i ≤ classLoad p G v (partner i (p v))) :
    ∃ f : Neighbours G v ≃ Neighbours G v,
      Function.Involutive f ∧ (∀ w : Neighbours G v, p (f w) ≠ p w) ∧
      (∀ w : Neighbours G v, G.Adj w (f w) ∧ ¬ B w (f w)) ∧
      ∀ j k, (univ.filter fun w : Neighbours G v =>
        localLabel p v w = j ∧ localLabel p v (f w) = k).card =
          pairDemand (classLoad p G v (p v)) (G.degree v / 2)
            (fun i => classLoad p G v (partner i (p v))) x j k := by
  classical
  have hnpos : 0 < Fintype.card V := by omega
  apply exists_neighbour_star_pairing G p v x B hB
    ⌈(1 / 4 + 8 * rho) * (Fintype.card V : ℝ)⌉₊
    ⌈(24 * rho + tau) * (Fintype.card V : ℝ)⌉₊
    (exceptional G p tau).card heven ha hrow hx
  · intro j
    have hc := class_upper_average G p rho hrho hnpos hdegree herr j
    have hh := hc.trans (Nat.le_ceil ((1 / 4 + 8 * rho) * (Fintype.card V : ℝ)))
    exact_mod_cast hh
  · intro w
    have hm := typical_missing_bound G p rho tau hrho hnpos hdegree herr w
      (neighbours_typical G p tau hS v w)
    have hh := hm.trans (Nat.le_ceil ((24 * rho + tau) * (Fintype.card V : ℝ)))
    exact_mod_cast hh
  · exact hused
  · exact graph_star_margin G p rho tau hn hrho htau htsmall hrsmall hdegree herr v

/-- Graph-only quotas and physical local consumers, with no supplied allocation.
Each consumer avoids the fixed forbidden relation. Distinct consumers are not
asserted to avoid each other until that relation is updated between centres. -/
theorem exists_allocated_neighbour_pairings (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hn : 128 ≤ Fintype.card V)
    (hrho : 0 ≤ rho) (htau : 0 < tau)
    (htsmall : tau ≤ 1 / 1024) (hrsmall : rho ≤ tau / 1024)
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hdiv : OnePart.Even3 G.edgeFinset)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (hS : ∀ u ∈ exceptional G p tau, ∀ w ∈ exceptional G p tau, ¬ G.Adj u w)
    (B : V → V → Prop) [DecidableRel B]
    (hB : ∀ u w, B u w → B w u)
    (hused : ∀ w, (univ.filter fun z => B w z).card ≤ (exceptional G p tau).card) :
    ∃ q : Fin 3 → ℕ, ∃ x : exceptional G p tau → Fin 3 → ℕ,
      (∀ i, 6 * q i + 3 * (cuts p G.edgeFinset i).card = 2 * G.edgeFinset.card) ∧
      (∑ i, q i) = (internal p G.edgeFinset).card ∧
      (∀ v : exceptional G p tau, ∑ i, x v i = classLoad p G v (p v)) ∧
      (∀ (v : exceptional G p tau) i,
        classLoad p G v (p v) + classLoad p G v (partner i (p v)) -
          G.degree v / 2 ≤ x v i ∧ x v i ≤ classLoad p G v (partner i (p v))) ∧
      (∀ i, ∑ v, x v i ≤ q i) ∧
      ∀ v : exceptional G p tau, ∃ f : Neighbours G v ≃ Neighbours G v,
        Function.Involutive f ∧ (∀ w : Neighbours G v, p (f w) ≠ p w) ∧
        (∀ w : Neighbours G v, G.Adj w (f w) ∧ ¬ B w (f w)) ∧
        ∀ j k, (univ.filter fun w : Neighbours G v =>
          localLabel p v w = j ∧ localLabel p v (f w) = k).card =
            pairDemand (classLoad p G v (p v)) (G.degree v / 2)
              (fun i => classLoad p G v (partner i (p v))) (x v) j k := by
  classical
  have hnpos : 0 < Fintype.card V := by omega
  have hr64 : rho ≤ 1 / 64 := by linarith
  have hd (v : V) : 3 * Fintype.card V ≤ 4 * G.degree v := by
    have hh : (3 : ℝ) * Fintype.card V ≤ 4 * G.degree v := by linarith [hdegree v]
    exact_mod_cast hh
  have hc (j : Fin 4) :
      8 * (univ.filter fun w => p w = j).card ≤ 3 * Fintype.card V :=
    class_budget_of_average p G rho hrho hr64 hnpos hdegree herr j
  obtain ⟨q, x, hq, hsum, hrow, hx, hcol⟩ :=
    exists_allocation_of_graph p G (exceptional G p tau) hd hdiv hS hc
  refine ⟨q, x, hq, hsum, hrow, hx, hcol, ?_⟩
  intro v
  have heven : G.degree v = 2 * (G.degree v / 2) := by
    obtain ⟨d, h⟩ := hdiv.2 v
    rw [IndependentStarQuotaStage144.incident_degree G v] at h
    omega
  have ha : classLoad p G v (p v) ≤ G.degree v / 2 := by
    have h1 := hc (p v)
    have h2 := hd v
    have h3 := classLoad_le_class_card p G v (p v)
    omega
  exact exists_geometric_star_pairing G p rho tau hn hrho htau htsmall hrsmall
    hdegree herr hS B hB hused v (x v) heven ha (hrow v) (hx v)

end PartitionedTriangleAbsorption.GeometricStarMarginStage146
