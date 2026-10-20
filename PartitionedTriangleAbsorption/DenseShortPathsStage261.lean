/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-! Quantitative paths within components of dense finite graphs.
No connectedness of the whole graph is assumed. Closed neighborhoods at
positions 0,3,... of a shortest walk are disjoint, by their distances from
the initial vertex. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset SimpleGraph

/-- Minimum closed-neighborhood size bounds every finite graph distance.
The hypothesis is integral, so no rounding of a real density is needed. -/
theorem reachable_short_walk {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ x, Fintype.card V < k * (G.degree x + 1))
    {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length < 3 * k := by
  classical
  obtain ⟨p, hpPath, hp⟩ := hr.exists_path_of_dist
  refine ⟨p, hpPath, ?_⟩
  by_contra hlong
  have hlong' : 3 * k ≤ p.length := by omega
  let center (i : Fin (k + 1)) := p.getVert (3 * i.val)
  let C (i : Fin (k + 1)) := insert (center i) (G.neighborFinset (center i))
  have hd (i : Fin (k + 1)) : G.dist u (center i) = 3 * i.val := by
    have ht := length_eq_dist_of_subwalk hp (p.isSubwalk_take (3 * i.val))
    rw [Walk.take_length, inf_eq_left.mpr (by omega)] at ht
    exact ht.symm
  have hclose (i : Fin (k + 1)) (x : V) (hx : x ∈ C i) :
      3 * i.val ≤ G.dist u x + 1 ∧ G.dist u x ≤ 3 * i.val + 1 := by
    rcases mem_insert.mp hx with hx | hx
    · rw [hx, hd]
      omega
    · have ha : G.Adj (center i) x := (G.mem_neighborFinset _ _).mp hx
      have hh := ha.diff_dist_adj (u := u)
      rw [hd] at hh
      omega
  have hdis : (↑(univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))).PairwiseDisjoint C := by
    intro i _ j _ hij
    change Disjoint (C i) (C j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi := hclose i x hxi
    have hj := hclose j x hxj
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  have hc := card_le_univ (s := (univ : Finset (Fin (k + 1))).biUnion C)
  rw [card_biUnion hdis] at hc
  have hcard (i : Fin (k + 1)) : (C i).card = G.degree (center i) + 1 := by
    simp [C]
  have hbound (i : Fin (k + 1)) : Fintype.card V + 1 ≤ k * (C i).card := by
    rw [hcard]
    exact Nat.succ_le_of_lt (hdeg (center i))
  have hsum := sum_le_sum (s := (univ : Finset (Fin (k + 1)))) (fun i _ => hbound i)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum] at hsum
  have hmul := Nat.mul_le_mul_left k hc
  nlinarith

/-- In particular, degree at least one fifth of the order gives paths of
length at most fourteen inside each connected component. -/
theorem reachable_walk_le_fourteen {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, Fintype.card V ≤ 5 * G.degree x)
    {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ 14 := by
  obtain ⟨p, hp, hlen⟩ := reachable_short_walk G 5 (fun x => by have := hdeg x; omega) hr
  exact ⟨p, hp, by omega⟩

end PartitionedTriangleAbsorption.GoodRemaindersStage261
