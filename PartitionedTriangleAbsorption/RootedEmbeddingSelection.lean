/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeSelection
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Push

/-! # A physical greedy step for rooted private absorbers

The common-neighbour set is computed from graph adjacency, not supplied as an
uninterpreted predicate. Blocking is by physical edges. This module proves one
embedding step; the template construction and simultaneous induction are separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootedEmbeddingSelection

open Finset AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

def blockedMany (B : Finset (Sym2 V)) (S : Finset V) : Finset V :=
  S.biUnion (blockedNeighbours B)

theorem blockedMany_card_le (B : Finset (Sym2 V)) (S : Finset V) :
    (blockedMany B S).card ≤ ∑ u ∈ S, incidentLoad B u := by
  exact (card_biUnion_le).trans (sum_le_sum fun u _ => blockedNeighbours_card_le B u)

theorem available_card_budget (W Z S : Finset V) (B : Finset (Sym2 V)) :
    W.card ≤ (W \ (Z ∪ blockedMany B S)).card + Z.card +
      ∑ u ∈ S, incidentLoad B u := by
  have hsub : W ⊆ (W \ (Z ∪ blockedMany B S)) ∪ (Z ∪ blockedMany B S) := by
    intro w hw
    by_cases hb : w ∈ Z ∪ blockedMany B S
    · exact mem_union.mpr (Or.inr hb)
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hw, hb⟩))
  have hb := (card_union_le Z (blockedMany B S)).trans
    (Nat.add_le_add_left (blockedMany_card_le B S) Z.card)
  exact ((card_le_card hsub).trans (card_union_le _ _)).trans
    (by simpa only [Nat.add_assoc] using
      Nat.add_le_add_left hb (W \ (Z ∪ blockedMany B S)).card)

def commonNeighbours (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter (fun w => ∀ u ∈ S, G.Adj u w)

def nonNeighbours (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  univ.filter (fun w => ¬ G.Adj u w)

omit [DecidableEq V] in
theorem neighbour_partition (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (univ.filter (fun w => G.Adj u w)).card + (nonNeighbours G u).card =
      Fintype.card V := by
  simpa [nonNeighbours] using
    (card_filter_add_card_filter_not (s := univ) (fun w => G.Adj u w))

theorem commonNeighbours_union_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    Fintype.card V ≤ (commonNeighbours G S).card + ∑ u ∈ S, (nonNeighbours G u).card := by
  have hsub : univ ⊆ commonNeighbours G S ∪ S.biUnion (nonNeighbours G) := by
    intro w _
    by_cases hw : ∀ u ∈ S, G.Adj u w
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _, hw⟩))
    · push Not at hw
      obtain ⟨u, hu, huw⟩ := hw
      exact mem_union.mpr (Or.inr (mem_biUnion.mpr
        ⟨u, hu, mem_filter.mpr ⟨mem_univ _, huw⟩⟩))
  have hc : Fintype.card V ≤ (commonNeighbours G S ∪ S.biUnion (nonNeighbours G)).card :=
    by simpa using card_le_card hsub
  exact hc.trans
    ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))

/-- Four prescribed neighbours have a linear common-neighbour supply above 3/4. -/
theorem commonNeighbours_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (eps : ℝ) (heps : eps ≤ 1 / 4) (hS : S.card ≤ 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ)) :
    4 * eps * (Fintype.card V : ℝ) ≤ ((commonNeighbours G S).card : ℝ) := by
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hnon : ∀ u, ((nonNeighbours G u).card : ℝ) ≤
      (1 / 4 - eps) * (Fintype.card V : ℝ) := by
    intro u
    have hp : ((univ.filter (fun w => G.Adj u w)).card : ℝ) +
        (nonNeighbours G u).card = Fintype.card V := by
      exact_mod_cast neighbour_partition G u
    linarith [hmin u]
  have hsum := sum_le_sum (s := S) (fun u _ => hnon u)
  have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  have hsum4 : (∑ u ∈ S, ((nonNeighbours G u).card : ℝ)) ≤
      4 * ((1 / 4 - eps) * (Fintype.card V : ℝ)) := by
    calc
      _ ≤ (S.card : ℝ) * ((1 / 4 - eps) * (Fintype.card V : ℝ)) := by
        simpa only [sum_const, nsmul_eq_mul] using hsum
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg (by linarith) hn)
  have hcount : (Fintype.card V : ℝ) ≤ ((commonNeighbours G S).card : ℝ) +
      ∑ u ∈ S, ((nonNeighbours G u).card : ℝ) := by
    exact_mod_cast commonNeighbours_union_budget G S
  linarith

/-- The chosen vertex is adjacent to every root, avoids forbidden images and used edges. -/
theorem exists_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) (B : Finset (Sym2 V)) (a : ℝ)
    (hsupply : a ≤ ((commonNeighbours G S).card : ℝ))
    (hbudget : (Z.card : ℝ) + ∑ u ∈ S, (incidentLoad B u : ℝ) < a) :
    ∃ w, (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧ ∀ u ∈ S, s(u, w) ∉ B := by
  let good := commonNeighbours G S \ (Z ∪ blockedMany B S)
  have hcount := available_card_budget (commonNeighbours G S) Z S B
  have hpos : 0 < good.card := by
    by_contra h
    have hz : good.card = 0 := by omega
    have hc : (commonNeighbours G S).card ≤ Z.card + ∑ u ∈ S, incidentLoad B u := by
      simpa only [show (commonNeighbours G S \ (Z ∪ blockedMany B S)).card = 0
        from hz, Nat.zero_add] using hcount
    have hcr : ((commonNeighbours G S).card : ℝ) ≤
        (Z.card : ℝ) + ∑ u ∈ S, (incidentLoad B u : ℝ) := by exact_mod_cast hc
    linarith
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  have hbad := (mem_sdiff.mp hw).2
  refine ⟨w, (mem_filter.mp (mem_sdiff.mp hw).1).2, ?_, ?_⟩
  · intro hz; exact hbad (mem_union.mpr (Or.inl hz))
  · intro u hu he
    exact hbad (mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨u, hu, mem_filter.mpr ⟨mem_univ _, he⟩⟩)))

/-- Concrete minimum degree supplies the greedy step for any rooted 4-degenerate template. -/
theorem exists_avoiding_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) (B : Finset (Sym2 V)) (eps d : ℝ)
    (heps : eps ≤ 1 / 4) (hS : S.card ≤ 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (Z.card : ℝ) + 4 * d < 4 * eps * (Fintype.card V : ℝ)) :
    ∃ w, (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧ ∀ u ∈ S, s(u, w) ∉ B := by
  apply exists_avoiding G S Z B (4 * eps * Fintype.card V)
    (commonNeighbours_four G S eps heps hS hmin)
  have hs := sum_le_sum (s := S) (fun u _ => hB u)
  have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  have hsd : (∑ u ∈ S, (incidentLoad B u : ℝ)) ≤ 4 * d := by
    calc
      _ ≤ (S.card : ℝ) * d := by
        simpa only [incidentLoad, sum_const, nsmul_eq_mul] using hs
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hd
  linarith

/-- Congestion is counted globally; vertices already at the cap cannot be selected. -/
theorem exists_unsaturated_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) (B : Finset (Sym2 V)) (eps d : ℝ)
    (heps : eps ≤ 1 / 4) (hS : S.card ≤ 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d) (load : V → ℕ)
    (q : ℕ) (hq : 0 < q)
    (hbudget : (Z.card : ℝ) + ((∑ v, load v : ℕ) : ℝ) / q + 4 * d <
      4 * eps * (Fintype.card V : ℝ)) :
    ∃ w, (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧ load w < q ∧
      ∀ u ∈ S, s(u, w) ∉ B := by
  let saturated := univ.filter (fun v => q ≤ load v)
  have hsat := saturated_card_budget load q
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hsatReal : (q : ℝ) * saturated.card ≤ (∑ v, load v : ℕ) := by
    exact_mod_cast hsat
  have hsatBound : (saturated.card : ℝ) ≤ ((∑ v, load v : ℕ) : ℝ) / q :=
    (le_div_iff₀ hqr).mpr (by simpa only [mul_comm] using hsatReal)
  have hZ : ((Z ∪ saturated).card : ℝ) ≤ (Z.card : ℝ) + saturated.card := by
    exact_mod_cast card_union_le Z saturated
  obtain ⟨w, hw, hz, hb⟩ := exists_avoiding_four G S (Z ∪ saturated) B eps d
    heps hS hmin hB hd (by linarith)
  have hnotSat : w ∉ saturated := fun h => hz (mem_union.mpr (Or.inr h))
  exact ⟨w, hw, fun h => hz (mem_union.mpr (Or.inl h)),
    by simpa only [saturated, mem_filter, mem_univ, true_and, not_le] using hnotSat, hb⟩

end PartitionedTriangleAbsorption.RootedEmbeddingSelection
