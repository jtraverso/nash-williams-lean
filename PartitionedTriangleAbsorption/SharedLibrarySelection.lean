/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedEmbeddingSelection

/-! # One shared-library placement step

Only the actual typed query needs a supply bound. The natural-number quota
`q` is half the final capacity: a new identity of weight at most `q` can be
placed at an image carrying less than `q`, leaving load at most `2*q`.
The production of these loads and the full placement induction are separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SharedLibrarySelection

open Finset AntiEdgeSelection TypedEmbeddingSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem exists_unsaturated_query (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (S Z : Finset V) (B : Finset (Sym2 V))
    (i : Fin t) (a : ℝ) (load : V → ℕ) (q weight : ℕ)
    (hq : 0 < q) (hweight : weight ≤ q)
    (hsupply : a ≤ (typedNeighbours p G S i).card)
    (hbudget : (Z.card : ℝ) + ((∑ v, load v : ℕ) : ℝ) / q +
      ∑ u ∈ S, (incidentLoad B u : ℝ) < a) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      load w < q ∧ load w + weight ≤ 2 * q ∧
      ∀ u ∈ S, s(u,w) ∉ B := by
  let saturated := univ.filter (fun v => q ≤ load v)
  have hsat : (saturated.card : ℝ) ≤ ((∑ v, load v : ℕ) : ℝ) / q := by
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hc : (q : ℝ) * saturated.card ≤ (∑ v, load v : ℕ) := by
      exact_mod_cast saturated_card_budget load q
    exact (le_div_iff₀ hqr).mpr (by simpa only [mul_comm] using hc)
  let W := typedNeighbours p G S i
  have hc := RootedEmbeddingSelection.available_card_budget W (Z ∪ saturated) S B
  have hunion : ((Z ∪ saturated).card : ℝ) ≤ Z.card + saturated.card := by
    exact_mod_cast card_union_le Z saturated
  have hpos : 0 < (W \ ((Z ∪ saturated) ∪ RootedEmbeddingSelection.blockedMany B S)).card := by
    by_contra h
    have hz :
        (W \ ((Z ∪ saturated) ∪ RootedEmbeddingSelection.blockedMany B S)).card = 0 := by
      omega
    rw [hz, Nat.zero_add] at hc
    have hr : (W.card : ℝ) ≤ (Z ∪ saturated).card +
        ∑ u ∈ S, (incidentLoad B u : ℝ) := by exact_mod_cast hc
    change a ≤ (W.card : ℝ) at hsupply
    linarith
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  obtain ⟨hw, hbad⟩ := mem_sdiff.mp hw
  have ht := (mem_filter.mp hw).2
  have hn : w ∉ Z ∪ saturated := fun h => hbad (mem_union.mpr (Or.inl h))
  have hl : load w < q := by
    have hns : w ∉ saturated := fun h => hn (mem_union.mpr (Or.inr h))
    simpa only [saturated, mem_filter, mem_univ, true_and, not_le] using hns
  refine ⟨w, ht.1, ht.2, (fun h => hn (mem_union.mpr (Or.inl h))), hl, by omega, ?_⟩
  intro u hu he
  exact hbad (mem_union.mpr (Or.inr (mem_biUnion.mpr
    ⟨u, hu, mem_filter.mpr ⟨mem_univ _, he⟩⟩)))

end PartitionedTriangleAbsorption.SharedLibrarySelection
