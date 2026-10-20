/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SharedLibrarySelection
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Request-centre labels compatible with F0 anti-edge supply

A centre between two equal-part endpoints uses the other part. For unequal
endpoints, part zero suffices. This supplies the actual two-root query from
anti-edgefulness. It does not yet relabel the entire compressed refiner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0RequestLabels

open Finset TypedApplicationLinks TypedEmbeddingSelection

def centrePart (i j : Fin 2) : Fin 2 := if i = j then other0 i else 0

theorem centre_permitted : ∀ i j : Fin 2,
    ({i,j,centrePart i j} : Multiset (Fin 2)) ∈ F0 := by decide

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem request_supply (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (hanti : AntiEdgeful p F0 G alpha) (u v : V) (huv : u ≠ v) :
    alpha * Fintype.card V ≤
      (typedNeighbours p G {u,v} (centrePart (p u) (p v))).card := by
  have hc := hanti _ (centre_permitted (p u) (p v))
    (p u) (p v) (centrePart (p u) (p v)) rfl u v huv rfl rfl
  have heq : univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧
      p w = centrePart (p u) (p v)) =
      typedNeighbours p G {u,v} (centrePart (p u) (p v)) := by
    ext w
    simp only [typedNeighbours, mem_filter, mem_univ, true_and,
      mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hu, hv, hp⟩
      exact ⟨hp, hu, G.adj_symm hv⟩
    · rintro ⟨hp, hu, hv⟩
      exact ⟨hu, G.adj_symm hv, hp⟩
  rw [heq] at hc
  exact hc

theorem request_available (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (hanti : AntiEdgeful p F0 G alpha) (u v : V) (huv : u ≠ v)
    (Z : Finset V) (B : Finset (Sym2 V)) (load : V → ℕ) (q weight : ℕ)
    (hq : 0 < q) (hweight : weight ≤ q)
    (hbudget : (Z.card : ℝ) + ((∑ x, load x : ℕ) : ℝ) / q +
      ∑ x ∈ ({u,v} : Finset V), (AntiEdgeSelection.incidentLoad B x : ℝ) <
        alpha * Fintype.card V) :
    ∃ w, p w = centrePart (p u) (p v) ∧ (∀ x ∈ ({u,v} : Finset V), G.Adj x w) ∧
      w ∉ Z ∧ load w < q ∧ load w + weight ≤ 2 * q ∧
      ∀ x ∈ ({u,v} : Finset V), s(x,w) ∉ B := by
  exact SharedLibrarySelection.exists_unsaturated_query p G {u,v} Z B
    (centrePart (p u) (p v)) (alpha * Fintype.card V) load q weight hq hweight
    (request_supply p G alpha hanti u v huv) hbudget

end PartitionedTriangleAbsorption.F0RequestLabels
