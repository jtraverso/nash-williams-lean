/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoherentTransformer.ChargeInvariant
public import PartitionedTriangleAbsorption.TypedApplicationLinks
public import Mathlib.Basic.Real.Basic

/-! # The candidate coherent F0 transformer target

This module only STATES the candidate target of the Stage46 coherence
request. It is refuted in `CoherentTransformer.Refutation`.

* `trailEdges σ x` is the physical closed-trail graph `{x_i x_(σ i)}`.
* `PhysicalTrail G σ x`: nonloop edges, injective position-to-edge map,
  every edge in `G`. Vertex repetitions are allowed.
* `CloneCondition`: the two-root same-part common-neighbour premise.
* `IsCoherentTransformer`: `T ⊆ E(G)`, edge-disjoint from `Hx ∪ Hy`, and
  both `T ∪ Hx` and `T ∪ Hy` are F0-decomposable.
* `CandidateTarget α β K`: uniform constants `C, N` chosen before the host,
  and a transformer with at most `C|I|` edges and `C|I|` auxiliary vertices.
  The optional root-degree bound is not included: dropping a conclusion only
  makes the refuted statement weaker, hence the refutation stronger.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer

open Finset TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The physical closed-trail graph `{x_i x_(σ i)}`. -/
def trailEdges (σ : Equiv.Perm I) (x : I → V) : Finset (Sym2 V) :=
  univ.image fun i => s(x i, x (σ i))

/-- Physical closed trail: nonloop edges, injective positions-to-edges, edges in `G`. -/
def PhysicalTrail (G : SimpleGraph V) (σ : Equiv.Perm I) (x : I → V) : Prop :=
  (∀ i, x i ≠ x (σ i)) ∧ Function.Injective (fun i => s(x i, x (σ i))) ∧
    ∀ i, G.Adj (x i) (x (σ i))

omit [DecidableEq I] in
theorem PhysicalTrail.trailEdges_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    {σ : Equiv.Perm I} {x : I → V} (h : PhysicalTrail G σ x) :
    trailEdges σ x ⊆ G.edgeFinset := by
  intro e he
  simp only [trailEdges, mem_image, mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact h.2.2 i

omit [Fintype V] [DecidableEq I] in
theorem PhysicalTrail.sum_trailEdges {G : SimpleGraph V} {σ : Equiv.Perm I} {x : I → V}
    (h : PhysicalTrail G σ x) (f : Sym2 V → ℤ) :
    ∑ e ∈ trailEdges σ x, f e = ∑ i, f s(x i, x (σ i)) := by
  rw [trailEdges, sum_image]
  intro i _ j _ hij
  exact h.2.1 hij

/-- The two-root same-part common-neighbour (root-clone) premise. -/
def CloneCondition (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (x y : I → V) : Prop :=
  ∀ i, ∀ j : Fin 2, β * Fintype.card V ≤
    ((univ.filter fun w => p w = j ∧ G.Adj (x i) w ∧ G.Adj (y i) w).card : ℝ)

/-- A physical coherent F0 transformer for `Hx` and `Hy` (no size bound). -/
def IsCoherentTransformer (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm I) (x y : I → V) (T : Finset (Sym2 V)) : Prop :=
  T ⊆ G.edgeFinset ∧ Disjoint T (trailEdges σ x ∪ trailEdges σ y) ∧
    HasDecomp p F0 (T ∪ trailEdges σ x) ∧ HasDecomp p F0 (T ∪ trailEdges σ y)

/-- Auxiliary vertices of `T`: its vertices outside all source/target roots. -/
def auxVertices (x y : I → V) (T : Finset (Sym2 V)) : Finset V :=
  (vertSet T).filter fun v => v ∉ univ.image x ∧ v ∉ univ.image y

/-- **The candidate target** (to be refuted). Constants `C, N` depend only on
`α, β, K`; they are chosen before the host, the positions and the roots. -/
def CandidateTarget (α β : ℝ) (K : ℕ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V)
      [DecidableRel G.Adj] (I : Type) [Fintype I] [DecidableEq I]
      (σ : Equiv.Perm I) (x y : I → V),
      N ≤ Fintype.card V → (∃ v, p v = 0) → (∃ v, p v = 1) →
      AntiEdgeful p F0 G α → Fintype.card I ≤ K →
      PhysicalTrail G σ x → PhysicalTrail G σ y →
      Disjoint (univ.image x) (univ.image y) → (∀ i, p (x i) = p (y i)) →
      CloneCondition p G β x y →
      ∃ T : Finset (Sym2 V), IsCoherentTransformer p G σ x y T ∧
        (T.card : ℝ) ≤ C * Fintype.card I ∧
        ((auxVertices x y T).card : ℝ) ≤ C * Fintype.card I

end PartitionedTriangleAbsorption.CoherentTransformer
