/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CloneSupply.Basic
public import PartitionedTriangleAbsorption.SignedCertificate.Basic

@[expose] public section

/-!
# The geometric hypotheses of the F₀ branch

The edit distance counts unordered, non-diagonal physical edges.  The two
models have precisely the prescribed balanced vertex partition; all vertex
sets are subsets of the original finite vertex type.

This module introduces definitions only.  In particular, `Statement` is a
target proposition, not a theorem.  The ambient host has no divisibility
field: a host obtained by sparse deletion need not itself be divisible.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced physical edge set on `D`. -/
def inducedEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) : Finset (Sym2 V) := G.edgeFinset ∩ triEdges D

/-- The union of the two complete graphs on the prescribed cut. -/
def cliqueModel (D X : Finset V) : Finset (Sym2 V) :=
  triEdges X ∪ triEdges (D \ X)

/-- The complete bipartite graph on the prescribed cut. -/
def bipartiteModel (D X : Finset V) : Finset (Sym2 V) :=
  triEdges D \ cliqueModel D X

/-- Unordered edge edit distance. -/
def editDistance (E H : Finset (Sym2 V)) : ℕ :=
  (E \ H).card + (H \ E).card

/-- Separation from both balanced extremal models inside `D`. -/
def Nonextreme (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (α : ℝ) : Prop :=
  ∀ X ⊆ D, X.card = D.card / 2 →
    α * (D.card : ℝ) ^ 2 < editDistance (inducedEdges G D) (bipartiteModel D X) ∧
    α * (D.card : ℝ) ^ 2 < editDistance (inducedEdges G D) (cliqueModel D X)

/-- Hypotheses 1, 2 and 4, without divisibility of the ambient host. -/
structure HostHyp (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α ε : ℝ) : Prop where
  part_size : ∀ i, (1 - ε) * Fintype.card V / 2 ≤ ((partSet p i).card : ℝ)
  internal_lower : ∀ v,
    (1 / 4 - ε) * Fintype.card V ≤ (partDeg p G (p v) v : ℝ)
  internal_upper : ∀ v,
    (partDeg p G (p v) v : ℝ) ≤ (1 / 4 + ε) * Fintype.card V
  cross_lower : ∀ v,
    (1 / 2 - ε) * Fintype.card V ≤ (partDeg p G (other0 (p v)) v : ℝ)
  good_part : ∃ i, Nonextreme G (partSet p i) α

/-- Literal asymptotic target with the project's integral divisibility API. -/
def Statement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
        HostHyp p G α ε → IsIntDiv p F0 G.edgeFinset → HasDecomp p F0 G.edgeFinset

end PartitionedTriangleAbsorption.BlowupB.F0Direct
