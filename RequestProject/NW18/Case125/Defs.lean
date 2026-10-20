/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128Reduction
public import PartitionedTriangleAbsorption.F0ParallelObstruction
public import PartitionedTriangleAbsorption.TypedPieceConditions

@[expose] public section

/-!
# Case (2) of §12.2 (Theorem 12.5): two-partitioned graphs

Notation of §15.2–15.3 of the paper for a graph `G` with a bipartition `p : V → Fin 2`
(the parts `V₁, V₂` of the paper are `p ⁻¹ {0}`, `p ⁻¹ {1}` here):

* `partClass p i` — the part `V_i`;
* `partDeg G p v i` — `d_i(v) = |N(v) ∩ V_i|`; `IntDeg(v) = d_{p v}(v)`, `CrossDeg(v)` is the
  degree into the other part;
* `intSurplus p E` — the internal surplus `IntSurplus = 2(e₁₁ + e₂₂) − e₁₂` of an edge set
  (Definition 15.1), written with the ordered edge-count vector `edgeVec` (which counts
  internal edges twice and cross edges once in the entry `(0, 1)`);
  *cross-divisible* means `intSurplus p E = 0`;
* `IsSideClose θ G D` — the induced graph `G[D]` is `θ`-close (edit distance at most
  `θ |D|²`) to `T₂(|D|)` (complete balanced bipartite graph) or to `T̄₂(|D|)` (two disjoint
  cliques of sizes `⌊|D|/2⌋`, `⌈|D|/2⌉`);
* `IsF0Idealized ε₀ G p` — hypotheses (a), (b) of Theorem 14.6.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The part `V_i = p⁻¹{i}`. -/
def partClass (p : V → Fin 2) (i : Fin 2) : Finset V := univ.filter (fun v => p v = i)

/-- `d_i(v) = |N(v) ∩ V_i|`, the degree of `v` into the part `i`. -/
def partDeg (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (v : V) (i : Fin 2) : ℕ :=
  (univ.filter (fun w => G.Adj v w ∧ p w = i)).card

/-- The internal surplus `IntSurplus = 2(e₁₁ + e₂₂) − e₁₂` (Definition 15.1) of the edge set
`E` with respect to the bipartition `p`.  In terms of the ordered edge-count vector:
`edgeVec p E 0 0 = 2 e₁₁`, `edgeVec p E 1 1 = 2 e₂₂`, `edgeVec p E 0 1 = e₁₂`. -/
def intSurplus (p : V → Fin 2) (E : Finset (Sym2 V)) : ℤ :=
  edgeVec p E 0 0 + edgeVec p E 1 1 - edgeVec p E 0 1

/-- The target adjacency of `T₂` (`b = true`: complete bipartite between `X` and its
complement) or of `T̄₂` (`b = false`: `X` and its complement are cliques, not joined). -/
def sideTarget (X : Finset V) (b : Bool) (x y : V) : Prop :=
  if b then (x ∈ X ↔ y ∉ X) else (x ∈ X ↔ y ∈ X)

open Classical in
/-- Number of ordered pairs of distinct vertices of `D` on which `G` differs from the target
`sideTarget X b` (twice the edit distance of `G[D]` to the target graph). -/
noncomputable def sideCost (G : SimpleGraph V) (D X : Finset V) (b : Bool) : ℕ :=
  ((D ×ˢ D).filter (fun q => q.1 ≠ q.2 ∧ ¬ (G.Adj q.1 q.2 ↔ sideTarget X b q.1 q.2))).card

/-- `G[D]` is `θ`-close to `T₂(|D|)` or to `T̄₂(|D|)`: for some split of `D` into parts of sizes
`⌊|D|/2⌋` and `⌈|D|/2⌉`, at most `θ |D|²` edges have to be changed in `G[D]` to obtain the
complete bipartite graph (`b = true`) or the disjoint union of two cliques (`b = false`) with
these parts. -/
def IsSideClose (θ : ℝ) (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∃ X ⊆ D, X.card = D.card / 2 ∧ ∃ b : Bool, (sideCost G D X b : ℝ) ≤ 2 * θ * (D.card : ℝ) ^ 2

/-- Hypotheses (a) and (b) of Theorem 14.6 (idealized `F₀`-decomposition): both parts have
size at least `(1 − ε₀) n / 2`, every vertex has `(1/4 − ε₀) n ≤ IntDeg(v) ≤ (1/4 + ε₀) n` and
cross degree at least `(1/2 − ε₀) n`. -/
def IsF0Idealized (ε₀ : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) : Prop :=
  (∀ i, (1 - ε₀) * Fintype.card V / 2 ≤ ((partClass p i).card : ℝ)) ∧
  (∀ v, (1 / 4 - ε₀) * Fintype.card V ≤ (partDeg G p v (p v) : ℝ) ∧
      (partDeg G p v (p v) : ℝ) ≤ (1 / 4 + ε₀) * Fintype.card V) ∧
  (∀ v i, i ≠ p v → (1 / 2 - ε₀) * Fintype.card V ≤ (partDeg G p v i : ℝ))

/-- A **2-partitioned graph is `γ`-extremal** (Definition 15.3): (i) at least `(1 − γ) n`
vertices have degree at most `(3/4 + γ) n`, and (ii) `e(V₁, V₂) ≥ (1 − γ) n² / 4`. -/
def IsTwoExtremal (γ : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) : Prop :=
  (1 - γ) * Fintype.card V ≤
      ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + γ) * Fintype.card V)).card : ℝ) ∧
    (1 - γ) * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (cutSize G (partClass p 0) : ℝ)

/-- **`γ`-cross-balanced** (Definition 15.3): `IntDeg(v) ≤ CrossDeg(v) + γ n` for every `v`. -/
def IsCrossBalanced (γ : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) : Prop :=
  ∀ v i, i ≠ p v → (partDeg G p v (p v) : ℝ) ≤ partDeg G p v i + γ * Fintype.card V

/-- A **triangle packing** of `G`: triangles of `G` that are pairwise edge-disjoint. -/
def IsTrianglePacking (G : SimpleGraph V) (T : Finset (Finset V)) : Prop :=
  (∀ s ∈ T, G.IsNClique 3 s) ∧ (T : Set (Finset V)).PairwiseDisjoint triEdges

end NashWilliams18
