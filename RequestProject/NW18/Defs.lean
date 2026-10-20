/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Base

@[expose] public section

/-!
# Theorem 1.8 (Nash-Williams' Conjecture): definitions for the proof

Definitions used in the proof of Theorem 1.8 of Delcourt–Postle,
*A Proof of Nash-Williams' Conjecture* (arXiv:2606.11178), §12.

* `HingefulN` — Definition 13.15 with the hinge count normalised as `α n^{i-4}`
  (see the discussion below);
* `Theorem1316Statement` — Theorem 13.16 (the refined-absorption decomposition theorem for
  partitioned triangles, special case of the paper's reference [17]), used as an explicit
  hypothesis, as authorised;
* `IsExtremal` — `σ`-extremal graphs (Definition 12.2);
* `IsClose`, `T2T2`, `T2bT2`, `T2bT2b` — `α`-closeness (edit distance) to the three
  extremal graphs `T₂(n/2)+T₂(n/2)`, `T̄₂(n/2)+T₂(n/2)` and `T̄₂(n/2)+T̄₂(n/2)`;
* `IsRegularFracDecomp` — `C`-regular fractional triangle decompositions (Definition 2.5).

## About the normalisation of hingefulness

Definition 13.15 of the paper asks for `α · n^{i-2}` hinges with `i` vertices.  Every `K₃`-hinge
for two triangles `S, S'` sharing an edge contains all four vertices of `S ∪ S'`, so there are
at most `2^{i²} n^{i-4}` hinges with `i` vertices; hence, read literally, condition (ii) of
Theorem 13.16 can never hold for large `n` once two copies share an edge (for instance in every
graph with `δ(G) ≥ 3n/4` and `n ≥ 3`).  The paper itself uses the normalisation `n^{i-4}`:
Lemma 14.4 produces about `α n^4` hinges on `8` vertices.  We therefore state Theorem 13.16
with `α · n^{i-4}`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`(α, C)`-`F`-hingeful** (Definition 13.15, normalised as `α n^{i-4}`): for every two
`F`-copies `S, S'` of `G` sharing exactly one edge there is `i ∈ [C]` such that `G` contains at
least `α n^{i-4}` `F`-hinges for `S, S'` with exactly `i` vertices. -/
noncomputable def HingefulN {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (C : ℕ) : Prop :=
  open Classical in
  ∀ S S', IsCopy p F G S → IsCopy p F G S' → (triEdges S ∩ triEdges S').card = 1 →
    ∃ i ∈ Icc 1 C, α * (Fintype.card V : ℝ) ^ ((i : ℤ) - 4) ≤
      ((G.edgeFinset.powerset.filter
        (fun H => IsHinge p F S S' H ∧ (vertSet H).card = i)).card : ℝ)

/-- **Theorem 13.16** (Delcourt–Postle; special case of the decomposition theorem of their
reference [17]), as a proposition, with hingefulness normalised as `α n^{i-4}`.
For every real `α > 0`, integer `C ≥ 1` and family `F` of `t`-partitioned triangles there is a
real `ε > 0` such that, for `n` sufficiently large, every `t`-partitioned graph `G` on `n`
vertices which
1. is fractionally `F`-divisible and has a `C`-regular `ε`-almost fractional `F`-packing, and
2. is integrally `F`-divisible, `α`-`F`-anti-edgeful and `(α, C)`-`F`-hingeful,

has an `F`-decomposition.  This is **not** proved; it is used as an explicit hypothesis. -/
def Theorem1316Statement : Prop :=
  ∀ (t : ℕ) (F : Finset (Multiset (Fin t))), (∀ τ ∈ F, Multiset.card τ = 3) →
    ∀ α : ℝ, 0 < α → ∀ C : ℕ, 1 ≤ C →
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      IsFracDiv p F G.edgeFinset →
      (∃ φ, IsRegularAlmostPacking p F G C ε φ) →
      IsIntDiv p F G.edgeFinset → AntiEdgeful p F G α → HingefulN p F G α C →
      HasDecomp p F G.edgeFinset

/-! ### Extremality (Definition 12.2) -/

/-- Number of edges of `G` with exactly one end in `S` (the cut `(S, V ∖ S)`). -/
def cutSize (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card

/-- **`σ`-extremal** (Definition 12.2): (i) at least `(1 - σ) n` vertices have degree at most
`(3/4 + σ) n`, and (ii) the maximum cut of `G` has at least `(1 - σ) n² / 4` edges. -/
def IsExtremal (σ : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (1 - σ) * Fintype.card V ≤
      ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ) ∧
    ∃ S : Finset V, (1 - σ) * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (cutSize G S : ℝ)

/-! ### Closeness to the extremal graphs (§12) -/

/-- `G` is **`α`-close** to the graph `H` (on a vertex type of the same size): after adding
and/or deleting at most `α n²` edges, `G` becomes isomorphic to `H`. -/
def IsClose (α : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] {W : Type*} [Fintype W]
    [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∃ e : V ≃ W, ((symmDiff G.edgeFinset (SimpleGraph.comap (⇑e) H).edgeFinset).card : ℝ) ≤
    α * (Fintype.card V : ℝ) ^ 2

/-- The class (in `Fin 4`) of the vertex `i` of `Fin n` in the four-class layout used for the
extremal graphs: the first half `[0, ⌊n/2⌋)` carries `H₁` with classes `0, 1` (of sizes
`⌊m/2⌋`, `⌈m/2⌉` where `m = ⌊n/2⌋`), the second half carries `H₂` with classes `2, 3`. -/
def quarter (n : ℕ) (i : Fin n) : Fin 4 :=
  if (i : ℕ) < n / 2 then (if (i : ℕ) < n / 2 / 2 then 0 else 1)
  else (if (i : ℕ) - n / 2 < (n - n / 2) / 2 then 2 else 3)

/-- The graph on `Fin n` whose adjacency is given by a symmetric pattern on the four classes. -/
def patternGraph (n : ℕ) (P : Fin 4 → Fin 4 → Bool) (hP : ∀ a b, P a b = P b a) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ P (quarter n i) (quarter n j) = true
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [hP]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance (n : ℕ) (P : Fin 4 → Fin 4 → Bool) (hP : ∀ a b, P a b = P b a) :
    DecidableRel (patternGraph n P hP).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ P (quarter n i) (quarter n j) = true))

/-- Pattern of `T₂(n/2) + T₂(n/2)`: all four classes independent, all pairs of distinct classes
complete. -/
def patT2T2 (a b : Fin 4) : Bool := decide (a ≠ b)

/-- Pattern of `T̄₂(n/2) + T₂(n/2)`: classes `0, 1` are cliques with no edges between them,
classes `2, 3` are independent and completely joined, and the two halves are completely
joined. -/
def patT2bT2 (a b : Fin 4) : Bool :=
  decide ((a.val < 2) ≠ (b.val < 2) ∨ (a = b ∧ a.val < 2) ∨ (a ≠ b ∧ 2 ≤ a.val ∧ 2 ≤ b.val))

/-- Pattern of `T̄₂(n/2) + T̄₂(n/2)`: all four classes are cliques, classes `0, 1` are not
joined, classes `2, 3` are not joined, and the two halves are completely joined. -/
def patT2bT2b (a b : Fin 4) : Bool := decide ((a.val < 2) ≠ (b.val < 2) ∨ a = b)

/-- `T₂(n/2) + T₂(n/2)`: the join of two balanced complete bipartite graphs, i.e. the
complete balanced 4-partite graph. -/
def T2T2 (n : ℕ) : SimpleGraph (Fin n) :=
  patternGraph n patT2T2 (by decide)

/-- `T̄₂(n/2) + T₂(n/2)`: the join of two disjoint cliques with a balanced complete bipartite
graph. -/
def T2bT2 (n : ℕ) : SimpleGraph (Fin n) :=
  patternGraph n patT2bT2 (by decide)

/-- `T̄₂(n/2) + T̄₂(n/2)`: the join of two graphs that are each a disjoint union of two
cliques. -/
def T2bT2b (n : ℕ) : SimpleGraph (Fin n) :=
  patternGraph n patT2bT2b (by decide)

instance (n : ℕ) : DecidableRel (T2T2 n).Adj := by unfold T2T2; infer_instance
instance (n : ℕ) : DecidableRel (T2bT2 n).Adj := by unfold T2bT2; infer_instance
instance (n : ℕ) : DecidableRel (T2bT2b n).Adj := by unfold T2bT2b; infer_instance

/-! ### Regular fractional decompositions (Definition 2.5) -/

/-- A **`C`-regular fractional triangle decomposition** of `G` (Definition 2.5): a fractional
triangle decomposition in which every triangle of `G` has weight in `[1/(C n), C/n]`. -/
def IsRegularFracDecomp (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℝ)
    (w : Finset V → ℝ) : Prop :=
  NashWilliams.IsFractionalTriangleDecomposition G w ∧
    ∀ s ∈ G.cliqueFinset 3, 1 / (C * Fintype.card V) ≤ w s ∧ w s ≤ C / Fintype.card V

/-! ### Closeness to one of the three extremal graphs -/

/-- `G` (on `n` vertices) is `α`-close to one of `T₂(n/2)+T₂(n/2)`, `T̄₂(n/2)+T₂(n/2)` or
`T̄₂(n/2)+T̄₂(n/2)`. -/
def IsCloseToExtremal {V : Type*} [Fintype V] [DecidableEq V] (α : ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  IsClose α G (T2T2 (Fintype.card V)) ∨ IsClose α G (T2bT2 (Fintype.card V)) ∨
    IsClose α G (T2bT2b (Fintype.card V))

end NashWilliams18
