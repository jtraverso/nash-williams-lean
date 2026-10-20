/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationLinks
public import PartitionedTriangleAbsorption.RootedEmbeddingSelection

/-! # Root-clone supply: definitions

All sets are computed from the actual adjacency of `G` and the labels `p`;
nothing here is a geometric oracle. `n = Fintype.card V`.

* `partSet p i` is `V_i = {v : p v = i}`;
* `partNbrs p G i x` is `N_i(x) = {v : p v = i ∧ G.Adj x v}`;
* `partDeg p G i x` is `d_i(x) = |N_i(x)|`;
* `commonCount p G i x y` is `c_i(x,y) = |N_i(x) ∩ N_i(y)|`;
* `commonPart p G k x y` is the set of common neighbours of `x, y` in part `k`;
* `beta α = α² / 2`;
* `cloneSet p G α i x` is `Y_x = {y ∈ V_i : c_i(x,y) ≥ β n}`.

`Y_x` may contain `x` itself; membership in `Y_x` is not a distinctness claim.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CloneSupply

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `V_i`: the vertices of part `i`. -/
def partSet (p : V → Fin 2) (i : Fin 2) : Finset V :=
  univ.filter fun v => p v = i

/-- `N_i(x)`: the neighbours of `x` lying in part `i`. -/
def partNbrs (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin 2)
    (x : V) : Finset V :=
  univ.filter fun v => p v = i ∧ G.Adj x v

/-- `d_i(x) = |N_i(x)|`. -/
def partDeg (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin 2)
    (x : V) : ℕ :=
  (partNbrs p G i x).card

/-- `c_i(x,y) = |N_i(x) ∩ N_i(y)|`. -/
def commonCount (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin 2)
    (x y : V) : ℕ :=
  (partNbrs p G i x ∩ partNbrs p G i y).card

/-- Common neighbours of `x` and `y` in the prescribed part `k`. -/
def commonPart (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (k : Fin 2)
    (x y : V) : Finset V :=
  univ.filter fun w => p w = k ∧ G.Adj x w ∧ G.Adj y w

/-- The clone threshold constant `β = α² / 2`. -/
noncomputable def beta (α : ℝ) : ℝ := α ^ 2 / 2

/-- `Y_x = {y ∈ V_i : c_i(x,y) ≥ β n}`. It may contain `x`. -/
noncomputable def cloneSet (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (i : Fin 2) (x : V) : Finset V :=
  (partSet p i).filter fun y =>
    beta α * (Fintype.card V : ℝ) ≤ (commonCount p G i x y : ℝ)

omit [DecidableEq V] in
theorem mem_partSet {p : V → Fin 2} {i : Fin 2} {v : V} :
    v ∈ partSet p i ↔ p v = i := by
  simp [partSet]

omit [DecidableEq V] in
theorem mem_partNbrs {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {i : Fin 2} {x v : V} : v ∈ partNbrs p G i x ↔ p v = i ∧ G.Adj x v := by
  simp [partNbrs]

omit [DecidableEq V] in
theorem mem_commonPart {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : Fin 2} {x y w : V} :
    w ∈ commonPart p G k x y ↔ p w = k ∧ G.Adj x w ∧ G.Adj y w := by
  simp [commonPart]

theorem mem_cloneSet {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {α : ℝ} {i : Fin 2} {x y : V} :
    y ∈ cloneSet p G α i x ↔
      p y = i ∧ beta α * (Fintype.card V : ℝ) ≤ (commonCount p G i x y : ℝ) := by
  simp [cloneSet, partSet]

/-- In the same part, the common-neighbour set is exactly `N_i(x) ∩ N_i(y)`. -/
theorem commonPart_same (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (x y : V) :
    commonPart p G i x y = partNbrs p G i x ∩ partNbrs p G i y := by
  ext w
  simp only [mem_commonPart, mem_inter, mem_partNbrs]
  tauto

theorem commonCount_eq_card_commonPart (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (i : Fin 2) (x y : V) :
    commonCount p G i x y = (commonPart p G i x y).card := by
  rw [commonCount, commonPart_same]

omit [DecidableEq V] in
theorem partDeg_le_card (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (x : V) : partDeg p G i x ≤ Fintype.card V :=
  card_le_univ _

theorem commonCount_le_card (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (x y : V) : commonCount p G i x y ≤ Fintype.card V :=
  card_le_univ _

/-- Both F0 types: `{i,i,j}` belongs to `F0` whenever `i ≠ j`. -/
theorem iij_mem_F0 (i j : Fin 2) (hij : i ≠ j) :
    ({i, i, j} : Multiset (Fin 2)) ∈ TypedApplicationLinks.F0 := by
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | decide

/-- The same type with the new corner listed last in part `i`: `{i,j,i} ∈ F0`. -/
theorem iji_mem_F0 (i j : Fin 2) (hij : i ≠ j) :
    ({i, j, i} : Multiset (Fin 2)) ∈ TypedApplicationLinks.F0 := by
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | decide

/-- In `Fin 2`, a label different from `i` is the other part. -/
theorem exists_other (i : Fin 2) : ∃ j : Fin 2, j ≠ i := by
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

end PartitionedTriangleAbsorption.CloneSupply
