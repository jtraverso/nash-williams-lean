/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.HingeModel

/-!
# Hinge configurations for Lemma 14.4

The eight vertices `u₁, u₂, v₁, v₂, x₁, x₂, x₃, x₄` of a configuration, configurations of a
model hinge, and their number.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The eight vertices of a configuration, as a map `Fin 8 → V`. -/
def cfgVec (u₁ u₂ v₁ v₂ : V) (x : V × V × V × V) : Fin 8 → V :=
  ![u₁, u₂, v₁, v₂, x.1, x.2.1, x.2.2.1, x.2.2.2]

section cfgVecValues
omit [Fintype V] [DecidableEq V]
variable (u₁ u₂ v₁ v₂ x₁ x₂ x₃ x₄ : V)
@[simp] lemma cfgVec_0 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 0 = u₁ := rfl
@[simp] lemma cfgVec_1 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 1 = u₂ := rfl
@[simp] lemma cfgVec_2 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 2 = v₁ := rfl
@[simp] lemma cfgVec_3 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 3 = v₂ := rfl
@[simp] lemma cfgVec_4 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 4 = x₁ := rfl
@[simp] lemma cfgVec_5 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 5 = x₂ := rfl
@[simp] lemma cfgVec_6 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 6 = x₃ := rfl
@[simp] lemma cfgVec_7 : cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) 7 = x₄ := rfl
end cfgVecValues

/-- A **configuration** for the model hinge `M` (`mH1` or `mH2`) and the triangles `u₁u₂v₁`,
`u₁u₂v₂`: four further vertices such that all eight vertices are distinct and every edge of the
model hinge is an edge of `G`.  For `M = mH1` this says that `x₁, …, x₄` are common neighbours
of `v₁, v₂` and `u₁ x₁ x₂ x₃ x₄ u₂` is a path; for `M = mH2` (with `x = (w, a, b, c)`) that `w`
is adjacent to `u₁, v₁, v₂, a, b, c`, that `u₂` is adjacent to `a, b, c`, and that `v₁ a b c v₂`
is a path. -/
def IsCfg (M : Finset (Sym2 (Fin 8))) (G : SimpleGraph V) (u₁ u₂ v₁ v₂ : V)
    (x : V × V × V × V) : Prop :=
  Function.Injective (cfgVec u₁ u₂ v₁ v₂ x) ∧
    ∀ i j : Fin 8, s(i, j) ∈ M → G.Adj (cfgVec u₁ u₂ v₁ v₂ x i) (cfgVec u₁ u₂ v₁ v₂ x j)

open Classical in
/-- The number of configurations of type `M`. -/
noncomputable def cfgCount (M : Finset (Sym2 (Fin 8))) (G : SimpleGraph V) (u₁ u₂ v₁ v₂ : V) :
    ℕ :=
  ((univ : Finset (V × V × V × V)).filter (fun x => IsCfg M G u₁ u₂ v₁ v₂ x)).card

end NashWilliams18
