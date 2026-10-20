/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.StabFinal

@[expose] public section

/-!
# Abstract local facts for the extremal neighbourhood structure lemma (Lemma 9.5)

We isolate, as hypotheses on abstract data, the consequences of Lemmas 9.2 and 9.3 that are used
in the proof of Lemma 9.5.  Here `C` is the common neighbourhood of the ends of the negative
edge `f = uv`, `a` the rescaled value weighting `Val_f / (2 |φ(f)|)`, `g x y = |φ(xy)| / |φ(f)|`
if `xy` is a negative edge (and `0` otherwise), `U, W, A` the `u`-obtuse, `v`-obtuse and acute
vertices, `du y, dv y` the normalised demands `dem(uy, f) / |φ(f)|`, `dem(vy, f) / |φ(f)|`, and
`Su, Sv` the obtuse vertices whose other edge to `{u, v}` is very negative.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

/-- The local facts (consequences of Lemmas 9.2 and 9.3 for a good weighting). -/
structure LocFacts (C : Finset V) (a g : V → V → ℝ) (U W A : V → Prop) (du dv : V → ℝ)
    (Su Sv : Finset V) : Prop where
  thin : ThinWeights C a
  gsymm : ∀ x y, g x y = g y x
  g0 : ∀ x y, 0 ≤ g x y
  cov : ∀ x ∈ C, U x ∨ W x ∨ A x
  AU : ∀ x, A x → ¬ U x
  AW : ∀ x, A x → ¬ W x
  UW : ∀ x, U x → ¬ W x
  SuU : ∀ x ∈ Su, U x
  SvW : ∀ x ∈ Sv, W x
  UU : ∀ x ∈ C, ∀ y ∈ C, U x → U y → a x y = 0
  WW : ∀ x ∈ C, ∀ y ∈ C, W x → W y → a x y = 0
  AA : ∀ x ∈ C, ∀ y ∈ C, A x → A y → g x y = 0 → a x y = 0
  tri : ∀ x y z, 0 < g x y → 0 < g x z → 0 < g y z → False
  du0 : ∀ y, 0 ≤ du y
  dv0 : ∀ y, 0 ≤ dv y
  dsum : ∀ y ∈ C, du y + dv y = 1
  F4u : ∀ z ∈ C, ∀ y ∈ C, U z → A y → g z y = 0 → 2 * a z y ≤ dv y
  F4w : ∀ z ∈ C, ∀ y ∈ C, W z → A y → g z y = 0 → 2 * a z y ≤ du y
  F5u : ∀ z ∈ C, ∀ y ∈ C, U z → A y → 2 * a z y ≤ 1 + dv y
  F5w : ∀ z ∈ C, ∀ y ∈ C, W z → A y → 2 * a z y ≤ 1 + du y
  F6u : ∀ z ∈ C, ∀ y ∈ C, U z → A y → 0 < g z y → 2 * a z y - dv y ≤ g z y
  F6w : ∀ z ∈ C, ∀ y ∈ C, W z → A y → 0 < g z y → 2 * a z y - du y ≤ g z y
  F7 : ∀ x ∈ C, ∀ y ∈ C, ∀ e : ℝ, 0 ≤ e → e ≤ 1/6 → 1 - e ≤ a x y →
    (x ∈ Su ∧ y ∈ Sv) ∨ (x ∈ Sv ∧ y ∈ Su) ∨ 1 - 6 * e ≤ g x y

/-- Number of pairs `(x, y) ∈ P × Q` with `g x y ≥ 1 - η` (normal pairs). -/
noncomputable def nrm (g : V → V → ℝ) (η : ℝ) (P Q : Finset V) : ℕ :=
  ((P ×ˢ Q).filter fun p => 1 - η ≤ g p.1 p.2).card

end NashWilliams.Frac
