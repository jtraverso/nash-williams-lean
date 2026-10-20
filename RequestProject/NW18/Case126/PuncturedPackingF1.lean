/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.SetNibbleF1

/-!
# Theorem 14.7 for `F₁`: the approximate packing `D₀` of the actual punctured level (producer)

Producer obligation 3, first half.  `F1_punctured_packing` (proved) composes

* the normalised punctured weighting of the actual damaged level (`punctured_weighting`, loads
  within `32 (κ + 2ξ + 2ζ + ε)` of `1`, weights `≤ 8/|W|`),
* the degree gap of the punctured level (`punc_degree_le`, `(1 - 1/16)|W|` for `κ ≤ 1/16`), and
* the ported typed near-load nibble, transported to the vertex set `W` (`typed_nibble_on_set`).

For every `η > 0` there are a tolerance `τ > 0` and `N` such that, whenever the level has
`|W| ≥ N`, satisfies `PuncHyp` and `32 (κ + 2ξ + 2ζ + ε) ≤ τ`, there is an `F₁`-decomposable
`D₀ ⊆ E(H)` with no edge inside `U` and no reserved edge, whose complement in the punctured level
(the edges of `H` inside `W`, not inside `U`, not reserved) has maximum degree `≤ η |W|`.

**Parameter caveat.**  The damage `ζ` enters the load tolerance additively (`64 ζ ≤ τ`).  The
tolerance `τ` of the nibble is far smaller than `η`.  At the next vortex level the damage equals
the visit load of the pairing step, of order `ρ / β` where `ρ` is the reserve density, while the
apex supply requires `η ≪ ρ² β`.  These constraints cannot hold simultaneously with fixed
constants; see the ledger §0sexies.  This theorem is therefore usable at a level whose damage is
small compared with `τ` (e.g. the first level, whose damage is `0`), not as the inductive step.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- **Approximate packing of the actual punctured level** (producer, proved). -/
theorem F1_punctured_packing (η : ℝ) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V)
      (Res : Finset (Sym2 V)) (κ ξ ζ ε q : ℝ),
      N ≤ W.card → PuncHyp p G H W U Res κ ξ ζ ε q → κ ≤ 1 / 16 →
      32 * (κ + 2 * ξ + 2 * ζ + ε) ≤ τ →
      ∃ D₀ : Finset (Sym2 V), D₀ ⊆ H.edgeFinset ∧ HasDecomp p F1 D₀ ∧
        (∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U) ∧ Disjoint D₀ Res ∧
        ∀ v, ((((punc H W U Res).edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
          η * W.card := by
  obtain ⟨δ, hδ, N, hN⟩ := typed_nibble_on_set 8 η (1 / 16) (by norm_num) hη (by norm_num)
  refine ⟨δ, hδ, N, ?_⟩
  intro V _ _ p G H _ _ W U Res κ ξ ζ ε q hNW h hκ hτ
  classical
  obtain ⟨hφ, hload⟩ := punctured_weighting h
  obtain ⟨D, Q, hQJ, hD, hres⟩ := hN V W hNW p F1 (punc H W U Res) (puncPhi W U q)
    (fun x y hxy => hxy.2.1) hφ
    (fun v => (punc_degree_le h v).trans (by
      have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
      nlinarith))
    (fun e he => (hload e he).trans hτ)
  have hQp : ∀ e ∈ Q, ∃ a b, e = s(a, b) ∧ (punc H W U Res).Adj a b := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, b, rfl, SimpleGraph.mem_edgeFinset.mp (hQJ he)⟩
  refine ⟨Q, ?_, ⟨D, hD⟩, ?_, ?_, hres⟩
  · intro e he
    obtain ⟨a, b, rfl, hab⟩ := hQp e he
    exact SimpleGraph.mem_edgeFinset.mpr hab.1
  · intro e he hall
    obtain ⟨a, b, rfl, hab⟩ := hQp e he
    exact hab.2.2.2.1 ⟨hall a (Sym2.mem_mk_left _ _), hall b (Sym2.mem_mk_right _ _)⟩
  · rw [disjoint_left]
    intro e he heR
    obtain ⟨a, b, rfl, hab⟩ := hQp e he
    exact hab.2.2.2.2 heR

end NashWilliams18.SpreadF1
