/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.LevelPackingF1

/-!
# Theorem 14.7 for `F₁`: the smallest missing statement of the level supply

`punctured_weighting` (proved) pays the damage `ζ` of the current graph as a LOAD LOSS: the loads
are within `32 (κ + 2ξ + 2ζ + ε)` of `1`, so the nibble (`F1_punctured_packing`) needs
`64 ζ ≤ τ(η)`, where `τ(η)` is the tolerance of the ported near-load nibble.  Along the vortex this
cannot be met with fixed constants (ledger §0sexies):

* the apex step needs `2γ + k/β' < s` with `γ = η|W|` (nibble residual) and `s ≈ ρ² |U_l|`
  (`apex_supply_lower`), i.e. `η ≪ ρ² β`;
* the pairing step covers every reserved cross edge `rv` (`v ∈ U`) not used by an apex by a
  triangle `r v v'` with `vv' ⊆ U`; so the damage passed to the next level is of order
  `deg_Res(v) ≈ ρ |W|` (`CrossResGood.r5`), i.e. `ζ' ≈ ρ / β` relative to `|U|`;
* the next level needs `64 ζ' ≤ τ(η)`, and the nibble tolerance `τ(η)` is much smaller than `η`.

Together: `η ≪ ρ² β ≲ β³ τ(η)² ≪ η`, a contradiction.  The circularity disappears iff the
damage need not be paid as a loss, i.e. iff the weighting can be CORRECTED for an arbitrary damage
of maximum degree `c₀ |W|` with `c₀` independent of the tolerance.  That is
`F1DamageRobustWeighting` below (NOT proved, a `def`); with it `ρ = c₀ β / 2`, `η ≪ c₀² β³`,
`τ = τ(η)`, and only `κ, ξ, ε` (fresh at every level from the original host and the sampling) have
to be below `τ`.

`F1_punctured_packing_of_robust` (proved) is the corresponding composition with the nibble, to
show exactly where the statement is used.  It is a reduction, not a closure.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- **Superseded: FALSE in this generality.**  A damage-robust near-unit weighting of the
punctured level: the damage bound `c₀` is FIXED, while the load tolerance `τ` is arbitrary (only
the class, typicality and reserve defects have to be small in terms of `τ`).  It omits the signed
balance forced by near-unit loads; `not_F1DamageRobustWeighting` (`RobustRefuteF1.lean`) proves
that it fails for every `c₀ > 0`.  The corrected target is `F1BalancedRobustWeighting`
(`BalancedWeightingF1.lean`). -/
def F1DamageRobustWeighting (c₀ b : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ σ : ℝ, 0 < σ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (W U : Finset V) (Res : Finset (Sym2 V)) (κ ξ ζ ε q : ℝ),
    N ≤ W.card → PuncHyp p G H W U Res κ ξ ζ ε q → κ + ξ + ε ≤ σ → ζ ≤ c₀ →
    ∃ φ : Finset V → ℝ, (∀ s, 0 ≤ φ s ∧ φ s ≤ b / W.card) ∧
      ∀ e ∈ (punc H W U Res).edgeFinset,
        |(∑ s ∈ copies p F1 (punc H W U Res) with e ∈ triEdges s, φ s) - 1| ≤ τ

/-- **Where the missing statement is used** (proved reduction): a damage-robust weighting gives
the approximate packing of the punctured level for damage up to the FIXED `c₀`. -/
theorem F1_punctured_packing_of_robust {c₀ b : ℝ} (hb : 0 < b)
    (hrob : F1DamageRobustWeighting c₀ b) (η : ℝ) (hη : 0 < η) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V)
      (Res : Finset (Sym2 V)) (κ ξ ζ ε q : ℝ),
      N ≤ W.card → PuncHyp p G H W U Res κ ξ ζ ε q → κ ≤ 1 / 16 → κ + ξ + ε ≤ σ → ζ ≤ c₀ →
      ∃ D₀ : Finset (Sym2 V), D₀ ⊆ H.edgeFinset ∧ HasDecomp p F1 D₀ ∧
        (∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U) ∧ Disjoint D₀ Res ∧
        ∀ v, ((((punc H W U Res).edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
          η * W.card := by
  obtain ⟨δ, hδ, N₁, hN₁⟩ := typed_nibble_on_set b η (1 / 16) hb hη (by norm_num)
  obtain ⟨σ, hσ, N₂, hN₂⟩ := hrob δ hδ
  refine ⟨σ, hσ, max N₁ N₂, ?_⟩
  intro V _ _ p G H _ _ W U Res κ ξ ζ ε q hN h hκ hσ' hζ
  classical
  obtain ⟨φ, hφ, hload⟩ := hN₂ V p G H W U Res κ ξ ζ ε q (le_trans (le_max_right _ _) hN) h hσ' hζ
  obtain ⟨D, Q, hQJ, hD, hres⟩ := hN₁ V W (le_trans (le_max_left _ _) hN) p F1
    (punc H W U Res) φ (fun x y hxy => hxy.2.1) hφ
    (fun v => (punc_degree_le h v).trans (by
      have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
      nlinarith))
    hload
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

/-- The proved weighting is the robust statement with damage bound proportional to the
tolerance (this is exactly what is too weak for the vortex). -/
theorem punctured_weighting_tolerance {V : Type} [Fintype V] [DecidableEq V] {p : V → Fin 4}
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] {W U : Finset V}
    {Res : Finset (Sym2 V)} {κ ξ ζ ε q τ : ℝ} (h : PuncHyp p G H W U Res κ ξ ζ ε q)
    (hσ : κ + ξ + ε ≤ τ / 128) (hζ : ζ ≤ τ / 128) :
    ∀ e ∈ (punc H W U Res).edgeFinset,
      |(∑ s ∈ copies p F1 (punc H W U Res) with e ∈ triEdges s, puncPhi W U q s) - 1| ≤ τ := by
  intro e he
  refine ((punctured_weighting h).2 e he).trans ?_
  have := h.hκ; have := h.hξ; have := h.hε
  nlinarith

end NashWilliams18.SpreadF1
