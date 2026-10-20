/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.RobustRefuteF1

/-!
# Theorem 14.7 for `F₁`: the corrected (balanced) robust weighting and the actual-level producer

`F1DamageRobustWeighting` is false (`not_F1DamageRobustWeighting`): it ignores the signed balance
that near-unit loads force.  This file states the corrected intermediate target and the proved
application-level producer around it.

* `F1BalancedRobustWeighting c₀ b` (**OPEN**, a `def`, not proved): the same statement with the
  additional premise `|balance(punc)| ≤ σ |W|²`.  It is the fractional correction of step 3 of the
  repair plan.  Nothing here proves it, assumes that a fractional LP is feasible, or claims that
  the balance condition is sufficient.
* `balance_premise_necessary` (proved): the added premise is necessary at the scale of the
  tolerance: any real weighting with loads within `τ` of `1` forces `|balance(punc)| ≤ τ |W|²`.
* `F1_punctured_packing_of_balanced_robust` (proved reduction): the corrected target gives the
  approximate packing of the punctured level with damage up to the FIXED `c₀`.
* `F1_actual_punctured_packing` (proved reduction): the ACTUAL-level producer.  Its premises are
  the actual vortex data — `PuncHyp`, integral divisibility of `H` inside `W`, protection of the
  child `U`, the SAME jointly good reserve (`CrossResGood`) — plus the compatibility premise
  `|ρ · bdDamCharge| ≤ σ' |W|²` (signed charge of the damaged boundary, **OPEN** as a next-level
  invariant).  The balance premise of the corrected target is DERIVED from these via
  `punctured_balance_defect`, not assumed.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.F1BalanceGateStage228 (pairCharge charge balance)

/-- **The corrected robust weighting (OPEN — NOT proved).**  As `F1DamageRobustWeighting`, but the
punctured level must be nearly balanced: `|balance(punc)| ≤ σ |W|²`.  The damage bound `c₀` is
fixed, the tolerance `τ` arbitrary. -/
def F1BalancedRobustWeighting (c₀ b : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ σ : ℝ, 0 < σ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (W U : Finset V) (Res : Finset (Sym2 V)) (κ ξ ζ ε q : ℝ),
    N ≤ W.card → PuncHyp p G H W U Res κ ξ ζ ε q → κ + ξ + ε ≤ σ → ζ ≤ c₀ →
    |balance p (punc H W U Res).edgeFinset| ≤ σ * W.card * W.card →
    ∃ φ : Finset V → ℝ, (∀ s, 0 ≤ φ s ∧ φ s ≤ b / W.card) ∧
      ∀ e ∈ (punc H W U Res).edgeFinset,
        |(∑ s ∈ copies p F1 (punc H W U Res) with e ∈ triEdges s, φ s) - 1| ≤ τ

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The absolute charge mass of the punctured level is at most `|W|²`. -/
theorem punc_mass_le (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V)
    (Res : Finset (Sym2 V)) :
    ∑ e ∈ (punc H W U Res).edgeFinset, |charge p e| ≤ (W.card : ℝ) * W.card := by
  have h2 := sum_edges_two (punc H W U Res) (fun e => |charge p e|)
  have hv : ∀ v, (∑ z ∈ univ.filter ((punc H W U Res).Adj v), |charge p s(v, z)|) ≤
      if v ∈ W then (2 : ℝ) * W.card else 0 := by
    intro v
    split_ifs with hvW
    · have hz : ∀ z ∈ univ.filter ((punc H W U Res).Adj v), |charge p s(v, z)| ≤ 2 := by
        intro z _
        rw [charge_mk]
        have : ∀ a b : Fin 4, |(pairCharge a b : ℝ)| ≤ 2 := by
          intro a b; unfold pairCharge; split_ifs <;> norm_num
        exact this _ _
      refine (sum_le_sum hz).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have hsub : univ.filter ((punc H W U Res).Adj v) ⊆ W := fun z hz =>
        ((punc_adj H W U Res v z).mp (mem_filter.mp hz).2).2.2.1
      have : ((univ.filter ((punc H W U Res).Adj v)).card : ℝ) ≤ W.card := by
        exact_mod_cast card_le_card hsub
      linarith
    · refine le_of_eq (sum_eq_zero fun z hz => ?_)
      exact absurd ((punc_adj H W U Res v z).mp (mem_filter.mp hz).2).2.1 hvW
  have := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hv v)
  rw [← h2, ← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter, univ_inter] at this
  linarith

/-- **The added premise is necessary** (proved): a real weighting of the `F₁`-copies of the
punctured level with all loads within `τ` of `1` forces `|balance(punc)| ≤ τ |W|²`. -/
theorem balance_premise_necessary (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) (Res : Finset (Sym2 V)) (φ : Finset V → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hload : ∀ e ∈ (punc H W U Res).edgeFinset,
      |(∑ s ∈ copies p F1 (punc H W U Res) with e ∈ triEdges s, φ s) - 1| ≤ τ) :
    |balance p (punc H W U Res).edgeFinset| ≤ τ * W.card * W.card := by
  have h := F1BalanceGateStage228.graph_near_load_requires_balance p (punc H W U Res) φ τ hload
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (punc_mass_le p H W U Res) hτ

/-- **Where the corrected target is used** (proved reduction): it gives the approximate packing
of a nearly balanced punctured level for damage up to the FIXED `c₀`. -/
theorem F1_punctured_packing_of_balanced_robust {c₀ b : ℝ} (hb : 0 < b)
    (hrob : F1BalancedRobustWeighting c₀ b) (η : ℝ) (hη : 0 < η) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V)
      (Res : Finset (Sym2 V)) (κ ξ ζ ε q : ℝ),
      N ≤ W.card → PuncHyp p G H W U Res κ ξ ζ ε q → κ ≤ 1 / 16 → κ + ξ + ε ≤ σ → ζ ≤ c₀ →
      |balance p (punc H W U Res).edgeFinset| ≤ σ * W.card * W.card →
      ∃ D₀ : Finset (Sym2 V), D₀ ⊆ H.edgeFinset ∧ HasDecomp p F1 D₀ ∧
        (∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U) ∧ Disjoint D₀ Res ∧
        ∀ v, ((((punc H W U Res).edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
          η * W.card := by
  obtain ⟨δ, hδ, N₁, hN₁⟩ := typed_nibble_on_set b η (1 / 16) hb hη (by norm_num)
  obtain ⟨σ, hσ, N₂, hN₂⟩ := hrob δ hδ
  refine ⟨σ, hσ, max N₁ N₂, ?_⟩
  intro V _ _ p G H _ _ W U Res κ ξ ζ ε q hN h hκ hσ' hζ hbal
  classical
  obtain ⟨φ, hφ, hload⟩ :=
    hN₂ V p G H W U Res κ ξ ζ ε q (le_trans (le_max_right _ _) hN) h hσ' hζ hbal
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

/-- If every edge of `H` lies inside `W`, the divisibility premise is about `H` itself. -/
theorem edgesIn_eq_edgeFinset (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V)
    (hW : ∀ a b, H.Adj a b → a ∈ W ∧ b ∈ W) : edgesIn H W = H.edgeFinset := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [edgesIn, mem_filter, mk_all_mem, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact ⟨fun h => h.1, fun h => ⟨h, hW a b h⟩⟩

/-- **The actual-level producer** (proved reduction to the OPEN `F1BalancedRobustWeighting`).
Premises: the actual level (`PuncHyp`), integral `F₁`-divisibility of `H` inside `W`, protection
of the child `U`, the SAME jointly good reserve `Res` (`CrossResGood`, density `ρ ∈ [0,1]`), and
the boundary-charge compatibility `|ρ · bdDamCharge| ≤ σ' |W|²`.  The near-balance required by
the corrected target is derived (`punctured_balance_defect`), with the damage bound `c₀` fixed and
independent of the load tolerance. -/
theorem F1_actual_punctured_packing {c₀ b : ℝ} (hb : 0 < b)
    (hrob : F1BalancedRobustWeighting c₀ b) (η : ℝ) (hη : 0 < η) :
    ∃ σ' : ℝ, 0 < σ' ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V)
      (Res : Finset (Sym2 V)) (κ ξ ζ ε q ρ ε' : ℝ),
      N ≤ W.card → PuncHyp p G H W U Res κ ξ ζ ε q → IsIntDiv p F1 (edgesIn H W) →
      (∀ a ∈ U, ∀ b ∈ U, G.Adj a b → H.Adj a b) →
      CrossResGood p H W U Res ρ ε' → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ ε' →
      κ ≤ 1 / 16 → κ + ξ + ε + ε' ≤ σ' → ζ ≤ c₀ →
      |ρ * bdDamCharge p G H W U| ≤ σ' * W.card * W.card →
      ∃ D₀ : Finset (Sym2 V), D₀ ⊆ H.edgeFinset ∧ HasDecomp p F1 D₀ ∧
        (∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U) ∧ Disjoint D₀ Res ∧
        ∀ v, ((((punc H W U Res).edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
          η * W.card := by
  obtain ⟨σ, hσ, N, hN⟩ := F1_punctured_packing_of_balanced_robust hb hrob η hη
  refine ⟨σ / 13, by positivity, N, ?_⟩
  intro V _ _ p G H _ _ W U Res κ ξ ζ ε q ρ ε' hNW h hdiv hprot hR hρ0 hρ1 hε' hκ hs hζ hdam
  have hdef := punctured_balance_defect h hdiv hprot hR hρ0 hε'
  have hκ0 := h.hκ; have hξ0 := h.hξ; have hε0 := h.hε
  have hW0 : (0 : ℝ) ≤ W.card * W.card := by positivity
  have hcoef : (2 * κ + ξ) + 6 * ε' + ρ * (4 * κ + 2 * ξ) ≤ 12 * (σ / 13) := by
    have : ρ * (4 * κ + 2 * ξ) ≤ 4 * κ + 2 * ξ := by
      have : 0 ≤ 4 * κ + 2 * ξ := by positivity
      nlinarith
    linarith
  refine hN V p G H W U Res κ ξ ζ ε q hNW h hκ (by linarith) hζ ?_
  have h1 : |balance p (punc H W U Res).edgeFinset| ≤
      |balance p (punc H W U Res).edgeFinset - ρ * bdDamCharge p G H W U| +
        |ρ * bdDamCharge p G H W U| := by
    have := abs_add_le (balance p (punc H W U Res).edgeFinset - ρ * bdDamCharge p G H W U)
      (ρ * bdDamCharge p G H W U)
    simpa using this
  have h2 : ((2 * κ + ξ) + 6 * ε' + ρ * (4 * κ + 2 * ξ)) * W.card * W.card ≤
      12 * (σ / 13) * W.card * W.card := by
    rw [mul_assoc, mul_assoc (12 * (σ / 13))]
    exact mul_le_mul_of_nonneg_right hcoef hW0
  have h3 : σ / 13 * W.card * W.card + 12 * (σ / 13) * W.card * W.card =
      σ * W.card * W.card := by ring
  linarith

end NashWilliams18.SpreadF1
