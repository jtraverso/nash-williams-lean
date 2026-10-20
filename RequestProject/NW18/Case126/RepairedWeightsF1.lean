/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.PuncturedExactWeightsF1
public import PartitionedTriangleAbsorption.F1ReserveCorrectionStage231

@[expose] public section

/-!
# Physical reserve repair followed by exact positive weights on the punctured `F₁` level

`F1_repaired_punctured_exact_weights` composes, on the SAME actual level:

1. Stage 231 (`exists_balanced_reserve_extension`): from the integrally divisible level
   `E = edgesIn H W`, the protected child edges `I = edgesIn H U`, the sampled reserve
   `R ⊆ E \ I` and two actual pools `P, M ⊆ (E \ I) \ R` of charges `+1`, `-2` satisfying the
   explicit cardinality/tail inequalities, it builds the corrected reserve `R' = R ∪ C` with
   `balance((E \ I) \ R') = 0`, `|C| ≤ 2(|q|+1)` and `Δ(C) ≤ 2(r D + b)`;
2. `F1_punctured_exact_weights` with the corrected reserve `R'`: the reserve-degree bound used
   is the actual degree of `R'` (old degree plus the correction degree).

The output is the corrected reserve together with exact positive weights on the actual
F1 triangles of `punc H W U R'`. Nothing here assumes that `R'` is an independent sample; the
corrected reserve's degree is bounded deterministically. Pools on the boundary `(W \ U, U)` and
the verification of the size/tail inequalities from the actual graph are NOT constructed here.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.F1BalanceGateStage228 (charge balance)
open PartitionedTriangleAbsorption.F1ReserveCorrectionStage231 (integerBalance
  exists_balanced_reserve_extension)
open scoped NNReal

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Vertex-neighbourhood count through a reserve is at most the reserve degree. -/
theorem nbr_card_le_deg (W : Finset V) (R : Finset (Sym2 V)) (u : V) :
    (W.filter fun v => s(u, v) ∈ R).card ≤ (R.filter fun e => u ∈ e).card := by
  apply card_le_card_of_injOn (fun v => s(u, v))
  · intro v hv
    simp only [coe_filter, Set.mem_setOf_eq] at hv
    exact mem_filter.mpr ⟨hv.2, Sym2.mem_mk_left _ _⟩
  · intro v _ w _ he
    exact Sym2.congr_right.mp he

/-- **Reserve repair + exact positive weights on the actual punctured level.** -/
theorem F1_repaired_punctured_exact_weights (p : V → Fin 4) (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V) (R P M : Finset (Sym2 V))
    {κ ξ ζ β ρ ρ' : ℝ} (r : ℝ≥0) (hr : r ≤ 1) (a b Dp : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hDp : 0 < Dp)
    (hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) (hHG : H ≤ G)
    (hcls : ∀ j : Fin 4, |((W.filter fun z => p z = j).card : ℝ) - W.card / 4| ≤ κ * W.card)
    (htyp : ∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card)
    (hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card)
    (hU : (U.card : ℝ) ≤ β * W.card) (hUW : U ⊆ W)
    (hdiv : IsIntDiv p F1 (edgesIn H W))
    (hR : R ⊆ edgesIn H W \ edgesIn H U)
    (hRdeg : ∀ v, ((R.filter fun e => v ∈ e).card : ℝ) ≤ ρ * W.card)
    (hpools : P ∪ M ⊆ (edgesIn H W \ edgesIn H U) \ R)
    (hP : 0 < P.card) (hM : 0 < M.card) (hPM : Disjoint P M)
    (hchargeP : ∀ e ∈ P, charge p e = 1) (hchargeM : ∀ e ∈ M, charge p e = -2)
    (hdegP : ∀ v, ((P.filter fun e => v ∈ e).card : ℝ) ≤ Dp)
    (hdegM : ∀ v, ((M.filter fun e => v ∈ e).card : ℝ) ≤ Dp)
    (hsizeP : (((-integerBalance p (edgesIn H U) - integerBalance p R).natAbs + 1 : ℕ) : ℝ)
      ≤ r * P.card - a)
    (hsizeM : (((-integerBalance p (edgesIn H U) - integerBalance p R).natAbs + 1 : ℕ) : ℝ)
      ≤ r * M.card - a)
    (htailP : 2 * Real.exp (-2 * a ^ 2 / P.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / Dp)) < 1)
    (htailM : 2 * Real.exp (-2 * a ^ 2 / M.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / Dp)) < 1)
    (hρ' : ρ * W.card + 2 * (r * Dp + b) ≤ ρ' * W.card)
    (hsmall : 3 * ξ + ζ + β + ρ' + 6 * κ ≤ 1 / 5120) (hN : 20480 ≤ W.card) :
    ∃ R' : Finset (Sym2 V), R ⊆ R' ∧ R' ⊆ edgesIn H W \ edgesIn H U ∧ R' \ R ⊆ P ∪ M ∧
      (R' \ R).card ≤
        2 * ((-integerBalance p (edgesIn H U) - integerBalance p R).natAbs + 1) ∧
      (∀ v, (((R' \ R).filter fun e => v ∈ e).card : ℝ) ≤ 2 * (r * Dp + b)) ∧
      balance p (punc H W U R').edgeFinset = 0 ∧
      ∃ w : Finset V → ℝ,
        (∀ e ∈ (punc H W U R').edgeFinset,
          F1BalanceGateStage228.load (copies p F1 (punc H W U R')) w e = 1) ∧
        (∀ x ∈ copies p F1 (punc H W U R'), 1 / (2 * W.card) ≤ w x ∧ w x ≤ 3 / W.card) ∧
        (∀ x ∉ copies p F1 (punc H W U R'), w x = 0) := by
  have hI : edgesIn H U ⊆ edgesIn H W := by
    intro e he
    simp only [edgesIn, mem_filter] at he ⊢
    exact ⟨he.1, fun v hv => hUW (he.2 v hv)⟩
  have hsupport : ∀ e ∈ edgesIn H W, ∀ v ∈ e, v ∈ W := fun e he => (mem_filter.mp he).2
  obtain ⟨R', hRR', hR'E, hR'C, hbal, hcard, hdegC, hdegR'⟩ :=
    exists_balanced_reserve_extension p W (edgesIn H W) (edgesIn H U) R P M r hr a b Dp ha hb
      hDp hI hR (balance_eq_zero_of_intDiv p _ hdiv) hsupport hpools hP hM hPM hchargeP
      hchargeM hdegP hdegM hsizeP hsizeM htailP htailM
  have hbal' : balance p (punc H W U R').edgeFinset = 0 := by
    rw [punc_edgeFinset_eq]; exact hbal
  have hRes : ∀ u ∈ W, ((W.filter fun v => s(u, v) ∈ R').card : ℝ) ≤ ρ' * W.card := by
    intro u _
    have h1 : ((W.filter fun v => s(u, v) ∈ R').card : ℝ) ≤ (R'.filter fun e => u ∈ e).card := by
      exact_mod_cast nbr_card_le_deg W R' u
    have h2 := hdegR' u
    have h3 := hRdeg u
    linarith
  obtain ⟨w, hw⟩ := F1_punctured_exact_weights p G H W U R' hGF hHG hcls htyp hdam hU hRes
    hsmall hN hbal'
  exact ⟨R', hRR', hR'E, hR'C, hcard, hdegC, hbal', w, hw⟩

end NashWilliams18.SpreadF1
