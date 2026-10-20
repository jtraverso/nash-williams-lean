/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Stage193Adapter
import PartitionedTriangleAbsorption.TerminalPackingRepairStage206

/-!
# Theorem 14.7 for `F₁`: the produced reserve and the confined residual (ported Stage 205)

This file applies the ported producer
`PartitionedTriangleAbsorption.F1FractionalConfinementStage205.uniform_F1_fractional_confinement`
to the hosts of `Theorem147F1Statement` (`IsIntDiv p F1`, `IsIdealizedT F1 ε G p`).
Nothing is supplied: the packing, the reserve `X` (whole triangles of that packing) and the
covered part `EQ` are all produced inside the theorem.

Translations (same as `F1_ideal_packing_with_natural_links`): `α = 1/8`, `b = 8`,
`ε = min (δ/12) (1/100)`; class sizes from `IsIdealizedT`'s first clause; non-neighbours from
its third clause via `admissiblePair_iff_allowedT_F1` and `card_nonNbr_add_degT`; weights/loads
from `isRegularAlmostPacking_ideal`; fractional divisibility from `isFracDiv_F1`.
The edge-typeability hypothesis of Stage 205 (`∀ uv ∈ E, ∃ k, {p u, p v, k} ∈ F1`) is the second
clause of `IsIdealizedT` (`AllowedT F1 (p u) (p v)` unfolds to exactly that), proved below as
`edge_typeable_of_idealized`.

**Producer vs consumer.**  `F1_ideal_reserve_confinement` is a *producer*.  It does **not**
decompose `J = E \ EQ`.  `F1_of_terminal_repair` is a *consumer*: it shows that the single
remaining obligation `F1TerminalRepair` (stated with the exact data produced here) implies
`Theorem147F1Statement`.  `F1TerminalRepair` is **not proved**; it is the open step.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- Edge-typeability of an idealized `F₁`-host, in the form required by Stage 205. -/
lemma edge_typeable_of_idealized {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} (hid : IsIdealizedT F1 ε G p) :
    ∀ u v : V, G.Adj u v → ∃ k : Fin 4, ({p u, p v, k} : Multiset (Fin 4)) ∈ F1 :=
  fun u v h => hid.2.1 u v h

/-- **Produced reserve and confined residual for Theorem 14.7, `F₁`** (Stage 205 on the hosts of
`Theorem147F1Statement`).  For every `η > 0` there are `ε ∈ (0, 1/100]` and `n₀` such that every
integrally `F₁`-divisible idealized `F₁`-host `G` on `n ≥ n₀` vertices contains edge sets
`X, EQ ⊆ E(G)` with `X` decomposable and `Δ(X) ≤ ηn`, `EQ` decomposable, and residual
`J = E(G) \ EQ ⊆ X` integrally divisible with `Δ(J) ≤ ηn` and `|J| ≤ ηn²/2`.
It does not decompose `J`. -/
theorem F1_ideal_reserve_confinement (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
        (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
        IsIntDiv p F1 G.edgeFinset → IsIdealizedT F1 ε G p →
        ∃ X EQ : Finset (Sym2 V), X ⊆ G.edgeFinset ∧
          DegBounded X (η * Fintype.card V) ∧ HasDecomp p F1 X ∧
          EQ ⊆ G.edgeFinset ∧ HasDecomp p F1 EQ ∧
          G.edgeFinset \ EQ ⊆ X ∧ IsIntDiv p F1 (G.edgeFinset \ EQ) ∧
          DegBounded (G.edgeFinset \ EQ) (η * Fintype.card V) ∧
          ((G.edgeFinset \ EQ).card : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2 / 2 := by
  obtain ⟨δ, hδ, -, N, hN⟩ :=
    F1FractionalConfinementStage205.uniform_F1_fractional_confinement (1 / 8) 8 η
      (by norm_num) (by norm_num) (by norm_num) hη
  refine ⟨min (δ / 12) (1 / 100), lt_min (by positivity) (by norm_num), min_le_right _ _,
    max N 1, ?_⟩
  intro V _ _ p G _ hn hint hid
  set ε := min (δ / 12) (1 / 100) with hεdef
  have hε0 : 0 ≤ ε := le_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 / 100 := min_le_right _ _
  have hε12 : 12 * ε ≤ δ := by have := min_le_left (δ / 12) (1 / 100); linarith
  have hnpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) hn
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hreg := isRegularAlmostPacking_ideal twoThirds_F1 hε0 hε1 (le_refl (12 * ε)) hnpos hid
  apply hN V (le_trans (le_max_left _ _) hn) p G (fun _ => 2 / ((1 + 3 * ε) * Fintype.card V))
  · intro l
    have h := hid.1 l
    have e : ((univ.filter fun v => p v = l).card : ℝ) = ((clsT p l).card : ℝ) := rfl
    rw [e]
    nlinarith
  · intro i j hij x hx
    have hal : AllowedT F1 (p x) j := by
      rw [hx]; exact (admissiblePair_iff_allowedT_F1 i j).mp hij
    have h1 := hid.2.2 x j hal
    have h2 := card_nonNbr_add_degT G p x j
    have h2' : ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) +
        (degT G p x j : ℝ) = ((clsT p j).card : ℝ) := by exact_mod_cast h2
    have h3 : ε * (Fintype.card V : ℝ) ≤ δ * Fintype.card V := by
      apply mul_le_mul_of_nonneg_right _ hnR.le; linarith
    linarith
  · exact edge_typeable_of_idealized p G hid
  · intro s hs
    obtain ⟨h1, h2⟩ := hreg.1 s hs
    exact ⟨by simpa using h1, by
      refine h2.trans ?_
      gcongr⟩
  · intro e he
    obtain ⟨h1, h2⟩ := hreg.2 e he
    have e1 : TypedLoadNecessity.edgeLoad p F1 G
        (fun _ => 2 / ((1 + 3 * ε) * Fintype.card V)) e =
        ∑ s ∈ copies p F1 G with e ∈ triEdges s, 2 / ((1 + 3 * ε) * Fintype.card V) := rfl
    rw [e1, abs_le]
    constructor <;> linarith
  · exact hint
  · exact isFracDiv_F1 hε0 hε1 hnpos hid hint

/-- **The single remaining open obligation of `Theorem147F1Statement`** (NOT proved here).
For some `η > 0` and `n₁`: on every idealized `F₁`-host with `n ≥ n₁` (for every `ε ≤ 1/100`
— the tolerance chosen by the producer), given the exact data produced by
`F1_ideal_reserve_confinement` (decomposable reserve `X`, decomposable `EQ`, residual
`J = E \ EQ ⊆ X` integrally divisible with `Δ(J) ≤ ηn`, `|J| ≤ ηn²/2`), the graph itself is
`F₁`-decomposable.  (Via `TerminalPackingRepairStage206.close_by_subpacking_repair` this is the
case when some sub-packing `B` of a decomposition of `EQ` can be re-decomposed together with `J`;
constructing `B` and that repair is the open mathematics.) -/
def F1TerminalRepair (η : ℝ) : Prop :=
  ∃ n₁ : ℕ, ∀ (ε : ℝ), ε ≤ 1 / 100 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₁ ≤ Fintype.card V →
      IsIntDiv p F1 G.edgeFinset → IsIdealizedT F1 ε G p →
      ∀ X EQ : Finset (Sym2 V), X ⊆ G.edgeFinset →
        DegBounded X (η * Fintype.card V) → HasDecomp p F1 X →
        EQ ⊆ G.edgeFinset → HasDecomp p F1 EQ →
        G.edgeFinset \ EQ ⊆ X → IsIntDiv p F1 (G.edgeFinset \ EQ) →
        DegBounded (G.edgeFinset \ EQ) (η * Fintype.card V) →
        ((G.edgeFinset \ EQ).card : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2 / 2 →
        HasDecomp p F1 G.edgeFinset

/-- **Consumer** (proved): the open terminal repair, for one `η > 0`, together with the proved
producer `F1_ideal_reserve_confinement`, gives `Theorem147F1Statement`.  This does not prove
`Theorem147F1Statement`: `F1TerminalRepair η` is an unproved hypothesis. -/
theorem F1_of_terminal_repair (η : ℝ) (hη : 0 < η) (hrep : F1TerminalRepair η) :
    Theorem147F1Statement := by
  obtain ⟨ε, hε, hε1, n₀, hprod⟩ := F1_ideal_reserve_confinement η hη
  obtain ⟨n₁, hrep⟩ := hrep
  refine ⟨ε, hε, max n₀ n₁, fun V _ _ p G _ hn hint hid => ?_⟩
  obtain ⟨X, EQ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    hprod V p G ((le_max_left _ _).trans hn) hint hid
  exact hrep ε hε1 V p G ((le_max_right _ _).trans hn) hint hid X EQ h1 h2 h3 h4 h5 h6 h7 h8 h9

end NashWilliams18
