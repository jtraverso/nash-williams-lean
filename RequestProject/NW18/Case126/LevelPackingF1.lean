/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.PuncturedPackingF1
public import RequestProject.NW18.Case126.CrossReserveF1

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: one level, reserve sampled FIRST, then the packing (producer)

Producer obligations 1–3 composed at one vortex level.

* `LevelHyp` is the reserve-free part of `PuncHyp`: near-quarter classes of `U` and `W \ U`
  (`κ`), typicality of the host `G` (`ξ`), damage of `H` (`ζ`).  These are the invariants of the
  ACTUAL level (for the top level they come from `IsIdealizedT F1 ε G p` via
  `nearQuarter_of_idealized`, with `ζ = 0`).
* `F1_level_packing_with_reserve` (proved): for every `η > 0` and every reserve density
  `ρ ∈ [0, 1/2]` there are `τ > 0` and `N` such that every level with `|W| ≥ N`, `κ ≤ 1/16` and
  `32 (κ + 2ξ + 2ζ) ≤ τ/2` carries a sampled cross reserve `Res` with all five joint regularity
  properties (`CrossResGood`, defect `τ/64`) AND an `F₁`-decomposable `D₀ ⊆ E(H)` avoiding `U`
  and `Res` whose complement in the punctured level has maximum degree `≤ η |W|`.  The reserve is
  chosen before the packing, from the original host data, and the weighting is normalised by the
  surviving density `1 - ρ` (no tolerance has to exceed the fixed loss `ρ`).
* `apex_supply_lower` (proved): every outside pair `x ≠ y` has at least
  `ρ² (|U_l| - 2ξ|W| - 2ζ|W|) - ε|W|` common reserved neighbours in each third class `l`; these are
  apexes of `F₁` triangles (`2γ + k/β' < s` then holds as soon as
  `η ≪ ρ² |U| / |W|`).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The reserve-free invariants of an actual `F₁` vortex level. -/
structure LevelHyp (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U : Finset V) (κ ξ ζ : ℝ) : Prop where
  hUW : U ⊆ W
  hW : 0 < W.card
  hUh : (U.card : ℝ) ≤ W.card / 2
  hκ : 0 ≤ κ
  hξ : 0 ≤ ξ
  hζ : 0 ≤ ζ
  hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)
  hHG : H ≤ G
  hout : ∀ j : Fin 4, |(((W \ U).filter fun z => p z = j).card : ℝ) - tOf W U| ≤ κ * W.card
  hin : ∀ j : Fin 4, |((U.filter fun z => p z = j).card : ℝ) - uOf U| ≤ κ * W.card
  htyp : ∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
    ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card
  hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card

lemma puncHyp_of {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {W U : Finset V} {κ ξ ζ ρ ε : ℝ} {Res : Finset (Sym2 V)} (h : LevelHyp p G H W U κ ξ ζ)
    (hR : CrossResGood p H W U Res ρ ε) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (hε : 0 ≤ ε) :
    PuncHyp p G H W U Res κ ξ ζ ε (1 - ρ) :=
  { hUW := h.hUW, hW := h.hW, hUh := h.hUh, hq := by linarith, hq1 := by linarith,
    hκ := h.hκ, hξ := h.hξ, hζ := h.hζ, hε := hε, hGF := h.hGF, hHG := h.hHG,
    hout := h.hout, hin := h.hin, htyp := h.htyp, hdam := h.hdam, hR0 := hR.out,
    hR1 := hR.r1, hR2 := hR.r2 }

/-- **One `F₁` level: sampled cross reserve, then the approximate packing** (producer). -/
theorem F1_level_packing_with_reserve (η ρ : ℝ) (hη : 0 < η) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V)
      (κ ξ ζ : ℝ), N ≤ W.card → LevelHyp p G H W U κ ξ ζ → κ ≤ 1 / 16 →
      32 * (κ + 2 * ξ + 2 * ζ) ≤ τ / 2 →
      ∃ (Res D₀ : Finset (Sym2 V)), CrossResGood p H W U Res ρ (τ / 64) ∧
        D₀ ⊆ H.edgeFinset ∧ HasDecomp p F1 D₀ ∧ (∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U) ∧
        Disjoint D₀ Res ∧
        ∀ v, ((((punc H W U Res).edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
          η * W.card := by
  obtain ⟨τ, hτ, N₁, hN₁⟩ := F1_punctured_packing η hη
  obtain ⟨N₂, hN₂⟩ := cross_reserve_exists (τ / 64) (by positivity)
  refine ⟨τ, hτ, max N₁ N₂, ?_⟩
  intro V _ _ p G H _ _ W U κ ξ ζ hN h hκ hsmall
  obtain ⟨Res, hRes⟩ := hN₂ V p H W U ρ h.hUW hρ0 (by linarith) (le_trans (le_max_right _ _) hN)
  have hP := puncHyp_of h hRes hρ0 hρ (by positivity)
  obtain ⟨D₀, h1, h2, h3, h4, h5⟩ := hN₁ V p G H W U Res κ ξ ζ (τ / 64) (1 - ρ)
    (le_trans (le_max_left _ _) hN) hP hκ (by linarith)
  exact ⟨Res, D₀, hRes, h1, h2, h3, h4, h5⟩

/-- **Apex supply of the sampled reserve** (proved).  For distinct outside `x, y ∈ W` and a third
class `l` of `(p x, p y)`, the common reserved neighbours of `x, y` in `U_l` are at least
`ρ² (|U_l| - 2ξ|W| - 2ζ|W|) - ε|W|`; each of them is the apex of an `F₁` triangle on `xy`. -/
theorem apex_supply_lower {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] {W U : Finset V} {κ ξ ζ ρ ε : ℝ} {Res : Finset (Sym2 V)}
    (h : LevelHyp p G H W U κ ξ ζ) (hR : CrossResGood p H W U Res ρ ε)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hxU : x ∉ U) (hyU : y ∉ U) {l : Fin 4}
    (hl : ({p x, p y, l} : Multiset (Fin 4)) ∈ F1) :
    ρ ^ 2 * (((U.filter fun z => p z = l).card : ℝ) - 2 * ξ * W.card - 2 * ζ * W.card) -
        ε * W.card ≤
      ((U.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card : ℝ) := by
  have hr3 := abs_le.mp (hR.r3 x hx y hy hxy hxU hyU l)
  obtain ⟨hC1, -⟩ := common_count_bounds p G H W U h.hUW ξ ζ h.htyp h.hdam x y hx hy l
    (allowedT_of_mem hl) (allowedT_of_mem' hl)
  have hsub : (U.filter fun z => p z = l ∧ H.Adj x z ∧ H.Adj y z ∧ s(x, z) ∈ Res ∧
      s(y, z) ∈ Res) ⊆ U.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1 := by
    intro z hz
    simp only [mem_filter] at hz ⊢
    obtain ⟨hzU, hzl, -, -, h1, h2⟩ := hz
    exact ⟨hzU, h1, h2, by rw [hzl]; exact hl⟩
  have hc : ((U.filter fun z => p z = l ∧ H.Adj x z ∧ H.Adj y z ∧ s(x, z) ∈ Res ∧
      s(y, z) ∈ Res).card : ℝ) ≤ (U.filter fun z => s(x, z) ∈ Res ∧ s(y, z) ∈ Res ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card := by
    exact_mod_cast card_le_card hsub
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  nlinarith [mul_le_mul_of_nonneg_left hC1 hρ2]

end NashWilliams18.SpreadF1
