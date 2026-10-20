/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.SpreadLevelF1
import RequestProject.NW18.Case126.VortexLevelF1
import RequestProject.NW18.Case126.RootedConeF1

/-!
# Theorem 14.7 for `F₁`, vortex route: the first open lemma after the spread cover-down

`F1_spread_level_cover_down` (proved, `SpreadLevelF1.lean`) is the physical second half of one
vortex level.  What remains of `CrossingCover.F1VortexCoverDown` is the FIRST half: the typed
approximate packing of the actual damaged level together with the jointly sampled reserves, which
must deliver the inputs of the proved cover-down.  This file states that remaining step exactly
(`F1LevelSupply`, **NOT proved**, a `def`) and proves the consumer
`F1_vortex_cover_down_of_supply : F1LevelSupply β ξ ζ θ → F1VortexCoverDownCone β ξ ζ θ`, where
`F1VortexCoverDownCone` is `F1VortexCoverDown` corrected by the rooted cone slack `θ`
(`RootedConeF1.lean`).

**Inputs of the cover-down and what implies them (source-graph accounting).**
* rooted parity at every root (`hpar` of the cover-down) — **derived here** from
  `IsIntDiv p F1 H` (`F1_degree_even_of_intDiv`) and the decomposability of the packed part `D₀`;
  it is NOT part of `F1LevelSupply`;
* classes of every cross neighbourhood in `{c, d₁(c), d₂(c)}` (`hcls`) — **derived here** from
  `G` having only `F₁`-allowed edges (`allowed_F1_classes`);
* `R ⊆ E(H[U])` with no edge inside `U'` — the internal reserve is `G[U]` minus the edges inside
  `U'` (no damage inside `U` by hypothesis), so this is free;
* density defect `γ₀` inside each cross neighbourhood `T0 j` — from typicality of `G` w.r.t. `U`
  (`ξ`), the overlap `|T0 j ∩ U'|` (from `|U'| ≤ β|U|`) and the concentration of the random cross
  reserve (open: sampling);
* margins `MarginsSlack` — from the class proportions of `U` and typed reserve densities (the
  `F₁` rooted cone `|T_c| ≤ |T_{d₁}| + |T_{d₂}|` must hold with linear slack; the reserve
  densities per class are a free design parameter) (open: sampling);
* overlaps `ω`, loads `L` with `(e-1) ω L / K + log ∑|T0 j| ≤ B` — from the joint random cross
  reserve (`ω ≈ ρ²|U|`, `L ≈ ρ|W|`, `K, B ≈ ρ|U|/100`, so `ρ ≲ β`) plus the leftover degree
  (open: sampling + nibble);
* apex supply `s`, leftover degree `γ`, leftover size `k` with `2γ + k/β' < s` — from the nibble
  leftover degree `≤ η|W|` and common reserve neighbourhoods `≈ ρ²|U|` (open: nibble + sampling);
* `L ≤ ζ |U|` — the in-`U` damage budget of the next level, paid at the CURRENT scale.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen ApexF1
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- **Corrected self-similar `F₁` vortex level (NOT proved, a `def`).**  Exactly
`CrossingCover.F1VortexCoverDown` with the additional set-level ROOTED CONE SLACK
`ClassConeSlack p S θ` for `S = W, U, U'` (see `RootedConeF1.lean`: without it the statement can
fail at a vertex whose cone is tight, by `cover_down_needs_cone`).  The slack is a property of the
nested vertex sets, so it reproduces itself one level down; with `θ > ξ + ζ` it gives the cone with
slack at every vertex. -/
def F1VortexCoverDownCone (β ξ ζ θ : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
    U' ⊆ U → U ⊆ W → m₀ ≤ W.card →
    β * W.card / 2 ≤ U.card → (U.card : ℝ) ≤ β * W.card →
    β * U.card / 2 ≤ U'.card → (U'.card : ℝ) ≤ β * U.card →
    (∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) →
    (∀ j : Fin 4, (W.card : ℝ) / 5 ≤ (W.filter fun z => p z = j).card ∧
      (U.card : ℝ) / 5 ≤ (U.filter fun z => p z = j).card ∧
      (U'.card : ℝ) / 5 ≤ (U'.filter fun z => p z = j).card) →
    (∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card ∧
      ((U.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * U.card) →
    (∀ v ∈ U, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((U'.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * U'.card) →
    ClassConeSlack p W θ → ClassConeSlack p U θ → ClassConeSlack p U' θ →
    IsIntDiv p F1 H.edgeFinset → H ≤ G → (∀ u v, H.Adj u v → u ∈ W) →
    (∀ u ∈ U, ∀ v ∈ U, G.Adj u v → H.Adj u v) →
    (∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card) →
    ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
      (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
      (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
      ∀ v, (((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℝ) ≤ ζ * U.card

/-- The original level statement implies the corrected one (it has fewer hypotheses). -/
theorem F1VortexCoverDownCone_of_old {β ξ ζ θ : ℝ} (h : F1VortexCoverDown β ξ ζ) :
    F1VortexCoverDownCone β ξ ζ θ := by
  obtain ⟨m₀, hm⟩ := h
  exact ⟨m₀, fun V _ _ p G H _ _ W U U' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _ _ _ =>
    hm V p G H W U U' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11⟩

/-- **Open obligation (NOT proved): typed approximate packing with joint reserves for one `F₁`
vortex level.**  Same hypotheses as `F1VortexCoverDownCone` (i.e.
`CrossingCover.F1VortexCoverDown` plus the rooted cone slack `θ`).  Conclusion: an
`F₁`-decomposable `D₀ ⊆ E(H)` with no edge inside `U` (the packing), such that the leftover
`E(H) \ (E(H[U]) ∪ D₀)` is exactly `Hout ∪ Q` with `Hout = {x_i y_i}` outside `U` and `Q` a cross
graph with distinct roots `r j ∉ U`; an internal reserve `R ⊆ E(H)` inside `U` with no edge inside
`U'`; and numbers satisfying every hypothesis of `F1_spread_level_cover_down` except the rooted
parity and the class restriction of the cross neighbourhoods (both derived in the consumer), with
`L ≤ ζ |U|`. -/
def F1LevelSupply (β ξ ζ θ : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
    U' ⊆ U → U ⊆ W → m₀ ≤ W.card →
    β * W.card / 2 ≤ U.card → (U.card : ℝ) ≤ β * W.card →
    β * U.card / 2 ≤ U'.card → (U'.card : ℝ) ≤ β * U.card →
    (∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) →
    (∀ j : Fin 4, (W.card : ℝ) / 5 ≤ (W.filter fun z => p z = j).card ∧
      (U.card : ℝ) / 5 ≤ (U.filter fun z => p z = j).card ∧
      (U'.card : ℝ) / 5 ≤ (U'.filter fun z => p z = j).card) →
    (∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card ∧
      ((U.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * U.card) →
    (∀ v ∈ U, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((U'.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * U'.card) →
    ClassConeSlack p W θ → ClassConeSlack p U θ → ClassConeSlack p U' θ →
    IsIntDiv p F1 H.edgeFinset → H ≤ G → (∀ u v, H.Adj u v → u ∈ W) →
    (∀ u ∈ U, ∀ v ∈ U, G.Adj u v → H.Adj u v) →
    (∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card) →
    ∃ (D₀ : Finset (Sym2 V)) (k : ℕ) (x y : ℕ → V) (kr : ℕ) (r : ℕ → V)
      (Q R : Finset (Sym2 V)) (s γ β' γ₀ K B ω L : ℕ),
      -- the packing and the exact leftover
      D₀ ⊆ H.edgeFinset ∧ HasDecomp p F1 D₀ ∧ (∀ e ∈ D₀, ¬ ∀ v ∈ e, v ∈ U) ∧
      (range k).image (fun i => s(x i, y i)) ∪ Q ⊆ H.edgeFinset ∧
      Disjoint ((range k).image (fun i => s(x i, y i)) ∪ Q) D₀ ∧
      (∀ e ∈ H.edgeFinset, (¬ ∀ v ∈ e, v ∈ U) → e ∉ D₀ →
        e ∈ (range k).image (fun i => s(x i, y i)) ∪ Q) ∧
      -- the internal reserve
      R ⊆ H.edgeFinset ∧ (∀ e ∈ R, ∀ v ∈ e, v ∈ U) ∧ (∀ e ∈ R, ¬ ∀ v ∈ e, v ∈ U') ∧
      -- the inputs of `F1_spread_level_cover_down` (rooted parity and classes: derived)
      (∀ i < k, x i ≠ y i) ∧
      (∀ i < k, ∀ j < k, s(x i, y i) = s(x j, y j) → i = j) ∧
      (∀ i < k, x i ∉ U) ∧ (∀ i < k, y i ∉ U) ∧
      (∀ v, ((range k).filter (fun i => v = x i ∨ v = y i)).card ≤ γ) ∧
      (∀ i < k, s ≤ (U.filter (fun z => s(x i, z) ∈ Q ∧ s(y i, z) ∈ Q ∧
        ({p (x i), p (y i), p z} : Multiset (Fin 4)) ∈ F1)).card) ∧
      0 < β' ∧ 2 * γ + k / β' < s ∧
      (∀ e ∈ Q, ∃ j < kr, ∃ u ∈ U, e = s(r j, u)) ∧
      (∀ i < kr, ∀ j < kr, r i = r j → i = j) ∧
      (∀ j < kr, r j ∉ U) ∧
      0 < K ∧
      (∀ j < kr, ∀ v ∈ tgt U Q (r j), ∀ c : Fin 4, LinkPair (p (r j)) (p v) c →
        ((tgt U Q (r j)).filter fun z => p z = c ∧ ¬ (z ≠ v ∧ s(v, z) ∈ R)).card ≤ γ₀) ∧
      (∀ j < kr, MarginsSlack p (p (r j)) (tgt U Q (r j)) (γ₀ + (B + K)) γ) ∧
      (∀ i < kr, ∀ j < kr, i ≠ j → ((tgt U Q (r i)) ∩ (tgt U Q (r j))).card ≤ ω) ∧
      (∀ v, visits (fun j => tgt U Q (r j)) kr v ≤ L) ∧
      (Real.exp 1 - 1) * ω * L / K +
        Real.log (∑ j ∈ range kr, ((tgt U Q (r j)).card : ℝ)) ≤ B ∧
      (L : ℝ) ≤ ζ * U.card

/-- The degree of `x` in an edge set, counted by neighbours. -/
theorem deg_eq_card_nbrs {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (x : V) :
    deg E x = (univ.filter fun y => s(x, y) ∈ E).card := by
  classical
  unfold deg
  symm
  apply Finset.card_nbij (fun y => s(x, y))
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
    exact ⟨hy, Sym2.mem_mk_left _ _⟩
  · intro a _ b _ hab
    exact Sym2.congr_right.mp hab
  · intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at he
    obtain ⟨heE, hxe⟩ := he
    refine ⟨Sym2.Mem.other hxe, ?_, Sym2.other_spec hxe⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [Sym2.other_spec hxe]; exact heE

/-- **Consumer (proved): the open supply step together with the proved spread cover-down gives
the corrected self-similar `F₁` vortex level.**  The rooted parity at every root is derived from
`IsIntDiv p F1 H`. -/
theorem F1_vortex_cover_down_of_supply {β ξ ζ θ : ℝ} (h : F1LevelSupply β ξ ζ θ) :
    F1VortexCoverDownCone β ξ ζ θ := by
  obtain ⟨m₀, hm⟩ := h
  refine ⟨m₀, fun V _ _ p G H _ _ W U U' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hc1 hc2 hc3 hdiv hHG
    hHW hU hdam => ?_⟩
  classical
  obtain ⟨D₀, k, x, y, kr, r, Q, R, s, γ, β', γ₀, K, B, ω, L, hD₀H, hD₀dec, hD₀U, hLH, hLD₀,
    hleft, hRH, hRU, hRU', hxy, hinj, hxU, hyU, hdegH, hsup, hβ', hs, hQ, hr, hrU, hK,
    hdense, hmarg, hover, hload, hB, hLζ⟩ :=
    hm V p G H W U U' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hc1 hc2 hc3 hdiv hHG hHW hU hdam
  set Hout := (range k).image (fun i => s(x i, y i)) with hHout
  have hloopH : ∀ e ∈ H.edgeFinset, ¬ e.IsDiag := fun e he =>
    H.not_isDiag_of_mem_edgeFinset he
  -- the rooted parity at every root, from integral divisibility
  have hpar : ∀ j < kr, Even (deg (Hout ∪ Q) (r j)) := by
    intro j hj
    have hH : Even (deg H.edgeFinset (r j)) := by
      rw [deg_eq_card_nbrs]
      exact F1_degree_even_of_intDiv p _ hloopH hdiv (r j)
    have hD : Even (deg D₀ (r j)) := even_deg_of_hasDecomp hD₀dec (r j)
    have hsplit : H.edgeFinset.filter (fun e => r j ∈ e) =
        D₀.filter (fun e => r j ∈ e) ∪ (Hout ∪ Q).filter (fun e => r j ∈ e) := by
      ext e
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨he, hre⟩
        by_cases heD : e ∈ D₀
        · exact Or.inl ⟨heD, hre⟩
        · exact Or.inr ⟨mem_union.mp (hleft e he (fun hall => hrU j hj (hall _ hre)) heD), hre⟩
      · rintro (⟨he, hre⟩ | ⟨he, hre⟩)
        · exact ⟨hD₀H he, hre⟩
        · exact ⟨hLH (mem_union.mpr he), hre⟩
    have hcount : deg H.edgeFinset (r j) = deg D₀ (r j) + deg (Hout ∪ Q) (r j) := by
      unfold deg
      rw [hsplit, card_union_of_disjoint (disjoint_filter_filter hLD₀.symm)]
    rw [hcount] at hH
    exact (Nat.even_add.mp hH).mp hD
  -- the classes of every cross neighbourhood, from the `F₁`-allowed host
  have hcls : ∀ j < kr, ∀ u ∈ tgt U Q (r j),
      p u = p (r j) ∨ p u = partner1 (p (r j)) ∨ p u = partner2 (p (r j)) := by
    intro j _ u hu
    have hQe : s(r j, u) ∈ Q := (mem_filter.mp hu).2
    have hHe : H.Adj (r j) u := SimpleGraph.mem_edgeFinset.mp (hLH (mem_union_right _ hQe))
    exact allowed_F1_classes _ _ (h8 _ _ (hHG hHe))
  obtain ⟨M, hMR, hMdeg, hMdec⟩ := F1_spread_level_cover_down p U Q R k x y kr r s γ β' γ₀ K B ω L
    hxy hinj hxU hyU hdegH hsup hβ' hs hQ hr hrU hpar hRU hK hcls hdense hmarg hover hload hB
  refine ⟨D₀ ∪ (Hout ∪ Q ∪ M), ?_, ?_, ?_, ?_, ?_⟩
  · exact union_subset hD₀H (union_subset hLH (hMR.trans hRH))
  · refine hD₀dec.union hMdec ?_
    rw [disjoint_union_right]
    refine ⟨hLD₀.symm, ?_⟩
    rw [disjoint_left]
    intro e heD heM
    exact hD₀U e heD (hRU e (hMR heM))
  · intro e he hne v hv
    by_contra hvU
    have hnot : ¬ ∀ w ∈ e, w ∈ U := fun hall => hvU (hall v hv)
    by_cases heD : e ∈ D₀
    · exact hne (mem_union_left _ heD)
    · exact hne (mem_union_right _ (mem_union_left _ (hleft e he hnot heD)))
  · intro e he hall
    rcases mem_union.mp he with heD | he
    · exact hD₀U e heD (fun v hv => h1 (hall v hv))
    rcases mem_union.mp he with heL | heM
    · rcases mem_union.mp heL with heH | heQ
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp heH
        exact hxU i (mem_range.mp hi) (h1 (hall _ (Sym2.mem_mk_left _ _)))
      · obtain ⟨j, hj, u, -, rfl⟩ := hQ e heQ
        exact hrU j hj (h1 (hall _ (Sym2.mem_mk_left _ _)))
    · exact hRU' e (hMR heM) hall
  · intro v
    have hsub : ((D₀ ∪ (Hout ∪ Q ∪ M)).filter fun e => ∀ w ∈ e, w ∈ U).filter (fun e => v ∈ e)
        ⊆ M.filter (fun e => v ∈ e) := by
      intro e he
      simp only [mem_filter, mem_union] at he ⊢
      obtain ⟨⟨he, hall⟩, hve⟩ := he
      refine ⟨?_, hve⟩
      rcases he with heD | (heH | heQ) | heM
      · exact absurd hall (hD₀U e heD)
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp heH
        exact absurd (hall _ (Sym2.mem_mk_left _ _)) (hxU i (mem_range.mp hi))
      · obtain ⟨j, hj, u, -, rfl⟩ := hQ e heQ
        exact absurd (hall _ (Sym2.mem_mk_left _ _)) (hrU j hj)
      · exact heM
    have h1' := card_le_card hsub
    have h2' : (M.filter (fun e => v ∈ e)).card ≤ L := hMdeg v
    calc (((D₀ ∪ (Hout ∪ Q ∪ M)).filter fun e => ∀ w ∈ e, w ∈ U).filter
          (fun e => v ∈ e)).card ≤ (L : ℝ) := by exact_mod_cast h1'.trans h2'
      _ ≤ ζ * U.card := hLζ

end NashWilliams18.SpreadF1
