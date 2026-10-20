/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.ProtectedLevelF1
public import PartitionedTriangleAbsorption.TypedAnnularIterationStage236

@[expose] public section

/-!
# Feeding the protected `F₁` level producer into the protected iteration

* `LevelConstants` bundles the scalar inequalities of `F1_protected_level`;
  `exists_level_constants` exhibits concrete values (`β = 10⁻⁶`, `ζ = 10⁻²⁶`, `ρ = 10⁻³³`,
  `κ = ξ = ε = η = 10⁻⁸⁰`).
* `F1Vortex p G W L β κ ξ` is the explicit geometric input: a nested vertex sequence
  `W 0 ⊇ W 1 ⊇ …` with child ratio in `[β/2, β]`, near-quarter classes with error `κ |W i|`
  and typicality `ξ |W i|` of the host `G` on every level.
* `F1_vortex_step` (proved) derives the step hypothesis of Stage 236 (`iterate_protected_levels`)
  for `R i = E(G[W i])` and `cap i = ζ |W i|` from `F1_protected_level`: the protected child
  `G[W (i+1)]` is untouched by the damage `D`, so each level is a `ProtLevel`.
* `F1_close_from_vortex` (proved) feeds the step into `f1_close_constructing_absorber`:
  constants first, then `Nlev`, then (for each terminal size `M`) the threshold `N`; every
  integrally divisible `F₁`-typed host with compatible supply and such a vortex of `L` levels
  of size `≥ Nlev` ending at size `≤ M` has an `F₁`-decomposition.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.TypedAnnularIterationStage236
open PartitionedTriangleAbsorption.PairMoveSelectionStage85 (CompatibleSupply)

/-- The scalar inequalities of the uniform protected level producer. -/
def LevelConstants (β κ ξ ζ ρ ε η : ℝ) : Prop :=
  (0 < β ∧ β ≤ 1 / 2 ∧ 0 ≤ κ ∧ 0 ≤ ξ ∧ 0 ≤ ζ ∧ 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 < ε ∧ 0 < η ∧
    κ ≤ 1 / 16) ∧
  κ + ξ + ζ + ρ + ε ≤ β / 16 ∧
  3 * repDem β κ ξ ζ ρ ε ≤ β / 256 ∧
  3 * ξ + ζ + β + (ρ + ε + repDelta β κ ξ ζ ρ ε) + 6 * (2 * κ) ≤ 1 / 5120 ∧
  8 * (ρ * (β ^ 2 + ξ) + ε + (repDelta β κ ξ ζ ρ ε + η)) +
      16 * (ρ * β / 10000) + 2 * η +
      (ρ * (3 * κ + 2 * ξ + 2 * ζ) + 9 * ε + (repDelta β κ ξ ζ ρ ε + η)) < ρ * β / 8 ∧
  ρ + ε + (repDelta β κ ξ ζ ρ ε + η) ≤ ζ * β / 2 ∧
  2 * (ρ ^ 2 * β + 12 * ε + 2 * (repDelta β κ ξ ζ ρ ε + η)) *
      (ρ + ε + (repDelta β κ ξ ζ ρ ε + η)) / (ρ * β / 10000) ≤ (ρ * β / 10000) / 2 ∧
  3 * η < ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε

/-- **Concrete constants** satisfying every scalar inequality (proved by `norm_num`). -/
theorem exists_level_constants :
    LevelConstants (1 / 10 ^ 6) (1 / 10 ^ 80) (1 / 10 ^ 80) (1 / 10 ^ 26) (1 / 10 ^ 33)
      (1 / 10 ^ 80) (1 / 10 ^ 80) := by
  unfold LevelConstants repDelta repDem
  norm_num

/-- The uniform level producer stated with the bundled constants. -/
theorem F1_protected_level_of_constants {β κ ξ ζ ρ ε η : ℝ}
    (hc : LevelConstants β κ ξ ζ ρ ε η) :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
      ProtLevel p G H W U U' β κ ξ ζ → N ≤ W.card →
      ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
        (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
        (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
        ∀ v, (((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℝ) ≤
          ζ * U.card := by
  obtain ⟨⟨hβ, hβ1, hκ, hξ, hζ, hρ, hρ1, hε, hη, hκ16⟩, hpool, hprob, hsmall, hmargin, hvis,
    hover, hapex⟩ := hc
  exact F1_protected_level β κ ξ ζ ρ ε η hβ hβ1 hκ hξ hζ hρ hρ1 hε hη hκ16 hpool hprob hsmall
    hmargin hvis hover hapex

theorem LevelConstants.zeta_pos {β κ ξ ζ ρ ε η : ℝ} (hc : LevelConstants β κ ξ ζ ρ ε η) :
    0 < ζ := by
  obtain ⟨⟨hβ, -, hκ, hξ, hζ, hρ, -, hε, hη, -⟩, -, -, -, -, hvis, -, -⟩ := hc
  by_contra hz
  have h0 : ζ = 0 := le_antisymm (not_lt.mp hz) hζ
  subst h0
  have hδ : 0 ≤ repDelta β κ ξ 0 ρ ε := by
    unfold repDelta repDem; positivity
  linarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The current graph of a level: host edges inside `S` minus the damage `D`. -/
def levelGraph (G : SimpleGraph V) (S : Finset V) (D : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ s(u, v) ∉ D
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2.1, h.2.1, by rw [Sym2.eq_swap]; exact h.2.2.2⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (D : Finset (Sym2 V)) :
    DecidableRel (levelGraph G S D).Adj := fun u v => by
  unfold levelGraph; infer_instance

theorem levelGraph_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (D : Finset (Sym2 V)) : (levelGraph G S D).edgeFinset = edgesIn G S \ D := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset]
    simp only [edgesIn, mem_sdiff, mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, mk_all_mem]
    change (G.Adj a b ∧ a ∈ S ∧ b ∈ S ∧ s(a, b) ∉ D) ↔
      (G.Adj a b ∧ a ∈ S ∧ b ∈ S) ∧ s(a, b) ∉ D
    tauto

/-- **The geometric vortex input** (explicit premise, not derived here). -/
structure F1Vortex (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (W : ℕ → Finset V)
    (L : ℕ) (β κ ξ : ℝ) : Prop where
  sub : ∀ i ≤ L, W (i + 1) ⊆ W i
  hi : ∀ i ≤ L, ((W (i + 1)).card : ℝ) ≤ β * (W i).card
  lo : ∀ i < L, β * (W i).card / 2 ≤ (W (i + 1)).card
  out : ∀ i < L, ∀ j : Fin 4,
    |((((W i) \ W (i + 1)).filter fun z => p z = j).card : ℝ) - tOf (W i) (W (i + 1))| ≤
      κ * (W i).card
  inn : ∀ i < L, ∀ j : Fin 4,
    |(((W (i + 1)).filter fun z => p z = j).card : ℝ) - uOf (W (i + 1))| ≤ κ * (W i).card
  typ : ∀ i < L, ∀ v ∈ W i, ∀ j : Fin 4, AllowedT F1 (p v) j →
    (((W i).filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * (W i).card

omit [Fintype V] in
theorem deg_le_of_subset_image {E : Finset (Sym2 V)} {S : Finset V} (v : V)
    (hE : ∀ e ∈ E, ∀ w ∈ e, w ∈ S) : (E.filter fun e => v ∈ e).card ≤ S.card := by
  have hsub : E.filter (fun e => v ∈ e) ⊆ S.image (fun w => s(v, w)) := by
    intro e he
    obtain ⟨heE, hve⟩ := mem_filter.mp he
    refine mem_image.mpr ⟨Sym2.Mem.other hve, hE e heE _ (Sym2.other_mem hve), ?_⟩
    exact Sym2.other_spec hve
  exact (card_le_card hsub).trans card_image_le

/-- **One step of the protected iteration from the uniform level producer** (proved). -/
theorem F1_vortex_step {β κ ξ ζ : ℝ} (N : ℕ)
    (hlev : ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
      ProtLevel p G H W U U' β κ ξ ζ → N ≤ W.card →
      ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
        (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
        (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
        ∀ v, (((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℝ) ≤
          ζ * U.card)
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (W : ℕ → Finset V) (L : ℕ)
    (hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) (hW : F1Vortex p G W L β κ ξ)
    (hN : ∀ i < L, N ≤ (W i).card) :
    ∀ i < L, ∀ D, LevelState p F1 (fun i => edgesIn G (W i)) (fun i => ζ * (W i).card) i D →
      ∃ P ⊆ edgesIn G (W i) \ D, HasDecomp p F1 P ∧
        (edgesIn G (W i) \ D) \ P ⊆ edgesIn G (W (i + 1)) ∧
        Disjoint P (edgesIn G (W (i + 2))) ∧
        DegBounded (P ∩ edgesIn G (W (i + 1))) (ζ * (W (i + 1)).card) := by
  intro i hi D hD
  have hsub1 := hW.sub i hi.le
  have hsub2 := hW.sub (i + 1) hi
  have hlvl : ProtLevel p G (levelGraph G (W i) D) (W i) (W (i + 1)) (W (i + 2)) β κ ξ ζ := by
    refine ⟨hsub2, hsub1, hW.lo i hi, hW.hi i hi.le, hW.hi (i + 1) hi, hGF,
      fun u v h => h.1, fun u v h => h.2.1, hW.out i hi, hW.inn i hi, hW.typ i hi, ?_, ?_, ?_⟩
    · intro u hu
      have hinj : ((W i).filter fun v => G.Adj u v ∧ ¬ (levelGraph G (W i) D).Adj u v).card ≤
          (D.filter fun e => u ∈ e).card := by
        apply card_le_card_of_injOn (fun v => s(u, v))
        · intro v hv
          simp only [coe_filter, Set.mem_setOf_eq] at hv ⊢
          obtain ⟨hvW, hadj, hn⟩ := hv
          refine ⟨?_, Sym2.mem_mk_left _ _⟩
          by_contra hD'
          exact hn ⟨hadj, hu, hvW, hD'⟩
        · intro a _ b _ hab
          exact (Sym2.congr_right.mp hab)
      exact (by exact_mod_cast hinj : ((((W i).filter fun v => G.Adj u v ∧
        ¬ (levelGraph G (W i) D).Adj u v).card : ℕ) : ℝ) ≤ (D.filter fun e => u ∈ e).card).trans
        (hD.load u)
    · intro u hu v hv hadj
      refine ⟨hadj, hsub1 hu, hsub1 hv, fun hmem => ?_⟩
      have hR : s(u, v) ∈ edgesIn G (W (i + 1)) :=
        mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, (mk_all_mem _ _ _).mpr ⟨hu, hv⟩⟩
      exact disjoint_left.mp hD.clean hmem hR
    · rw [levelGraph_edgeFinset]; exact hD.divisible
  obtain ⟨P, hPH, hPdec, hcov, hU', hdeg⟩ := hlev V p G (levelGraph G (W i) D) (W i) (W (i + 1))
    (W (i + 2)) hlvl (hN i hi)
  rw [levelGraph_edgeFinset] at hPH hcov
  refine ⟨P, hPH, hPdec, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨he1, he2⟩ := mem_sdiff.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp he1).1).1, hcov e he1 he2⟩
  · exact disjoint_left.mpr fun e heP heR => hU' e heP (mem_filter.mp heR).2
  · intro v
    have h1 : ((P ∩ edgesIn G (W (i + 1))).filter fun e => v ∈ e) ⊆
        ((P.filter fun e => ∀ w ∈ e, w ∈ W (i + 1)).filter fun e => v ∈ e) := by
      intro e he
      obtain ⟨he1, hv⟩ := mem_filter.mp he
      obtain ⟨heP, heR⟩ := mem_inter.mp he1
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨heP, (mem_filter.mp heR).2⟩, hv⟩
    have h2 : (((P ∩ edgesIn G (W (i + 1))).filter fun e => v ∈ e).card : ℝ) ≤
        (((P.filter fun e => ∀ w ∈ e, w ∈ W (i + 1)).filter fun e => v ∈ e).card : ℝ) := by
      exact_mod_cast card_le_card h1
    exact h2.trans (hdeg v)

/-- **Closing the `F₁` case from the uniform level producer and an explicit vortex**
(proved). Constants first (`LevelConstants`, `γ`); then `Nlev`; then for each terminal size
`M` a threshold `N`. Remaining inputs: compatible supply, integral divisibility, the `F₁`
typing of the host and the geometric vortex (`F1Vortex`) with all non-terminal levels of
size `≥ Nlev` and terminal level of size `≤ M`. -/
theorem F1_close_from_vortex {β κ ξ ζ ρ ε η : ℝ} (hc : LevelConstants β κ ξ ζ ρ ε η)
    (γ : ℝ) (hγ : 0 < γ) (hγβ : 5 * β ≤ γ) :
    ∃ Nlev : ℕ, 0 < Nlev ∧ ∀ M : ℕ, ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (W : ℕ → Finset V) (L : ℕ),
      N ≤ Fintype.card V → CompatibleSupply p F1 G (γ * Fintype.card V) →
      IsIntDiv p F1 G.edgeFinset → (∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) →
      W 0 = univ → F1Vortex p G W L β κ ξ → (∀ i < L, Nlev ≤ (W i).card) →
      (W L).card ≤ M → HasDecomp p F1 G.edgeFinset := by
  have hζ := hc.zeta_pos
  have hβ : 0 < β := hc.1.1
  obtain ⟨Nlev, hNlev, hlev⟩ := F1_protected_level_of_constants hc
  refine ⟨Nlev, hNlev, fun M => ?_⟩
  obtain ⟨N₁, hN₁⟩ := f1_close_constructing_absorber (M * M) γ ζ hγ hζ
  refine ⟨max N₁ (M + 1), ?_⟩
  intro V _ _ G _ p W L hn hs hdiv hGF hW0 hW hN hM
  have hcardW0 : (W 0).card = Fintype.card V := by rw [hW0]; rfl
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; rw [hcardW0] at hM; have := le_max_right N₁ (M + 1); omega
    · exact h
  have hchain : ∀ k, 1 ≤ k → k ≤ L → W k ⊆ W 1 := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; exact subset_rfl
      · exact (hW.sub k (by omega)).trans (ih h (by omega))
  have hmonoE : ∀ {S T : Finset V}, S ⊆ T → edgesIn G S ⊆ edgesIn G T := by
    intro S T hST e he
    obtain ⟨he1, he2⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨he1, fun v hv => hST (he2 v hv)⟩
  apply hN₁ G p (fun i => edgesIn G (W i)) (fun i => ζ * (W i).card) L
    (le_trans (le_max_left _ _) hn) hs
  · show edgesIn G (W 0) = G.edgeFinset
    rw [hW0]; ext e; simp [edgesIn]
  · intro i hi; exact hmonoE (hW.sub i hi.le)
  · exact filter_subset _ _
  · exact hmonoE (hchain L hL le_rfl)
  · show (edgesIn G (W L)).card ≤ M * M
    have hsub : edgesIn G (W L) ⊆ (W L ×ˢ W L).image (fun x => s(x.1, x.2)) := by
      intro e he
      obtain ⟨-, hall⟩ := mem_filter.mp he
      induction e using Sym2.ind with
      | _ a b =>
        exact mem_image.mpr ⟨(a, b), mem_product.mpr ⟨hall a (Sym2.mem_mk_left _ _),
          hall b (Sym2.mem_mk_right _ _)⟩, rfl⟩
    calc (edgesIn G (W L)).card ≤ (W L ×ˢ W L).card := (card_le_card hsub).trans card_image_le
      _ = (W L).card * (W L).card := card_product _ _
      _ ≤ M * M := Nat.mul_le_mul hM hM
  · intro v
    have h1 := deg_le_of_subset_image v (fun e he => (mem_filter.mp he).2 : ∀ e ∈ edgesIn G (W 1),
      ∀ w ∈ e, w ∈ W 1)
    have h2 := hW.hi 0 (Nat.zero_le _)
    rw [hcardW0] at h2
    have h3 : β * (Fintype.card V : ℝ) ≤ γ * Fintype.card V / 5 := by
      have := mul_le_mul_of_nonneg_right hγβ (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
      linarith
    exact (by exact_mod_cast h1 : (((edgesIn G (W 1)).filter fun e => v ∈ e).card : ℝ) ≤
      (W 1).card).trans (h2.trans h3)
  · show ζ * Fintype.card V ≤ ζ * (W 0).card
    rw [hcardW0]
  · exact hdiv
  · exact F1_vortex_step Nlev (hlev) G p W L hGF hW hN

/-- The closing theorem with the concrete constants of `exists_level_constants`
(`β = 10⁻⁶`), for any compatible-supply parameter `γ ≥ 5 β`. -/
theorem F1_close_from_vortex_concrete (γ : ℝ) (hγ : 5 / 10 ^ 6 ≤ γ) :
    ∃ Nlev : ℕ, 0 < Nlev ∧ ∀ M : ℕ, ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (W : ℕ → Finset V) (L : ℕ),
      N ≤ Fintype.card V → CompatibleSupply p F1 G (γ * Fintype.card V) →
      IsIntDiv p F1 G.edgeFinset → (∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) →
      W 0 = univ → F1Vortex p G W L (1 / 10 ^ 6) (1 / 10 ^ 80) (1 / 10 ^ 80) →
      (∀ i < L, Nlev ≤ (W i).card) → (W L).card ≤ M → HasDecomp p F1 G.edgeFinset :=
  F1_close_from_vortex exists_level_constants γ (lt_of_lt_of_le (by norm_num) hγ)
    (by linarith)

end NashWilliams18.SpreadF1
