/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.LevelReserveF1
public import RequestProject.NW18.Case126.RepairedWeightsF1
public import RequestProject.NW18.Case126.LevelPackingF1
public import RequestProject.NW18.Case126.SetNibbleF1
public import PartitionedTriangleAbsorption.F1GraphReserveStage234

@[expose] public section

/-!
# The protected `F₁` level, part 1: pool capacity, charge demand, repair, weights, packing

`ProtLevel p G H W U U' β κ ξ ζ` collects the graph hypotheses of one protected vortex level
(child `U`, protected grandchild `U'`, near-quarter classes with error `κ|W|`, typicality `ξ|W|`
of the fixed host `G`, damage `ζ|W|` of the current graph `H`, protected child `H[U] = G[U]`,
and integral divisibility of `E(H)`, all of whose edges lie in `W`).

`level_repaired_packing` (proved): for constants satisfying explicit scalar inequalities, chosen
before the graph, there is `N` such that every protected level with `|W| ≥ N` has

1. ONE sampled reserve `R` (`level_reserve_exists`),
2. the boundary pools of Stage 233 built from the actual graph and the repair of THAT reserve
   (Stage 234, `balanced_reserve_from_graph`), whose premises are DERIVED here:
   * pool capacity `|A| (|U_k| - d - r) ≥ (β/256)|W|²` from the class sizes, typicality, damage
     and the reserve degree (`d = (ξ+ζ)|W|`, `r = (ρ+ε)|W|`);
   * charge demand `|q| ≤ (repDem - ε)|W|²` from the exact puncture ledger, the protected child,
     the reserve statistics and the inherited boundary damage `|bdDamCharge| ≤ 2ζ|U||W|`;
   * the sampling tail, uniformly above a threshold fixed before the graph;
3. exact positive weights on the repaired punctured level and an actual `F₁` packing `D₀` of it
   whose leave has maximum degree `≤ η|W|`.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.F1BalanceGateStage228 (pairCharge charge balance)
open PartitionedTriangleAbsorption.F1ReserveCorrectionStage231 (integerBalance
  cast_integerBalance)
open scoped NNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The graph hypotheses of one protected `F₁` vortex level.** -/
structure ProtLevel (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U U' : Finset V) (β κ ξ ζ : ℝ) : Prop where
  hU'U : U' ⊆ U
  hUW : U ⊆ W
  hUlo : β * W.card / 2 ≤ U.card
  hUhi : (U.card : ℝ) ≤ β * W.card
  hU'hi : (U'.card : ℝ) ≤ β * U.card
  hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)
  hHG : H ≤ G
  hHW : ∀ u v, H.Adj u v → u ∈ W
  hout : ∀ j : Fin 4, |(((W \ U).filter fun z => p z = j).card : ℝ) - tOf W U| ≤ κ * W.card
  hin : ∀ j : Fin 4, |((U.filter fun z => p z = j).card : ℝ) - uOf U| ≤ κ * W.card
  htyp : ∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
    ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card
  hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card
  hprot : ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → H.Adj u v
  hdiv : IsIntDiv p F1 H.edgeFinset

namespace ProtLevel

variable {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
  {W U U' : Finset V} {β κ ξ ζ : ℝ}

theorem edgesIn_W (h : ProtLevel p G H W U U' β κ ξ ζ) : edgesIn H W = H.edgeFinset := by
  ext e
  simp only [edgesIn, mem_filter, and_iff_left_iff_imp]
  intro he v hv
  induction e using Sym2.ind with
  | _ a b =>
    have hab := SimpleGraph.mem_edgeFinset.mp he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact h.hHW _ _ hab
    · exact h.hHW _ _ hab.symm

theorem support (h : ProtLevel p G H W U U' β κ ξ ζ) : ∀ e ∈ H.edgeFinset, ∀ v ∈ e, v ∈ W := by
  intro e he v hv
  rw [← h.edgesIn_W] at he
  exact (mem_filter.mp he).2 v hv

theorem levelHyp (h : ProtLevel p G H W U U' β κ ξ ζ) (hW : 0 < W.card) (hβ : β ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) : LevelHyp p G H W U κ ξ ζ :=
  { hUW := h.hUW, hW := hW, hUh := by
      have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
      nlinarith [h.hUhi]
    hκ := hκ, hξ := hξ, hζ := hζ, hGF := h.hGF, hHG := h.hHG, hout := h.hout, hin := h.hin,
    htyp := h.htyp, hdam := h.hdam }

/-- Classes of `W` are near-quarter with error `2κ|W|`. -/
theorem cls (h : ProtLevel p G H W U U' β κ ξ ζ) (j : Fin 4) :
    |((W.filter fun z => p z = j).card : ℝ) - W.card / 4| ≤ 2 * κ * W.card := by
  have hsplit : (W.filter fun z => p z = j).card =
      ((W \ U).filter fun z => p z = j).card + (U.filter fun z => p z = j).card := by
    rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff_self_left),
      ← filter_union, sdiff_union_of_subset h.hUW]
  have hWU : ((W \ U).card : ℝ) = W.card - U.card := by
    rw [card_sdiff_of_subset h.hUW, Nat.cast_sub (card_le_card h.hUW)]
  have h1 := abs_le.mp (h.hout j)
  have h2 := abs_le.mp (h.hin j)
  rw [hsplit, Nat.cast_add]
  unfold tOf uOf at *
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end ProtLevel

omit [Fintype V] in
/-- **Inherited boundary damage**: the signed charge of the damaged boundary edges is at most
`2 ζ |U| |W|` in absolute value (counted from the child side). -/
theorem bdDamCharge_abs_le (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U : Finset V) (hUW : U ⊆ W) (ζ : ℝ)
    (hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card) :
    |bdDamCharge p G H W U| ≤ 2 * ζ * U.card * W.card := by
  unfold bdDamCharge
  have hx : ∀ x ∈ W \ U,
      |∑ z ∈ U.filter (fun z => G.Adj x z ∧ ¬ H.Adj x z), (pairCharge (p x) (p z) : ℝ)| ≤
        ∑ z ∈ U, if G.Adj x z ∧ ¬ H.Adj x z then (2 : ℝ) else 0 := by
    intro x _
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_filter]
    refine sum_le_sum fun z _ => ?_
    split_ifs
    · have : ∀ i j : Fin 4, |(pairCharge i j : ℝ)| ≤ 2 := by
        intro i j; fin_cases i <;> fin_cases j <;> norm_num [pairCharge]
      exact this _ _
    · exact le_refl _
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hx).trans ?_)
  rw [sum_comm]
  have hz : ∀ z ∈ U, (∑ x ∈ W \ U, if G.Adj x z ∧ ¬ H.Adj x z then (2 : ℝ) else 0) ≤
      2 * (ζ * W.card) := by
    intro z hz
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hsub : (W \ U).filter (fun x => G.Adj x z ∧ ¬ H.Adj x z) ⊆
        W.filter fun v => G.Adj z v ∧ ¬ H.Adj z v := by
      intro x hx
      simp only [mem_filter, mem_sdiff] at hx ⊢
      exact ⟨hx.1.1, hx.2.1.symm, fun h => hx.2.2 h.symm⟩
    have hc : (((W \ U).filter (fun x => G.Adj x z ∧ ¬ H.Adj x z)).card : ℝ) ≤ ζ * W.card :=
      (show (((W \ U).filter (fun x => G.Adj x z ∧ ¬ H.Adj x z)).card : ℝ) ≤
        (W.filter fun v => G.Adj z v ∧ ¬ H.Adj z v).card by
          exact_mod_cast card_le_card hsub).trans (hdam z (hUW hz))
    linarith
  refine (sum_le_sum hz).trans (le_of_eq ?_)
  rw [sum_const, nsmul_eq_mul]
  ring

/-- Degree gap of any subgraph of the level host inside `W`. -/
theorem sub_degree_le {p : V → Fin 4} {G : SimpleGraph V} [DecidableRel G.Adj]
    {W : Finset V} {κ : ℝ} (hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v))
    (hcls : ∀ j : Fin 4, |((W.filter fun z => p z = j).card : ℝ) - W.card / 4| ≤ κ * W.card)
    (J : SimpleGraph V) [DecidableRel J.Adj] (hJG : J ≤ G) (hJW : ∀ x y, J.Adj x y → x ∈ W)
    (v : V) :
    ((J.edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤ (1 - (1 / 4 - κ)) * W.card := by
  rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
  set M := W.filter fun z => p z = missedF1 (p v) with hM
  have hsub : J.neighborFinset v ⊆ W \ M := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    rw [mem_sdiff]
    refine ⟨hJW z v hz.symm, fun hzM => ?_⟩
    have hzl : p z = missedF1 (p v) := (mem_filter.mp hzM).2
    have := hGF v z (hJG hz)
    rw [hzl] at this
    exact not_allowedT_missedF1 _ this
  have hMW : M ⊆ W := filter_subset _ _
  have hc := card_le_card hsub
  rw [card_sdiff_of_subset hMW, SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hMc := abs_le.mp (hcls (missedF1 (p v)))
  have hMle : M.card ≤ W.card := card_le_card hMW
  have hc' : (J.degree v : ℝ) ≤ (W.card : ℝ) - M.card := by
    rw [← Nat.cast_sub hMle]; exact_mod_cast hc
  rw [← hM] at hMc
  nlinarith [hMc.1]

/-- Charge-demand coefficient of the repaired level (with one unit `ε` of slack). -/
noncomputable def repDem (β κ ξ ζ ρ ε : ℝ) : ℝ :=
  2 * ρ * ζ * β + (2 * κ + ξ) + 18 * ε + ρ * (4 * κ + 2 * ξ) + ε

/-- Degree coefficient of the charge correction: `2 (prob + b/|W|)` with pool capacity
`σ = β/256`, `prob = 3 repDem / σ` and `b = (repDem/σ) |W|`. -/
noncomputable def repDelta (β κ ξ ζ ρ ε : ℝ) : ℝ := 2048 * repDem β κ ξ ζ ρ ε / β

set_option maxHeartbeats 3200000 in
/-- **Pool capacity, charge demand and inherited damage for the SAME repaired reserve, then
exact weights and an actual `F₁` packing of the repaired punctured level** (producer, proved).
All constants precede the graph; the threshold `N` depends only on them. -/
theorem level_repaired_packing (β κ ξ ζ ρ ε η : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hε : 0 < ε)
    (hη : 0 < η) (hκ16 : κ ≤ 1 / 16)
    (hpool : κ + ξ + ζ + ρ + ε ≤ β / 16)
    (hprob : 3 * repDem β κ ξ ζ ρ ε ≤ β / 256)
    (hsmall : 3 * ξ + ζ + β + (ρ + ε + repDelta β κ ξ ζ ρ ε) + 6 * (2 * κ) ≤ 1 / 5120) :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
      ProtLevel p G H W U U' β κ ξ ζ → N ≤ W.card →
      ∃ R R' D₀ : Finset (Sym2 V),
        R ⊆ bdEdges H W U ∧ CrossResGood p H W U R ρ (3 * ε) ∧
        (∀ x, ((R.filter fun e => x ∈ e).card : ℝ) ≤ (ρ + ε) * W.card) ∧
        (∀ x ∈ W, ∀ v ∈ W, ∀ c : Fin 4,
          ((U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(x, z) ∈ R).card : ℝ) ≤
            ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ H.Adj v z).card) + ε * W.card) ∧
        R ⊆ R' ∧ R' ⊆ H.edgeFinset \ edgesIn H U ∧
        (∀ e ∈ R' \ R, ∃ x ∈ W \ U, ∃ y ∈ U, s(x, y) = e) ∧
        (∀ v, (((R' \ R).filter fun e => v ∈ e).card : ℝ) ≤ repDelta β κ ξ ζ ρ ε * W.card) ∧
        D₀ ⊆ (punc H W U R').edgeFinset ∧ HasDecomp p F1 D₀ ∧
        ∀ v, ((((punc H W U R').edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
          η * W.card := by
  set κd := repDem β κ ξ ζ ρ ε with hκd
  set σ : ℝ := β / 256 with hσ
  have hκd0 : 0 < κd := by rw [hκd]; unfold repDem; positivity
  have hσ0 : 0 < σ := by positivity
  obtain ⟨N₁, hN₁0, hN₁⟩ := level_reserve_exists ε hε
  obtain ⟨N₂, hN₂⟩ := F1GraphReserveStage234.exists_tail_threshold κd (κd / σ) hκd0
    (by positivity)
  obtain ⟨δn, hδn, N₃, hN₃⟩ := typed_nibble_on_set 3 η (1 / 8) (by norm_num) hη (by norm_num)
  refine ⟨max (max N₁ N₂) (max N₃ (max 20480 ⌈1 / ε⌉₊)), by positivity, ?_⟩
  intro V _ _ p G H _ _ W U U' h hNW
  have hN1 : N₁ ≤ W.card := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNW
  have hN2 : N₂ ≤ W.card := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNW
  have hN3 : N₃ ≤ W.card := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNW
  have hN4 : 20480 ≤ W.card := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) hNW
  have hN5 : ⌈1 / ε⌉₊ ≤ W.card := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) hNW
  have hW : 0 < W.card := by omega
  set n : ℝ := (W.card : ℝ) with hn
  have hn0 : (20480 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hN4
  have hεn : 1 ≤ ε * n := by
    have h1 : 1 / ε ≤ n := (Nat.le_ceil _).trans (by rw [hn]; exact_mod_cast hN5)
    rw [div_le_iff₀ hε] at h1; linarith
  obtain ⟨R, hRbd, hRg, hRdeg, hRbad⟩ := hN₁ V p H W U U' ρ h.hUW hρ.le (by linarith) hN1
  have hLH := h.levelHyp hW hβ1 hκ hξ hζ
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  -- the reserve avoids the child
  have hRI : R ⊆ H.edgeFinset \ edgesIn H U := by
    intro e he
    obtain ⟨heH, x, hx, z, hz, rfl⟩ := mem_filter.mp (hRbd he)
    refine mem_sdiff.mpr ⟨heH, fun hin => ?_⟩
    exact (mem_sdiff.mp hx).2 ((mem_filter.mp hin).2 x (Sym2.mem_mk_left _ _))
  have hRsub : R ⊆ edgesIn H W \ edgesIn H U := by rw [h.edgesIn_W]; exact hRI
  have hdivW : IsIntDiv p F1 (edgesIn H W) := by rw [h.edgesIn_W]; exact h.hdiv
  -- the pool block and its geometric estimates
  set A := (W \ U).filter fun z => p z = 0 with hAdef
  have hAWU : A ⊆ W \ U := filter_subset _ _
  have hlabel : ∀ x ∈ A, p x = 0 := fun x hx => (mem_filter.mp hx).2
  have hcross : pairCharge 0 2 = 1 := by decide
  have hmiss : ∀ x ∈ A, ∀ k ∈ ({0, 2} : Finset (Fin 4)),
      ((U.filter fun y => p y = k ∧ ¬ H.Adj x y).card : ℝ) ≤ (ξ + ζ) * n := by
    intro x hx k hk
    have hxW : x ∈ W := (mem_sdiff.mp (hAWU hx)).1
    have hallow : AllowedT F1 (p x) k := by
      rw [hlabel x hx]
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl <;> decide
    have hsub : U.filter (fun y => p y = k ∧ ¬ H.Adj x y) ⊆
        W.filter (fun y => p y = k ∧ ¬ G.Adj x y) ∪
          W.filter (fun y => G.Adj x y ∧ ¬ H.Adj x y) := by
      intro y hy
      obtain ⟨hyU, hyk, hyH⟩ := mem_filter.mp hy
      by_cases hG : G.Adj x y
      · exact mem_union_right _ (mem_filter.mpr ⟨h.hUW hyU, hG, hyH⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨h.hUW hyU, hyk, hG⟩)
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    have hc' : ((U.filter fun y => p y = k ∧ ¬ H.Adj x y).card : ℝ) ≤
        (W.filter (fun y => p y = k ∧ ¬ G.Adj x y)).card +
          (W.filter (fun y => G.Adj x y ∧ ¬ H.Adj x y)).card := by exact_mod_cast hc
    have := h.htyp x hxW k hallow
    have := h.hdam x hxW
    linarith
  have hres : ∀ x ∈ A, ((R.filter fun e => x ∈ e).card : ℝ) ≤ (ρ + ε) * n :=
    fun x _ => hRdeg x
  -- pool capacity
  have hAcard : n / 16 ≤ (A.card : ℝ) := by
    have h0 := (abs_le.mp (h.hout 0)).1
    unfold tOf at h0
    have := h.hUhi
    nlinarith
  have hUk : ∀ k : Fin 4, β * n / 16 ≤
      ((U.filter fun y => p y = k).card : ℝ) - (ξ + ζ) * n - (ρ + ε) * n := by
    intro k
    have h0 := (abs_le.mp (h.hin k)).1
    unfold uOf at h0
    have := h.hUlo
    nlinarith
  have hcap : ∀ k : Fin 4, σ * n ^ 2 ≤
      (A.card : ℝ) * (((U.filter fun y => p y = k).card : ℝ) - (ξ + ζ) * n - (ρ + ε) * n) := by
    intro k
    have h1 := hUk k
    have h2 : 0 ≤ β * n / 16 := by positivity
    calc σ * n ^ 2 = (n / 16) * (β * n / 16) := by rw [hσ]; ring
      _ ≤ _ := mul_le_mul hAcard h1 h2 (by positivity)
  -- charge demand on the same reserve
  set q : ℤ := -integerBalance p (H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U) -
    integerBalance p R with hq
  have hqR : (q : ℝ) = balance p (punc H W U R).edgeFinset := by
    rw [punc_balance_ledger p H W U R h.hUW hdivW hRsub, hq]
    push_cast [cast_integerBalance]
    rfl
  have hdefect := punctured_balance_defect (puncHyp_of hLH hRg hρ.le hρ1 (by positivity))
    hdivW h.hprot hRg hρ.le (by positivity)
  have hdam := bdDamCharge_abs_le p G H W U h.hUW ζ h.hdam
  have hqb : |(q : ℝ)| ≤ (κd - ε) * n ^ 2 := by
    rw [hqR]
    have hρd : |ρ * bdDamCharge p G H W U| ≤ ρ * (2 * ζ * U.card * n) := by
      rw [abs_mul, abs_of_pos hρ]; exact mul_le_mul_of_nonneg_left hdam hρ.le
    have hUb : ρ * (2 * ζ * U.card * n) ≤ 2 * ρ * ζ * β * n ^ 2 := by
      have := h.hUhi
      have : 0 ≤ 2 * ρ * ζ * n := by positivity
      nlinarith
    have hsplit := abs_sub_abs_le_abs_sub (balance p (punc H W U R).edgeFinset)
      (ρ * bdDamCharge p G H W U)
    rw [hκd]; unfold repDem
    nlinarith
  set prob : ℝ≥0 := ⟨3 * κd / σ, by positivity⟩ with hprobdef
  have hprob1 : prob ≤ 1 := by
    rw [← NNReal.coe_le_coe, hprobdef]
    show 3 * κd / σ ≤ 1
    rw [div_le_one hσ0]; exact hprob
  have hsize : ∀ k ∈ ({0, 2} : Finset (Fin 4)),
      (((-integerBalance p (H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U)
        - integerBalance p R).natAbs + 1 : ℕ) : ℝ) ≤
      prob * ((A.card : ℝ) * ((U.filter fun y => p y = k).card - (ξ + ζ) * n - (ρ + ε) * n)) -
        κd * n ^ 2 := by
    intro k _
    rw [← hq]
    have hcast : (((q.natAbs + 1 : ℕ)) : ℝ) = |(q : ℝ)| + 1 := by
      push_cast [Nat.cast_natAbs, Int.cast_abs]; ring
    rw [hcast]
    have hp : (prob : ℝ) = 3 * κd / σ := rfl
    have hm := mul_le_mul_of_nonneg_left (hcap k) (show (0 : ℝ) ≤ prob from prob.2)
    have he : (prob : ℝ) * (σ * n ^ 2) = 3 * κd * n ^ 2 := by
      rw [hp]; field_simp
    have hεn2 : 1 ≤ ε * n ^ 2 := by nlinarith
    nlinarith
  have htail := (hN₂ W.card hN2).2
  obtain ⟨R', hRR', hR'E, hbal, hnew, -, hdegC, hdegR'⟩ :=
    F1GraphReserveStage234.balanced_reserve_from_graph H p W U A R 0 2 hW h.hUW hAWU h.support
      hlabel hcross (balance_eq_zero_of_intDiv p _ h.hdiv) hRI ((ξ + ζ) * n) ((ρ + ε) * n)
      prob hprob1 (κd * n ^ 2) (κd / σ * n) (by positivity) (by positivity) hmiss hres hsize
      htail
  have hδ : 2 * ((prob : ℝ) * n + κd / σ * n) = repDelta β κ ξ ζ ρ ε * n := by
    have hp : (prob : ℝ) = 3 * κd / σ := rfl
    rw [hp, hσ]; unfold repDelta; rw [← hκd]; field_simp; ring
  rw [hδ] at hdegC hdegR'
  -- exact weights on the repaired punctured level
  have hbal' : balance p (punc H W U R').edgeFinset = 0 := by
    rw [punc_edgeFinset_eq, h.edgesIn_W]; exact hbal
  have hRes' : ∀ u ∈ W, ((W.filter fun v => s(u, v) ∈ R').card : ℝ) ≤
      (ρ + ε + repDelta β κ ξ ζ ρ ε) * n := by
    intro u _
    have h1 : ((W.filter fun v => s(u, v) ∈ R').card : ℝ) ≤ (R'.filter fun e => u ∈ e).card := by
      exact_mod_cast nbr_card_le_deg W R' u
    have h2 := hdegR' u
    have h3 := hRdeg u
    linarith
  obtain ⟨w, hload, hw, hw0⟩ := F1_punctured_exact_weights p G H W U R' h.hGF h.hHG h.cls
    h.htyp h.hdam h.hUhi hRes' hsmall hN4 hbal'
  -- the packing
  have hJG : punc H W U R' ≤ G := fun a b hab => h.hHG hab.1
  have hdegJ : ∀ v, (((punc H W U R').edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤
      (1 - 1 / 8) * n := by
    intro v
    refine (sub_degree_le h.hGF h.cls (punc H W U R') hJG (fun x y hxy => hxy.2.1) v).trans ?_
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hφ : ∀ s, 0 ≤ w s ∧ w s ≤ 3 / n := by
    intro s
    by_cases hs : s ∈ copies p F1 (punc H W U R')
    · obtain ⟨h1, h2⟩ := hw s hs
      exact ⟨le_trans (by positivity) h1, h2⟩
    · rw [hw0 s hs]; exact ⟨le_refl _, by positivity⟩
  obtain ⟨D, Q, hQJ, hD, hresQ⟩ := hN₃ V W hN3 p F1 (punc H W U R') w
    (fun x y hxy => hxy.2.1) hφ hdegJ (fun e he => by
      have := hload e he
      unfold F1BalanceGateStage228.load at this
      rw [this, sub_self, abs_zero]; exact hδn.le)
  have hR'E' : R' ⊆ H.edgeFinset \ edgesIn H U := hR'E
  exact ⟨R, R', Q, hRbd, hRg, hRdeg, hRbad, hRR', hR'E', hnew, hdegC, hQJ, ⟨D, hD⟩, hresQ⟩

end NashWilliams18.SpreadF1
