/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.LevelFieldsF1

/-!
# The uniform protected `F₁` level producer

`F1_protected_level` (proved): for constants `β κ ξ ζ ρ ε η` satisfying explicit scalar
inequalities (chosen before any graph; `exists_level_constants` exhibits concrete values), there
is `N` such that EVERY protected level `ProtLevel p G H W U U' β κ ξ ζ` with `|W| ≥ N` has an
actual `F₁`-decomposable `D ⊆ E(H)` such that

* every edge of `H` not covered by `D` lies inside the child `U`;
* `D` uses no edge inside the protected grandchild `U'`;
* the edges of `D` inside `U` have maximum degree at most `ζ |U|` (the next damage budget).

The proof samples ONE reserve, repairs its charge on the actual boundary pools, packs the
repaired punctured level with exact weights (`level_repaired_packing`), takes the actual
leftover `Hout` (inside `W \ U`) and the cross graph `Q = R ∪ (C ∪ Lc)` (reserve, correction,
cross leftover), derives every numerical input of the spread cover-down from the physical
counts (`LevelCountsF1.lean`) and assembles the level (`level_of_supply_data`).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen ApexF1
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

set_option maxHeartbeats 4000000 in
/-- **One protected level from the repaired packing** (proved): given the actual outputs of
`level_repaired_packing` for a fixed level and the scalar inequalities, the leftover outside the
child is covered by actual apices and the cross leftover by the spread cover-down. -/
theorem protected_level_of_packing {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V)
    {β κ ξ ζ ρ ε η δ θ b g ωc Lc X : ℝ} (h : ProtLevel p G H W U U' β κ ξ ζ)
    (hW : 0 < W.card) (hβ1 : β ≤ 1 / 2) (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) (hρ : 0 < ρ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hb0 : 0 < b) (hβ : 0 ≤ β)
    (hθ : θ = δ + η) (hg : g = ρ * (β ^ 2 + ξ) + ε + θ)
    (hωc : ωc = ρ ^ 2 * β + 12 * ε + 2 * θ) (hLc : Lc = ρ + ε + θ)
    (hX : X = ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε)
    (hkey : (8 * g + 16 * b + 2 * η) * W.card + 35 +
      (ρ * (3 * κ + 2 * ξ + 2 * ζ) + 9 * ε + θ) * W.card ≤ ρ * (U.card / 4))
    (hsan : 5 ≤ (X - 3 * η) * W.card)
    (hbn : 8 * Lc / b ^ 2 + 256 / b ^ 2 ≤ W.card)
    (hover : 2 * ωc * Lc / b ≤ b / 2)
    (hLz : Lc * W.card ≤ ζ * U.card)
    (R R' D₀ : Finset (Sym2 V))
    (hRbd : R ⊆ bdEdges H W U) (hRg : CrossResGood p H W U R ρ (3 * ε))
    (hRdeg : ∀ x, ((R.filter fun e => x ∈ e).card : ℝ) ≤ (ρ + ε) * W.card)
    (hRbad : ∀ x ∈ W, ∀ v ∈ W, ∀ c : Fin 4,
      ((U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(x, z) ∈ R).card : ℝ) ≤
        ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ H.Adj v z).card) + ε * W.card)
    (hRR' : R ⊆ R') (hR'E : R' ⊆ H.edgeFinset \ edgesIn H U)
    (hnew : ∀ e ∈ R' \ R, ∃ x ∈ W \ U, ∃ y ∈ U, s(x, y) = e)
    (hdegC : ∀ v, (((R' \ R).filter fun e => v ∈ e).card : ℝ) ≤ δ * W.card)
    (hD₀J : D₀ ⊆ (punc H W U R').edgeFinset) (hD₀dec : HasDecomp p F1 D₀)
    (hresD : ∀ v, ((((punc H W U R').edgeFinset \ D₀).filter fun e => v ∈ e).card : ℝ) ≤
      η * W.card) :
    ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
      (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
      (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
      ∀ v, (((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℝ) ≤
        ζ * U.card := by
  subst hθ hg hωc hLc hX
  obtain ⟨v0, -⟩ := card_pos.mp hW
  have hn0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW
  set J := punc H W U R' with hJdef
  set Lft := J.edgeFinset \ D₀ with hLft
  set Hout := Lft.filter fun e => ∀ v ∈ e, v ∉ U with hHout
  set Lcr := Lft.filter fun e => ¬ ∀ v ∈ e, v ∉ U with hLcr
  set E := (R' \ R) ∪ Lcr with hE
  set Q := R ∪ E with hQ
  set Rint := edgesIn H U \ edgesIn H U' with hRint
  have hJmem : ∀ a c, s(a, c) ∈ J.edgeFinset ↔
      H.Adj a c ∧ a ∈ W ∧ c ∈ W ∧ ¬ (a ∈ U ∧ c ∈ U) ∧ s(a, c) ∉ R' := by
    intro a c; rw [SimpleGraph.mem_edgeFinset]; exact punc_adj H W U R' a c
  have hJH : J.edgeFinset ⊆ H.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a c => exact SimpleGraph.mem_edgeFinset.mpr ((hJmem a c).mp he).1
  have hEdeg : ∀ v, ((E.filter fun e => v ∈ e).card : ℝ) ≤ (δ + η) * W.card := by
    intro v
    have h1 : (E.filter fun e => v ∈ e).card ≤ ((R' \ R).filter fun e => v ∈ e).card +
        (Lcr.filter fun e => v ∈ e).card := by
      rw [hE, filter_union]; exact card_union_le _ _
    have h2 : (Lcr.filter fun e => v ∈ e).card ≤ (Lft.filter fun e => v ∈ e).card :=
      card_le_card (filter_subset_filter _ (filter_subset _ _))
    have h1' : ((E.filter fun e => v ∈ e).card : ℝ) ≤ ((R' \ R).filter fun e => v ∈ e).card +
        (Lft.filter fun e => v ∈ e).card := by exact_mod_cast h1.trans (by omega)
    linarith only [h1', hdegC v, hresD v]
  have hQH : Q ⊆ H.edgeFinset := by
    intro e he
    rcases mem_union.mp he with heR | heE
    · exact (mem_filter.mp (hRbd heR)).1
    rcases mem_union.mp heE with heC | heL
    · exact (mem_sdiff.mp (hR'E (mem_sdiff.mp heC).1)).1
    · exact hJH (mem_sdiff.mp (mem_filter.mp heL).1).1
  have hQcross : ∀ e ∈ Q, ∃ x ∈ W \ U, ∃ z ∈ U, e = s(x, z) := by
    intro e he
    rcases mem_union.mp he with heR | heE
    · obtain ⟨-, x, hx, z, hz, rfl⟩ := mem_filter.mp (hRbd heR)
      exact ⟨x, hx, z, hz, rfl⟩
    rcases mem_union.mp heE with heC | heL
    · obtain ⟨x, hx, z, hz, hxz⟩ := hnew e heC
      exact ⟨x, hx, z, hz, hxz.symm⟩
    · obtain ⟨heLft, hnot⟩ := mem_filter.mp heL
      have heJ := (mem_sdiff.mp heLft).1
      induction e using Sym2.ind with
      | _ a c =>
        obtain ⟨-, ha, hc, hnU, -⟩ := (hJmem a c).mp heJ
        push_neg at hnot
        obtain ⟨w, hw, hwU⟩ := hnot
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact ⟨c, mem_sdiff.mpr ⟨hc, fun hcU => hnU ⟨hwU, hcU⟩⟩, w, hwU, Sym2.eq_swap⟩
        · exact ⟨a, mem_sdiff.mpr ⟨ha, fun haU => hnU ⟨haU, hwU⟩⟩, w, hwU, rfl⟩
  have hHoutH : Hout ⊆ H.edgeFinset := fun e he =>
    hJH (mem_sdiff.mp (mem_filter.mp he).1).1
  have hHoutW : ∀ e ∈ Hout, ∃ a c, e = s(a, c) ∧ H.Adj a c ∧ a ∈ W ∧ c ∈ W ∧ a ∉ U ∧ c ∉ U := by
    intro e he
    obtain ⟨heLft, hall⟩ := mem_filter.mp he
    have heJ := (mem_sdiff.mp heLft).1
    induction e using Sym2.ind with
    | _ a c =>
      obtain ⟨hac, ha, hc, -, -⟩ := (hJmem a c).mp heJ
      exact ⟨a, c, rfl, hac, ha, hc, hall a (Sym2.mem_mk_left _ _),
        hall c (Sym2.mem_mk_right _ _)⟩
  have hHoutdiag : ∀ e ∈ Hout, ¬ e.IsDiag := fun e he =>
    H.not_isDiag_of_mem_edgeFinset (hHoutH he)
  obtain ⟨x, y, himg, hxy, hinj, hxyH⟩ := enum_edges Hout hHoutdiag v0
  obtain ⟨r, hrinj, hrmem, hrsurj⟩ := enum_verts (W \ U) v0
  set k := Hout.card with hk
  set kr := (W \ U).card with hkr
  have hxyW : ∀ i < k, x i ∈ W ∧ y i ∈ W ∧ x i ∉ U ∧ y i ∉ U ∧ H.Adj (x i) (y i) := by
    intro i hi
    obtain ⟨a, c, hac, hadj, ha, hc, haU, hcU⟩ := hHoutW _ (hxyH i hi)
    rcases Sym2.eq_iff.mp hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hc, haU, hcU, hadj⟩
    · exact ⟨hc, ha, hcU, haU, hadj.symm⟩
  have hrW : ∀ j < kr, r j ∈ W ∧ r j ∉ U := fun j hj => mem_sdiff.mp (hrmem j hj)
  have hdegHout : ∀ v, (Hout.filter fun e => v ∈ e).card ≤ ⌈η * W.card⌉₊ := by
    intro v
    have h1 : ((Hout.filter fun e => v ∈ e).card : ℝ) ≤ η * W.card :=
      (by exact_mod_cast card_le_card (filter_subset_filter _ (filter_subset _ _)) :
        ((Hout.filter fun e => v ∈ e).card : ℝ) ≤ (Lft.filter fun e => v ∈ e).card).trans
        (hresD v)
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have hdegH : ∀ v, ((range k).filter (fun i => v = x i ∨ v = y i)).card ≤ ⌈η * W.card⌉₊ := by
    intro v
    refine le_trans ?_ (hdegHout v)
    apply card_le_card_of_injOn (fun i => s(x i, y i))
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
      simp only [coe_filter, Set.mem_setOf_eq]
      refine ⟨hxyH i hi.1, ?_⟩
      rcases hi.2 with rfl | rfl
      · exact Sym2.mem_mk_left _ _
      · exact Sym2.mem_mk_right _ _
    · intro i hi j hj hij
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      exact hinj i hi.1 j hj.1 hij
  have hLH : (range k).image (fun i => s(x i, y i)) ∪ Q ⊆ H.edgeFinset := by
    rw [himg]; exact union_subset hHoutH hQH
  have hLD₀ : Disjoint ((range k).image (fun i => s(x i, y i)) ∪ Q) D₀ := by
    rw [himg, disjoint_left]
    intro e he heD
    have heJ := hD₀J heD
    rcases mem_union.mp he with heH | heQ
    · exact (mem_sdiff.mp (mem_filter.mp heH).1).2 heD
    rcases mem_union.mp heQ with heR | heE
    · induction e using Sym2.ind with
      | _ a c => exact ((hJmem a c).mp heJ).2.2.2.2 (hRR' heR)
    rcases mem_union.mp heE with heC | heL
    · induction e using Sym2.ind with
      | _ a c => exact ((hJmem a c).mp heJ).2.2.2.2 (mem_sdiff.mp heC).1
    · exact (mem_sdiff.mp (mem_filter.mp heL).1).2 heD
  have hleft : ∀ e ∈ H.edgeFinset, (¬ ∀ v ∈ e, v ∈ U) → e ∉ D₀ →
      e ∈ (range k).image (fun i => s(x i, y i)) ∪ Q := by
    intro e he hnot heD
    rw [himg]
    by_cases heR' : e ∈ R'
    · refine mem_union_right _ ?_
      by_cases heR : e ∈ R
      · exact mem_union_left _ heR
      · exact mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨heR', heR⟩))
    · have heJ : e ∈ J.edgeFinset := by
        induction e using Sym2.ind with
        | _ a c =>
          have hac := SimpleGraph.mem_edgeFinset.mp he
          refine (hJmem a c).mpr ⟨hac, h.hHW a c hac, h.hHW c a hac.symm, ?_, heR'⟩
          rintro ⟨haU, hcU⟩
          exact hnot (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
      have heLft : e ∈ Lft := mem_sdiff.mpr ⟨heJ, heD⟩
      by_cases hall : ∀ v ∈ e, v ∉ U
      · exact mem_union_left _ (mem_filter.mpr ⟨heLft, hall⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _
          (mem_filter.mpr ⟨heLft, hall⟩)))
  have hRintH : Rint ⊆ H.edgeFinset := fun e he => (mem_filter.mp (mem_sdiff.mp he).1).1
  have hRintU : ∀ e ∈ Rint, ∀ v ∈ e, v ∈ U := fun e he => (mem_filter.mp (mem_sdiff.mp he).1).2
  have hRintU' : ∀ e ∈ Rint, ¬ ∀ v ∈ e, v ∈ U' := by
    intro e he hall
    exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp he).1).1, hall⟩)
  have hRQ : R ⊆ Q := fun e he => mem_union_left E he
  have hsup : ∀ i < k, ⌊(ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε) * W.card⌋₊ ≤ (U.filter (fun z => s(x i, z) ∈ Q ∧ s(y i, z) ∈ Q ∧
      ({p (x i), p (y i), p z} : Multiset (Fin 4)) ∈ F1)).card := by
    intro i hi
    obtain ⟨hxW, hyW, hxU, hyU, hadj⟩ := hxyW i hi
    exact field_apex h hW hβ1 hκ hξ hζ hRg hRQ hxW hyW (hxy i hi) hxU hyU
      (h.hGF _ _ (h.hHG hadj))
  have hkγ : k ≤ W.card * ⌈η * W.card⌉₊ := by
    have hsub : Hout ⊆ W.biUnion (fun v => Hout.filter fun e => v ∈ e) := by
      intro e he
      obtain ⟨a, c, rfl, -, ha, -, -, -⟩ := hHoutW e he
      exact mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨he, Sym2.mem_mk_left _ _⟩⟩
    calc k ≤ (W.biUnion (fun v => Hout.filter fun e => v ∈ e)).card := card_le_card hsub
      _ ≤ ∑ v ∈ W, (Hout.filter fun e => v ∈ e).card := card_biUnion_le
      _ ≤ ∑ _v ∈ W, ⌈η * W.card⌉₊ := sum_le_sum fun v _ => hdegHout v
      _ = W.card * ⌈η * W.card⌉₊ := by rw [sum_const, smul_eq_mul]
  have hs := field_apex_budget k W.card _ _ hkγ (field_three η (ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε) W.card hη hn0 hsan)
  have hQroot : ∀ e ∈ Q, ∃ j < kr, ∃ u ∈ U, e = s(r j, u) := by
    intro e he
    obtain ⟨x0, hx0, z, hz, rfl⟩ := hQcross e he
    obtain ⟨j, hj, hrj⟩ := hrsurj x0 hx0
    exact ⟨j, hj, z, hz, by rw [hrj]⟩
  have hmarg : ∀ j < kr, MarginsSlack p (p (r j)) (tgt U Q (r j))
      ((⌈(ρ * (β ^ 2 + ξ) + ε + (δ + η)) * W.card⌉₊ + 1) + (⌈b * W.card⌉₊ + ⌈b * W.card⌉₊)) ⌈η * W.card⌉₊ := by
    intro j hj
    exact field_margins h hRg hρ hEdeg (hrW j hj).1 (hrW j hj).2 hκ
      (by positivity) hb0.le hη hkey
  have hdense : ∀ j < kr, ∀ v ∈ tgt U Q (r j), ∀ c : Fin 4, LinkPair (p (r j)) (p v) c →
      ((tgt U Q (r j)).filter fun z => p z = c ∧ ¬ (z ≠ v ∧ s(v, z) ∈ Rint)).card ≤
        ⌈(ρ * (β ^ 2 + ξ) + ε + (δ + η)) * W.card⌉₊ + 1 := by
    intro j hj v hv c hc
    exact field_defect h hρ.le hβ hRbad hEdeg (hrW j hj).1 (mem_filter.mp hv).1
      (linkPair_allowed _ _ _ hc)
  have hoverlap : ∀ i < kr, ∀ j < kr, i ≠ j → ((tgt U Q (r i)) ∩ (tgt U Q (r j))).card ≤
      ⌈(ρ ^ 2 * β + 12 * ε + 2 * (δ + η)) * W.card⌉₊ := by
    intro i hi j hj hij
    exact field_overlap h hRg hEdeg (hrW i hi).1 (hrW j hj).1
      (fun he => hij (hrinj i hi j hj he)) (hrW i hi).2 (hrW j hj).2
  have hload : ∀ v, visits (fun j => tgt U Q (r j)) kr v ≤ ⌊(ρ + ε + (δ + η)) * W.card⌋₊ :=
    field_visits U R E kr r hrinj hRdeg hEdeg
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ range kr, ((tgt U Q (r j)).card : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hS := field_total W U Q h.hUW kr r (card_le_card sdiff_subset)
  have hB := spread_log_budget (W.card : ℝ) (ρ ^ 2 * β + 12 * ε + 2 * (δ + η)) (ρ + ε + (δ + η)) b
    (∑ j ∈ range kr, ((tgt U Q (r j)).card : ℝ)) ⌈(ρ ^ 2 * β + 12 * ε + 2 * (δ + η)) * W.card⌉₊ ⌊(ρ + ε + (δ + η)) * W.card⌋₊
    ⌈b * W.card⌉₊ ⌈b * W.card⌉₊ hb0
    (by positivity) (by positivity) hn1 (Nat.ceil_lt_add_one (by positivity)).le
    (Nat.floor_le (by positivity)) (Nat.le_ceil _) hS0 hS hover hbn (Nat.le_ceil _)
  have hK0 : 0 < ⌈b * W.card⌉₊ := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨D, hDH, hDdec, hDcov, hDU', hDdeg⟩ := level_of_supply_data p G H U U' h.hU'U h.hGF
    h.hHG h.hdiv D₀ k x y kr r Q Rint ⌊(ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε) * W.card⌋₊ ⌈η * W.card⌉₊ W.card
    (⌈(ρ * (β ^ 2 + ξ) + ε + (δ + η)) * W.card⌉₊ + 1) ⌈b * W.card⌉₊ ⌈b * W.card⌉₊ ⌈(ρ ^ 2 * β + 12 * ε + 2 * (δ + η)) * W.card⌉₊ ⌊(ρ + ε + (δ + η)) * W.card⌋₊
    (hD₀J.trans hJH) hD₀dec
    (fun e he hall => by
      have heJ := hD₀J he
      induction e using Sym2.ind with
      | _ a c =>
        exact ((hJmem a c).mp heJ).2.2.2.1
          ⟨hall a (Sym2.mem_mk_left _ _), hall c (Sym2.mem_mk_right _ _)⟩)
    hLH hLD₀ hleft hRintH hRintU hRintU' hxy hinj (fun i hi => (hxyW i hi).2.2.1)
    (fun i hi => (hxyW i hi).2.2.2.1) hdegH hsup hW hs hQroot hrinj
    (fun j hj => (hrW j hj).2) hK0 hdense hmarg hoverlap hload hB
  refine ⟨D, hDH, hDdec, hDcov, hDU', fun v => ?_⟩
  have h1 : ((((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℕ) : ℝ) ≤
      ((⌊(ρ + ε + (δ + η)) * W.card⌋₊ : ℕ) : ℝ) := by exact_mod_cast hDdeg v
  exact h1.trans ((Nat.floor_le (by positivity)).trans hLz)

set_option maxHeartbeats 4000000 in
/-- **The uniform protected `F₁` level producer** (proved). The constants and their scalar
inequalities come first; `N` depends only on them; then every protected level with `|W| ≥ N`
has an actual `F₁`-decomposable `D ⊆ E(H)` covering every edge of `H` outside the child `U`,
avoiding the protected grandchild `U'`, with child consumption at most `ζ |U|` per vertex. -/
theorem F1_protected_level (β κ ξ ζ ρ ε η : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hε : 0 < ε)
    (hη : 0 < η) (hκ16 : κ ≤ 1 / 16)
    (hpool : κ + ξ + ζ + ρ + ε ≤ β / 16)
    (hprob : 3 * repDem β κ ξ ζ ρ ε ≤ β / 256)
    (hsmall : 3 * ξ + ζ + β + (ρ + ε + repDelta β κ ξ ζ ρ ε) + 6 * (2 * κ) ≤ 1 / 5120)
    (hmargin : 8 * (ρ * (β ^ 2 + ξ) + ε + (repDelta β κ ξ ζ ρ ε + η)) +
        16 * (ρ * β / 10000) + 2 * η +
        (ρ * (3 * κ + 2 * ξ + 2 * ζ) + 9 * ε + (repDelta β κ ξ ζ ρ ε + η)) < ρ * β / 8)
    (hvis : ρ + ε + (repDelta β κ ξ ζ ρ ε + η) ≤ ζ * β / 2)
    (hover : 2 * (ρ ^ 2 * β + 12 * ε + 2 * (repDelta β κ ξ ζ ρ ε + η)) *
        (ρ + ε + (repDelta β κ ξ ζ ρ ε + η)) / (ρ * β / 10000) ≤ (ρ * β / 10000) / 2)
    (hapex : 3 * η < ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
      ProtLevel p G H W U U' β κ ξ ζ → N ≤ W.card →
      ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
        (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
        (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
        ∀ v, (((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℝ) ≤
          ζ * U.card := by
  have hδ0 : 0 ≤ repDelta β κ ξ ζ ρ ε := by unfold repDelta repDem; positivity
  have hb0 : 0 < ρ * β / 10000 := by positivity
  set sm := ρ * β / 8 - (8 * (ρ * (β ^ 2 + ξ) + ε + (repDelta β κ ξ ζ ρ ε + η)) +
        16 * (ρ * β / 10000) + 2 * η +
        (ρ * (3 * κ + 2 * ξ + 2 * ζ) + 9 * ε + (repDelta β κ ξ ζ ρ ε + η))) with hsmdef
  have hsm : 0 < sm := by rw [hsmdef]; linarith
  set sa := ρ ^ 2 * (β / 8 - κ - 2 * ξ - 2 * ζ) - 3 * ε - 3 * η with hsadef
  have hsa : 0 < sa := by rw [hsadef]; linarith
  set Nb := 8 * (ρ + ε + (repDelta β κ ξ ζ ρ ε + η)) / (ρ * β / 10000) ^ 2 +
    256 / (ρ * β / 10000) ^ 2 with hNb
  obtain ⟨N₀, hN₀, hN₀'⟩ := level_repaired_packing β κ ξ ζ ρ ε η hβ hβ1 hκ hξ hζ hρ hρ1 hε hη
    hκ16 hpool hprob hsmall
  refine ⟨max N₀ (max ⌈35 / sm⌉₊ (max ⌈5 / sa⌉₊ ⌈Nb⌉₊)), by positivity, ?_⟩
  intro V _ _ p G H _ _ W U U' h hNW
  have hN0 : N₀ ≤ W.card := le_trans (le_max_left _ _) hNW
  have hNm : ⌈35 / sm⌉₊ ≤ W.card :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNW
  have hNa : ⌈5 / sa⌉₊ ≤ W.card :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hNW
  have hNb' : ⌈Nb⌉₊ ≤ W.card :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hNW
  have hW : 0 < W.card := lt_of_lt_of_le hN₀ hN0
  have hn1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW
  have hsmn : 35 ≤ sm * W.card := by
    have h1 : 35 / sm ≤ W.card := (Nat.le_ceil _).trans (by exact_mod_cast hNm)
    rw [div_le_iff₀ hsm] at h1; linarith
  have hsan : 5 ≤ sa * W.card := by
    have h1 : 5 / sa ≤ W.card := (Nat.le_ceil _).trans (by exact_mod_cast hNa)
    rw [div_le_iff₀ hsa] at h1; linarith
  have hbn : Nb ≤ W.card := (Nat.le_ceil _).trans (by exact_mod_cast hNb')
  have hUlo := h.hUlo
  have hkey : (8 * (ρ * (β ^ 2 + ξ) + ε + (repDelta β κ ξ ζ ρ ε + η)) +
        16 * (ρ * β / 10000) + 2 * η) * W.card + 35 +
      (ρ * (3 * κ + 2 * ξ + 2 * ζ) + 9 * ε + (repDelta β κ ξ ζ ρ ε + η)) * W.card ≤
        ρ * (U.card / 4) := by
    have := mul_le_mul_of_nonneg_left hUlo hρ.le
    rw [hsmdef] at hsmn
    linarith
  have hLz : (ρ + ε + (repDelta β κ ξ ζ ρ ε + η)) * W.card ≤ ζ * U.card := by
    have h1 := mul_le_mul_of_nonneg_left hUlo hζ
    have h2 := mul_le_mul_of_nonneg_right hvis (Nat.cast_nonneg (α := ℝ) W.card)
    linarith
  obtain ⟨R, R', D₀, hRbd, hRg, hRdeg, hRbad, hRR', hR'E, hnew, hdegC, hD₀J, hD₀dec, hresD⟩ :=
    hN₀' V p G H W U U' h hN0
  exact protected_level_of_packing p G H W U U' h hW hβ1 hκ hξ hζ hρ hε.le hη.le hδ0 hb0 hβ.le
    rfl rfl rfl rfl rfl hkey (by rw [hsadef] at hsan; linarith) hbn hover hLz
    R R' D₀ hRbd hRg hRdeg hRbad hRR' hR'E hnew hdegC hD₀J hD₀dec hresD

end NashWilliams18.SpreadF1
