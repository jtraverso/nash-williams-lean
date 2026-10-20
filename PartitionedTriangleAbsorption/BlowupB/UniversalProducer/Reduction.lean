/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.PatternSupply
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ReductionArith
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Refiner
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.PairLattice

/-!
# From a shared EVEN refiner to the shared (integrally divisible) refiner

`EvenRefinerProducer` is the parity part of `RefinerProducer`: the same quantifiers and
budgets, but library pieces are only required to be loopless and even (with at most `m0`
edges), not integrally divisible.

`refinerProducer_of_evenRefinerProducer_pair` proves, for a family with `PairLattice`, that an
even refiner producer gives a `RefinerProducer` with explicit constants chosen before any
host:

* the integral type-charge group `TypeChargeGroup F` (torsion included) is generated, on all
  bounded active even pieces, by the FIXED finite list `genList F m0 (2 m0)` of pattern charges;
* for each generator a cyclic charge layer (`group_layer`, iterated by `iterate_layers`)
  is applied, with physical plus/minus tokens produced by the guarded supply
  (`tokSupply_of_pattern`), one shared token family per layer, fixed before the leftover;
* afterwards every library piece has charge `0`; with `PairLattice` it is integrally
  divisible (`isIntDiv_iff_charge_zero_pair`). The original `ThreeStepLinks` theorem remains
  a corollary. The remainder is not assumed divisible: the
  `L = ∅` case of the refinement property gives it.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse

variable {t : ℕ}

/-- **Shared even refiner producer** (the parity part of `RefinerProducer`): same hosts,
same scales and same reserve quantifier; one remainder `R0` and one finite library of
loopless even pieces of `X ∪ R0` with at most `m0` edges, refining `R0 ∪ L` for every
integrally divisible `L ⊆ X`, with `Δ(R0) ≤ K0 λ n`, at most `K0 ρ n²` pieces and total
library load at most `K0 λ n`. -/
def EvenRefinerProducer (F : Finset (Multiset (Fin t))) (κ0 : Type)
    (Sref0 m0 : ℕ) (K0 c0 : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) Sref0 (ω * Fintype.card V) →
    0 < lam → lam ≤ c0 * ω → 0 < rho → rho ≤ c0 * lam ^ 2 →
    1 ≤ rho * Fintype.card V → 1 ≤ c0 * lam * Fintype.card V →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
    ∃ E : PredRefiner κ0 X (IsIntDiv p F),
      E.R0 ⊆ G.edgeFinset ∧ (∀ i ∈ E.lib, (E.P i).card ≤ m0) ∧
      DegBounded E.R0 (K0 * lam * Fintype.card V) ∧
      (E.lib.card : ℝ) ≤ K0 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ i ∈ E.lib, incidentLoad (E.P i) v : ℕ) : ℝ) ≤ K0 * lam * Fintype.card V

/-- Host-independent finite sets of possible charges of edge sets with at most `k` edges. -/
noncomputable def chargeVals (F : Finset (Multiset (Fin t))) (k : ℕ) :
    Finset (TypeChargeGroup F) := by
  classical
  exact (univ : Finset (Fin t → Fin t → Fin (2 * k + 1))).image
    fun x => globalCharge F (fun i j => ((x i j : ℕ) : ℤ))

theorem pairVec_bounds {V : Type*} (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    0 ≤ pairVec p e i j ∧ pairVec p e i j ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    constructor <;> split_ifs <;> norm_num

theorem edgeVec_bounds {V : Type*} (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    0 ≤ edgeVec p E i j ∧ edgeVec p E i j ≤ 2 * E.card := by
  have h : edgeVec p E i j = ∑ e ∈ E, pairVec p e i j := by
    simp only [edgeVec, Finset.sum_apply]
  rw [h]
  constructor
  · exact sum_nonneg fun e _ => (pairVec_bounds p e i j).1
  · calc ∑ e ∈ E, pairVec p e i j ≤ ∑ _e ∈ E, (2 : ℤ) :=
          sum_le_sum fun e _ => (pairVec_bounds p e i j).2
      _ = 2 * E.card := by rw [sum_const, nsmul_eq_mul]; ring

theorem mem_chargeVals {V : Type} [DecidableEq V] (F : Finset (Multiset (Fin t)))
    (p : V → Fin t) (E : Finset (Sym2 V)) (k : ℕ) (hk : E.card ≤ k) :
    edgeVal (chargeVal F p) E ∈ chargeVals F k := by
  classical
  unfold chargeVals
  rw [mem_image]
  refine ⟨fun i j => ⟨(edgeVec p E i j).toNat, ?_⟩, mem_univ _, ?_⟩
  · have := edgeVec_bounds p E i j
    omega
  · rw [edgeVal_chargeVal]
    congr 1
    funext i j
    simp only
    exact Int.toNat_of_nonneg (edgeVec_bounds p E i j).1

/-- **Reduction theorem.** An even refiner producer gives a refiner producer with
explicit constants chosen before any host; library indices `LIdx r κ0` with
`r = (genList F m0 (2 m0)).length`. -/
theorem refinerProducer_of_evenRefinerProducer_pair (F : Finset (Multiset (Fin t)))
    (hpair : PairLattice F) (κ0 : Type) [DecidableEq κ0] (Sref0 m0 : ℕ) (K0 c0 : ℝ)
    (hc0 : 0 < c0) (heven : EvenRefinerProducer F κ0 Sref0 m0 K0 c0) :
    ∃ (Sref m : ℕ) (K c : ℝ), 0 ≤ K ∧ 0 < c ∧
      RefinerProducer F (LIdx (genList F m0 (2 * m0)).length κ0) Sref m K c := by
  classical
  set l := genList F m0 (2 * m0) with hl
  set r := l.length with hr
  set U := Fintype.card (TU (2 * m0)) with hU
  obtain ⟨m', Lc, Tc, hLc, hit⟩ := iterate_layers (chargeVals F) l (2 * m0) m0
  set K0' := max K0 0 with hK0'
  have hK0'0 : 0 ≤ K0' := le_max_right _ _
  have hK0K : K0 ≤ K0' := le_max_left _ _
  set Bc := redBig U r m0 Tc K0' with hBc
  have hBc1 : 1 ≤ Bc := (one_le_redBig U r m0 Tc hK0'0).2.2.2
  set c := min (min c0 1) (1 / (8 * Bc)) with hc
  have hcpos : 0 < c := lt_min (lt_min hc0 one_pos) (by positivity)
  have hcc0 : c ≤ c0 := (min_le_left _ _).trans (min_le_left _ _)
  have hc1 : c ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hcB : c ≤ 1 / (8 * Bc) := min_le_right _ _
  have hLc0 : (1 : ℝ) ≤ Lc := by exact_mod_cast hLc
  refine ⟨max Sref0 U, m', Lc * (K0' + 2 * r + 2), c, by positivity, hcpos, ?_⟩
  intro V _ _ p G _ ω lam rho hω hω1 hact hsup hlam hlamc hrho hrhoc hrn hcn X hXG hXdeg
  set n := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hVpos : 0 < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · rw [hn, h] at hrn; simp at hrn; linarith
    · exact h
  haveI : Nonempty V := Fintype.card_pos_iff.mp hVpos
  -- the even refiner
  have hlamc0 : lam ≤ c0 * ω := hlamc.trans (mul_le_mul_of_nonneg_right hcc0 hω.le)
  have hrhoc0 : rho ≤ c0 * lam ^ 2 := hrhoc.trans (mul_le_mul_of_nonneg_right hcc0 (sq_nonneg _))
  have hcn0 : 1 ≤ c0 * lam * n := by
    refine hcn.trans ?_
    have := mul_le_mul_of_nonneg_right hcc0 (mul_nonneg hlam.le hn0)
    linarith [show c * lam * n = c * (lam * n) by ring, show c0 * lam * n = c0 * (lam * n) by ring]
  obtain ⟨E, hEG, hEm, hEdeg, hEcard, hEload⟩ := heven V p G ω lam rho hω hω1 hact
    (hsup.mono (le_max_left _ _) le_rfl) hlam hlamc0 hrho hrhoc0 hrn hcn0 X hXG hXdeg
  -- the arithmetic
  obtain ⟨hbud, hcnt, hΔ2, hΔm⟩ := red_arith U r m0 Tc K0' c ω lam rho n hK0'0 hcpos hc1 hcB
    hω hω1 hn0 hlam hlamc hrhoc hcn
  set Δ : ℕ := ⌈lam * n⌉₊ + 2 * m0 + 1 with hΔ
  set d0 : ℝ := K0 * lam * n + 2 * rho * n with hd0
  set dB : ℝ := d0 + r * Δ with hdB
  have hd0E : DegBounded (E.R0 ∪ X) d0 := degBounded_union hEdeg hXdeg
  have hdB0 : 0 ≤ dB := by
    have h1 : (0 : ℝ) ≤ incidentLoad (E.R0 ∪ X) (Classical.arbitrary V) := Nat.cast_nonneg _
    have h2 := hd0E (Classical.arbitrary V)
    have h3 : (0 : ℝ) ≤ r * Δ := by positivity
    change (0 : ℝ) ≤ d0 + r * Δ
    have : ((filter (fun e => Classical.arbitrary V ∈ e) (E.R0 ∪ X)).card : ℝ) ≥ 0 :=
      Nat.cast_nonneg _
    linarith
  have hlib0 : (E.lib.card : ℝ) ≤ K0' * rho * n ^ 2 :=
    hEcard.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0K hrho.le)
      (sq_nonneg _))
  -- token supply for every generator
  have hsupU : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (Fintype.card (TU (2 * m0)))
      (ω * n) := hsup.mono (le_max_right _ _) le_rfl
  have hbud' : (Fintype.card (TU (2 * m0)) : ℝ) +
      Fintype.card (TU (2 * m0)) * (dB + Δ) < ω * n / 2 := by
    have hK : K0 * lam * n ≤ K0' * lam * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0K hlam.le) hn0
    have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (show dB + Δ ≤
      (K0' * lam * n + 2 * rho * n + r * (Δ : ℝ)) + Δ by
        change d0 + r * Δ + Δ ≤ _; linarith) hU0
    rw [← hU]
    linarith
  have hcnt' : 4 * ((2 * m0 : ℕ) : ℝ) * ((Tc * E.lib.card : ℕ) : ℝ) ≤
      ((Δ : ℝ) - (2 * m0 : ℕ)) * (ω * n) := by
    refine le_trans ?_ hcnt
    push_cast
    have h4 : (0 : ℝ) ≤ 4 * (2 * m0) * Tc := by positivity
    have := mul_le_mul_of_nonneg_left hlib0 h4
    linarith [show 4 * (2 * (m0 : ℝ)) * (Tc * E.lib.card) = 4 * (2 * m0) * Tc * E.lib.card by ring,
      show 4 * (2 * (m0 : ℝ)) * (Tc * (K0' * rho * n ^ 2)) =
        4 * (2 * m0) * Tc * (K0' * rho * n ^ 2) by ring]
  have hΔm' : 2 * m0 < Δ := by exact_mod_cast hΔm
  have hTok : ∀ g ∈ l, TokSupply (chargeVal F p) g ((fun _ => 2 * m0) g) G.edgeFinset
      (Tc * E.lib.card) dB Δ := by
    intro g hg
    obtain ⟨P, hP, rfl⟩ := exists_pattern_of_mem_genList hg
    exact tokSupply_of_pattern F p G (mem_patterns.mp hP) (ω * n) hsupU (Tc * E.lib.card) Δ dB
      hdB0 hΔm' hbud' hcnt'
  have hactE : ∀ i ∈ E.lib, ∀ u v, s(u, v) ∈ E.P i → ∃ c, Link F (p u) (p v) c := by
    intro i hi u v huv
    have hmem := E.subP i hi huv
    have hG : s(u, v) ∈ G.edgeFinset := by
      rcases mem_union.mp hmem with h | h
      · exact hEG h
      · exact hXG h
    exact hact u v (SimpleGraph.mem_edgeFinset.mp hG)
  have hchg : ∀ i ∈ E.lib, edgeVal (chargeVal F p) (E.P i) ∈
      AddSubgroup.closure {x | x ∈ l} := fun i hi =>
    charge_mem_closure_genList F p le_rfl (E.P i) (E.loopP i hi) (E.evenP i hi) (hactE i hi)
      (hEm i hi)
  have hdBle : d0 + l.length * Δ ≤ dB := le_rfl
  obtain ⟨E', hval', hcard', hlib', hsub, hnewG, hnewload, hload'⟩ :=
    hit V (chargeVal F p) (fun E k hk => mem_chargeVals F p E k hk) X (IsIntDiv p F)
      (IsIntDiv p F) (fun _ h => h) RefinerAssembly.empty_isIntDiv
      (fun L _ hL => charge_zero_of_isIntDiv hL) G.edgeFinset (Tc * E.lib.card) Δ dB
      (fun _ => 2 * m0) (fun _ _ => le_rfl) hTok κ0 E hchg hEm le_rfl d0 hd0E hdBle
  -- the final refiner
  have hΔ2' : (Δ : ℝ) ≤ 2 * (lam * n) := hΔ2
  have hlamn : 0 ≤ lam * n := mul_nonneg hlam.le hn0
  have hRG : E'.R0 ⊆ G.edgeFinset := by
    intro e he
    by_cases h : e ∈ E.R0
    · exact hEG h
    · exact hnewG (mem_sdiff.mpr ⟨he, h⟩)
  refine ⟨E'.lib, E'.P, E'.R0, hRG, E'.disjRX, E'.refinesReserve (fun _ _ h => h), ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hsubj : E'.P j ⊆ X ∪ E'.R0 := by rw [union_comm]; exact E'.subP j hj
    refine ⟨hsubj, ?_, hcard' j hj⟩
    have hGj : E'.P j ⊆ G.edgeFinset := fun e he => by
      rcases mem_union.mp (hsubj he) with h | h
      · exact hXG h
      · exact hRG h
    have hactj : ActiveEdges F p (E'.P j) := fun a b hab =>
      hact a b (SimpleGraph.mem_edgeFinset.mp (hGj hab))
    rw [isIntDiv_iff_charge_zero_pair p F hpair _ (E'.loopP j hj) hactj (E'.evenP j hj),
      ← edgeVal_chargeVal]
    exact hval' j hj
  · intro v
    have h1 := incidentLoad_sdiff_union_le ∅ E.R0 E'.R0 v
    simp only [sdiff_empty] at h1
    have h2 : (incidentLoad E.R0 v : ℝ) ≤ K0 * lam * n := hEdeg v
    have h3 : (incidentLoad (E'.R0 \ E.R0) v : ℝ) ≤ r * Δ := by exact_mod_cast hnewload v
    have h1' : (incidentLoad E'.R0 v : ℝ) ≤ incidentLoad (E'.R0 \ E.R0) v + incidentLoad E.R0 v := by
      exact_mod_cast h1
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have h4 : (r : ℝ) * Δ ≤ r * (2 * (lam * n)) := mul_le_mul_of_nonneg_left hΔ2' hr0
    have hK : K0 * lam * n ≤ K0' * (lam * n) := by
      have := mul_le_mul_of_nonneg_right hK0K hlamn
      linarith [show K0 * lam * n = K0 * (lam * n) by ring]
    have h5 : K0' * (lam * n) + r * (2 * (lam * n)) ≤ Lc * (K0' + 2 * r + 2) * lam * n := by
      have h6 : 0 ≤ (K0' + 2 * r + 2) * (lam * n) := by positivity
      have h7 := mul_le_mul_of_nonneg_right hLc0 h6
      have e1 : Lc * (K0' + 2 * r + 2) * lam * n = Lc * ((K0' + 2 * r + 2) * (lam * n)) := by ring
      have e2 : K0' * (lam * n) + r * (2 * (lam * n)) + 2 * (lam * n) =
          1 * ((K0' + 2 * r + 2) * (lam * n)) := by ring
      linarith only [h7, e1, e2, hlamn]
    change (incidentLoad E'.R0 v : ℝ) ≤ _
    linarith only [h1', h2, h3, h4, hK, h5]
  · have h1 : (E'.lib.card : ℝ) ≤ Lc * E.lib.card := by exact_mod_cast hlib'
    have h2 : (Lc : ℝ) * E.lib.card ≤ Lc * (K0' * rho * n ^ 2) :=
      mul_le_mul_of_nonneg_left hlib0 (by positivity)
    have h3 : (Lc : ℝ) * (K0' * rho * n ^ 2) ≤ Lc * (K0' + 2 * r + 2) * rho * n ^ 2 := by
      have h4 : 0 ≤ (Lc : ℝ) * rho * n ^ 2 := by positivity
      have h5 : (0 : ℝ) ≤ 2 * r + 2 := by positivity
      have h6 := mul_nonneg h5 h4
      have e1 : (Lc : ℝ) * (K0' + 2 * r + 2) * rho * n ^ 2 =
          Lc * (K0' * rho * n ^ 2) + (2 * r + 2) * (Lc * rho * n ^ 2) := by ring
      linarith only [h6, e1]
    linarith only [h1, h2, h3]
  · intro v
    have h1 : ((∑ j ∈ E'.lib, incidentLoad (E'.P j) v : ℕ) : ℝ) ≤
        Lc * (((∑ i ∈ E.lib, incidentLoad (E.P i) v : ℕ) : ℝ) + Δ) := by
      exact_mod_cast hload' v
    have h2 := hEload v
    have hK : K0 * lam * n ≤ K0' * (lam * n) := by
      have := mul_le_mul_of_nonneg_right hK0K hlamn
      linarith [show K0 * lam * n = K0 * (lam * n) by ring]
    have h3 : ((∑ i ∈ E.lib, incidentLoad (E.P i) v : ℕ) : ℝ) + Δ ≤ (K0' + 2 * r + 2) * (lam * n) := by
      have hr0 : (0 : ℝ) ≤ 2 * r * (lam * n) := by positivity
      have e1 : (K0' + 2 * r + 2) * (lam * n) = K0' * (lam * n) + 2 * r * (lam * n) + 2 * (lam * n) := by
        ring
      linarith only [h2, hK, hΔ2', hr0, e1]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ Lc)
    linarith only [h1, h4, show (Lc : ℝ) * ((K0' + 2 * r + 2) * (lam * n)) =
      Lc * (K0' + 2 * r + 2) * lam * n by ring]

/-- The original `ThreeStepLinks` reduction remains a corollary. -/
theorem refinerProducer_of_evenRefinerProducer (F : Finset (Multiset (Fin t)))
    (hthree : ThreeStepLinks F) (κ0 : Type) [DecidableEq κ0] (Sref0 m0 : ℕ) (K0 c0 : ℝ)
    (hc0 : 0 < c0) (heven : EvenRefinerProducer F κ0 Sref0 m0 K0 c0) :
    ∃ (Sref m : ℕ) (K c : ℝ), 0 ≤ K ∧ 0 < c ∧
      RefinerProducer F (LIdx (genList F m0 (2 * m0)).length κ0) Sref m K c :=
  refinerProducer_of_evenRefinerProducer_pair F (pairLattice_of_threeStepLinks hthree) κ0
    Sref0 m0 K0 c0 hc0 heven

/-- **Composition with the existing assembly.** For a card-three family with
`ThreeStepLinks`, an even refiner producer yields the universal-absorber target. -/
theorem producerTarget_of_evenRefinerProducer (F : Finset (Multiset (Fin 4)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (κ0 : Type) [DecidableEq κ0] (Sref0 m0 : ℕ) (K0 c0 : ℝ) (hc0 : 0 < c0)
    (heven : EvenRefinerProducer F κ0 Sref0 m0 K0 c0) :
    ∃ S : ℕ, 4 ≤ S ∧ ProducerTarget F S := by
  obtain ⟨Sref, m, K, c, hK, hc, href⟩ :=
    refinerProducer_of_evenRefinerProducer F hthree κ0 Sref0 m0 K0 c0 hc0 heven
  obtain ⟨S, hS4, -, hS⟩ := producerTarget_of_refinerProducer F hF3 hthree _ Sref m K c hK hc href
  exact ⟨S, hS4, hS⟩

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
