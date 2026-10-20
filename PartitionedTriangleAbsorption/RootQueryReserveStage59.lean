/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SparseReserveAssembly
public import PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour
public import PartitionedTriangleAbsorption.RootQueryBudgetStage59
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Physical reserves preserving bounded-root common-neighbour queries

This producer explicitly assumes the corresponding queries in the host.
Only the edge blocks within one query need to be disjoint; different queries
use the same probability space and are combined by a union bound.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQueryReserveStage59

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks

variable {V : Type*} [Fintype V] [DecidableEq V]

def starEdges (R : Finset V) (w : V) : Finset (Sym2 V) :=
  R.image (fun u => s(u, w))

omit [Fintype V] in
theorem starEdges_card (R : Finset V) (w : V) : (starEdges R w).card = R.card := by
  apply card_image_of_injective
  intro a b hab
  rcases Sym2.eq_iff.mp hab with h | h
  · exact h.1
  · exact h.1.trans h.2

omit [Fintype V] in
theorem starEdges_disjoint (R : Finset V) (w z : V)
    (hw : w ∉ R) (hwz : w ≠ z) :
    Disjoint (starEdges R w) (starEdges R z) := by
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨a, ha, rfl⟩ := mem_image.mp he
  obtain ⟨b, hb, hab⟩ := mem_image.mp he'
  rcases Sym2.eq_iff.mp hab with h | h
  · exact hwz h.2.symm
  · exact hw (h.1 ▸ hb)

def neighbours (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (i : Fin 2) : Finset V :=
  univ.filter (fun w => p w = i ∧ ∀ u ∈ R, G.Adj u w)

theorem neighbour_not_root (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (i : Fin 2) (w : V) (hw : w ∈ neighbours p G R i) : w ∉ R := by
  intro hroot
  exact G.irrefl ((mem_filter.mp hw).2.2 w hroot)

theorem blockEvent_star_iff (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (i : Fin 2) (w : V) (hw : w ∈ neighbours p G R i)
    (ω : Sym2 V → Bool) :
    ω ∈ blockEvent (fun e => {ω | ω e = true}) (starEdges R w) ↔
      ∀ u ∈ R, (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w := by
  have hadj := (mem_filter.mp hw).2.2
  simp only [blockEvent, starEdges, Set.mem_iInter, Set.mem_ofPred_eq, mem_image]
  constructor
  · intro h u hu
    exact (sampledEdges_adj G ω u w).mpr ⟨hadj u hu, h _ ⟨u, hu, rfl⟩⟩
  · intro h e he
    obtain ⟨u, hu, rfl⟩ := he
    exact ((sampledEdges_adj G ω u w).mp (h u hu)).2

theorem retained_star_count (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (i : Fin 2) (ω : Sym2 V → Bool) :
    ((neighbours p (ReserveCoverDown.reserveGraph (sampledEdges G ω)) R i).card : ℝ) =
      ∑ w : {w // w ∈ neighbours p G R i},
        (blockEvent (fun e => {ω | ω e = true}) (starEdges R w.val)).indicator
          (fun _ => (1 : ℝ)) ω := by
  classical
  change ((univ.filter (fun w => p w = i ∧ ∀ u ∈ R,
    (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w)).card : ℝ) = _
  rw [← Finset.sum_boole]
  simp_rw [Set.indicator_apply, blockEvent_star_iff p G R i _ (Subtype.property _)]
  rw [show (univ : Finset {w // w ∈ neighbours p G R i}) =
      (univ : Finset V).subtype (fun w => w ∈ neighbours p G R i) by ext; simp]
  rw [Finset.sum_subtype_eq_sum_filter (s := univ) (fun w : V =>
    if ∀ u ∈ R, (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w
    then (1 : ℝ) else 0)]
  simp only [sum_filter, neighbours, mem_filter, mem_univ, true_and]
  apply sum_congr rfl
  intro w _
  simp only [sampledEdges_adj]
  split_ifs <;> simp_all

theorem root_query_lower_tail (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Finset V) (i : Fin 2) (r : ℕ) (hR : R.card ≤ r)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hcount : β * Fintype.card V ≤ ((neighbours p G R i).card : ℝ))
    (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ) :
    μ.real {ω | ((neighbours p (ReserveCoverDown.reserveGraph (sampledEdges G ω)) R i).card
      : ℝ) ≤ β * ρ ^ r / 2 * Fintype.card V} ≤
      Real.exp (-(ρ ^ r) ^ 2 * β * Fintype.card V / 2) := by
  classical
  let W := {w // w ∈ neighbours p G R i}
  let A := fun w : W => blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true})
    (starEdges R w.val)
  have hc : β * Fintype.card V ≤ (Fintype.card W : ℝ) := by
    simpa only [W, Fintype.card_coe] using hcount
  have hpos : 0 < Fintype.card W := by
    exact_mod_cast (mul_pos hβ hn).trans_le hc
  have : Nonempty W := Fintype.card_pos_iff.mp hpos
  have hdis : Pairwise (fun a b : W => Disjoint (starEdges R a.val) (starEdges R b.val)) := by
    intro a b hab
    exact starEdges_disjoint R a.val b.val
      (neighbour_not_root p G R i a.val a.property) (fun h => hab (Subtype.ext h))
  have hblocks : iIndepSet A μ := independent_blocks _ μ
    (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) hind _ hdis
  have hreal : ∀ w : W, μ.real (A w) = ρ ^ R.card := by
    intro w
    rw [measureReal_def, block_probability _ μ hind _ hmarg, starEdges_card,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le]
  have hb := FiniteBernoulliTail.lower_half_mean μ A
    (fun w => blockEvent_measurable _
      (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) _) hblocks
    (ρ ^ R.card) (pow_nonneg hρ.le _) hreal
  have hp := pow_le_pow_of_le_one hρ.le hρ1 hR
  have hmean := mul_le_mul hp hc (mul_pos hβ hn).le (pow_nonneg hρ.le _)
  have hsub : {ω | ((neighbours p
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)) R i).card : ℝ) ≤
      β * ρ ^ r / 2 * Fintype.card V} ⊆
      {ω | (∑ w : W, (A w).indicator (fun _ => (1 : ℝ)) ω) ≤
      ρ ^ R.card * Fintype.card W / 2} := by
    intro ω hω
    change _ ≤ _ at hω ⊢
    rw [retained_star_count] at hω
    nlinarith
  refine (measureReal_mono hsub).trans (hb.trans (Real.exp_le_exp.mpr ?_))
  have hs : (ρ ^ r) ^ 2 ≤ (ρ ^ R.card) ^ 2 := by
    nlinarith [pow_nonneg hρ.le r, pow_nonneg hρ.le R.card]
  have hm := mul_le_mul hs hc (mul_pos hβ hn).le (sq_nonneg (ρ ^ R.card))
  nlinarith

def Query (r : ℕ) := {R : Finset V // R.card ≤ r} × Fin 2

noncomputable instance queryFintype (r : ℕ) : Fintype (Query (V := V) r) := by
  classical
  unfold Query
  infer_instance

omit [DecidableEq V] in
theorem query_card_le (r : ℕ) :
    Fintype.card (Query (V := V) r) ≤ 2 * (r + 1) * (Fintype.card V + 1) ^ r := by
  classical
  let B := (range (r + 1)).biUnion (fun m => powersetCard m (univ : Finset V))
  have hsub : (univ.filter (fun R : Finset V => R.card ≤ r)) ⊆ B := by
    intro R hR
    have hcard := (mem_filter.mp hR).2
    exact mem_biUnion.mpr ⟨R.card, mem_range.mpr (by omega), mem_powersetCard.mpr
      ⟨subset_univ R, rfl⟩⟩
  have hb := (card_le_card hsub).trans (card_biUnion_le
    (s := range (r + 1)) (t := fun m => powersetCard m (univ : Finset V)))
  have hs : ∑ m ∈ range (r + 1), (powersetCard m (univ : Finset V)).card ≤
      (r + 1) * (Fintype.card V + 1) ^ r := by
    calc
      _ ≤ ∑ _m ∈ range (r + 1), (Fintype.card V + 1) ^ r := by
        apply sum_le_sum
        intro m hm
        rw [card_powersetCard, card_univ]
        exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
          (Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _))
            (by have := mem_range.mp hm; omega)))
      _ = _ := by simp
  have hf : Fintype.card {R : Finset V // R.card ≤ r} ≤
      (r + 1) * (Fintype.card V + 1) ^ r := by
    simpa only [Fintype.card_subtype] using hb.trans hs
  simpa only [Query, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_right 2 hf

/-- The exact query count is used, so no hidden independence or asymptotic
threshold assumption is needed. Empty-root queries are included. -/
theorem exists_root_rich_reserve_of_budget (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ)) (hG : F0Geometric.CommonNbrRich r p G β)
    (hbudget : (Fintype.card V : ℝ) * Real.exp (-2 * ρ ^ 2 * Fintype.card V) +
      Fintype.card (Query (V := V) r) *
        Real.exp (-(ρ ^ r) ^ 2 * β * Fintype.card V / 2) < 1) :
    ∃ X : Finset (Sym2 V), X ⊆ G.edgeFinset ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      F0Geometric.CommonNbrRich r p (ReserveCoverDown.reserveGraph X) (β * ρ ^ r / 2) := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Sym2 V) ρ hρ.le hρ1
  let : IsProbabilityMeasure μ := hμ
  let bad : V ⊕ Query (V := V) r → Set (Sym2 V → Bool)
    | Sum.inl v => {ω | 2 * ρ * Fintype.card V ≤
        (((sampledEdges G ω).filter (fun e => v ∈ e)).card : ℝ)}
    | Sum.inr q => {ω | ((neighbours p
        (ReserveCoverDown.reserveGraph (sampledEdges G ω)) q.1.val q.2).card : ℝ) ≤
        β * ρ ^ r / 2 * Fintype.card V}
  let bound : V ⊕ Query (V := V) r → ℝ
    | Sum.inl _ => Real.exp (-2 * ρ ^ 2 * Fintype.card V)
    | Sum.inr _ => Real.exp (-(ρ ^ r) ^ 2 * β * Fintype.card V / 2)
  have htail : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    cases i with
    | inl v =>
      simpa only [bad, bound, neg_mul] using
        PhysicalStarTail.sampled_star_degree_tail μ hind ρ hρ hmarg G v
    | inr q =>
      exact root_query_lower_tail p G q.1.val q.2 r q.1.property β ρ hβ hρ hρ1 hn
        (hG q.1.val q.1.property q.2) μ hind hmarg
  have hsum : ∑ i, bound i < 1 := by
    simpa only [Fintype.sum_sum_type, bound, sum_const, card_univ, nsmul_eq_mul] using hbudget
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ bad bound htail hsum
  refine ⟨sampledEdges G ω, sampledEdges_subset G ω, ?_, ?_⟩
  · intro v
    exact (not_le.mp (hω (Sum.inl v))).le
  · intro R hR i
    exact (not_le.mp (hω (Sum.inr (⟨R, hR⟩, i)))).le

/-- A concrete four-root producer. The geometric input remains explicit. -/
theorem exists_four_root_rich_reserve (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 1 ≤ (Fintype.card V : ℝ)) (hG : F0Geometric.CommonNbrRich 4 p G β)
    (hsize : 1228800 ≤ β ^ 5 * ρ ^ 40 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V) :
    ∃ X : Finset (Sym2 V), X ⊆ G.edgeFinset ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      F0Geometric.CommonNbrRich 4 p (ReserveCoverDown.reserveGraph X) (β * ρ ^ 4 / 2) := by
  apply exists_root_rich_reserve_of_budget p G 4 β ρ hβ hρ hρ1 (by linarith) hG
  have hc : (Fintype.card (Query (V := V) 4) : ℝ) ≤
      10 * ((Fintype.card V : ℝ) + 1) ^ 4 := by
    have h := query_card_le (V := V) 4
    norm_num at h
    exact_mod_cast h
  have hb := RootQueryBudgetStage59.explicit_four_root_budget
    (Fintype.card V) β ρ hn hβ.le hsize hdegrees
  have hmult := mul_le_mul_of_nonneg_right hc
    (Real.exp_pos (-(ρ ^ 4) ^ 2 * β * Fintype.card V / 2)).le
  linarith

universe u

/-- The order threshold is quantified before the vertex type and the host. -/
theorem exists_four_root_rich_reserve_uniform (β ρ : ℝ)
    (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (p : W → Fin 2)
      (G : SimpleGraph W) [DecidableRel G.Adj], N ≤ Fintype.card W →
      F0Geometric.CommonNbrRich 4 p G β →
      ∃ X : Finset (Sym2 W), X ⊆ G.edgeFinset ∧
        DegBounded X (2 * ρ * Fintype.card W) ∧
        F0Geometric.CommonNbrRich 4 p (ReserveCoverDown.reserveGraph X) (β * ρ ^ 4 / 2) := by
  obtain ⟨N, hN⟩ := RootQueryBudgetStage59.exists_uniform_threshold β ρ hβ hρ
  refine ⟨N, ?_⟩
  intro W _ _ p G _ hn hG
  obtain ⟨h1, hsize, hdeg⟩ := hN (Fintype.card W) hn
  exact exists_four_root_rich_reserve p G β ρ hβ hρ hρ1 h1 hG hsize hdeg

end PartitionedTriangleAbsorption.RootQueryReserveStage59
