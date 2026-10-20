/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage15

/-! # Transporting physical reserve queries to the typed graph interface

One query is a pair of distinct roots and the third part of an allowed type.
The cherry events and the graph cardinality below describe the same outcome.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SparseReserveAssembly

open Finset BernoulliBlocks AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def Query (p : V → Fin t) (F : Finset (Multiset (Fin t))) :=
  {q : V × V × Fin t // q.1 ≠ q.2.1 ∧
    ({p q.1, p q.2.1, q.2.2} : Multiset (Fin t)) ∈ F}

noncomputable instance queryFintype (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    Fintype (Query p F) := by
  classical
  unfold Query
  infer_instance

theorem query_card_le (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    Fintype.card (Query p F) ≤ Fintype.card V ^ 2 * t := by
  classical
  have h := Fintype.card_subtype_le (fun q : V × V × Fin t =>
    q.1 ≠ q.2.1 ∧ ({p q.1, p q.2.1, q.2.2} : Multiset (Fin t)) ∈ F)
  simpa only [Query, Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_assoc] using h

theorem retained_cherry_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin t) (u v : V) (k : Fin t) (ω : Sym2 V → Bool) :
    let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
    let A := fun w : W => blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true})
      (pathEdges u v w.val)
    ((univ.filter (fun w =>
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w ∧
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w v ∧ p w = k)).card : ℝ) =
      ∑ w : W, (A w).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  dsimp only
  rw [← Finset.sum_boole]
  have heq : ∀ w : {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k},
      (blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true})
        (pathEdges u v w.val)).indicator (fun _ => (1 : ℝ)) ω =
      if (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w.val ∧
        (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w.val v
      then 1 else 0 := by
    intro w
    simp only [Set.indicator_apply,
      blockEvent_path_iff G u v w.val w.property.1 w.property.2.1]
  simp_rw [heq]
  rw [show (univ : Finset {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}) =
      (univ : Finset V).subtype (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k) by ext; simp]
  rw [Finset.sum_subtype_eq_sum_filter (s := univ) (fun w : V =>
    if (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w ∧
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w v then (1 : ℝ) else 0)]
  rw [sum_filter]
  apply sum_congr rfl
  intro w _
  simp only [sampledEdges_adj]
  split_ifs <;> simp_all

open MeasureTheory ProbabilityTheory

theorem query_lower_tail (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ)
    (hn : 0 < (Fintype.card V : ℝ)) (hG : AntiEdgeful p F G α)
    (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ)
    (q : Query p F) :
    μ.real {ω | ((univ.filter (fun w =>
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj q.val.1 w ∧
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w q.val.2.1 ∧
      p w = q.val.2.2)).card : ℝ) ≤ α * ρ ^ 2 / 2 * Fintype.card V} ≤
      Real.exp (-ρ ^ 4 * α * Fintype.card V / 2) := by
  classical
  let W := {w : V // G.Adj q.val.1 w ∧ G.Adj w q.val.2.1 ∧ p w = q.val.2.2}
  have hc : α * Fintype.card V ≤ (Fintype.card W : ℝ) := by
    simpa only [W, Fintype.card_subtype] using
      hG _ q.property.2 _ _ _ rfl _ _ q.property.1 rfl rfl
  have hpos : 0 < Fintype.card W := by
    have : 0 < (Fintype.card W : ℝ) := (mul_pos hα hn).trans_le hc
    exact_mod_cast this
  have hne : Nonempty W := Fintype.card_pos_iff.mp hpos
  have hb := PhysicalReserveTails.commonNeighbour_lower_tail μ hind ρ hρ.le hmarg
    G p q.val.1 q.val.2.1 q.property.1 q.val.2.2 hne
  dsimp only at hb
  simp_rw [← retained_cherry_count] at hb
  have hsub : {ω | ((univ.filter (fun w =>
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj q.val.1 w ∧
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w q.val.2.1 ∧
      p w = q.val.2.2)).card : ℝ) ≤ α * ρ ^ 2 / 2 * Fintype.card V} ⊆
      {ω | ((univ.filter (fun w =>
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj q.val.1 w ∧
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w q.val.2.1 ∧
      p w = q.val.2.2)).card : ℝ) ≤ ρ ^ 2 * Fintype.card W / 2} := by
    intro ω hω
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg ρ)
    change _ ≤ _ at hω ⊢
    nlinarith
  refine (measureReal_mono hsub).trans (hb.trans (Real.exp_le_exp.mpr ?_))
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ ρ ^ 4 by positivity)
  nlinarith

/-- An actual common reserve; the hypothesis is an explicit numerical failure
budget, not an assumed good outcome or an independence claim about queries. -/
theorem exists_sparse_reserve_of_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ)) (hG : AntiEdgeful p F G α)
    (hbudget : (Fintype.card V : ℝ) * Real.exp (-2 * ρ ^ 2 * Fintype.card V) +
      (Fintype.card V : ℝ) ^ 2 * t * Real.exp (-ρ ^ 4 * α * Fintype.card V / 2) < 1) :
    ∃ X : Finset (Sym2 V), X ⊆ G.edgeFinset ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      AntiEdgeful p F (ReserveCoverDown.reserveGraph X) (α * ρ ^ 2 / 2) := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Sym2 V) ρ hρ.le hρ1
  let : IsProbabilityMeasure μ := hμ
  let bad : V ⊕ Query p F → Set (Sym2 V → Bool)
    | Sum.inl v => {ω | 2 * ρ * Fintype.card V ≤
        (((sampledEdges G ω).filter (fun e => v ∈ e)).card : ℝ)}
    | Sum.inr q => {ω | ((univ.filter (fun w =>
        (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj q.val.1 w ∧
        (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w q.val.2.1 ∧
        p w = q.val.2.2)).card : ℝ) ≤ α * ρ ^ 2 / 2 * Fintype.card V}
  let bound : V ⊕ Query p F → ℝ
    | Sum.inl _ => Real.exp (-2 * ρ ^ 2 * Fintype.card V)
    | Sum.inr _ => Real.exp (-ρ ^ 4 * α * Fintype.card V / 2)
  have htail : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    cases i with
    | inl v =>
      simpa only [bad, bound, neg_mul] using
        PhysicalStarTail.sampled_star_degree_tail μ hind ρ hρ hmarg G v
    | inr q => exact query_lower_tail G p F α ρ hα hρ hn hG μ hind hmarg q
  have hcount : (Fintype.card (Query p F) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * t := by
    exact_mod_cast query_card_le p F
  have hsum : ∑ i, bound i < 1 := by
    rw [Fintype.sum_sum_type]
    simp only [bound, sum_const, card_univ, nsmul_eq_mul]
    exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcount
      (Real.exp_pos _).le)).trans_lt hbudget
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ bad bound htail hsum
  refine ⟨sampledEdges G ω, sampledEdges_subset G ω, ?_, ?_⟩
  · intro v
    exact (not_le.mp (hω (Sum.inl v))).le
  · intro τ hτ i j k hτeq u v huv hu hv
    let q : Query p F := ⟨(u, v, k), huv, by simpa only [hu, hv, hτeq] using hτ⟩
    exact (not_le.mp (hω (Sum.inr q))).le

/-- Concrete sufficient size conditions. The coarse query count is `t*n²`,
not the sharper `6*|F|*n²`; no enumeration of type orderings is assumed. -/
theorem exists_sparse_reserve (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ)) (hG : AntiEdgeful p F G α)
    (hsize : 96 * (t : ℝ) ≤ α ^ 3 * ρ ^ 12 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V) :
    ∃ X : Finset (Sym2 V), X ⊆ G.edgeFinset ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      AntiEdgeful p F (ReserveCoverDown.reserveGraph X) (α * ρ ^ 2 / 2) := by
  apply exists_sparse_reserve_of_budget G p F α ρ hα hρ hρ1 hn hG
  have hb := SparseReserveTailBudget.explicit_threshold (Fintype.card V) α ρ
    ((t : ℝ) / 6) hn hα.le (by nlinarith [hsize]) hdegrees
  have he : -(α * ρ ^ 4 / 2 * Fintype.card V) =
      -ρ ^ 4 * α * Fintype.card V / 2 := by ring
  rw [he] at hb
  simp only [neg_mul] at hb
  have hc : (Fintype.card V : ℝ) * Real.exp (-2 * ρ ^ 2 * Fintype.card V) +
      (Fintype.card V : ℝ) ^ 2 * t * Real.exp (-ρ ^ 4 * α * Fintype.card V / 2) ≤ 3 / 4 := by
    convert hb using 1
    ring_nf
  exact hc.trans_lt (by norm_num)

end PartitionedTriangleAbsorption.SparseReserveAssembly
