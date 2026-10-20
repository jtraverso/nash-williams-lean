/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SparseReserveGeometry
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-! # Grouping actual independent physical-edge trials

A block is retained when every edge in it is retained. Pairwise disjoint
blocks inherit mutual event independence, not merely pairwise independence.
This supplies the probabilistic independence prerequisite for L2; the
concentration and simultaneous reserve-existence theorem are separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BernoulliBlocks

open Finset MeasureTheory ProbabilityTheory

variable {E I Ω : Type*} [MeasurableSpace Ω]

def blockEvent (A : E → Set Ω) (B : Finset E) : Set Ω := ⋂ e ∈ B, A e

theorem blockEvent_measurable (A : E → Set Ω) (hA : ∀ e, MeasurableSet (A e))
    (B : Finset E) : MeasurableSet (blockEvent A B) := by
  exact Finset.measurableSet_biInter B fun e _ => hA e

omit [MeasurableSpace Ω] in
theorem blockEvent_biUnion [DecidableEq E] (A : E → Set Ω) (B : I → Finset E) (s : Finset I) :
    blockEvent A (s.biUnion B) = ⋂ i ∈ s, blockEvent A (B i) := by
  ext ω
  simp only [blockEvent, Set.mem_iInter, mem_biUnion]
  aesop

/-- A mutually independent physical-edge family remains mutually independent
when grouped into disjoint blocks of arbitrary finite sizes. -/
theorem independent_blocks (A : E → Set Ω) (μ : Measure Ω)
    (hA : ∀ e, MeasurableSet (A e)) (hind : iIndepSet A μ)
    (B : I → Finset E) (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    iIndepSet (fun i => blockEvent A (B i)) μ := by
  classical
  apply (iIndepSet_iff_meas_biInter (fun i => blockEvent_measurable A hA (B i))).mpr
  intro s
  rw [← blockEvent_biUnion]
  change μ (⋂ e ∈ s.biUnion B, A e) = _
  rw [hind.meas_biInter]
  rw [prod_biUnion (fun i _ j _ hij => hB hij)]
  apply prod_congr rfl
  intro i _
  exact (hind.meas_biInter (B i)).symm

/-- Equal marginal edge probabilities give the exact block probability. -/
theorem block_probability (A : E → Set Ω) (μ : Measure Ω) (hind : iIndepSet A μ)
    (prob : ENNReal) (hprob : ∀ e, μ (A e) = prob) (B : Finset E) :
    μ (blockEvent A B) = prob ^ B.card := by
  classical
  change μ (⋂ e ∈ B, A e) = _
  rw [hind.meas_biInter]
  simp [hprob]

/-- Construction, rather than an assumed independent-trial interface. The
coordinates may be all unordered pairs; only actual graph edges will be used. -/
theorem exists_edge_trials [Finite E] (prob : ℝ) (hp0 : 0 ≤ prob) (hp1 : prob ≤ 1) :
    ∃ μ : Measure (E → Bool), IsProbabilityMeasure μ ∧
      iIndepSet (fun e => {ω | ω e = true}) μ ∧
      ∀ e, μ {ω | ω e = true} = ENNReal.ofReal prob := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  let q : unitInterval := ⟨prob, hp0, hp1⟩
  let ν : Measure Bool := bernoulliMeasure true false q
  let μ : Measure (E → Bool) := Measure.pi (fun _ => ν)
  have hμ : IsProbabilityMeasure μ := Measure.pi.instIsProbabilityMeasure (fun _ : E => ν)
  have hfun : iIndepFun (fun e (ω : E → Bool) => ω e) μ := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : E => ν) (X := fun _ => id)
        (fun _ => measurable_id.aemeasurable))
  have hpred : iIndepFun (fun e (ω : E → Bool) => ω e = true) μ := by
    exact hfun.comp (fun _ b => b = true) (fun _ => Measurable.of_discrete)
  have hind : iIndepSet (fun e => {ω : E → Bool | ω e = true}) μ := by
    rw [← iIndep_comap_mem_iff]
    apply (iIndepFun_iff_iIndep _ _ _).1
    exact hpred
  refine ⟨μ, hμ, hind, ?_⟩
  intro e
  change Measure.pi (fun _ : E => ν) (Function.eval e ⁻¹' ({true} : Set Bool)) = _
  rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true)]
  rw [Measure.pi_map_eval]
  have hν : ν Set.univ = 1 := measure_univ
  rw [show ∏ j ∈ Finset.univ.erase e, ν Set.univ = 1 by
    exact Finset.prod_eq_one (fun _ _ => hν)]
  rw [one_smul]
  change bernoulliMeasure true false q {true} = ENNReal.ofReal prob
  rw [bernoulliMeasure_apply q (measurableSet_singleton true)]
  simpa [q] using ENNReal.coe_nnreal_eq (unitInterval.toNNReal q)

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- Coordinates not belonging to the graph never create a reserve edge. -/
def sampledEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) : Finset (Sym2 V) := G.edgeFinset.filter (fun e => ω e = true)

omit [DecidableEq V] in
theorem sampledEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) : sampledEdges G ω ⊆ G.edgeFinset := filter_subset _ _

omit [DecidableEq V] in
theorem sampledEdges_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (u v : V) :
    (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u v ↔
      G.Adj u v ∧ ω s(u, v) = true := by
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [sampledEdges, mem_coe, mem_filter, SimpleGraph.mem_edgeFinset]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, h.1.ne⟩

/-- The abstract block event is exactly the two retained physical legs, not a
triangle event and not an independent trial added by assumption. -/
theorem blockEvent_path_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) (huw : G.Adj u w) (hwv : G.Adj w v) (ω : Sym2 V → Bool) :
    ω ∈ blockEvent (fun e => {ω | ω e = true}) (AntiEdgeSelection.pathEdges u v w) ↔
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj u w ∧
      (ReserveCoverDown.reserveGraph (sampledEdges G ω)).Adj w v := by
  rw [sampledEdges_adj, sampledEdges_adj]
  simp [blockEvent, AntiEdgeSelection.pathEdges, huw, hwv,
    Sym2.eq_swap (a := w) (b := v)]

omit [Fintype V] in
/-- The exact mutually independent Bernoulli(`prob²`) events for a fixed typed
root query, derived from sampling the physical graph-edge coordinates. -/
theorem commonNeighbour_trials [Finite V] (G : SimpleGraph V)
    (p : V → Fin t) (u v : V) (huv : u ≠ v) (k : Fin t)
    (prob : ℝ) (hp0 : 0 ≤ prob) (hp1 : prob ≤ 1) :
    ∃ μ : Measure (Sym2 V → Bool), IsProbabilityMeasure μ ∧
      let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
      let A := fun w : W => blockEvent (fun e => {ω | ω e = true})
        (AntiEdgeSelection.pathEdges u v w.val)
      iIndepSet A μ ∧ ∀ w, μ (A w) = (ENNReal.ofReal prob) ^ 2 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Sym2 V) prob hp0 hp1
  refine ⟨μ, hμ, ?_⟩
  let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
  have hdis : Pairwise (fun a b : W => Disjoint
      (AntiEdgeSelection.pathEdges u v a.val) (AntiEdgeSelection.pathEdges u v b.val)) := by
    intro a b hab
    exact SparseReserveGeometry.pathEdges_disjoint u v a.val b.val
      (fun h => hab (Subtype.ext h)) a.property.1.ne.symm a.property.2.1.ne
  constructor
  · exact independent_blocks _ μ
      (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) hind _ hdis
  · intro w
    rw [block_probability _ μ hind _ hmarg,
      AntiEdgeSelection.pathEdges_card u v w.val huv]

end PartitionedTriangleAbsorption.BernoulliBlocks
