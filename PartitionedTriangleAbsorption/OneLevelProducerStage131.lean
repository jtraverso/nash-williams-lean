/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AmbientChildStage131
public import PartitionedTriangleAbsorption.BalancedReserveStage126
public import PartitionedTriangleAbsorption.ProtectedCoreStage125

/-! # Stage131: one physical level, produced without oracles

This file chains three constructions on the *same* objects:

1. Stage126 (`exists_produced_balanced_reserve`): a physical reserve `T` of
   pairwise edge-disjoint rainbow triangles with roots in `X` and bases in the
   zone `W`, balanced category counts and rich self-excluding queries;
2. Stage131 (`inner_child_balance`, `inner_load_le_card`): the balance and
   degree inputs of the induced child `J = E(G)[W]`, from class sizes and the
   forbidden load only;
3. Stage127 (`exists_geometric_recut`, `query_supply_after_recut`): a sparse
   recut `Y ⊆ J \ R` making `(R ∪ J) \ Y` exactly balanced, and survival of
   every query against every later packing avoiding `J \ Y`.

All premises of `one_level_producer` are geometric or numerical facts about
the input graph and the chosen parameters. No packing, seed, balance bound,
recut, query supply or decomposition is assumed. What this file does **not**
provide: the iteration of levels, confinement of the final leftover in a
bounded core, the fractional repair on the actual host, and the public form
of Theorem 13.16 (see `STAGE129_STATUS.md`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.OneLevelProducerStage131

open Finset AntiEdgeSelection CoverDownStage105 TypedApplicationLinks
open ReserveQueryGeometryStage123 F3ReserveTrimStage109 SeedDrivenTrimStage114
open AmbientChildStage131

variable {V : Type*} [DecidableEq V]

/-- The natural-division quota of Stage114 is bounded by its real value. -/
theorem quota_le_real (m D P : ℕ) (hP : m < P) :
    (quota m D P : ℝ) ≤ 2 * m * D / ((P : ℝ) - m) + 1 := by
  unfold quota
  push_cast
  have hsub : ((P - m : ℕ) : ℝ) = (P : ℝ) - m := by
    rw [Nat.cast_sub hP.le]
  have h := Nat.cast_div_le (α := ℝ) (m := 2 * m * D) (n := P - m)
  rw [hsub] at h
  push_cast at h
  linarith

/-- **Ambient recut.** Stage127's recut with its balance input `β` and its
degree input `D` discharged: `β = η|U|² + |U|f` and `D = |U|`. -/
theorem exists_ambient_recut [Finite V] (p : V → Fin 4) (E F : Finset (Sym2 V))
    (U : Finset V) [DecidablePred (IsInner U)] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hdec : HasDecomp p F3 (resEdges T))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (s b f m P S : ℕ) (z t eta : ℝ)
    (hsize : ∀ i, s ≤ (U.filter fun v => p v = i).card)
    (hroom : ∀ i, b + f ≤ (U.filter fun v => p v = i).card)
    (hF : ∀ v, incidentLoad F v ≤ f)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (hc : ∀ i, |((T.filter fun r => category p s(r.2.1, r.2.2) = i).card : ℝ) - z| ≤ t)
    (hS : 0 < S) (heta : eta ≤ 1 / 2)
    (hclass : ∀ i, (1 - eta) * S ≤ ((U.filter fun v => p v = i).card : ℝ) ∧
      ((U.filter fun v => p v = i).card : ℝ) ≤ S)
    (hcapacity : (P : ℝ) + z + t ≤ s * b)
    (hm : 2 * ((eta * (U.card : ℝ) ^ 2 + U.card * f) + 2 * t) ≤ (m : ℝ)) (hP : m < P) :
    ∃ Y ⊆ (E.filter (IsInner U)) \ resEdges T, Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m U.card P) ∧
      ∀ k : Fin 2, bal p k ((resEdges T ∪ E.filter (IsInner U)) \ Y) = 0 :=
  GeometricRecutStage127.exists_geometric_recut p E F U T hd hT hdec hcross s b f m U.card P
    z t (eta * (U.card : ℝ) ^ 2 + U.card * f) hsize hroom hF hE hc
    (inner_child_balance p U E F hcross hE f S hF hS eta heta hclass)
    hcapacity hm hP (inner_load_le_card U E)

/-- The candidates of one query in a reserve `T`, exactly as counted by the
Stage126 producer: rooted at `x`, both connectors present in `G`, outside the
forbidden and blocked sets, and disjoint from the whole reserve. -/
def queryCands (G : SimpleGraph V) [DecidableRel G.Adj] (F B : Finset (Sym2 V))
    (T : Finset (V × V × V)) (x y z : V) : Finset (V × V × V) :=
  T.filter fun r => r.1 = x ∧ G.Adj y r.2.1 ∧ G.Adj r.2.2 z ∧
    s(y, r.2.1) ∉ F ∪ B ∧ s(r.2.2, z) ∉ F ∪ B ∧ Disjoint (connectors y z r) (resEdges T)

/-- **One physical level, produced.** From geometric and numerical premises
on the actual graph `G`, construct simultaneously

* a physical reserve `T` (edge-disjoint rainbow triangles of `G`, avoiding
  `B`, with roots in `X` outside the zone `W` and bases inside it), which is
  F3-decomposable and has bounded load;
* a sparse recut `Y` of the induced child `J = E(G)[W]` avoiding the reserve,
  such that `(R ∪ J) \ Y` is exactly balanced for both F3 functionals;
* for every later packing `Pk` that avoids `J \ Y` (an arbitrary packing is
  *not* allowed) and every query `j`, more than `target` candidates whose
  connectors survive `Pk`.

Every premise is a fact about `G`, `F`, `B`, the class sizes of `W`, or the
numerical parameters. -/
theorem one_level_producer {Q : Type*} [Fintype Q] [Fintype V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGcross : ∀ u v, G.Adj u v → p u ≠ p v)
    (X W : Finset V) [DecidablePred (IsInner W)] (F B : Finset (Sym2 V))
    (f d L q b a : ℕ)
    (hF : ∀ v, incidentLoad F v ≤ f) (hB : ∀ v, incidentLoad B v ≤ d)
    (hG : ∀ u v, p u ≠ p v → s(u, v) ∉ F → G.Adj u v)
    (hpart : ∀ c, b + 2 * f ≤ (W.filter fun w => p w = c).card)
    (hXW : Disjoint X W)
    (hquota : 2 * (3 * X.card * L) + 2 * (d + 2 * (3 * L + q)) * q < b * q)
    (x y z : Q → V) (hx : ∀ j, x j ∈ X) (hy : ∀ j, y j ≠ x j) (hz : ∀ j, z j ≠ x j)
    (hyW : ∀ j, y j ∈ W) (hzW : ∀ j, z j ∈ W)
    (ha : 0 < a) (hsupply : a + 2 * (f + d) + 2 ≤ L)
    (t : ℝ) (ht : 0 ≤ t) (hM : 0 < X.card * L)
    (hprob : (Fintype.card Q : ℝ) * Real.exp (-(a : ℝ) / 1536) +
      6 * Real.exp (-2 * t ^ 2 / (X.card * L)) < 1)
    (S : ℕ) (hS : 0 < S) (eta : ℝ) (heta : eta ≤ 1 / 2)
    (hclass : ∀ i, (1 - eta) * S ≤ ((W.filter fun v => p v = i).card : ℝ) ∧
      ((W.filter fun v => p v = i).card : ℝ) ≤ S)
    (s cap m P : ℕ) (hsize : ∀ i, s ≤ (W.filter fun v => p v = i).card)
    (hroom : ∀ i, cap + f ≤ (W.filter fun v => p v = i).card)
    (hcapacity : (P : ℝ) + ((X.card * L : ℕ) : ℝ) / 2 + t ≤ s * cap)
    (hm : 2 * ((eta * (W.card : ℝ) ^ 2 + W.card * f) + 2 * t) ≤ (m : ℝ)) (hP : m < P)
    (target : ℝ) (hbudget : target + 6 * (quota m W.card P : ℝ) ≤ (a : ℝ) / 192) :
    ∃ T : Finset (V × V × V), ∃ Y : Finset (Sym2 V),
      (T : Set (V × V × V)).PairwiseDisjoint resTri ∧
      (∀ r ∈ T, r.1 ∈ X ∧ r.1 ∉ W ∧ r.2.1 ∈ W ∧ r.2.2 ∈ W ∧
        resTri r ⊆ G.edgeFinset ∧ Disjoint (resTri r) B) ∧
      HasDecomp p F3 (resEdges T) ∧
      (∀ v, incidentLoad (resEdges T) v ≤ 2 * (3 * L + q)) ∧
      Y ⊆ G.edgeFinset.filter (IsInner W) \ resEdges T ∧ Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m W.card P) ∧
      (∀ k : Fin 2, bal p k ((resEdges T ∪ G.edgeFinset.filter (IsInner W)) \ Y) = 0) ∧
      ∀ Pk : Finset (Sym2 V), Disjoint Pk (G.edgeFinset.filter (IsInner W) \ Y) →
        ∀ j, target < (((queryCands G F B T (x j) (y j) (z j)).filter
          fun r => Disjoint (connectors (y j) (z j) r) Pk).card : ℝ) := by
  obtain ⟨T, hd, hphys, hload, hc, hrich⟩ :=
    RootQuotaPackingStage124.exists_produced_balanced_reserve p G X W F B f d L q b a
      hF hB hG hpart hXW hquota x y z hx hy hz ha hsupply t ht hM hprob
  have hcrossE : ∀ u v, s(u, v) ∈ G.edgeFinset → p u ≠ p v :=
    fun u v h => hGcross u v (SimpleGraph.mem_edgeFinset.mp h)
  have htri : ∀ r ∈ T, resTri r ⊆ G.edgeFinset := by
    intro r hr e he
    obtain ⟨-, -, -, -, h1, h2, h3, -⟩ := hphys r hr
    simp only [resTri, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> exact SimpleGraph.mem_edgeFinset.mpr ‹_›
  have hdec := LateReserveStage125.reserve_decomp p G.edgeFinset hcrossE T hd htri
  have hE : ∀ u ∈ W, ∀ v ∈ W, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ G.edgeFinset :=
    fun u _ v _ h hFuv => SimpleGraph.mem_edgeFinset.mpr (hG u v h hFuv)
  obtain ⟨Y, hYsub, hYcard, hYdeg, hYbal⟩ :=
    exists_ambient_recut p G.edgeFinset F W T hd
      (fun r hr => ⟨(hphys r hr).2.1, (hphys r hr).2.2.1, (hphys r hr).2.2.2.1, htri r hr⟩)
      hdec hcrossE s cap f m P S (((X.card * L : ℕ) : ℝ) / 2) t eta hsize hroom hF hE hc
      hS heta hclass hcapacity hm hP
  refine ⟨T, Y, hd, ?_, hdec, hload, hYsub, hYcard, hYdeg, hYbal, ?_⟩
  · intro r hr
    obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, h11⟩ := hphys r hr
    exact ⟨h1, h2, h3, h4, htri r hr, h11⟩
  · intro Pk hPk j
    refine GeometricRecutStage127.query_supply_after_recut
      (queryCands G F B T (x j) (y j) (z j))
      (hd.subset (coe_subset.mpr (filter_subset _ _))) (x j) (y j) (z j)
      (fun r hr => (mem_filter.mp hr).2.1) (G.edgeFinset.filter (IsInner W)) Y Pk
      (quota m W.card P) a target ?_ hPk hYdeg (hrich j) hbudget
    intro r hr e he
    obtain ⟨hrT, -, hAy, hAz, -⟩ := mem_filter.mp hr
    have hr1 := (hphys r hrT).2.2.1
    have hr2 := (hphys r hrT).2.2.2.1
    simp only [connectors, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · refine mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hAy, ?_⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hyW j
      · exact hr1
    · refine mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hAz, ?_⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hr2
      · exact hzW j

/-- **Deleted-edge ledger for the next level.** Every edge removed by a level
(the reserve `R` and the recut `Y`) is moved into the forbidden set. The
next host `G \ (R ∪ Y)` then satisfies the same "every allowed cross pair is
an edge" premise with forbidden set `F ∪ R ∪ Y`, whose load is at most
`f + r + y`. This is bookkeeping only; it does not perform the cover-down. -/
theorem next_level_ledger (p : V → Fin 4) (G : SimpleGraph V) (F R Y : Finset (Sym2 V))
    (f r y : ℕ) (hF : ∀ v, incidentLoad F v ≤ f) (hR : ∀ v, incidentLoad R v ≤ r)
    (hY : ∀ v, incidentLoad Y v ≤ y)
    (hG : ∀ u v, p u ≠ p v → s(u, v) ∉ F → G.Adj u v) :
    (∀ v, incidentLoad (F ∪ R ∪ Y) v ≤ f + r + y) ∧
      ∀ u v, p u ≠ p v → s(u, v) ∉ F ∪ R ∪ Y →
        (G.deleteEdges ((R ∪ Y : Finset (Sym2 V)) : Set (Sym2 V))).Adj u v := by
  refine ⟨fun v => ?_, fun u v huv hnot => ?_⟩
  · have h1 := incidentLoad_union_le (F ∪ R) Y v
    have h2 := incidentLoad_union_le F R v
    have := hF v; have := hR v; have := hY v
    omega
  · rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hG u v huv fun h => hnot (mem_union_left _ (mem_union_left _ h)), ?_⟩
    intro hm
    rcases mem_union.mp (mem_coe.mp hm) with h | h
    · exact hnot (mem_union_left _ (mem_union_right _ h))
    · exact hnot (mem_union_right _ h)

end PartitionedTriangleAbsorption.OneLevelProducerStage131
