/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BipartiteQuotaStage76
public import PartitionedTriangleAbsorption.NeutralQuotaBudgetStage76
public import PartitionedTriangleAbsorption.NeutralChargeStage76
public import PartitionedTriangleAbsorption.TypedLoadReserveObstruction
public import PartitionedTriangleAbsorption.ClassRepresentativesStage65

/-! # Physical neutral augmentation of a sparse four-class reserve

Correction edges are selected in three distinct bipartite blocks. They avoid
the original defects and the original reserve. The reserve is enlarged, never
replaced, so its anti-edgeful supply survives. This theorem does not assume
integral divisibility of the reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NeutralAugmentationStage77

open Finset AntiEdgeSelection BipartiteQuotaStage76 NeutralChargeStage76
open ClassRepresentativesStage65 TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem class_disjoint (p : V → Fin 4) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (classSet p i) (classSet p j) := by
  apply disjoint_left.mpr
  intro v hi hj
  simp only [classSet, mem_filter, mem_univ, true_and] at hi hj
  exact hij (hi.symm.trans hj)

omit [DecidableEq V] in
theorem joins_disjoint (p : V → Fin 4) {i j : Fin 4}
    (hj : j ≠ 0) (hij : i ≠ j) {A B : Finset (Sym2 V)}
    (hA : Joins (classSet p 0) (classSet p i) A)
    (hB : Joins (classSet p 0) (classSet p j) B) : Disjoint A B := by
  apply disjoint_left.mpr
  intro e heA heB
  obtain ⟨u, hu, v, hv, he⟩ := hA e heA
  obtain ⟨u', hu', v', hv', he'⟩ := hB e heB
  simp only [classSet, mem_filter, mem_univ, true_and] at hu hv hu' hv'
  have heq := he.symm.trans he'
  rcases Sym2.eq_iff.mp heq with ⟨_, hvv⟩ | ⟨huv, _⟩
  · exact hij (hv.symm.trans ((congrArg p hvv).trans hv'))
  · exact hj (hv'.symm.trans ((congrArg p huv.symm).trans hu))

omit [DecidableEq V] in
theorem joins_charges (p : V → Fin 4) {i j : Fin 4} {Y : Finset (Sym2 V)}
    (hY : Joins (classSet p i) (classSet p j) Y) :
    a p Y = TypedRefinerCharge.chi3a i j * Y.card ∧
    b p Y = TypedRefinerCharge.chi3b i j * Y.card := by
  have he : ∀ e ∈ Y, aEdge p e = TypedRefinerCharge.chi3a i j ∧
      bEdge p e = TypedRefinerCharge.chi3b i j := by
    intro e he
    obtain ⟨u, hu, v, hv, rfl⟩ := hY e he
    simp only [classSet, mem_filter, mem_univ, true_and] at hu hv
    rw [aEdge_mk, bEdge_mk, hu, hv]
    exact ⟨rfl,rfl⟩
  constructor
  · calc a p Y = ∑ _e ∈ Y, TypedRefinerCharge.chi3a i j :=
            sum_congr rfl fun e heY => (he e heY).1
      _ = _ := by simp [mul_comm]
  · calc b p Y = ∑ _e ∈ Y, TypedRefinerCharge.chi3b i j :=
            sum_congr rfl fun e heY => (he e heY).2
      _ = _ := by simp [mul_comm]

omit [DecidableEq V] in
theorem joins_host (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
    (hG0 : ∀ u v, G0.Adj u v ↔ p u ≠ p v)
    {i j : Fin 4} (hij : i ≠ j) {Y : Finset (Sym2 V)}
    (hY : Joins (classSet p i) (classSet p j) Y) : Y ⊆ G0.edgeFinset := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := hY e he
  simp only [classSet, mem_filter, mem_univ, true_and] at hu hv
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (hG0 u v).mpr (by simpa only [hu,hv] using hij)

theorem physical_augmentation (p : V → Fin 4) (G0 : SimpleGraph V)
    [DecidableRel G0.Adj] (F X0 : Finset (Sym2 V))
    (gamma r : ℝ) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 0 < r)
    (hG0 : ∀ u v, G0.Adj u v ↔ p u ≠ p v)
    (hsize : ∀ i, gamma * Fintype.card V ≤ ((classSet p i).card : ℝ))
    (hlarge : 1 ≤ r * Fintype.card V) (hsmall : 1024 * r ≤ gamma ^ 2)
    (hF : DegBounded F (r * Fintype.card V))
    (hX0 : X0 ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset)
    (hdX0 : DegBounded X0 (r * Fintype.card V)) :
    ∃ X : Finset (Sym2 V), X0 ⊆ X ∧
      X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset ∧
      DegBounded X (196 * r * Fintype.card V / gamma) ∧
      ∀ l : Fin 4 → Fin 4 → ℤ, Annihilates TypedApplicationLinks.F3 l →
        ∑ e ∈ X, (pairFun l (pairVec p e) : ℝ) = 0 := by
  classical
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by dsimp [n]; nlinarith
  let q : ℕ := ⌈64 * r * n / gamma⌉₊
  let bq : ℕ := ⌈2 * r * n⌉₊
  let B := F ∪ X0
  let M := 2 * X0.card
  have hXG0 : X0 ⊆ G0.edgeFinset := hX0.trans
    (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))
  have hcX := TypedCoverDown.card_le_of_degBounded X0
    (TypedCoverDown.not_isDiag_of_mem_edgeFinset G0 hXG0) (r * n) hdX0
  have hM : (M : ℝ) ≤ 4 * r * n ^ 2 := by dsimp [M]; push_cast; nlinarith
  obtain ⟨hq,hqu,hb,hbu⟩ := NeutralQuotaBudgetStage76.rounded_quotas gamma r n
    hg hg1 hr hn hlarge
  have hB : ∀ v, incidentLoad B v ≤ bq := by
    have h := TypedLoadReserveObstruction.degBounded_union hF hdX0
    intro v
    have hh := (h v).trans (by
      change r * n + r * n ≤ (bq : ℝ)
      linarith)
    exact_mod_cast hh
  have hbud : ∀ i : Fin 4, 2 * M < q * (classSet p 0).card ∧
      2 * M + 2 * q * (bq + q) < q * (classSet p i).card := by
    intro i
    obtain ⟨h1,h2,_⟩ := NeutralQuotaBudgetStage76.quota_capacity gamma r n M
      (classSet p 0).card (classSet p i).card q bq hg hg1 hr hn hsmall
      hM (hsize 0) (hsize i) hq hqu hbu
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2
  obtain ⟨m01,m02,m03,hm01,hm02,hm03,ha,hbb⟩ := correction_counts p X0
  obtain ⟨Y01,hc01,hj01,hd01,hdeg01⟩ := exists_edges_of_quota
    (classSet p 0) (classSet p 1) B M q bq (class_disjoint p (by decide)) hB
    (hbud 1).1 (hbud 1).2 m01 hm01
  obtain ⟨Y02,hc02,hj02,hd02,hdeg02⟩ := exists_edges_of_quota
    (classSet p 0) (classSet p 2) B M q bq (class_disjoint p (by decide)) hB
    (hbud 2).1 (hbud 2).2 m02 hm02
  obtain ⟨Y03,hc03,hj03,hd03,hdeg03⟩ := exists_edges_of_quota
    (classSet p 0) (classSet p 3) B M q bq (class_disjoint p (by decide)) hB
    (hbud 3).1 (hbud 3).2 m03 hm03
  have hj12 : Disjoint Y01 Y02 := joins_disjoint p (by decide) (by decide) hj01 hj02
  have hj13 : Disjoint Y01 Y03 := joins_disjoint p (by decide) (by decide) hj01 hj03
  have hj23 : Disjoint Y02 Y03 := joins_disjoint p (by decide) (by decide) hj02 hj03
  have hx01 : Disjoint X0 Y01 := (hd01.mono_right subset_union_right).symm
  have hx02 : Disjoint X0 Y02 := (hd02.mono_right subset_union_right).symm
  have hx03 : Disjoint X0 Y03 := (hd03.mono_right subset_union_right).symm
  let X := X0 ∪ ((Y01 ∪ Y02) ∪ Y03)
  have hs : ∀ Y, Joins (classSet p 0) (classSet p 1) Y ∨
      Joins (classSet p 0) (classSet p 2) Y ∨ Joins (classSet p 0) (classSet p 3) Y →
      Disjoint Y B → Y ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset := by
    intro Y hj hd e he
    have hG : Y ⊆ G0.edgeFinset := by
      rcases hj with hj | hj | hj
      all_goals exact joins_host p G0 hG0 (by decide) hj
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact mem_sdiff.mpr ⟨hG he, fun hf => disjoint_left.mp hd he (mem_union_left X0 hf)⟩
  have hXG : X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset := union_subset hX0
    (union_subset (union_subset (hs Y01 (Or.inl hj01) hd01)
      (hs Y02 (Or.inr (Or.inl hj02)) hd02)) (hs Y03 (Or.inr (Or.inr hj03)) hd03))
  have h01 := joins_charges p hj01
  have h02 := joins_charges p hj02
  have h03 := joins_charges p hj03
  norm_num [TypedRefinerCharge.chi3a, TypedRefinerCharge.chi3b, hc01,hc02,hc03] at h01 h02 h03
  have hXY : Disjoint X0 ((Y01 ∪ Y02) ∪ Y03) :=
    disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨hx01,hx02⟩,hx03⟩
  have hY03 : Disjoint (Y01 ∪ Y02) Y03 := disjoint_union_left.mpr ⟨hj13,hj23⟩
  have haX : a p X = 0 := by
    simp only [X,a,sum_union hXY,sum_union hY03,sum_union hj12]
    change a p X0 + ((a p Y01 + a p Y02) + a p Y03) = 0
    rw [h01.1,h02.1,h03.1]
    omega
  have hbX : b p X = 0 := by
    simp only [X,b,sum_union hXY,sum_union hY03,sum_union hj12]
    change b p X0 + ((b p Y01 + b p Y02) + b p Y03) = 0
    rw [h01.2,h02.2,h03.2]
    omega
  refine ⟨X,subset_union_left,hXG,?_,?_⟩
  · have hY1 : DegBounded Y01 (q : ℝ) := fun v => by exact_mod_cast hdeg01 v
    have hY2 : DegBounded Y02 (q : ℝ) := fun v => by exact_mod_cast hdeg02 v
    have hY3 : DegBounded Y03 (q : ℝ) := fun v => by exact_mod_cast hdeg03 v
    have h := TypedLoadReserveObstruction.degBounded_union hdX0
      (TypedLoadReserveObstruction.degBounded_union
        (TypedLoadReserveObstruction.degBounded_union hY1 hY2) hY3)
    have hfinal := (NeutralQuotaBudgetStage76.quota_capacity gamma r n M
      (classSet p 0).card (classSet p 1).card q bq hg hg1 hr hn hsmall
      hM (hsize 0) (hsize 1) hq hqu hbu).2.2
    intro v
    exact (h v).trans (by linarith)
  · intro l hl
    rw [← Int.cast_sum]
    exact_mod_cast neutral_of_two_charges p X (fun e he u v heq => by
      have h := SimpleGraph.mem_edgeFinset.mp ((hXG.trans
        (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))) he)
      rw [heq,SimpleGraph.mem_edgeSet] at h
      exact (hG0 u v).mp h) haX hbX l hl

end PartitionedTriangleAbsorption.NeutralAugmentationStage77
