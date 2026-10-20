/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQuotaPackingStage124
public import PartitionedTriangleAbsorption.TypedPhysicalCorrection

/-! # Physical cleanup from per-request common-neighbour supply

The supply is required only for the prescribed base edges and destination
labels. No global AntiEdgeful hypothesis is introduced. Root demand and reuse
of third vertices are bounded separately, and every selected path is physically
edge-disjoint from the others.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RequestPackingStage140

open Finset AntiEdgeSelection
open RootQuotaPackingStage124 (packingEdges)
open TypedCorrectionFamily (edges)

variable {V I : Type*} [DecidableEq V]

def candidates [Fintype V] {t : ℕ} (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) (k : Fin t) : Finset V :=
  univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k

/-- Select every requested two-edge path, with a shared auxiliary quota. -/
theorem exists_paths [Fintype V] {t : ℕ} (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : I → V) (k : I → Fin t) (s : Finset I) (d q b : ℕ)
    (hroot : ∀ x, rootLoad s u v x ≤ d)
    (hsupply : ∀ i ∈ s, b ≤ (candidates p G (u i) (v i) (k i)).card)
    (hbudget : 2 * s.card + 2 * (d + 2 * q) * q < b * q) :
    ∃ f : I → V,
      (∀ i ∈ s, G.Adj (u i) (f i) ∧ G.Adj (f i) (v i) ∧ p (f i) = k i) ∧
      (s : Set I).PairwiseDisjoint (fun i => pathEdges (u i) (v i) (f i)) ∧
      ∀ x, auxiliaryLoad s f x ≤ q := by
  classical
  revert hroot hsupply hbudget
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      exact ⟨u, by simp, by simp [Set.PairwiseDisjoint, Set.Pairwise],
        by simp [auxiliaryLoad]⟩
  | @insert a s ha ih =>
      intro hroot hsupply hbudget
      have hsub : s ⊆ insert a s := subset_insert _ _
      have hr : ∀ x, rootLoad s u v x ≤ d :=
        fun x => (rootLoad_mono hsub u v x).trans (hroot x)
      have hb : 2 * s.card + 2 * (d + 2 * q) * q < b * q := by
        have := card_le_card hsub
        omega
      obtain ⟨f, hf, hdis, haux⟩ := ih hr
        (fun i hi => hsupply i (hsub hi)) hb
      let used := familyEdges s u v f
      have hused : ∀ x, incidentLoad used x ≤ d + 2 * q := by
        intro x
        exact (family_incident_card_le s u v f x).trans
          (Nat.add_le_add (hr x) (Nat.mul_le_mul_left 2 (haux x)))
      have hsum : ∑ x, auxiliaryLoad s f x ≤ 2 * s.card := by
        rw [auxiliaryLoad_sum]
        omega
      obtain ⟨w, hw, hwq, heU, heV⟩ := RootQuotaPackingStage124.select_unsaturated
        (candidates p G (u a) (v a) (k a)) used (u a) (v a)
        (auxiliaryLoad s f) q (d + 2 * q) s.card b
        (hsupply a (mem_insert_self _ _)) (hused _) (hused _) hsum hb
      have hwG := (mem_filter.mp hw).2
      have hnew : Disjoint (pathEdges (u a) (v a) w) used := by
        apply disjoint_left.mpr
        intro e he heOld
        rcases mem_insert.mp he with he | he
        · exact heU (he ▸ heOld)
        · exact heV ((mem_singleton.mp he) ▸ heOld)
      let f' := Function.update f a w
      have hold : ∀ i ∈ s, f' i = f i := by
        intro i hi
        exact Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) w f
      have hfa : f' a = w := Function.update_self _ _ _
      refine ⟨f', ?_, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfa]
          exact hwG
        · rw [hold i hi]
          exact hf i hi
      · intro i hi j hj hij
        change Disjoint (pathEdges (u i) (v i) (f' i)) (pathEdges (u j) (v j) (f' j))
        by_cases hia : i = a
        · subst i
          have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hij.symm
          rw [hfa, hold j hjs]
          exact hnew.mono_right
            (subset_biUnion_of_mem (fun l => pathEdges (u l) (v l) (f l)) hjs)
        · have his : i ∈ s := (mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            rw [hold i his, hfa]
            exact (hnew.mono_right
              (subset_biUnion_of_mem (fun l => pathEdges (u l) (v l) (f l)) his)).symm
          · have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hja
            rw [hold i his, hold j hjs]
            exact hdis his hjs hij
      · intro x
        rw [show f' = Function.update f a w from rfl, auxiliaryLoad_insert_update s a ha]
        split_ifs with hx
        · subst x
          exact Nat.succ_le_of_lt hwq
        · simpa only [Nat.add_zero] using haux x

/-- Added cross paths cost one unit per base incidence and two per use of a
third vertex; the base edges themselves are not included in this bound. -/
theorem path_degree_bound (s : Finset I) (u v f : I → V) (d q : ℕ)
    (hroot : ∀ x, rootLoad s u v x ≤ d)
    (haux : ∀ x, auxiliaryLoad s f x ≤ q) :
    DegBounded (familyEdges s u v f) (d + 2 * q) := by
  intro x
  have h := (family_incident_card_le s u v f x).trans
    (Nat.add_le_add (hroot x) (Nat.mul_le_mul_left 2 (haux x)))
  exact_mod_cast h

/-- Full triangles include the original base-edge incidence as well. -/
theorem packing_degree_bound (s : Finset I) (u v f : I → V) (d q : ℕ)
    (hroot : ∀ x, rootLoad s u v x ≤ d)
    (haux : ∀ x, auxiliaryLoad s f x ≤ q) :
    DegBounded (packingEdges s u v f) (2 * d + 2 * q) := by
  intro x
  have h := RootQuotaPackingStage124.packing_incident_le s u v f x
  have hr := hroot x
  have hq := haux x
  have heq : auxiliaryLoad s u x + RootQuotaPackingStage124.innerLoad s v f x =
      rootLoad s u v x + auxiliaryLoad s f x := by
    simp [rootLoad, auxiliaryLoad, RootQuotaPackingStage124.innerLoad, Nat.add_assoc]
  rw [heq] at h
  have hb : incidentLoad (packingEdges s u v f) x ≤ 2 * d + 2 * q := by omega
  exact_mod_cast hb

/-- An internal base cannot coincide with a cross path. -/
theorem base_not_path {t : ℕ} (p : V → Fin t) {a b u v w : V}
    (hab : p a = p b) (huv : p u = p v) (hwu : p w ≠ p u) :
    s(a, b) ∉ pathEdges u v w := by
  intro he
  rcases mem_insert.mp he with he | he
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hwu hab.symm
    · exact hwu hab
  · rcases Sym2.eq_iff.mp (mem_singleton.mp he) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hwu (hab.symm.trans huv.symm)
    · exact hwu (hab.trans huv.symm)

/-- Distinct internal bases plus disjoint cross paths are disjoint triangles. -/
theorem triangle_pairwise {t : ℕ} (p : V → Fin t) (s : Finset I) (u v f : I → V)
    (hinternal : ∀ i ∈ s, p (u i) = p (v i))
    (hcross : ∀ i ∈ s, p (f i) ≠ p (u i))
    (hinj : Set.InjOn (fun i => s(u i, v i)) (s : Set I))
    (hpaths : (s : Set I).PairwiseDisjoint (fun i => pathEdges (u i) (v i) (f i))) :
    (s : Set I).PairwiseDisjoint (fun i => edges (u i) (v i) (f i)) := by
  intro i hi j hj hij
  have he : ∀ l, edges (u l) (v l) (f l) = {s(u l, v l)} ∪ pathEdges (u l) (v l) (f l) :=
    fun l => by ext e; simp only [edges, pathEdges, mem_insert, mem_singleton, mem_union]
  change Disjoint (edges (u i) (v i) (f i)) (edges (u j) (v j) (f j))
  rw [he, he, disjoint_union_left, disjoint_union_right, disjoint_union_right]
  refine ⟨⟨?_, ?_⟩, ?_, hpaths hi hj hij⟩
  · simp only [disjoint_singleton_left, mem_singleton]
    exact fun h => hij (hinj hi hj h)
  · simpa only [disjoint_singleton_left] using
      base_not_path p (hinternal i hi) (hinternal j hj) (hcross j hj)
  · simpa only [disjoint_singleton_right] using
      base_not_path p (hinternal j hj) (hinternal i hi) (hcross i hi)

/-- Construct a physical triangle cleanup with its chosen witnesses exposed.
The caller can therefore count requested destination categories exactly. -/
theorem exists_cleanup [Fintype V] {t : ℕ} (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : I → V) (k : I → Fin t) (s : Finset I) (d q b : ℕ)
    (hbase : ∀ i ∈ s, G.Adj (u i) (v i))
    (hinternal : ∀ i ∈ s, p (u i) = p (v i))
    (hk : ∀ i ∈ s, k i ≠ p (u i))
    (hinj : Set.InjOn (fun i => s(u i, v i)) (s : Set I))
    (hroot : ∀ x, rootLoad s u v x ≤ d)
    (hsupply : ∀ i ∈ s, b ≤ (candidates p G (u i) (v i) (k i)).card)
    (hbudget : 2 * s.card + 2 * (d + 2 * q) * q < b * q) :
    ∃ f : I → V,
      (∀ i ∈ s, G.Adj (u i) (f i) ∧ G.Adj (f i) (v i) ∧ p (f i) = k i) ∧
      (s : Set I).PairwiseDisjoint (fun i => edges (u i) (v i) (f i)) ∧
      (∀ x, auxiliaryLoad s f x ≤ q) ∧
      packingEdges s u v f ⊆ G.edgeFinset ∧
      HasDecomp (fun _ : V => (0 : Fin 1)) {{0, 0, 0}} (packingEdges s u v f) ∧
      (∀ i ∈ s, s(u i, v i) ∈ packingEdges s u v f) ∧
      DegBounded (packingEdges s u v f) (2 * d + 2 * q) := by
  classical
  obtain ⟨f, hf, hpaths, haux⟩ := exists_paths p G u v k s d q b hroot hsupply hbudget
  have hcross : ∀ i ∈ s, p (f i) ≠ p (u i) := by
    intro i hi
    rw [(hf i hi).2.2]
    exact hk i hi
  have htri := triangle_pairwise p s u v f hinternal hcross hinj hpaths
  refine ⟨f, hf, htri, haux, ?_, ?_, ?_, packing_degree_bound s u v f d q hroot haux⟩
  · intro e he
    obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
    rcases mem_insert.mp he with rfl | he
    · exact G.mem_edgeFinset.mpr (hbase i hi)
    · rcases mem_insert.mp he with rfl | he
      · exact G.mem_edgeFinset.mpr (hf i hi).1
      · rcases mem_singleton.mp he with rfl
        exact G.mem_edgeFinset.mpr ((hf i hi).2.1.symm)
  · apply RefinerAssembly.hasDecomp_biUnion
    · intro i hi
      apply TypedPhysicalCorrection.edges_decomp
        (fun _ : V => (0 : Fin 1)) {{0, 0, 0}}
        (hbase i hi).ne (hf i hi).1.ne (hf i hi).2.1.ne.symm
      simp
    · exact htri
  · intro i hi
    exact mem_biUnion.mpr ⟨i, hi, by simp [edges]⟩

end PartitionedTriangleAbsorption.RequestPackingStage140
