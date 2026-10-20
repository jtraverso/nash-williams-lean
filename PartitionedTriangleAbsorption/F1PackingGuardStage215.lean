/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingGuardFamilyStage214
public import PartitionedTriangleAbsorption.F0PrivateSchedule
public import PartitionedTriangleAbsorption.F1BoundedCoreStage207

/-! # F1 private libraries with controlled whole-triangle retirement

Private sets are physically constructed from the near-F1 host. The bound
includes every edge freed by retiring triangles of the SAME supplied
packing. It does not assert that this freed complement is decomposable.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1PackingGuardStage215

open Finset AntiEdgeSelection TypedApplicationLinks TypedF1AssemblyStage179
  PackingPrivateClosureStage213 PackingGuardFamilyStage214 F0PrivateLedger
  ReserveRetirementStage194

theorem closure_union {V : Type} [DecidableEq V] (D : Finset (Finset V))
    (A B : Finset (Sym2 V)) : closure D (A ∪ B) = closure D A ∪ closure D B := by
  classical
  have ht : touching D (A ∪ B) = touching D A ∪ touching D B := by
    ext s
    simp only [touching, mem_filter, mem_union, disjoint_union_right, not_and_or]
    tauto
  unfold PackingPrivateClosureStage213.closure
  rw [ht, union_biUnion]
  ext e
  simp only [mem_union]
  tauto

theorem closure_biUnion {V I : Type} [DecidableEq V] (D : Finset (Finset V))
    (s : Finset I) (A : I → Finset (Sym2 V)) :
    closure D (s.biUnion A) = s.biUnion (fun i => closure D (A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PackingPrivateClosureStage213.closure, touching]
  | insert i s hi ih => rw [biUnion_insert, biUnion_insert, closure_union, ih]

theorem exists_uniform_F1_guarded_library (α η : ℝ) (hα : 0 < α) (hη : 0 < η)
    (m : ℕ) :
    ∃ μ δ : ℝ, 0 < μ ∧ 0 < δ ∧ ∃ N : ℕ,
      ∀ (V I : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ k, α * Fintype.card V ≤ ((univ.filter fun w => p w = k).card : ℝ)) →
      (∀ i j, admissiblePair i j → ∀ x, p x = i →
        ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) →
      ∀ (Q : Finset (Sym2 V)) (D : Finset (Finset V)),
      Q ⊆ G.edgeFinset → IsDecomp p F1 Q D →
      ∀ (s : Finset I) (P : I → Finset (Sym2 V)) (B : Finset (Sym2 V)),
      DegBounded B (3 * μ * Fintype.card V) →
      (∀ i ∈ s, P i ⊆ G.edgeFinset ∧ (P i).card ≤ m ∧ IsIntDiv p F1 (P i)) →
      (∀ v, (∑ i ∈ s, incidentLoad (P i) v : ℕ) ≤ μ * Fintype.card V) →
      (s.card : ℝ) ≤ μ ^ 2 * (Fintype.card V : ℝ) ^ 2 →
      ∃ A : I → Finset (Sym2 V),
        (∀ i ∈ s, A i ⊆ G.edgeFinset ∧ Disjoint (A i) B ∧
          HasDecomp p F1 (A i) ∧ HasDecomp p F1 (A i ∪ P i)) ∧
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) ∧
        closure D (s.biUnion A) ⊆ G.edgeFinset ∧
        DegBounded (closure D (s.biUnion A)) (η * Fintype.card V) := by
  obtain ⟨b, Np, -, hprivate⟩ := PackingGuardFamilyStage214.exists_family
    F1 (by decide) TypedTransformer.F1_three_step (α / 2) (by positivity) m
  obtain ⟨μ, hμ, Ns, hschedule⟩ :=
    F0PrivateSchedule.exists_schedule (α / 10) η (by positivity) hη b
  refine ⟨μ, α / 8, hμ, by positivity, max Np Ns, ?_⟩
  intro V I _ _ hn p G _ hsize hmiss Q D hQG hD s P B hB hP hload hmass
  classical
  let n := Fintype.card V
  have hnp : Np ≤ n := (le_max_left _ _).trans hn
  have hns : Ns ≤ n := (le_max_right _ _).trans hn
  have hs := F1BoundedCoreStage207.compatible_supply_from_class_missing
    p G α (α / 8) (by positivity) le_rfl hsize hmiss
  obtain ⟨M, q, hq, -, hM, hmassq, hgeometry, hdegree⟩ := hschedule n hns
  have hroots : ∀ v, roots s P v ≤ M := by
    intro v
    have h : (roots s P v : ℝ) ≤ (∑ i ∈ s, incidentLoad (P i) v : ℕ) :=
      by exact_mod_cast roots_le_incidence s P v
    exact_mod_cast (h.trans (hload v)).trans hM
  have hmass' : b * s.card ≤ q * q := by
    have h := (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg b)).trans hmassq
    exact_mod_cast h
  have hnonneg : (0 : ℝ) ≤ 3 * μ * n + b * (M + q) := by positivity
  have hgeometry' : (5 * q : ℝ) + 4 * (3 * μ * n + b * (M + q)) ≤ α / 2 * n / 2 := by
    linarith only [hgeometry, hnonneg]
  obtain ⟨A, hgood, hdisj, -, hdeg⟩ := hprivate V I p G Q D hD s P B
    (3 * μ * n) M q q hnp (by positivity) hq hs hB hmass' hgeometry' hroots hP
  refine ⟨A, ?_, hdisj, ?_, ?_⟩
  · intro i hi
    obtain ⟨hG, havoid, hdec, habs, -, -, -⟩ := hgood i hi
    exact ⟨hG, havoid, hdec, habs⟩
  · intro e he
    rcases mem_union.mp he with heA | heR
    · obtain ⟨i, hi, hei⟩ := mem_biUnion.mp heA
      exact (hgood i hi).1 hei
    · obtain ⟨r, hr, her⟩ := mem_biUnion.mp heR
      apply hQG
      rw [← hD.2.2]
      exact mem_biUnion.mpr ⟨r, (mem_filter.mp hr).1, her⟩
  · rw [closure_biUnion]
    intro v
    have hμn : (0 : ℝ) ≤ μ * n := by positivity
    exact (hdeg v).trans (by linarith only [hdegree, hμn])


end PartitionedTriangleAbsorption.F1PackingGuardStage215
