/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerTransportStage143
public import Mathlib.Tactic

/-! # The eight-cut integral transport criterion

This theorem solves the natural-number allocation problem, not the graph
problem of producing its capacities or physically realizing its pairs.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ThreeColumnTransportStage143

open Finset IntegerTransportStage143

variable {V : Type*} [Fintype V] [DecidableEq V]

def leftCap (R : V → ℕ) (U : V → Fin 3 → ℕ) : V ⊕ (V × Fin 3) → ℕ :=
  Sum.elim R fun g => U g.1 g.2

def rightCap (U : V → Fin 3 → ℕ) (C : Fin 3 → ℕ) : (V × Fin 3) ⊕ Fin 3 → ℕ :=
  Sum.elim (fun g => U g.1 g.2) C

noncomputable def neighbours : V ⊕ (V × Fin 3) → Finset ((V × Fin 3) ⊕ Fin 3) := by
  classical
  exact Sum.elim (fun v => univ.image fun i => Sum.inl (v, i))
    (fun g => {Sum.inl g, Sum.inr g.2})

/-- The eight column cuts imply weighted Hall for the capacity gadgets. -/
theorem cuts_imply_hall (R : V → ℕ) (U : V → Fin 3 → ℕ) (C : Fin 3 → ℕ)
    (hcut : ∀ J : Finset (Fin 3),
      (∑ v, (R v - ∑ i ∈ univ \ J, U v i)) ≤ ∑ i ∈ J, C i)
    (s : Finset (V ⊕ (V × Fin 3))) :
    (∑ a ∈ s, leftCap R U a) ≤ ∑ b ∈ s.biUnion neighbours, rightCap U C b := by
  classical
  let A := s.toLeft
  let D := s.toRight
  let J := D.image Prod.snd
  let B := A.product (univ \ J)
  let E := (D ∪ B).disjSum J
  have hdis : Disjoint D B := by
    apply disjoint_left.mpr
    intro g hg hb
    have hj : g.2 ∈ J := mem_image.mpr ⟨g, hg, rfl⟩
    exact (mem_sdiff.mp (mem_product.mp hb).2).2 hj
  have he : E ⊆ s.biUnion neighbours := by
    intro b hb
    cases b with
    | inl g =>
      have hg : g ∈ D ∪ B := by simpa [E] using hb
      rcases mem_union.mp hg with hg | hg
      · exact mem_biUnion.mpr ⟨Sum.inr g, mem_toRight.mp hg,
          by simp [neighbours]⟩
      · have ha := (mem_product.mp hg).1
        exact mem_biUnion.mpr ⟨Sum.inl g.1, mem_toLeft.mp ha,
          by simp [neighbours]⟩
    | inr i =>
      have hi : i ∈ J := by simpa [E] using hb
      obtain ⟨g, hg, hgi⟩ := mem_image.mp hi
      exact mem_biUnion.mpr ⟨Sum.inr g, mem_toRight.mp hg,
        by simp [neighbours, hgi]⟩
  have hb : (∑ g ∈ B, U g.1 g.2) = ∑ v ∈ A, ∑ i ∈ univ \ J, U v i := by
    exact sum_product _ _ _
  have hr : (∑ v ∈ A, R v) ≤ (∑ g ∈ B, U g.1 g.2) + ∑ i ∈ J, C i := by
    have hs : (∑ v ∈ A, (R v - ∑ i ∈ univ \ J, U v i)) ≤
        ∑ v, (R v - ∑ i ∈ univ \ J, U v i) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun _ _ _ => Nat.zero_le _)
    have ht : (∑ v ∈ A, R v) ≤
        ∑ v ∈ A, ((R v - ∑ i ∈ univ \ J, U v i) + ∑ i ∈ univ \ J, U v i) := by
      apply sum_le_sum
      intro v _
      omega
    rw [sum_add_distrib] at ht
    have hc := hcut J
    omega
  have hl : (∑ a ∈ s, leftCap R U a) =
      (∑ v ∈ A, R v) + ∑ g ∈ D, U g.1 g.2 := by
    simpa only [leftCap, Sum.elim_inl, Sum.elim_inr] using
      sum_sum_eq_sum_toLeft_add_sum_toRight s (leftCap R U)
  have hw : (∑ b ∈ E, rightCap U C b) =
      (∑ g ∈ D, U g.1 g.2) + (∑ g ∈ B, U g.1 g.2) + ∑ i ∈ J, C i := by
    dsimp only [E]
    rw [sum_disjSum]
    simp only [rightCap, Sum.elim_inl, Sum.elim_inr]
    rw [sum_union hdis]
  calc
    (∑ a ∈ s, leftCap R U a) ≤ ∑ b ∈ E, rightCap U C b := by rw [hl, hw]; omega
    _ ≤ ∑ b ∈ s.biUnion neighbours, rightCap U C b :=
      sum_le_sum_of_subset_of_nonneg he (fun _ _ _ => Nat.zero_le _)

omit [DecidableEq V] in
/-- Integral three-column transport, from the eight natural-number cut tests. -/
theorem exists_transport (R : V → ℕ) (U : V → Fin 3 → ℕ) (C : Fin 3 → ℕ)
    (hcut : ∀ J : Finset (Fin 3),
      (∑ v, (R v - ∑ i ∈ univ \ J, U v i)) ≤ ∑ i ∈ J, C i) :
    ∃ x : V → Fin 3 → ℕ,
      (∀ v, ∑ i, x v i = R v) ∧
      (∀ v i, x v i ≤ U v i) ∧
      (∀ i, ∑ v, x v i ≤ C i) := by
  classical
  obtain ⟨z, hrow, hcol, hz⟩ := weighted_assignment
    (leftCap R U) (rightCap U C) neighbours (cuts_imply_hall R U C hcut)
  let x (v : V) (i : Fin 3) := z (Sum.inl v) (Sum.inl (v, i))
  let y (v : V) (i : Fin 3) := z (Sum.inr (v, i)) (Sum.inr i)
  have hr0 (v : V) (i : Fin 3) : z (Sum.inl v) (Sum.inr i) = 0 := by
    exact hz _ _ (by simp [neighbours])
  have hrg (v : V) (g : V × Fin 3) : z (Sum.inl v) (Sum.inl g) =
      if g.1 = v then x v g.2 else 0 := by
    rcases g with ⟨w, i⟩
    by_cases hw : w = v
    · subst w
      simp [x]
    · simp only [hw, ite_false]
      exact hz _ _ (by simp [neighbours, Ne.symm hw])
  have hdc (g : V × Fin 3) (i : Fin 3) : z (Sum.inr g) (Sum.inr i) =
      if i = g.2 then y g.1 g.2 else 0 := by
    by_cases hi : i = g.2
    · subst i
      simp [y]
    · simp only [hi, ite_false]
      exact hz _ _ (by simp [neighbours, hi])
  have hrows (v : V) : ∑ i, x v i = R v := by
    have hv := hrow (Sum.inl v)
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hv
    simp only [hrg, hr0, leftCap, Sum.elim_inl] at hv
    simpa using hv
  have hd (v : V) (i : Fin 3) :
      z (Sum.inr (v, i)) (Sum.inl (v, i)) + y v i = U v i := by
    have hv := hrow (Sum.inr (v, i))
    have hg : (∑ g : V × Fin 3, z (Sum.inr (v, i)) (Sum.inl g)) =
        z (Sum.inr (v, i)) (Sum.inl (v, i)) := by
      apply sum_eq_single (v, i)
      · intro g _ hne
        exact hz _ _ (by simp [neighbours, hne])
      · intro hnot
        exact (hnot (mem_univ _)).elim
    have hi : (∑ j : Fin 3, z (Sum.inr (v, i)) (Sum.inr j)) = y v i := by
      simpa only [hdc] using (show (∑ j : Fin 3,
        if j = i then y v i else 0) = y v i by simp)
    rw [Fintype.sum_sum_type] at hv
    rw [hg, hi] at hv
    exact hv
  have hxy (v : V) (i : Fin 3) : x v i ≤ y v i := by
    have hc := hcol (Sum.inl (v, i))
    rw [Fintype.sum_sum_type] at hc
    have ha : x v i ≤ ∑ w : V, z (Sum.inl w) (Sum.inl (v, i)) := by
      change z (Sum.inl v) (Sum.inl (v, i)) ≤ _
      exact single_le_sum (f := fun w : V => z (Sum.inl w) (Sum.inl (v, i)))
        (fun _ _ => Nat.zero_le _) (mem_univ v)
    have hb : z (Sum.inr (v, i)) (Sum.inl (v, i)) ≤
        ∑ g : V × Fin 3, z (Sum.inr g) (Sum.inl (v, i)) :=
      single_le_sum (f := fun g : V × Fin 3 => z (Sum.inr g) (Sum.inl (v, i)))
        (fun _ _ => Nat.zero_le _) (mem_univ (v, i))
    have he := hd v i
    change _ ≤ U v i at hc
    omega
  have hy (i : Fin 3) : ∑ v, y v i ≤ C i := by
    have hc := hcol (Sum.inr i)
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hc
    simp only [hr0, hdc, rightCap, Sum.elim_inr] at hc
    simpa using hc
  refine ⟨x, hrows, ?_, ?_⟩
  · intro v i
    have he := hd v i
    have hl := hxy v i
    omega
  · intro i
    exact (sum_le_sum (fun v _ => hxy v i)).trans (hy i)

omit [DecidableEq V] in
/-- Every natural allocation satisfies each column cut. -/
theorem cuts_of_transport (R : V → ℕ) (U : V → Fin 3 → ℕ) (C : Fin 3 → ℕ)
    (x : V → Fin 3 → ℕ) (hrow : ∀ v, ∑ i, x v i = R v)
    (hcap : ∀ v i, x v i ≤ U v i) (hcol : ∀ i, ∑ v, x v i ≤ C i)
    (J : Finset (Fin 3)) :
    (∑ v, (R v - ∑ i ∈ univ \ J, U v i)) ≤ ∑ i ∈ J, C i := by
  classical
  have hv (v : V) : (R v - ∑ i ∈ univ \ J, U v i) ≤ ∑ i ∈ J, x v i := by
    have he := sum_sdiff (s₁ := J) (s₂ := univ) (f := fun i => x v i) (subset_univ J)
    have hl : (∑ i ∈ univ \ J, x v i) ≤ ∑ i ∈ univ \ J, U v i :=
      sum_le_sum (fun i _ => hcap v i)
    have hr := hrow v
    omega
  calc
    _ ≤ ∑ v, ∑ i ∈ J, x v i := sum_le_sum (fun v _ => hv v)
    _ = ∑ i ∈ J, ∑ v, x v i := sum_comm
    _ ≤ ∑ i ∈ J, C i := sum_le_sum (fun i _ => hcol i)

omit [DecidableEq V] in
/-- An exact finite criterion: no real-flow hypothesis or integrality axiom. -/
theorem transport_iff_cuts (R : V → ℕ) (U : V → Fin 3 → ℕ) (C : Fin 3 → ℕ) :
    (∃ x : V → Fin 3 → ℕ,
      (∀ v, ∑ i, x v i = R v) ∧
      (∀ v i, x v i ≤ U v i) ∧
      (∀ i, ∑ v, x v i ≤ C i)) ↔
    ∀ J : Finset (Fin 3),
      (∑ v, (R v - ∑ i ∈ univ \ J, U v i)) ≤ ∑ i ∈ J, C i := by
  constructor
  · rintro ⟨x, hr, hu, hc⟩
    exact cuts_of_transport R U C x hr hu hc
  · exact exists_transport R U C

end PartitionedTriangleAbsorption.ThreeColumnTransportStage143
