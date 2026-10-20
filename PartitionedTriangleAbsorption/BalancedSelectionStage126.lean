/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BalancedTrialsStage126

/-! # One selection for clean connectors and all three category counts -/

@[expose] public section

namespace PartitionedTriangleAbsorption.BalancedSelectionStage126

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks
open SelfExcludingReserveStage123 BalancedTrialsStage126

theorem exists_balanced_selection {I Q : Type*} [Finite I] [DecidableEq I] [Fintype Q]
    (s : Q → Finset I) (B : Q → I → Finset I)
    (hself : ∀ q i, i ∈ s q → i ∈ B q i)
    (hsize : ∀ q i, i ∈ s q → (B q i).card ≤ 3)
    (hread : ∀ q j, ((s q).filter fun i => j ∈ B q i).card ≤ 4)
    (C : Fin 3 → Finset I) (M : ℕ) (hM : 0 < M) (hC : ∀ c, (C c).card = M)
    (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hcard : ∀ q, a ≤ ((s q).card : ℝ))
    (hbudget : (Fintype.card Q : ℝ) * Real.exp (-a / 1536) +
      6 * Real.exp (-2 * t ^ 2 / M) < 1) :
    ∃ ω : I → Bool,
      (∀ q, a / 192 < ((good (s q) (B q) ω).card : ℝ)) ∧
      ∀ c, |(((C c).filter fun i => ω i = true).card : ℝ) - (M : ℝ) / 2| ≤ t := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := I) (1 / 2)
    (by norm_num) (by norm_num)
  let : IsProbabilityMeasure μ := hμ
  let bad : Q ⊕ Fin 3 → Set (I → Bool) := Sum.elim
    (fun q => {ω | ((good (s q) (B q) ω).card : ℝ) ≤ a / 192})
    (fun c => {ω | t < |(((C c).filter fun i => ω i = true).card : ℝ) - (M : ℝ) / 2|})
  let bound : Q ⊕ Fin 3 → ℝ := Sum.elim (fun _ => Real.exp (-a / 1536))
    (fun _ => 2 * Real.exp (-2 * t ^ 2 / M))
  have htail : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    cases i with
    | inl q =>
      exact good_tail (s q) (B q) (hself q) (hsize q) (hread q)
        a ha (hcard q) μ hind hmarg
    | inr c =>
      have hn : (C c).Nonempty := card_pos.mp (by rw [hC]; exact hM)
      change μ.real {ω | t < |(((C c).filter fun i => ω i = true).card : ℝ) -
        (M : ℝ) / 2|} ≤ 2 * Real.exp (-2 * t ^ 2 / M)
      simpa only [hC] using fair_finset_tail μ hind hmarg (C c) hn t ht
  have htotal : ∑ i, bound i = (Fintype.card Q : ℝ) * Real.exp (-a / 1536) +
      6 * Real.exp (-2 * t ^ 2 / M) := by
    rw [Fintype.sum_sum_type]
    simp [bound]
    ring
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ bad bound htail
    (by rw [htotal]; exact hbudget)
  exact ⟨ω, fun q => not_le.mp (hω (.inl q)), fun c => not_lt.mp (hω (.inr c))⟩

open CoverDownStage105 ReserveQueryGeometryStage123

theorem exists_balanced_physical_thinning {V Q : Type*} [Finite V] [DecidableEq V]
    [Fintype Q] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (S : Q → Finset (V × V × V)) (x y z : Q → V)
    (hST : ∀ q, S q ⊆ T) (hroot : ∀ q r, r ∈ S q → r.1 = x q)
    (hself : ∀ q r, r ∈ S q → Disjoint (connectors (y q) (z q) r) (resTri r))
    (cat : V × V × V → Fin 3) (M : ℕ) (hM : 0 < M)
    (hcat : ∀ c, (T.filter fun r => cat r = c).card = M)
    (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hcard : ∀ q, a ≤ ((S q).card : ℝ))
    (hbudget : (Fintype.card Q : ℝ) * Real.exp (-a / 1536) +
      6 * Real.exp (-2 * t ^ 2 / M) < 1) :
    ∃ T' ⊆ T, (T' : Set (V × V × V)).PairwiseDisjoint resTri ∧
      (∀ q, a / 192 < ((T'.filter fun r => r ∈ S q ∧
        Disjoint (connectors (y q) (z q) r) (resEdges T')).card : ℝ)) ∧
      ∀ c, |((T'.filter fun r => cat r = c).card : ℝ) - (M : ℝ) / 2| ≤ t := by
  classical
  obtain ⟨ω, hω, hc⟩ := exists_balanced_selection S (fun q => queryBlock T (y q) (z q))
    (fun _ r _ => mem_insert_self _ _)
    (fun q r _ => queryBlock_card_le T hd (y q) (z q) r)
    (fun q => queryBlock_read_le T (S q) hd (hST q) (x q) (y q) (z q) (hroot q))
    (fun c => T.filter fun r => cat r = c) M hM hcat a t ha ht hcard hbudget
  let T' := T.filter fun r => ω r = true
  have hsub : T' ⊆ T := filter_subset _ _
  refine ⟨T', hsub, hd.subset hsub, ?_, ?_⟩
  · intro q
    apply (hω q).trans_le
    apply Nat.cast_le.mpr
    apply card_le_card
    intro r hr
    obtain ⟨hrs, hon, hoff⟩ := (mem_good _ _ _ _).mp hr
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hST q hrs, hon⟩, hrs,
      clean_connectors T (y q) (z q) r ω (hself q r hrs) hoff⟩
  · intro c
    simpa only [T', filter_filter, and_comm] using hc c

end PartitionedTriangleAbsorption.BalancedSelectionStage126
