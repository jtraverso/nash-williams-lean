/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case127.Core
import RequestProject.NW18.Case126.Theorem126

/-!
# Proof of Theorem 12.7 (case (4) of §12.2)

If `G` is `α`-close to `T̄₂(n/2) + T₂(n/2)` (the complete `F₂`-blowup), pulling back the
four-class layout of `T̄₂(n/2) + T₂(n/2)` along the closeness bijection gives a partition `p`
with classes of size `n/4 ± 1` for which the `F₂`-abnormal pairs are exactly the pairs where `G`
differs from `T̄₂(n/2) + T₂(n/2)`: there are at most `2 α n²` ordered ones.  With `α = s²` and
`A = {v : at least s n abnormal pairs at v}`, we get `|A| ≤ 2 s n`, so `Setup127 G p A s` holds
and `core_12_7` applies.
-/

namespace NashWilliams18.C127

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

lemma patT2bT2_iff (a b : Fin 4) : patT2bT2 a b = true ↔ AllowedT F2 a b := by
  revert a b; decide

/-- **Theorem 12.7**, proof (same statement as `theorem_12_7` in `Cases.lean`). -/
theorem theorem_12_7_of_147 (h147 : Theorem147F2Statement) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2bT2 (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨s, hs, n₀, hcore⟩ := core_12_7_of_147 h147
  refine ⟨s ^ 2, by positivity, max n₀ 1, fun V _ _ G _ hn hdiv hδ hcl => ?_⟩
  set N := Fintype.card V with hNdef
  set n : ℝ := (N : ℝ) with hndef
  obtain ⟨e, he⟩ := hcl
  have hnpos : 0 < n := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hn
    rw [hndef]; exact_mod_cast this
  set p : V → Fin 4 := fun v => quarter N (e v) with hpdef
  set S := symmDiff G.edgeFinset (SimpleGraph.comap (⇑e) (T2bT2 N)).edgeFinset with hSdef
  -- abnormal pairs are differences with `T̄₂(n/2) + T̄₂(n/2)`
  have habn : ∀ v, (abnSet G p v).card ≤ (S.filter (fun x => v ∈ x)).card := by
    intro v
    refine card_le_card_of_injOn (fun w => s(v, w)) (fun w hw => ?_) (fun w _ w' _ hww => ?_)
    · simp only [abnSet, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
      simp only [coe_filter, Set.mem_setOf_eq]
      refine ⟨?_, Sym2.mem_mk_left _ _⟩
      rw [hSdef, Finset.mem_symmDiff]
      have hcomap : (SimpleGraph.comap (⇑e) (T2bT2 N)).Adj v w ↔ AllowedT F2 (p v) (p w) := by
        simp only [SimpleGraph.comap_adj, T2bT2, patternGraph, hpdef, patT2bT2_iff]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨fun h' => hw.1 (e.injective h').symm, h⟩
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [hcomap]
      tauto
    · simp only [Sym2.eq_iff, true_and] at hww
      rcases hww with h' | ⟨h1, h2⟩
      · exact h'
      · rw [h2, h1]
  have hsum : ∑ v, (abnSet G p v).card ≤ 2 * S.card :=
    (sum_le_sum fun v _ => habn v).trans (sum_card_incident_le S univ)
  set A : Finset V := univ.filter (fun v => s * n ≤ ((abnSet G p v).card : ℝ)) with hAdef
  apply hcore V G p A (le_trans (le_max_left _ _) hn) hdiv
  have hcls : ∀ i, (clsT p i).card = (classOf N i).card := by
    intro i
    rw [← card_map e.toEmbedding]
    congr 1
    ext j
    simp only [clsT, classOf, mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply,
      hpdef]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · intro hj; exact ⟨e.symm j, by simp [hj], by simp⟩
  refine ⟨hδ, fun i => ?_, fun i => ?_, ?_, fun v hv => ?_⟩
  · rw [hcls]; exact (card_classOf_bounds N i).1
  · rw [hcls]; exact (card_classOf_bounds N i).2
  · have h1 : (A.card : ℝ) * (s * n) ≤ ∑ v, ((abnSet G p v).card : ℝ) := by
      calc (A.card : ℝ) * (s * n) = ∑ _v ∈ A, s * n := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ v ∈ A, ((abnSet G p v).card : ℝ) := sum_le_sum fun v hv => (mem_filter.mp hv).2
        _ ≤ ∑ v, ((abnSet G p v).card : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    have h2 : (∑ v, ((abnSet G p v).card : ℝ)) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hsum
    have h3 : (S.card : ℝ) ≤ s ^ 2 * n ^ 2 := he
    have hsn : 0 < s * n := by positivity
    have : (A.card : ℝ) * (s * n) ≤ (2 * s * n) * (s * n) := by nlinarith
    exact le_of_mul_le_mul_right this hsn
  · simp only [hAdef, mem_filter, mem_univ, true_and, not_le] at hv
    exact hv.le

/-- **Theorem 12.7** from the global interface `Theorem1316Statement` (kept for
compatibility; see `theorem_12_7_of_147` for the version with the specialised premise). -/
theorem theorem_12_7_proof (h1316 : Theorem1316Statement) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2bT2 (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G :=
  theorem_12_7_of_147 (theorem_14_7_F2 h1316)

end NashWilliams18.C127
