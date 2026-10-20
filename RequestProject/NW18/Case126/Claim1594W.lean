/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Lemma159

@[expose] public section

/-!
# Claim 15.9.4 with a protected edge set

The variant of `oddball_induction` used in cases (3) and (4): a small set `W` of *protected*
edges (at most `4` at every vertex, an even number at every vertex of `A`) is avoided by the
triangles at the oddballs, which then cover every edge at `A` except the protected ones.
In the paper this is the set `E` of Lemma 15.9 (together with the parity-fixer triangles, which
are removed beforehand); here the protected set is simply added to the set of used edges.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem oddball_induction_W (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (T' : Finset (Finset V)) (W : Finset (Sym2 V)) (A Astar : Finset V) {γ r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1 / 1000) (hγ : γ = r * r) (hrn : 100 ≤ r * Fintype.card V)
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hbal : IsCrossBalanced γ G p)
    (hV : ∀ i, ((partClass p i).card : ℝ) ≤ (1 + r) * Fintype.card V / 2)
    (hnorm : ∀ v, v ∉ Astar → (1 / 4 - r) * Fintype.card V ≤ (partDeg G p v (p v) : ℝ) ∧
      ∀ i, i ≠ p v → (1 / 2 - 2 * r) * Fintype.card V ≤ (partDeg G p v i : ℝ))
    (hAc : (Astar.card : ℝ) ≤ 2 * r * Fintype.card V)
    (hev : ∀ v, Even (G.degree v))
    (hT' : IsTrianglePacking G T') (hT'A : ∀ s ∈ T', ∀ x ∈ s, x ∉ A)
    (hT'deg : ∀ v, (((T'.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
      r * Fintype.card V)
    (hWG : W ⊆ G.edgeFinset) (hWx : ∀ x, (W.filter (fun e => x ∈ e)).card ≤ 4)
    (hWev : ∀ a ∈ A, Even (W.filter (fun e => a ∈ e)).card)
    (hA : (A.card : ℝ) ≤ r * Fintype.card V) :
    ∀ R : Finset V, R ⊆ A → ∃ T₁ : Finset (Finset V), IsTrianglePacking G T₁ ∧
      Disjoint (T₁.biUnion triEdges) (T'.biUnion triEdges) ∧
      Disjoint (T₁.biUnion triEdges) W ∧
      (∀ t ∈ T₁, ∃ a ∈ t, a ∈ R) ∧
      (∀ u v, G.Adj u v → (u ∈ R ∨ v ∈ R) → s(u, v) ∉ W → s(u, v) ∈ T₁.biUnion triEdges) ∧
      ((T₁.filter (fun t => IsInteriorTri p t)).card : ℝ) ≤
        0.01 * (Fintype.card V : ℝ) * ((R.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤
          (partDeg G p v (p v) : ℝ))).card : ℝ) ∧
      ∀ v, v ∉ R → (T₁.filter (fun t => v ∈ t)).card ≤ R.card := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨∅, ⟨by simp, by simp⟩, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | insert z R hzR ih =>
    intro hsub
    obtain ⟨T₁, hT₁, hdisj, hdisjW, hmeet, hcov, hint, hcnt⟩ :=
      ih ((subset_insert _ _).trans hsub)
    have hzA : z ∈ A := hsub (mem_insert_self z R)
    have hRA : (R.card : ℝ) ≤ r * Fintype.card V :=
      (Nat.cast_le.mpr (card_le_card ((subset_insert _ _).trans hsub))).trans hA
    set U := T₁.biUnion triEdges ∪ T'.biUnion triEdges ∪ W with hU
    have h3 : ∀ t ∈ T₁, t.card = 3 := fun t ht => (hT₁.1 t ht).card_eq
    have hedge : ∀ v, ((T₁.biUnion triEdges).filter (fun e => v ∈ e)).card =
        2 * (T₁.filter (fun t => v ∈ t)).card := fun v => covered_incident_card T₁ h3 hT₁.2 v
    have hUG : U ⊆ G.edgeFinset := union_subset (union_subset
      (biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT₁.1 t ht))
      (biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT'.1 t ht))) hWG
    have hUzeq : U.filter (fun e => z ∈ e) =
        (T₁.biUnion triEdges).filter (fun e => z ∈ e) ∪ W.filter (fun e => z ∈ e) := by
      rw [hU, filter_union, filter_union]
      have : (T'.biUnion triEdges).filter (fun e => z ∈ e) = ∅ :=
        filter_false_of_mem fun e he hze => not_mem_edges_of_avoid hT'A hzA he hze
      rw [this, union_empty]
    have hUzcard : (U.filter (fun e => z ∈ e)).card =
        2 * (T₁.filter (fun t => z ∈ t)).card + (W.filter (fun e => z ∈ e)).card := by
      rw [hUzeq, card_union_of_disjoint (disjoint_filter_filter hdisjW), hedge z]
    have hUfilter : ∀ x, (U.filter (fun e => x ∈ e)).card ≤
        2 * (T₁.filter (fun t => x ∈ t)).card +
          ((T'.biUnion triEdges).filter (fun e => x ∈ e)).card + 4 := by
      intro x
      rw [hU, filter_union, filter_union, ← hedge x]
      have := hWx x
      have := card_union_le ((T₁.biUnion triEdges).filter (fun e => x ∈ e) ∪
        (T'.biUnion triEdges).filter (fun e => x ∈ e)) (W.filter (fun e => x ∈ e))
      have := card_union_le ((T₁.biUnion triEdges).filter (fun e => x ∈ e))
        ((T'.biUnion triEdges).filter (fun e => x ∈ e))
      omega
    have hUz : ((U.filter (fun e => z ∈ e)).card : ℝ) ≤ 4 * r * Fintype.card V := by
      rw [hUzcard]
      have h1 := hcnt z hzR
      have h2 := hWx z
      have : ((2 * (T₁.filter (fun t => z ∈ t)).card + (W.filter (fun e => z ∈ e)).card : ℕ) : ℝ)
          ≤ 2 * R.card + 4 := by
        have : 2 * (T₁.filter (fun t => z ∈ t)).card + (W.filter (fun e => z ∈ e)).card ≤
            2 * R.card + 4 := by omega
        exact_mod_cast this
      linarith
    have hUzev : Even (U.filter (fun e => z ∈ e)).card := by
      rw [hUzcard]; exact (even_two_mul _).add (hWev z hzA)
    have hUx : ∀ x, G.Adj z x → s(z, x) ∉ U →
        ((U.filter (fun e => x ∈ e)).card : ℝ) ≤ 5 * r * Fintype.card V := by
      intro x hzx hzxU
      have hxR : x ∉ R := fun hxR => hzxU (mem_union_left _ (mem_union_left _
        (hcov z x hzx (Or.inr hxR) (fun h => hzxU (mem_union_right _ h)))))
      have h1 := hUfilter x
      have h2 := hcnt x hxR
      have h3 := hT'deg x
      have h1' : ((U.filter (fun e => x ∈ e)).card : ℝ) ≤
          2 * (T₁.filter (fun t => x ∈ t)).card +
            ((T'.biUnion triEdges).filter (fun e => x ∈ e)).card + 4 := by exact_mod_cast h1
      have h2' : ((T₁.filter (fun t => x ∈ t)).card : ℝ) ≤ R.card := by exact_mod_cast h2
      linarith
    obtain ⟨D, hD, hDpd, hDcov, hDone, hDint0, hDint⟩ := oddball_step G p U z Astar hr0 hr1 hγ
      hrn hδ hbal hV hnorm hAc hUG (hev z) hUz hUzev hUx
    have hDU : ∀ t ∈ D, ∀ e ∈ triEdges t, e ∉ U := fun t ht e he heU =>
      disjoint_left.mp (hD t ht).2.2 he heU
    refine ⟨T₁ ∪ D, ⟨fun t ht => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases mem_union.mp ht with h | h
      · exact hT₁.1 t h
      · exact (hD t h).1
    · rw [coe_union]
      refine hT₁.2.union hDpd fun i hi j hj _ => disjoint_left.mpr fun e hei hej =>
        hDU j hj e hej (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨i, hi, hei⟩)))
    · rw [union_biUnion]
      refine disjoint_union_left.mpr ⟨hdisj, disjoint_left.mpr fun e he he' => ?_⟩
      obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
      exact hDU t ht e het (mem_union_left _ (mem_union_right _ he'))
    · rw [union_biUnion]
      refine disjoint_union_left.mpr ⟨hdisjW, disjoint_left.mpr fun e he he' => ?_⟩
      obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
      exact hDU t ht e het (mem_union_right _ he')
    · intro t ht
      rcases mem_union.mp ht with h | h
      · obtain ⟨a, hat, haR⟩ := hmeet t h
        exact ⟨a, hat, mem_insert_of_mem haR⟩
      · exact ⟨z, (hD t h).2.1, mem_insert_self z R⟩
    · have hzcov : ∀ w, G.Adj z w → s(z, w) ∉ W → s(z, w) ∈ (T₁ ∪ D).biUnion triEdges := by
        intro w hzw hzwW
        rw [union_biUnion]
        by_cases hzwU : s(z, w) ∈ U
        · rcases mem_union.mp hzwU with h | h
          · rcases mem_union.mp h with h | h
            · exact mem_union_left _ h
            · exact absurd (not_mem_edges_of_avoid hT'A hzA h (Sym2.mem_mk_left z w)) id
          · exact absurd h hzwW
        · exact mem_union_right _ (hDcov w hzw hzwU)
      intro u v huv huvR huvW
      rcases huvR with hu | hv
      · rcases mem_insert.mp hu with rfl | hu
        · exact hzcov v huv huvW
        · rw [union_biUnion]; exact mem_union_left _ (hcov u v huv (Or.inl hu) huvW)
      · rcases mem_insert.mp hv with rfl | hv
        · rw [Sym2.eq_swap]; exact hzcov u huv.symm (by rwa [Sym2.eq_swap])
        · rw [union_biUnion]; exact mem_union_left _ (hcov u v huv (Or.inr hv) huvW)
    · have hle : (((T₁ ∪ D).filter (fun t => IsInteriorTri p t)).card : ℝ) ≤
          (T₁.filter (fun t => IsInteriorTri p t)).card +
            (D.filter (fun t => IsInteriorTri p t)).card := by
        rw [filter_union]; exact_mod_cast card_union_le _ _
      have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      by_cases hzB : 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G p z (p z) : ℝ)
      · rw [filter_insert, if_pos hzB, card_insert_of_notMem (fun h => hzR (mem_filter.mp h).1)]
        push_cast
        nlinarith
      · rw [filter_insert, if_neg hzB]
        have := hDint0 (lt_of_not_ge hzB)
        rw [this, Nat.cast_zero, add_zero] at hle
        linarith
    · intro v hv
      have hvz : v ≠ z := fun h => hv (h ▸ mem_insert_self z R)
      have hvR : v ∉ R := fun h => hv (mem_insert_of_mem h)
      rw [filter_union, card_insert_of_notMem hzR]
      exact (card_union_le _ _).trans (add_le_add (hcnt v hvR) (hDone v hvz))

end NashWilliams18
