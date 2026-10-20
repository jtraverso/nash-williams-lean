/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.OddballStep

/-!
# Claim 15.9.4: decomposing all oddballs, one at a time

The vertices of `A` are processed one by one with `oddball_step` (Lemma 15.7), the used edges
being those of the reserve packing `T'` and of the triangles already chosen.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma not_mem_edges_of_avoid {T' : Finset (Finset V)} {A : Finset V}
    (hT'A : ∀ s ∈ T', ∀ x ∈ s, x ∉ A) {a : V} (ha : a ∈ A) {e : Sym2 V}
    (he : e ∈ T'.biUnion triEdges) (hae : a ∈ e) : False := by
  obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
  have : a ∈ t := (mem_sym2_iff.mp (mem_filter.mp het).1) a hae
  exact hT'A t ht a this ha

/-- The invariant of the iteration, after processing the set `R ⊆ A`. -/
theorem oddball_induction (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (T' : Finset (Finset V)) (A Astar : Finset V) {γ r : ℝ}
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
    (hA : (A.card : ℝ) ≤ 2 * r * Fintype.card V) :
    ∀ R : Finset V, R ⊆ A → ∃ T₁ : Finset (Finset V), IsTrianglePacking G T₁ ∧
      Disjoint (T₁.biUnion triEdges) (T'.biUnion triEdges) ∧
      (∀ t ∈ T₁, ∃ a ∈ t, a ∈ R) ∧
      (∀ u v, G.Adj u v → (u ∈ R ∨ v ∈ R) → s(u, v) ∈ T₁.biUnion triEdges) ∧
      ((T₁.filter (fun t => IsInteriorTri p t)).card : ℝ) ≤
        0.01 * (Fintype.card V : ℝ) * ((R.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤
          (partDeg G p v (p v) : ℝ))).card : ℝ) ∧
      ∀ v, v ∉ R → (T₁.filter (fun t => v ∈ t)).card ≤ R.card := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨∅, ⟨by simp, by simp⟩, by simp, by simp, by simp, by simp, by simp⟩
  | insert z R hzR ih =>
    intro hsub
    obtain ⟨T₁, hT₁, hdisj, hmeet, hcov, hint, hcnt⟩ := ih ((subset_insert _ _).trans hsub)
    have hzA : z ∈ A := hsub (mem_insert_self z R)
    have hRA : (R.card : ℝ) ≤ 2 * r * Fintype.card V :=
      (Nat.cast_le.mpr (card_le_card ((subset_insert _ _).trans hsub))).trans hA
    set U := T₁.biUnion triEdges ∪ T'.biUnion triEdges with hU
    have h3 : ∀ t ∈ T₁, t.card = 3 := fun t ht => (hT₁.1 t ht).card_eq
    have hedge : ∀ v, ((T₁.biUnion triEdges).filter (fun e => v ∈ e)).card =
        2 * (T₁.filter (fun t => v ∈ t)).card := fun v => covered_incident_card T₁ h3 hT₁.2 v
    have hUG : U ⊆ G.edgeFinset := union_subset
      (biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT₁.1 t ht))
      (biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT'.1 t ht))
    have hUzeq : U.filter (fun e => z ∈ e) = (T₁.biUnion triEdges).filter (fun e => z ∈ e) := by
      rw [hU, filter_union]
      have : (T'.biUnion triEdges).filter (fun e => z ∈ e) = ∅ :=
        filter_false_of_mem fun e he hze => not_mem_edges_of_avoid hT'A hzA he hze
      rw [this, union_empty]
    have hUfilter : ∀ x, (U.filter (fun e => x ∈ e)).card ≤
        2 * (T₁.filter (fun t => x ∈ t)).card +
          ((T'.biUnion triEdges).filter (fun e => x ∈ e)).card := by
      intro x
      rw [hU, filter_union, ← hedge x]
      exact card_union_le _ _
    have hUz : ((U.filter (fun e => z ∈ e)).card : ℝ) ≤ 4 * r * Fintype.card V := by
      rw [hUzeq, hedge z]
      have := hcnt z hzR
      have : ((2 * (T₁.filter (fun t => z ∈ t)).card : ℕ) : ℝ) ≤ 2 * R.card := by
        push_cast; exact_mod_cast (by omega : 2 * (T₁.filter (fun t => z ∈ t)).card ≤ 2 * R.card)
      linarith
    have hUzev : Even (U.filter (fun e => z ∈ e)).card := by
      rw [hUzeq, hedge z]; exact even_two_mul _
    have hUx : ∀ x, G.Adj z x → s(z, x) ∉ U →
        ((U.filter (fun e => x ∈ e)).card : ℝ) ≤ 5 * r * Fintype.card V := by
      intro x hzx hzxU
      have hxR : x ∉ R := fun hxR =>
        hzxU (mem_union_left _ (hcov z x hzx (Or.inr hxR)))
      have h1 := hUfilter x
      have h2 := hcnt x hxR
      have h3 := hT'deg x
      have h1' : ((U.filter (fun e => x ∈ e)).card : ℝ) ≤
          2 * (T₁.filter (fun t => x ∈ t)).card +
            ((T'.biUnion triEdges).filter (fun e => x ∈ e)).card := by exact_mod_cast h1
      have h2' : ((T₁.filter (fun t => x ∈ t)).card : ℝ) ≤ R.card := by exact_mod_cast h2
      linarith
    obtain ⟨D, hD, hDpd, hDcov, hDone, hDint0, hDint⟩ := oddball_step G p U z Astar hr0 hr1 hγ
      hrn hδ hbal hV hnorm hAc hUG (hev z) hUz hUzev hUx
    have hDU : ∀ t ∈ D, ∀ e ∈ triEdges t, e ∉ U := fun t ht e he heU =>
      disjoint_left.mp (hD t ht).2.2 he heU
    refine ⟨T₁ ∪ D, ⟨fun t ht => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rcases mem_union.mp ht with h | h
      · exact hT₁.1 t h
      · exact (hD t h).1
    · rw [coe_union]
      refine hT₁.2.union hDpd fun i hi j hj _ => disjoint_left.mpr fun e hei hej =>
        hDU j hj e hej (mem_union_left _ (mem_biUnion.mpr ⟨i, hi, hei⟩))
    · rw [union_biUnion]
      refine disjoint_union_left.mpr ⟨hdisj, disjoint_left.mpr fun e he he' => ?_⟩
      obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
      exact hDU t ht e het (mem_union_right _ he')
    · intro t ht
      rcases mem_union.mp ht with h | h
      · obtain ⟨a, hat, haR⟩ := hmeet t h
        exact ⟨a, hat, mem_insert_of_mem haR⟩
      · exact ⟨z, (hD t h).2.1, mem_insert_self z R⟩
    · have hzcov : ∀ w, G.Adj z w → s(z, w) ∈ (T₁ ∪ D).biUnion triEdges := by
        intro w hzw
        rw [union_biUnion]
        by_cases hzwU : s(z, w) ∈ U
        · rcases mem_union.mp hzwU with h | h
          · exact mem_union_left _ h
          · exact absurd (not_mem_edges_of_avoid hT'A hzA h (Sym2.mem_mk_left z w)) id
        · exact mem_union_right _ (hDcov w hzw hzwU)
      intro u v huv huvR
      rcases huvR with hu | hv
      · rcases mem_insert.mp hu with rfl | hu
        · exact hzcov v huv
        · rw [union_biUnion]; exact mem_union_left _ (hcov u v huv (Or.inl hu))
      · rcases mem_insert.mp hv with rfl | hv
        · rw [Sym2.eq_swap]; exact hzcov u huv.symm
        · rw [union_biUnion]; exact mem_union_left _ (hcov u v huv (Or.inr hv))
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

/-- **Claim 15.9.4** (proof; the statement is `claim_15_9_4` in `Lemma159.lean`). -/
theorem claim_15_9_4_proof :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 2) (T' : Finset (Finset V)) (A : Finset V),
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
        IsTwoExtremal γ G p → IsCrossBalanced γ G p →
        IsTrianglePacking G T' → (∀ s ∈ T', IsInteriorTri p s) →
        (∀ s ∈ T', ∀ x ∈ s, x ∉ A) →
        (∀ v, (((T'.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
          Real.sqrt γ * Fintype.card V) →
        (∀ v, 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G p v (p v) : ℝ) → v ∈ A) →
        (A.card : ℝ) ≤ 2 * Real.sqrt γ * Fintype.card V →
        ∃ T₁ : Finset (Finset V), IsTrianglePacking G T₁ ∧
          Disjoint (T₁.biUnion triEdges) (T'.biUnion triEdges) ∧
          (∀ t ∈ T₁, ∃ a ∈ t, a ∈ A) ∧
          (∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ T₁.biUnion triEdges) ∧
          ((T₁.filter (fun t => IsInteriorTri p t)).card : ℝ) ≤
            0.01 * (Fintype.card V : ℝ) *
              ((univ.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤
                (partDeg G p v (p v) : ℝ))).card : ℝ) := by
  refine ⟨1 / 1000000, by norm_num, fun γ hγ hγ₀ => ?_⟩
  set r := Real.sqrt γ with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hγ
  have hr1 : r ≤ 1 / 1000 := by
    have : r ≤ Real.sqrt ((1 / 1000) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hγr : γ = r * r := (Real.mul_self_sqrt hγ.le).symm
  refine ⟨⌈100 / r⌉₊ + 1, fun V _ _ G _ p T' A hn hdiv hδ hext hbal hT' _ hT'A hT'deg _ hA => ?_⟩
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hrn : 100 ≤ r * n := by
    have h1 : ((⌈100 / r⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
    have h2 := Nat.le_ceil (100 / r)
    push_cast at h1
    have : 100 / r ≤ n := by linarith
    rw [div_le_iff₀ hr0] at this; linarith
  obtain ⟨hAs, hcls, hnormal⟩ := lemma_15_6 hγ (by linarith) G p hδ hext
  set Astar := univ.filter (fun v => (1 / 4 + 2 * r) * n ≤ (partDeg G p v (p v) : ℝ)) with hAstar
  have hV : ∀ i, ((partClass p i).card : ℝ) ≤ (1 + r) * n / 2 := by
    intro i
    obtain ⟨j, hj, -⟩ := fin2_exists_ne i
    have h1 := hcls j
    have h2 : ((partClass p i).card : ℝ) + (partClass p j).card = n := by
      rw [hndef]; exact_mod_cast card_partClass_add' p (Ne.symm hj)
    linarith
  have hnorm : ∀ v, v ∉ Astar → (1 / 4 - r) * n ≤ (partDeg G p v (p v) : ℝ) ∧
      ∀ i, i ≠ p v → (1 / 2 - 2 * r) * n ≤ (partDeg G p v i : ℝ) := by
    intro v hv
    have : (partDeg G p v (p v) : ℝ) < (1 / 4 + 2 * r) * n := by
      by_contra h
      exact hv (mem_filter.mpr ⟨mem_univ _, le_of_not_gt h⟩)
    exact hnormal v this
  obtain ⟨T₁, h1, h2, h3, h4, h5, -⟩ := oddball_induction G p T' A Astar hr0 hr1 hγr hrn hδ
    hbal hV hnorm hAs hdiv.2 hT' hT'A hT'deg hA A subset_rfl
  refine ⟨T₁, h1, h2, h3, h4, h5.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ A))

end NashWilliams18
