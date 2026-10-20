/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedF1AssemblyStage179

/-! # Root-aware balanced selection from a physical packing

The root of each request is exempt from the saturation test. Every other
vertex is charged. The supply inequalities are explicit, not inferred here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootBalancedSelectionStage180

open Finset BalancedTrimStage170

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem blocked_away (D : Finset (Finset V)) (Z : Finset V) (r : V) (b : ℕ)
    (hZ : r ∉ Z) (hinc : ∀ v, v ≠ r → incidence D v ≤ b) :
    (D.filter fun s => ∃ v ∈ Z, v ∈ s).card ≤ b * Z.card := by
  have heq : (D.filter fun s => ∃ v ∈ Z, v ∈ s) =
      Z.biUnion (fun v => D.filter fun s => v ∈ s) := by
    ext s
    simp only [mem_filter, mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ v ∈ Z, (D.filter fun s => v ∈ s).card := card_biUnion_le
    _ ≤ ∑ _v ∈ Z, b := sum_le_sum fun v hv => hinc v (fun h => hZ (h ▸ hv))
    _ = b * Z.card := by simp [mul_comm]

omit [Fintype V] in
theorem extend_at_root [Finite V] (D S : Finset (Finset V)) (r : V) (k b d M : ℕ)
    (hD : ∀ s ∈ D, s.card = 3) (hS : ∀ s ∈ S, s.card = 3)
    (hroot : ∀ s ∈ D, r ∈ s) (hinc : ∀ v, v ≠ r → incidence D v ≤ b)
    (hd : 0 < d) (hsize : S.card + k ≤ M)
    (hbudget : d * (incidence S r + k) + 3 * M * b < d * D.card) :
    ∃ S', S ⊆ S' ∧ S' ⊆ S ∪ D ∧ S'.card = S.card + k ∧
      incidence S' r = incidence S r + k ∧
      (∀ v, v ≠ r → incidence S' v ≤ max (incidence S v) d) ∧
      k ≤ (S' ∩ D).card := by
  classical
  let := Fintype.ofFinite V
  induction k with
  | zero =>
    exact ⟨S, subset_rfl, subset_union_left, by simp, by simp,
      by intro v _; exact le_max_left _ _, by omega⟩
  | succ k ih =>
    obtain ⟨T, hST, hTD, hTk, hTr, hcap, _⟩ := ih (by omega) (by nlinarith)
    have htri : ∀ s ∈ T, s.card = 3 := by
      intro s hs
      rcases mem_union.mp (hTD hs) with hs | hs
      · exact hS s hs
      · exact hD s hs
    let Z := univ.filter fun v => v ≠ r ∧ d ≤ incidence T v
    let B := D.filter fun s => ∃ v ∈ Z, v ∈ s
    have hZ : r ∉ Z := by simp [Z]
    have hz : d * Z.card ≤ 3 * M := by
      have hsub : Z ⊆ univ.filter fun v => d ≤ incidence T v := by
        intro v hv
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2.2⟩
      exact (Nat.mul_le_mul_left d (card_le_card hsub)).trans
        ((saturated_mass T d htri).trans (by omega))
    have hb : B.card ≤ b * Z.card := blocked_away D Z r b hZ hinc
    have hused : (T ∩ D).card ≤ incidence T r := by
      apply card_le_card
      intro s hs
      exact mem_filter.mpr ⟨(mem_inter.mp hs).1, hroot s (mem_inter.mp hs).2⟩
    have hex : ∃ s ∈ D, s ∉ T ∧ s ∉ B := by
      by_contra hn
      have hcover : D ⊆ (T ∩ D) ∪ B := by
        intro s hs
        by_cases ht : s ∈ T
        · exact mem_union_left _ (mem_inter.mpr ⟨ht, hs⟩)
        · have hB : s ∈ B := by
            by_contra hB
            exact hn ⟨s, hs, ht, hB⟩
          exact mem_union_right _ hB
      have hN : D.card ≤ incidence T r + b * Z.card :=
        (card_le_card hcover).trans ((card_union_le _ _).trans (by omega))
      have hmul := Nat.mul_le_mul_left d hN
      have hzb := Nat.mul_le_mul_right b hz
      rw [hTr] at hmul
      nlinarith
    obtain ⟨s, hsD, hsT, hsB⟩ := hex
    have hr := hroot s hsD
    refine ⟨insert s T, hST.trans (subset_insert _ _),
      insert_subset (mem_union_right _ hsD) hTD, by simp [hsT, hTk, Nat.add_assoc], ?_, ?_, ?_⟩
    · have hnot : s ∉ T.filter (fun s => r ∈ s) := fun hs => hsT (mem_filter.mp hs).1
      simp only [incidence, filter_insert, hr, ite_true, card_insert_of_notMem hnot]
      dsimp [incidence] at hTr
      omega
    · intro v hvr
      by_cases hv : v ∈ s
      · have hvZ : v ∉ Z := fun hvZ => hsB (mem_filter.mpr ⟨hsD, v, hvZ, hv⟩)
        have hlt : incidence T v < d := by
          have : ¬ (v ≠ r ∧ d ≤ incidence T v) := by simpa [Z] using hvZ
          exact lt_of_not_ge (fun h => this ⟨hvr, h⟩)
        have hnot : s ∉ T.filter (fun s => v ∈ s) := fun hs => hsT (mem_filter.mp hs).1
        simp only [incidence, filter_insert, hv, ite_true, card_insert_of_notMem hnot]
        dsimp [incidence] at hlt
        exact (show (T.filter fun s => v ∈ s).card + 1 ≤ d by omega).trans (le_max_right _ _)
      · simpa only [incidence, filter_insert, hv, ite_false] using hcap v hvr
    · have hdiff : (insert s T) \ S ⊆ (insert s T) ∩ D := by
        intro t ht
        have hD' := (insert_subset (mem_union_right S hsD) hTD) (mem_sdiff.mp ht).1
        have htD : t ∈ D := (mem_union.mp hD').resolve_left (mem_sdiff.mp ht).2
        exact mem_inter.mpr ⟨(mem_sdiff.mp ht).1, htD⟩
      have hsubset : S ⊆ insert s T := hST.trans (subset_insert _ _)
      have hc := card_sdiff_of_subset hsubset
      have hi : (insert s T).card = S.card + (k + 1) := by simp [hsT, hTk, Nat.add_assoc]
      have hle := card_le_card hdiff
      omega

omit [Fintype V] in
theorem balanced_roots [Finite V] (F : Finset V) (D : V → Finset (Finset V))
    (k : V → ℕ) (b d K M : ℕ)
    (htri : ∀ r ∈ F, ∀ s ∈ D r, s.card = 3)
    (hroot : ∀ r ∈ F, ∀ s ∈ D r, r ∈ s)
    (hinc : ∀ r ∈ F, ∀ v, v ≠ r → incidence (D r) v ≤ b)
    (hd : 0 < d) (hK : ∀ r ∈ F, k r ≤ K)
    (hM : ∑ r ∈ F, k r ≤ M)
    (hsupply : ∀ r ∈ F, d * (d + K) + 3 * M * b < d * (D r).card) :
    ∃ S ⊆ F.biUnion D, S.card = ∑ r ∈ F, k r ∧
      (∀ v, incidence S v ≤ d + if v ∈ F then k v else 0) ∧
      (∀ r ∈ F, k r ≤ (S ∩ D r).card) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨∅, empty_subset _, by simp, by intro v; simp [incidence], by simp⟩
  | @insert r F hr ih =>
    obtain ⟨S, hSF, hSc, hcap, hcredit⟩ := ih
      (fun v hv => htri v (mem_insert_of_mem hv))
      (fun v hv => hroot v (mem_insert_of_mem hv))
      (fun v hv => hinc v (mem_insert_of_mem hv))
      (fun v hv => hK v (mem_insert_of_mem hv))
      (by rw [sum_insert hr] at hM; omega)
      (fun v hv => hsupply v (mem_insert_of_mem hv))
    have hS : ∀ s ∈ S, s.card = 3 := by
      intro s hs
      obtain ⟨v, hv, hs⟩ := mem_biUnion.mp (hSF hs)
      exact htri v (mem_insert_of_mem hv) s hs
    have hrcap : incidence S r ≤ d := by simpa [hr] using hcap r
    have hsize : S.card + k r ≤ M := by rw [sum_insert hr] at hM; omega
    have hbudget : d * (incidence S r + k r) + 3 * M * b < d * (D r).card := by
      have hk := hK r (mem_insert_self _ _)
      have hs := hsupply r (mem_insert_self _ _)
      nlinarith
    obtain ⟨T, hST, hTD, hTc, hTr, hTcap, hTcredit⟩ :=
      extend_at_root (D r) S r (k r) b d M (htri r (mem_insert_self _ _)) hS
        (hroot r (mem_insert_self _ _)) (hinc r (mem_insert_self _ _)) hd hsize hbudget
    refine ⟨T, ?_, by rw [sum_insert hr]; omega, ?_, ?_⟩
    · intro s hs
      rcases mem_union.mp (hTD hs) with hs | hs
      · obtain ⟨v, hv, hs⟩ := mem_biUnion.mp (hSF hs)
        exact mem_biUnion.mpr ⟨v, mem_insert_of_mem hv, hs⟩
      · exact mem_biUnion.mpr ⟨r, mem_insert_self _ _, hs⟩
    · intro v
      by_cases hv : v = r
      · subst v
        simp only [mem_insert_self, ite_true]
        omega
      · have h := hTcap v hv
        have hmax : max (incidence S v) d ≤ d + if v ∈ F then k v else 0 :=
          max_le (hcap v) (by split_ifs <;> omega)
        simpa only [mem_insert, hv, false_or] using h.trans hmax
    · intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact hTcredit
      · apply (hcredit v hv).trans
        apply card_le_card
        intro s hs
        exact mem_inter.mpr ⟨hST (mem_inter.mp hs).1, (mem_inter.mp hs).2⟩

end PartitionedTriangleAbsorption.RootBalancedSelectionStage180

