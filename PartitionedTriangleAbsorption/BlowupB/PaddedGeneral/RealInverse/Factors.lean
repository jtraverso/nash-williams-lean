/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Modes

@[expose] public section

/-! # The mode multipliers

* `vertexFactor_prop`: at a root of class `i ∈ τ`, the vertex-mode profile is an
  exact positive multiple `κ` of the column `typeDegVec τ i`, with
  `κ ≥ m² / 8` whenever all class sizes are at least `m ≥ 8`. Repeated labels
  keep their multiplicities.
* `edgeFactor_lower`: the edge-mode multiplier of an allowed pair is at least `m - 4`. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption

theorem third_unique {i j z z' : Fin 4} {τ : Multiset (Fin 4)}
    (h : ({i, j, z} : Multiset (Fin 4)) = τ) (h' : ({i, j, z'} : Multiset (Fin 4)) = τ) :
    z' = z := by
  rw [← h] at h'
  have h2 : ({z'} : Multiset (Fin 4)) = {z} :=
    (Multiset.cons_inj_right j).mp ((Multiset.cons_inj_right i).mp h')
  exact Multiset.singleton_inj.mp h2

theorem edgeFactor_eq {n : Fin 4 → ℝ} {τ : Multiset (Fin 4)} {i j z : Fin 4}
    (h : ({i, j, z} : Multiset (Fin 4)) = τ) :
    edgeFactor n τ i j = n z - 2 * ind i z - 2 * ind j z := by
  unfold edgeFactor
  rw [sum_eq_single z]
  · rw [if_pos h]
  · intro z' _ hz'
    rw [if_neg (fun h' => hz' (third_unique h h'))]
  · intro hz
    exact absurd (mem_univ z) hz

theorem edgeFactor_lower {n : Fin 4 → ℝ} {m : ℝ} (hn : ∀ k, m ≤ n k)
    {τ : Multiset (Fin 4)} {i j z : Fin 4} (h : ({i, j, z} : Multiset (Fin 4)) = τ) :
    m - 4 ≤ edgeFactor n τ i j := by
  rw [edgeFactor_eq h]
  have h1 : ind i z ≤ 1 := by unfold ind; split_ifs <;> norm_num
  have h2 : ind j z ≤ 1 := by unfold ind; split_ifs <;> norm_num
  linarith [hn z]

theorem edgeFactor_eq_zero {n : Fin 4 → ℝ} {τ : Multiset (Fin 4)} {i j : Fin 4}
    (h : ∀ z, ({i, j, z} : Multiset (Fin 4)) ≠ τ) : edgeFactor n τ i j = 0 := by
  unfold edgeFactor
  exact sum_eq_zero fun z _ => if_neg (h z)

theorem vertexFactor_eq_zero {n : Fin 4 → ℝ} {τ : Multiset (Fin 4)} {i : Fin 4}
    (hi : i ∉ τ) (l : Fin 4) : vertexFactor n τ i l = 0 := by
  unfold vertexFactor
  refine sum_eq_zero fun z _ => if_neg ?_
  intro h
  apply hi
  rw [← h]
  exact Multiset.mem_cons_self _ _

theorem pair_eq_pair_iff (l z x y : Fin 4) :
    ({l, z} : Multiset (Fin 4)) = {x, y} ↔ (l = x ∧ z = y) ∨ (l = y ∧ z = x) := by
  revert l z x y
  decide

/-- The vertex-mode quadratic for root `i`, profile class `l` and completing class `z`. -/
def vq (n : Fin 4 → ℝ) (i l z : Fin 4) : ℝ :=
  (n l - 2 * ind i l) * (n z - ind i z - ind l z) - ind i z * (n l - ind i l) +
    ind l z * ind i l

theorem vertexFactor_cons (n : Fin 4 → ℝ) (i x y l : Fin 4) :
    vertexFactor n (i ::ₘ {x, y}) i l =
      ∑ z : Fin 4, if (l = x ∧ z = y) ∨ (l = y ∧ z = x) then vq n i l z else 0 := by
  unfold vertexFactor
  apply sum_congr rfl
  intro z _
  have : (({i, l, z} : Multiset (Fin 4)) = i ::ₘ {x, y}) ↔
      ((l = x ∧ z = y) ∨ (l = y ∧ z = x)) := by
    rw [← pair_eq_pair_iff]
    exact Multiset.cons_inj_right i
  by_cases h : (l = x ∧ z = y) ∨ (l = y ∧ z = x)
  · rw [if_pos (this.mpr h), if_pos h, vq]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

theorem typeDegVec_cons (i x y l : Fin 4) :
    ((typeDegVec (i ::ₘ {x, y}) i l : ℤ) : ℝ) = ind l x + ind l y := by
  unfold typeDegVec ind
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> simp_all <;> norm_num

theorem vq_symm {n : Fin 4 → ℝ} {i x y : Fin 4} (hxy : x ≠ y) : vq n i y x = vq n i x y := by
  unfold vq ind
  split_ifs <;> simp_all <;> ring

theorem vq_lower {n : Fin 4 → ℝ} {m : ℝ} (hm : 8 ≤ m) (hn : ∀ k, m ≤ n k)
    {i x y : Fin 4} (hxy : x ≠ y) : m ^ 2 / 8 ≤ vq n i x y := by
  have hx := hn x
  have hy := hn y
  have e1 : ind x y = 0 := if_neg hxy
  unfold vq
  rw [e1]
  unfold ind
  split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem vq_lower_diag {n : Fin 4 → ℝ} {m : ℝ} (hm : 8 ≤ m) (hn : ∀ k, m ≤ n k)
    (i x : Fin 4) : m ^ 2 / 8 ≤ vq n i x x / 2 := by
  have hx := hn x
  unfold vq ind
  simp only [↓reduceIte]
  split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ n x + m - 5),
    mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ n x + m - 1)]

theorem vertexFactor_prop (n : Fin 4 → ℝ) {m : ℝ} (hm : 8 ≤ m) (hn : ∀ k, m ≤ n k)
    {τ : Multiset (Fin 4)} (hτ : Multiset.card τ = 3) {i : Fin 4} (hi : i ∈ τ) :
    ∃ κ : ℝ, m ^ 2 / 8 ≤ κ ∧
      ∀ l, vertexFactor n τ i l = κ * ((typeDegVec τ i l : ℤ) : ℝ) := by
  have h1 : τ = i ::ₘ τ.erase i := (Multiset.cons_erase hi).symm
  have h2 : Multiset.card (τ.erase i) = 2 := by
    rw [Multiset.card_erase_of_mem hi, hτ]; rfl
  obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp h2
  have hτ' : τ = i ::ₘ {x, y} := by rw [h1, hxy]
  subst hτ'
  by_cases hxy' : x = y
  · subst hxy'
    refine ⟨vq n i x x / 2, vq_lower_diag hm hn i x, fun l => ?_⟩
    rw [vertexFactor_cons, typeDegVec_cons]
    by_cases hl : l = x
    · subst hl
      rw [sum_eq_single l]
      · rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
        norm_num [ind]
        try ring
      · intro z _ hz
        rw [if_neg]
        rintro (h | h) <;> exact hz h.2
      · intro h; exact absurd (mem_univ _) h
    · rw [sum_eq_zero]
      · unfold ind; rw [if_neg hl]; ring
      · intro z _
        rw [if_neg]
        rintro (h | h) <;> exact hl h.1
  · refine ⟨vq n i x y, vq_lower hm hn hxy', fun l => ?_⟩
    rw [vertexFactor_cons, typeDegVec_cons]
    by_cases hlx : l = x
    · subst hlx
      rw [sum_eq_single y]
      · rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
        unfold ind
        rw [if_pos rfl, if_neg hxy']
        ring
      · intro z _ hz
        rw [if_neg]
        rintro (h | h)
        · exact hz h.2
        · exact hxy' h.1
      · intro h; exact absurd (mem_univ _) h
    · by_cases hly : l = y
      · subst hly
        rw [sum_eq_single x]
        · rw [if_pos (Or.inr ⟨rfl, rfl⟩), vq_symm hxy']
          unfold ind
          rw [if_pos rfl, if_neg hlx]
          ring
        · intro z _ hz
          rw [if_neg]
          rintro (h | h)
          · exact hlx h.1
          · exact hz h.2
        · intro h; exact absurd (mem_univ _) h
      · rw [sum_eq_zero]
        · unfold ind; rw [if_neg hlx, if_neg hly]; ring
        · intro z _
          rw [if_neg]
          rintro (h | h)
          · exact hlx h.1
          · exact hly h.1

end PaddedGeneral.RealInverse
