/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.StabMain

/-!
# Partitions into four classes: block sums and bipartitions built from classes
-/

namespace NashWilliams.Frac

open Finset

variable {α : Type*} [DecidableEq α]

/-- A partition of `S` into four (possibly empty) classes. -/
structure Part4 (S : Finset α) (Y : Fin 4 → Finset α) : Prop where
  sub : ∀ i, Y i ⊆ S
  disj : ∀ i j, i ≠ j → Disjoint (Y i) (Y j)
  cover : ∀ x ∈ S, ∃ i, x ∈ Y i

namespace Part4

variable {S : Finset α} {Y : Fin 4 → Finset α}

lemma eq_biUnion (P : Part4 S Y) : S = univ.biUnion Y := by
  ext x; simp only [mem_biUnion, mem_univ, true_and]
  exact ⟨fun hx => P.cover x hx, fun ⟨i, hi⟩ => P.sub i hi⟩

lemma card_eq (P : Part4 S Y) : (S.card : ℝ) = ∑ i, ((Y i).card : ℝ) := by
  rw [P.eq_biUnion, card_biUnion (fun i _ j _ hij => P.disj i j hij)]
  push_cast; rfl

lemma bsum_eq (P : Part4 S Y) (a : α → α → ℝ) :
    bsum a S S = ∑ i, ∑ j, bsum a (Y i) (Y j) := by
  have hd : ((univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint Y :=
    fun i _ j _ hij => P.disj i j hij
  unfold bsum
  conv_lhs => rw [P.eq_biUnion]
  rw [sum_biUnion hd]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm, sum_biUnion hd]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]

lemma card_biUnion_eq (P : Part4 S Y) (I : Finset (Fin 4)) :
    ((I.biUnion Y).card : ℝ) = ∑ i ∈ I, ((Y i).card : ℝ) := by
  rw [card_biUnion (fun i _ j _ hij => P.disj i j hij)]; push_cast; rfl

/-- **Cut builder.** A union of classes whose size is close to `|S|/2` and such that the
classes on the two sides are almost completely joined by weight `1` gives `CutStruct`. -/
lemma cut_of_blocks (P : Part4 S Y) {a : α → α → ℝ} (h1 : ∀ i j, a i j ≤ 1)
    (I : Finset (Fin 4)) {δ : ℝ} (hδ : 0 < δ)
    (hbal : |∑ i ∈ I, ((Y i).card : ℝ) - S.card / 2| ≤ δ * S.card)
    (hbad : ∑ i ∈ I, ∑ j ∈ Iᶜ, (((Y i).card : ℝ) * (Y j).card - bsum a (Y i) (Y j)) ≤
      δ ^ 2 * (S.card : ℝ) ^ 2) :
    CutStruct S a δ := by
  set A := I.biUnion Y with hAdef
  have hAS : A ⊆ S := biUnion_subset.2 fun i _ => P.sub i
  have hcA : (A.card : ℝ) = ∑ i ∈ I, ((Y i).card : ℝ) := P.card_biUnion_eq I
  have hcB : ((S \ A).card : ℝ) = S.card - A.card := by
    rw [card_sdiff_of_subset hAS, Nat.cast_sub (card_le_card hAS)]
  refine ⟨A, hAS, ?_, ?_, ?_⟩
  · rw [hcA]; have := (abs_le.1 hbal).2; linarith
  · rw [hcB, hcA]; have := (abs_le.1 hbal).1; linarith
  · -- the bad pairs lie in the blocks `Y i × Y j` with `i ∈ I`, `j ∉ I`
    have hsub : (A ×ˢ (S \ A)).filter (fun p => a p.1 p.2 < 1 - δ) ⊆
        (I ×ˢ Iᶜ).biUnion fun ij => (Y ij.1 ×ˢ Y ij.2).filter fun p => a p.1 p.2 < 1 - δ := by
      intro p hp
      simp only [mem_filter, mem_product, mem_sdiff, hAdef, mem_biUnion] at hp
      obtain ⟨⟨⟨i, hi, hpi⟩, hpS, hpA⟩, hlt⟩ := hp
      obtain ⟨j, hj⟩ := P.cover _ hpS
      have hjI : j ∉ I := fun hjI => hpA ⟨j, hjI, hj⟩
      simp only [mem_biUnion, mem_product, mem_filter, mem_compl]
      exact ⟨(i, j), ⟨hi, hjI⟩, ⟨hpi, hj⟩, hlt⟩
    have hblock : ∀ i j, (((Y i ×ˢ Y j).filter fun p => a p.1 p.2 < 1 - δ).card : ℝ) * δ ≤
        ((Y i).card : ℝ) * (Y j).card - bsum a (Y i) (Y j) := by
      intro i j
      have := card_filter_mul_le (Y i ×ˢ Y j) (fun p => 1 - a p.1 p.2)
        (fun p _ => by linarith [h1 p.1 p.2]) δ
      have he : (Y i ×ˢ Y j).filter (fun p => δ < 1 - a p.1 p.2) =
          (Y i ×ˢ Y j).filter (fun p => a p.1 p.2 < 1 - δ) :=
        filter_congr fun p _ => by constructor <;> intro h <;> linarith
      rw [he, sum_product] at this
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one] at this
      unfold bsum; linarith
    have hcard : (((A ×ˢ (S \ A)).filter fun p => a p.1 p.2 < 1 - δ).card : ℝ) * δ ≤
        δ ^ 2 * (S.card : ℝ) ^ 2 := by
      calc _ ≤ (∑ ij ∈ I ×ˢ Iᶜ,
            (((Y ij.1 ×ˢ Y ij.2).filter fun p => a p.1 p.2 < 1 - δ).card : ℝ)) * δ := by
            gcongr
            exact_mod_cast (card_le_card hsub).trans card_biUnion_le
        _ = ∑ i ∈ I, ∑ j ∈ Iᶜ,
            (((Y i ×ˢ Y j).filter fun p => a p.1 p.2 < 1 - δ).card : ℝ) * δ := by
            rw [sum_mul, sum_product]
        _ ≤ _ := (sum_le_sum fun i _ => sum_le_sum fun j _ => hblock i j).trans hbad
    have : (((A ×ˢ (S \ A)).filter fun p => a p.1 p.2 < 1 - δ).card : ℝ) * δ ≤
        (δ * (S.card : ℝ) ^ 2) * δ := by nlinarith
    exact le_of_mul_le_mul_right this hδ

end Part4

end NashWilliams.Frac
