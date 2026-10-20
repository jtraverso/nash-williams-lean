/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerCharge

/-! # Charge transport lower bound for every typed refiner

Fix any edge set `S` (a "region"). If a refiner selects pairwise edge-disjoint pieces of
zero charge covering `R ∪ L`, then the charge of `(R ∪ L) ∩ S` is carried entirely by the
selected pieces that meet both `S` and its complement. Each such piece carries at most
`M·K` charge. Hence a region in which two divisible leftovers differ in charge by `D`
forces at least `D / (2MK)` library pieces crossing the region boundary. This holds for any
library, any remainder `R`, and any physical or abstract realization: it is a necessary
condition, not a construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerTransport

open Finset TypedRefinerCharge

variable {V I : Type*} [DecidableEq V] {t : ℕ}

/-- `E` meets both the region `S` and its complement. -/
def Crosses (S E : Finset (Sym2 V)) : Prop := (E ∩ S).Nonempty ∧ (E \ S).Nonempty

instance (S E : Finset (Sym2 V)) : Decidable (Crosses S E) := by
  unfold Crosses; infer_instance

/-- Library pieces crossing the region. -/
def crossing [DecidableEq I] (S : Finset (Sym2 V)) (indices : Finset I)
    (B : I → Finset (Sym2 V)) : Finset I :=
  indices.filter fun i => Crosses S (B i)

theorem charge_inter_of_not_crosses (χ : Fin t → Fin t → ℤ) (p : V → Fin t)
    {S E : Finset (Sym2 V)} (hE : charge χ p E = 0) (h : ¬ Crosses S E) :
    charge χ p (E ∩ S) = 0 := by
  unfold Crosses at h
  rw [not_and_or, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty] at h
  rcases h with h | h
  · rw [h, charge_empty]
  · have : E ∩ S = E := by
      rw [inter_eq_left]
      intro e he
      by_contra hS
      have : e ∈ E \ S := mem_sdiff.mpr ⟨he, hS⟩
      rw [h] at this
      simp at this
    rw [this, hE]

/-- The charge inside the region is carried by the selected crossing pieces. -/
theorem charge_inter_selected (χ : Fin t → Fin t → ℤ) (p : V → Fin t)
    (S : Finset (Sym2 V)) (s : Finset I) (B : I → Finset (Sym2 V))
    (hdis : (s : Set I).PairwiseDisjoint B) (hzero : ∀ i ∈ s, charge χ p (B i) = 0) :
    charge χ p (s.biUnion B ∩ S) =
      ∑ i ∈ s.filter (fun i => Crosses S (B i)), charge χ p (B i ∩ S) := by
  have hset : s.biUnion B ∩ S = s.biUnion (fun i => B i ∩ S) := by
    ext e; simp only [mem_inter, mem_biUnion]; tauto
  have hdis' : (s : Set I).PairwiseDisjoint (fun i => B i ∩ S) := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono inter_subset_left inter_subset_left
  rw [hset, charge_biUnion χ p s _ hdis', sum_filter]
  refine sum_congr rfl fun i hi => ?_
  split_ifs with h
  · rfl
  · exact charge_inter_of_not_crosses χ p (hzero i hi) h

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- **Transport bound.** For every divisible leftover, the charge of `(R ∪ L) ∩ S` is at
most `M·K` times the number of library pieces crossing `S`. -/
theorem transport_bound [DecidableEq I] (χ : Fin t → Fin t → ℤ) {M : ℤ} {K : ℕ}
    (hM0 : 0 ≤ M) (hM : ∀ e : Sym2 V, |pair χ (pairVec p e)| ≤ M)
    (indices : Finset I) (B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V))
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) indices B X R)
    (hzero : ∀ i ∈ indices, charge χ p (B i) = 0)
    (hsize : ∀ i ∈ indices, (B i).card ≤ K)
    (S L : Finset (Sym2 V)) (hLX : L ⊆ X) (hdiv : IsIntDiv p F L) :
    |charge χ p ((R ∪ L) ∩ S)| ≤ M * K * (crossing S indices B).card := by
  obtain ⟨s, hsub, hdis, hcover⟩ := href L hLX hdiv
  rw [← hcover, charge_inter_selected χ p S s B hdis (fun i hi => hzero i (hsub hi))]
  calc |∑ i ∈ s.filter (fun i => Crosses S (B i)), charge χ p (B i ∩ S)|
      ≤ ∑ i ∈ s.filter (fun i => Crosses S (B i)), |charge χ p (B i ∩ S)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s.filter (fun i => Crosses S (B i)), M * K := by
        refine sum_le_sum fun i hi => ?_
        have hi' := hsub (mem_filter.mp hi).1
        calc |charge χ p (B i ∩ S)| ≤ M * (B i ∩ S).card := abs_charge_le p hM _
          _ ≤ M * K := by
            apply mul_le_mul_of_nonneg_left _ hM0
            exact_mod_cast (card_le_card inter_subset_left).trans (hsize i hi')
    _ = M * K * (s.filter (fun i => Crosses S (B i))).card := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ M * K * (crossing S indices B).card := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM0 (Nat.cast_nonneg K))
        exact_mod_cast card_le_card (filter_subset_filter _ hsub)

/-- **Crossing lower bound.** Two divisible leftovers whose charges inside `S` differ by `D`
force at least `D / (2MK)` crossing library pieces, for every remainder disjoint from `X`. -/
theorem crossing_lower_bound [DecidableEq I] (χ : Fin t → Fin t → ℤ) {M : ℤ} {K : ℕ}
    (hM0 : 0 ≤ M) (hM : ∀ e : Sym2 V, |pair χ (pairVec p e)| ≤ M)
    (indices : Finset I) (B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V))
    (hRX : Disjoint R X)
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) indices B X R)
    (hzero : ∀ i ∈ indices, charge χ p (B i) = 0)
    (hsize : ∀ i ∈ indices, (B i).card ≤ K)
    (S L₁ L₂ : Finset (Sym2 V)) (h₁ : L₁ ⊆ X) (hd₁ : IsIntDiv p F L₁)
    (h₂ : L₂ ⊆ X) (hd₂ : IsIntDiv p F L₂) :
    |charge χ p (L₁ ∩ S) - charge χ p (L₂ ∩ S)| ≤
      2 * (M * K * (crossing S indices B).card) := by
  have split : ∀ L ⊆ X, charge χ p ((R ∪ L) ∩ S) = charge χ p (R ∩ S) + charge χ p (L ∩ S) := by
    intro L hL
    rw [union_inter_distrib_right]
    exact charge_union χ p ((hRX.mono_right hL).mono inter_subset_left inter_subset_left)
  have b₁ := transport_bound χ hM0 hM indices B X R href hzero hsize S L₁ h₁ hd₁
  have b₂ := transport_bound χ hM0 hM indices B X R href hzero hsize S L₂ h₂ hd₂
  rw [split L₁ h₁] at b₁
  rw [split L₂ h₂] at b₂
  have := abs_sub (charge χ p (R ∩ S) + charge χ p (L₁ ∩ S))
    (charge χ p (R ∩ S) + charge χ p (L₂ ∩ S))
  have e : charge χ p (R ∩ S) + charge χ p (L₁ ∩ S) -
      (charge χ p (R ∩ S) + charge χ p (L₂ ∩ S)) =
      charge χ p (L₁ ∩ S) - charge χ p (L₂ ∩ S) := by ring
  rw [e] at this
  linarith

/-- **Bottleneck obstruction.** If the region boundary is crossed by too few library pieces,
no refiner of zero-charge bounded pieces exists. In particular a hierarchy which hands only a
bounded amount of information from a region to the rest cannot be typed. -/
theorem no_refiner_of_bottleneck [DecidableEq I] (χ : Fin t → Fin t → ℤ) {M : ℤ} {K : ℕ}
    (hM0 : 0 ≤ M) (hM : ∀ e : Sym2 V, |pair χ (pairVec p e)| ≤ M)
    (indices : Finset I) (B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V))
    (hRX : Disjoint R X)
    (hzero : ∀ i ∈ indices, charge χ p (B i) = 0)
    (hsize : ∀ i ∈ indices, (B i).card ≤ K)
    (S L₁ L₂ : Finset (Sym2 V)) (h₁ : L₁ ⊆ X) (hd₁ : IsIntDiv p F L₁)
    (h₂ : L₂ ⊆ X) (hd₂ : IsIntDiv p F L₂)
    (hgap : 2 * (M * K * (crossing S indices B).card) <
      |charge χ p (L₁ ∩ S) - charge χ p (L₂ ∩ S)|) :
    ¬ RefinerAssembly.RefinesReserve (p := p) (F := F) indices B X R := by
  intro href
  have := crossing_lower_bound χ hM0 hM indices B X R hRX href hzero hsize S L₁ L₂ h₁ hd₁ h₂ hd₂
  linarith

end PartitionedTriangleAbsorption.TypedRefinerTransport
