/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupCutBalanceStage140
public import PartitionedTriangleAbsorption.TypedPhysicalCorrection

/-! # Exact quota consumption of an arbitrary physical triangle packing

This ledger includes monochromatic triangles. It does not assume that an
exceptional preclean is quota-safe, nor does it construct such a preclean.
The criterion below is precisely the obligation its producer must discharge.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ExceptionalQuotaStage142

open Finset MatchedQuotaStage140

variable {V : Type*} [DecidableEq V]

def sixQuota (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) : ℤ :=
  2 * (E.card : ℤ) - 3 * (cuts p E i).card

theorem sixQuota_sdiff (p : V → Fin 4) (E Q : Finset (Sym2 V))
    (hQE : Q ⊆ E) (i : Fin 3) :
    sixQuota p (E \ Q) i = sixQuota p E i - sixQuota p Q i := by
  have hc : (cuts p (E \ Q) i).card + (cuts p Q i).card = (cuts p E i).card := by
    have heq : cuts p (E \ Q) i = cuts p E i \ cuts p Q i := by
      ext e
      simp only [cuts, mem_filter, mem_sdiff]
      tauto
    rw [heq]
    exact card_sdiff_add_card_eq_card (filter_subset_filter _ hQE)
  have he := card_sdiff_add_card_eq_card hQE
  unfold sixQuota
  omega

theorem triangle_card (a b w : V) (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) :
    (TypedCorrectionFamily.edges a b w).card = 3 := by
  simp [TypedCorrectionFamily.edges, hab, haw, hbw, Ne.symm hab, Ne.symm hbw]

theorem triangle_cut (p : V → Fin 4) (a b w : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (i : Fin 3) :
    (cuts p (TypedCorrectionFamily.edges a b w) i).card =
      if side i (p a) = side i (p b) ∧ side i (p a) = side i (p w) then 0 else 2 := by
  unfold cuts
  simp only [TypedCorrectionFamily.edges, filter_insert, filter_singleton,
    Sym2.map_mk, Sym2.mk_isDiag_iff, Function.comp_apply]
  generalize side i (p a) = x
  generalize side i (p b) = y
  generalize side i (p w) = z
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [hab, haw, hbw, Ne.symm hab, Ne.symm hbw]

theorem sixQuota_triangle (p : V → Fin 4) (a b w : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (i : Fin 3) :
    sixQuota p (TypedCorrectionFamily.edges a b w) i =
      if side i (p a) = side i (p b) ∧ side i (p a) = side i (p w) then 6 else 0 := by
  rw [sixQuota, triangle_card a b w hab haw hbw, triangle_cut p a b w hab haw hbw i]
  split_ifs <;> norm_num

def usage {I : Type*} (p : V → Fin 4) (s : Finset I) (u v w : I → V)
    (i : Fin 3) : ℕ :=
  (s.filter fun j => side i (p (u j)) = side i (p (v j)) ∧
    side i (p (u j)) = side i (p (w j))).card

theorem sixQuota_packing {I : Type*} (p : V → Fin 4) (s : Finset I)
    (u v w : I → V)
    (hne : ∀ j ∈ s, u j ≠ v j ∧ u j ≠ w j ∧ v j ≠ w j)
    (hdis : (s : Set I).PairwiseDisjoint
      (fun j => TypedCorrectionFamily.edges (u j) (v j) (w j))) (i : Fin 3) :
    sixQuota p (RootQuotaPackingStage124.packingEdges s u v w) i =
      6 * (usage p s u v w i : ℤ) := by
  classical
  have he : (RootQuotaPackingStage124.packingEdges s u v w).card =
      ∑ j ∈ s, (TypedCorrectionFamily.edges (u j) (v j) (w j)).card := by
    exact card_biUnion hdis
  have hc : (cuts p (RootQuotaPackingStage124.packingEdges s u v w) i).card =
      ∑ j ∈ s, (cuts p (TypedCorrectionFamily.edges (u j) (v j) (w j)) i).card := by
    unfold cuts RootQuotaPackingStage124.packingEdges
    rw [filter_biUnion]
    exact card_biUnion (fun j hj k hk hjk =>
      (hdis hj hk hjk).mono (filter_subset _ _) (filter_subset _ _))
  have hsum : sixQuota p (RootQuotaPackingStage124.packingEdges s u v w) i =
      ∑ j ∈ s, sixQuota p (TypedCorrectionFamily.edges (u j) (v j) (w j)) i := by
    unfold sixQuota
    rw [he, hc]
    simp only [Nat.cast_sum, mul_sum, sum_sub_distrib]
  rw [hsum]
  have ht : (∑ j ∈ s, sixQuota p (TypedCorrectionFamily.edges (u j) (v j) (w j)) i) =
      ∑ j ∈ s, if side i (p (u j)) = side i (p (v j)) ∧
        side i (p (u j)) = side i (p (w j)) then (6 : ℤ) else 0 := by
    apply sum_congr rfl
    intro j hj
    exact sixQuota_triangle p _ _ _ (hne j hj).1 (hne j hj).2.1 (hne j hj).2.2 i
  rw [ht]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, usage]
  ring

theorem residual_quota_exact {I : Type*} (p : V → Fin 4) (E : Finset (Sym2 V))
    (s : Finset I) (u v w : I → V) (q : Fin 3 → ℕ)
    (hquota : ∀ i, 6 * q i + 3 * (cuts p E i).card = 2 * E.card)
    (hQE : RootQuotaPackingStage124.packingEdges s u v w ⊆ E)
    (hne : ∀ j ∈ s, u j ≠ v j ∧ u j ≠ w j ∧ v j ≠ w j)
    (hdis : (s : Set I).PairwiseDisjoint
      (fun j => TypedCorrectionFamily.edges (u j) (v j) (w j))) (i : Fin 3) :
    sixQuota p (E \ RootQuotaPackingStage124.packingEdges s u v w) i =
      6 * ((q i : ℤ) - usage p s u v w i) := by
  rw [sixQuota_sdiff p E _ hQE i, sixQuota_packing p s u v w hne hdis i]
  have hq := hquota i
  unfold sixQuota
  omega

theorem residual_quota_nonneg_iff {I : Type*} (p : V → Fin 4)
    (E : Finset (Sym2 V)) (s : Finset I) (u v w : I → V) (q : Fin 3 → ℕ)
    (hquota : ∀ i, 6 * q i + 3 * (cuts p E i).card = 2 * E.card)
    (hQE : RootQuotaPackingStage124.packingEdges s u v w ⊆ E)
    (hne : ∀ j ∈ s, u j ≠ v j ∧ u j ≠ w j ∧ v j ≠ w j)
    (hdis : (s : Set I).PairwiseDisjoint
      (fun j => TypedCorrectionFamily.edges (u j) (v j) (w j))) (i : Fin 3) :
    0 ≤ sixQuota p (E \ RootQuotaPackingStage124.packingEdges s u v w) i ↔
      usage p s u v w i ≤ q i := by
  rw [residual_quota_exact p E s u v w q hquota hQE hne hdis i]
  omega

/-- A quota-safe physical packing leaves the explicit natural quotas `q - usage`.
Their total is the actual remaining internal inventory. -/
theorem residual_quotas {I : Type*} (p : V → Fin 4)
    (E : Finset (Sym2 V)) (s : Finset I) (u v w : I → V) (q : Fin 3 → ℕ)
    (hquota : ∀ i, 6 * q i + 3 * (cuts p E i).card = 2 * E.card)
    (hQE : RootQuotaPackingStage124.packingEdges s u v w ⊆ E)
    (hne : ∀ j ∈ s, u j ≠ v j ∧ u j ≠ w j ∧ v j ≠ w j)
    (hdis : (s : Set I).PairwiseDisjoint
      (fun j => TypedCorrectionFamily.edges (u j) (v j) (w j)))
    (hsafe : ∀ i, usage p s u v w i ≤ q i) :
    let R := E \ RootQuotaPackingStage124.packingEdges s u v w
    (∀ i, 6 * (q i - usage p s u v w i) + 3 * (cuts p R i).card = 2 * R.card) ∧
      (∑ i : Fin 3, (q i - usage p s u v w i)) = (internal p R).card := by
  let R := E \ RootQuotaPackingStage124.packingEdges s u v w
  have hnew : ∀ i, 6 * (q i - usage p s u v w i) +
      3 * (cuts p R i).card = 2 * R.card := by
    intro i
    have hi := residual_quota_exact p E s u v w q hquota hQE hne hdis i
    have hs := hsafe i
    change sixQuota p R i = _ at hi
    unfold sixQuota at hi
    omega
  refine ⟨hnew, ?_⟩
  change (∑ i : Fin 3, (q i - usage p s u v w i)) = (internal p R).card
  have hc := cuts_sum p R
  have hi := card_le_card (filter_subset (fun e => (e.map p).IsDiag) R)
  have h0 := hnew 0
  have h1 := hnew 1
  have h2 := hnew 2
  rw [Fin.sum_univ_three] at hc ⊢
  change (internal p R).card ≤ R.card at hi
  omega

end PartitionedTriangleAbsorption.ExceptionalQuotaStage142
