/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ThreePairPackingStage124
public import PartitionedTriangleAbsorption.F3ReserveTrimStage109

/-! # Exact category counts in the three-pair slot construction

Every root, regardless of its colour, contributes once to each opposite-edge
category. Thus no balance assumption on the root colour classes is needed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQuotaPackingStage124

open Finset F3ReserveTrimStage109

theorem pair_category_count : ∀ (i : Fin 4) (c : Fin 3),
    (∑ j : Fin 3, if categoryTab (pairLeft i j) (pairRight i j) = c then (1 : ℕ) else 0) = 1 := by
  decide

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem slot_category_card (p : V → Fin 4) (X : Finset V) (L : ℕ) (c : Fin 3) :
    ((univ : Finset (Slot X L)).filter fun i =>
      categoryTab (pairLeft (p i.1.val) i.2.1) (pairRight (p i.1.val) i.2.1) = c).card =
      X.card * L := by
  classical
  rw [← Nat.cast_id ((univ : Finset (Slot X L)).filter fun i =>
    categoryTab (pairLeft (p i.1.val) i.2.1) (pairRight (p i.1.val) i.2.1) = c).card,
    ← sum_boole]
  change (∑ i : {x // x ∈ X} × Fin 3 × Fin L,
    if categoryTab (pairLeft (p i.1.val) i.2.1) (pairRight (p i.1.val) i.2.1) = c
      then (1 : ℕ) else 0) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  change (∑ x : {x // x ∈ X}, ∑ j : Fin 3, ∑ _ : Fin L,
    if categoryTab (pairLeft (p x.val) j) (pairRight (p x.val) j) = c
      then (1 : ℕ) else 0) = _
  have hL (k : ℕ) : (∑ _ : Fin L, k) = L * k := by simp
  simp_rw [hL]
  simp_rw [← mul_sum, pair_category_count]
  simp [Nat.mul_comm]

theorem physical_slot_category_card (p : V → Fin 4) (X : Finset V) (L : ℕ)
    (a b : Slot X L → V)
    (ha : ∀ i, p (a i) = pairLeft (p i.1.val) i.2.1)
    (hb : ∀ i, p (b i) = pairRight (p i.1.val) i.2.1)
    (hd : ((univ : Finset (Slot X L)) : Set (Slot X L)).PairwiseDisjoint
      (fun i => TypedCorrectionFamily.edges i.1.val (a i) (b i))) (c : Fin 3) :
    ((triples univ (fun i : Slot X L => i.1.val) a b).filter
      fun r => category p s(r.2.1, r.2.2) = c).card = X.card * L := by
  classical
  rw [triples_query_card univ (fun i : Slot X L => i.1.val) a b hd]
  have he : (fun i : Slot X L => category p s(a i, b i) = c) =
      (fun i => categoryTab (pairLeft (p i.1.val) i.2.1)
        (pairRight (p i.1.val) i.2.1) = c) := by
    funext i
    simp only [category, Sym2.lift_mk, ha, hb]
  change ((univ : Finset (Slot X L)).filter
    (fun i => category p s(a i, b i) = c)).card = _
  simpa only [he] using slot_category_card p X L c

end PartitionedTriangleAbsorption.RootQuotaPackingStage124
