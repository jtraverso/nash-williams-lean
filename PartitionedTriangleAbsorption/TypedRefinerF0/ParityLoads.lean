/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ParityRealize

/-! # Loads and sizes of the realised parity refiner

For the whole (even) library, not only a selected sublibrary:
* the incidence at an old vertex `inl u` is at most `33 · (deg + rootLoad)`;
* the incidence at a middle vertex `inr r` is at most `66`;
* every piece has at most `22` edges, and the total size of the library is linear in the
  total number of links of the hierarchy.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection UniversalRefiner

variable {U : Type*} [DecidableEq U]

theorem card_physA_le (rt : Req U → U × U) (a : Atom U) : (physA rt a).card ≤ 2 := by
  rcases a with r | e
  · exact card_le_two
  · simp [physA]

theorem card_physE_le (rt : Req U → U × U) (A : Finset (Atom U)) :
    (physE rt A).card ≤ 2 * A.card := by
  unfold physE
  refine card_biUnion_le.trans ?_
  calc ∑ a ∈ A, (physA rt a).card ≤ ∑ _a ∈ A, 2 := sum_le_sum fun a _ => card_physA_le rt a
    _ = 2 * A.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Root weight of an atom at an old vertex. -/
def oldW (rt : Req U → U × U) (u : U) : Atom U → ℕ
  | Sum.inl r => (if (rt r).1 = u then 1 else 0) + (if (rt r).2 = u then 1 else 0)
  | Sum.inr e => if u ∈ e then 1 else 0

theorem incidentLoad_physA_inl_le (rt : Req U → U × U) (a : Atom U) (u : U) :
    incidentLoad (physA rt a) (Sum.inl u) ≤ oldW rt u a := by
  rcases a with r | e
  · have key : ∀ a b : Sym2 (WP U), (({a, b} : Finset _).filter fun e => Sum.inl u ∈ e).card ≤
        (if Sum.inl u ∈ a then 1 else 0) + (if Sum.inl u ∈ b then 1 else 0) := by
      intro a b
      rw [filter_insert, filter_singleton]
      split_ifs <;> first | exact card_le_two | simp
    refine (key _ _).trans ?_
    simp only [oldW, Sym2.mem_iff, Sum.inl.injEq, reduceCtorEq, or_false]
    have h1 : u = (rt r).1 ↔ (rt r).1 = u := eq_comm
    have h2 : u = (rt r).2 ↔ (rt r).2 = u := eq_comm
    simp only [h1, h2, le_refl]
  · simp only [physA, oldW, incidentLoad, filter_singleton]
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Sym2.map_mk, Sym2.mem_iff, Sum.inl.injEq]
      split_ifs <;> simp_all

theorem incidentLoad_physA_inr_le (rt : Req U → U × U) (a : Atom U) (r : Req U) :
    incidentLoad (physA rt a) (Sum.inr r) ≤ if a = Sum.inl r then 2 else 0 := by
  rcases a with r' | e
  · simp only [physA, incidentLoad, Sum.inl.injEq]
    split_ifs with h
    · exact (card_filter_le _ _).trans card_le_two
    · rw [filter_insert, filter_singleton]
      have h' : r ≠ r' := fun e => h e.symm
      simp [Sym2.mem_iff, h']
  · simp only [physA, incidentLoad, filter_singleton, reduceCtorEq, ite_false]
    induction e using Sym2.ind with
    | _ x y => simp [Sym2.map_mk, Sym2.mem_iff]

section Library

variable [Fintype U] (X : Finset (Sym2 U)) (hmap : ℕ → U → U) (L : ℕ) (base : U)

/-- All atoms of the parity layer. -/
def allAtoms : Finset (Atom U) := parRem X hmap L ∪ adjRem 0 ∪ X.image Sum.inr

theorem sum_evenLib_le (g : Atom U → ℕ) :
    ∑ i ∈ evenLib X hmap L base, ∑ a ∈ UniversalRefiner.piece X hmap i, g a ≤
      33 * ∑ a ∈ allAtoms X hmap L, g a :=
  (sum_le_sum_of_subset (evenLib_subset base)).trans
    (sum_pieces_le X hmap L 0 _ (fun _ hi => piece_subset X hmap L 0 hi) g)

theorem sum_allAtoms (g : Atom U → ℕ) :
    ∑ a ∈ allAtoms X hmap L, g a =
      ∑ r ∈ parReqs X hmap L, g (Sum.inl r) + ∑ e ∈ X, g (Sum.inr e) := by
  rw [allAtoms, adjRem_zero, union_empty, sum_union disjoint_parRem_inr, parRem_eq,
    sum_image (fun _ _ _ _ h => Sum.inl_injective h),
    sum_image (fun _ _ _ _ h => Sum.inr_injective h)]

theorem card_allAtoms_le :
    (allAtoms X hmap L).card ≤ 8 * ∑ l ∈ range L, (links X hmap l).card + X.card := by
  have h := sum_allAtoms X hmap L (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at h
  rw [h]
  have := card_parReqs_le X hmap L
  omega

/-- **Whole-library load at an old vertex.** -/
theorem sum_evenLib_load_inl (u : U) :
    ∑ i ∈ evenLib X hmap L base,
        incidentLoad (physE (rtP hmap base) (UniversalRefiner.piece X hmap i)) (Sum.inl u) ≤
      33 * ((vChain X u).card + ∑ l ∈ range L, (2 * (vChain (links X hmap l) u).card +
        10 * hubWeight (links X hmap l) (hmap l) u)) := by
  have h1 : ∀ i ∈ evenLib X hmap L base,
      incidentLoad (physE (rtP hmap base) (UniversalRefiner.piece X hmap i)) (Sum.inl u) ≤
        ∑ a ∈ UniversalRefiner.piece X hmap i, oldW (rtP hmap base) u a := by
    intro i _
    rw [incidentLoad_physE]
    exact sum_le_sum fun a _ => incidentLoad_physA_inl_le _ a u
  refine (sum_le_sum h1).trans ((sum_evenLib_le X hmap L base _).trans ?_)
  refine Nat.mul_le_mul_left 33 ?_
  rw [sum_allAtoms]
  have hR := parRootLoad_le X hmap L (fun _ => (base, base)) (base, base) u
  have hE : ∑ e ∈ X, oldW (rtP hmap base) u (Sum.inr e) = (vChain X u).card := by
    simp only [oldW, vChain]
    rw [card_filter]
  have hQ : ∑ r ∈ parReqs X hmap L, oldW (rtP hmap base) u (Sum.inl r) =
      rootLoad (parReqs X hmap L) (fun r => (rootPair hmap (fun _ => (base, base))
        (base, base) r).1)
        (fun r => (rootPair hmap (fun _ => (base, base)) (base, base) r).2) u := by
    simp only [oldW, rootLoad, card_filter, sum_add_distrib]
    rfl
  rw [hE, hQ]
  omega

/-- **Whole-library load at a middle vertex.** -/
theorem sum_evenLib_load_inr (r : Req U) :
    ∑ i ∈ evenLib X hmap L base,
        incidentLoad (physE (rtP hmap base) (UniversalRefiner.piece X hmap i))
          (Sum.inr r) ≤ 66 := by
  have h1 : ∀ i ∈ evenLib X hmap L base,
      incidentLoad (physE (rtP hmap base) (UniversalRefiner.piece X hmap i)) (Sum.inr r) ≤
        ∑ a ∈ UniversalRefiner.piece X hmap i, (if a = Sum.inl r then 2 else 0) := by
    intro i _
    rw [incidentLoad_physE]
    exact sum_le_sum fun a _ => incidentLoad_physA_inr_le _ a r
  refine (sum_le_sum h1).trans ((sum_evenLib_le X hmap L base _).trans ?_)
  have : ∑ a ∈ allAtoms X hmap L, (if a = Sum.inl r then 2 else 0) ≤ 2 := by
    rw [sum_ite_eq']
    split_ifs <;> omega
  omega

/-- Every piece of the parity library has at most `22` edges. -/
theorem card_physE_piece_le {i : LibIdx U} (hi : i ∈ evenLib X hmap L base) :
    (physE (rtP hmap base) (UniversalRefiner.piece X hmap i)).card ≤ 22 := by
  refine (card_physE_le _ _).trans ?_
  have hi' := (mem_filter.mp hi).1
  obtain ⟨l, -, hl⟩ := mem_parLib.mp hi'
  rcases mem_levelLib.mp hl with ⟨π, -, x, ca, cb, cs, rfl⟩ | ⟨σ, -, rfl⟩
  · have := card_altAtoms_le (Λ := links X hmap l) (h := hmap l) (l := l) π x ca cb cs
    change 2 * (altAtoms (links X hmap l) (hmap l) l π x ca cb cs).card ≤ 22
    omega
  · change 2 * (cycAtoms l σ).card ≤ 22
    have : (cycAtoms (V := U) l σ).card ≤ 2 := card_le_two
    omega

/-- Total size of the parity library. -/
theorem sum_card_physE_le :
    ∑ i ∈ evenLib X hmap L base, (physE (rtP hmap base) (UniversalRefiner.piece X hmap i)).card ≤
      66 * (8 * ∑ l ∈ range L, (links X hmap l).card + X.card) := by
  have h1 : ∀ i ∈ evenLib X hmap L base,
      (physE (rtP hmap base) (UniversalRefiner.piece X hmap i)).card ≤
        ∑ a ∈ UniversalRefiner.piece X hmap i, 2 := by
    intro i _
    rw [sum_const, smul_eq_mul, mul_comm]
    exact card_physE_le _ _
  refine (sum_le_sum h1).trans ((sum_evenLib_le X hmap L base _).trans ?_)
  rw [sum_const, smul_eq_mul]
  have := card_allAtoms_le X hmap L
  nlinarith

theorem card_evenLib_le :
    (evenLib X hmap L base).card ≤ 17 * ∑ l ∈ range L, (links X hmap l).card :=
  (card_filter_le _ _).trans (card_parLib_le X hmap L)

end Library

end PartitionedTriangleAbsorption.TypedRefinerF0
