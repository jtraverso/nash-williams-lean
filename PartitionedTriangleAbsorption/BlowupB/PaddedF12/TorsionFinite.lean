/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TorsionChain
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.SplitIfs

/-!
# The universal torsion chain as finite libraries

This module supplies the finite sets and actual cardinality bounds needed to
transport `TorsionChain.fixed_chain_refines` to physical edge sets. The library
is built before the subsequently selected old pieces.
-/

namespace PaddedF12.TorsionChain

open Finset

noncomputable def rawLibrary (N : Nat) : Finset Index :=
  (((range N).product ({false, true} : Finset Bool)).product (range 2)).image
    (fun x => ⟨x.1.1, x.1.2, x.2⟩)

noncomputable def library (N : Nat) (eps : Nat → Bool) (r : Nat) : Finset Index :=
  by classical exact (rawLibrary N).filter (Valid N eps r)

theorem mem_rawLibrary {N : Nat} {i : Index} :
    i ∈ rawLibrary N ↔ i.row < N ∧ i.before < 2 := by
  rcases i with ⟨j, s, b⟩
  constructor
  · intro hi
    obtain ⟨⟨⟨j', s'⟩, b'⟩, hmem, heq⟩ := mem_image.mp hi
    cases heq
    have hprod := mem_product.mp hmem
    exact ⟨mem_range.mp (mem_product.mp hprod.1).1, mem_range.mp hprod.2⟩
  · rintro ⟨hj, hb⟩
    refine mem_image.mpr ⟨((j, s), b), ?_, rfl⟩
    apply mem_product.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr hj, ?_⟩, mem_range.mpr hb⟩
    cases s <;> simp

theorem mem_library {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index} :
    i ∈ library N eps r ↔ Valid N eps r i := by
  simp only [library, mem_filter, mem_rawLibrary]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

theorem card_library_le (N : Nat) (eps : Nat → Bool) (r : Nat) :
    (library N eps r).card ≤ 4 * N := by
  classical
  calc
    (library N eps r).card ≤ (rawLibrary N).card := card_filter_le _ _
    _ ≤ (((range N).product ({false, true} : Finset Bool)).product (range 2)).card := card_image_le
    _ = 4 * N := by simp [card_product]; omega

/-- Every token identity in the fixed enlarged remainder. -/
noncomputable def tokens (N r : Nat) : Finset Atom :=
  (range (N - 1)).image Atom.wireA ∪ (range (N - 1)).image Atom.wireB ∪
    (if 0 < N ∧ r = 1 then {Atom.tail} else ∅)

theorem mem_tokens {N r : Nat} {a : Atom} :
    a ∈ tokens N r ↔
      match a with
      | .old _ => False
      | .wireA j => j + 1 < N
      | .wireB j => j + 1 < N
      | .tail => 0 < N ∧ r = 1 := by
  cases a <;> by_cases ht : 0 < N ∧ r = 1 <;> simp [tokens, ht] <;> omega

theorem card_tokens_le (N r : Nat) : (tokens N r).card ≤ 2 * N := by
  unfold tokens
  have ha : ((range (N - 1)).image Atom.wireA).card ≤ N - 1 := by
    exact card_image_le.trans (by simp)
  have hb : ((range (N - 1)).image Atom.wireB).card ≤ N - 1 := by
    exact card_image_le.trans (by simp)
  by_cases ht : 0 < N ∧ r = 1
  · simp [ht]
    have h1 := card_union_le ((range (N - 1)).image Atom.wireA)
      ((range (N - 1)).image Atom.wireB)
    have h2 := card_union_le (((range (N - 1)).image Atom.wireA) ∪
      ((range (N - 1)).image Atom.wireB)) ({Atom.tail} : Finset Atom)
    simp only [card_singleton] at h2
    omega
  · simp [ht]
    exact (card_union_le _ _).trans (by omega)

/-- The whole atoms occurring in one library piece. -/
noncomputable def atoms (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) : Finset Atom :=
  (if i.useOld then {Atom.old i.row} else ∅) ∪
  (if 0 < i.row ∧ i.before = 1 then {Atom.wireB (i.row - 1)} else ∅) ∪
  (if i.row + 1 < N then
    {Atom.wireA i.row} ∪ (if after eps i = 0 then {Atom.wireB i.row} else ∅) else ∅) ∪
  (if i.row + 1 = N ∧ r = 1 then {Atom.tail} else ∅)

theorem mem_atoms {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index} {a : Atom}
    (hi : Valid N eps r i) : a ∈ atoms N eps r i ↔ Contains N eps r i a := by
  have hr := hi.1
  cases a <;> cases hs : i.useOld <;>
    by_cases hin : 0 < i.row ∧ i.before = 1 <;>
    by_cases hout : i.row + 1 < N <;>
    by_cases hz : after eps i = 0 <;>
    by_cases ht : i.row + 1 = N ∧ r = 1 <;>
    simp [atoms, Contains, hs, hin, hout, hz, ht] <;> omega

noncomputable def selectedLibrary (N : Nat) (eps choose : Nat → Bool) : Finset Index :=
  (range N).image (selected eps choose)

noncomputable def targetAtoms (N r : Nat) (choose : Nat → Bool) : Finset Atom :=
  ((range N).filter fun j => choose j = true).image Atom.old ∪ tokens N r

theorem mem_targetAtoms {N r : Nat} {choose : Nat → Bool} {a : Atom} :
    a ∈ targetAtoms N r choose ↔ Target N r choose a := by
  cases a <;> simp [targetAtoms, mem_tokens, Target]

theorem selectedLibrary_subset {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    (hfinal : carry eps choose N = r) :
    selectedLibrary N eps choose ⊆ library N eps r := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
  exact mem_library.mpr (selected_valid hfinal (mem_range.mp hj))

theorem biUnion_atoms_selected {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    (hfinal : carry eps choose N = r) :
    (selectedLibrary N eps choose).biUnion (atoms N eps r) = targetAtoms N r choose := by
  ext a
  rw [mem_biUnion, mem_targetAtoms]
  constructor
  · rintro ⟨i, hi, hai⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    have hj' := mem_range.mp hj
    exact selected_no_extra hj' ((mem_atoms (selected_valid hfinal hj')).mp hai)
  · intro ha
    obtain ⟨j, hj, ha⟩ := selected_covers (eps := eps) ha
    exact ⟨selected eps choose j, mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩,
      (mem_atoms (selected_valid hfinal hj)).mpr ha⟩

theorem pairwiseDisjoint_atoms_selected {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    (hfinal : carry eps choose N = r) :
    (selectedLibrary N eps choose : Set Index).PairwiseDisjoint (atoms N eps r) := by
  intro i hi j hj hne
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hj
  change Disjoint _ _
  rw [disjoint_left]
  intro a hak hal
  have hk' := mem_range.mp hk
  have hl' := mem_range.mp hl
  have hkl := selected_disjoint
    ((mem_atoms (selected_valid hfinal hk')).mp hak)
    ((mem_atoms (selected_valid hfinal hl')).mp hal)
  exact hne (congrArg (selected eps choose) hkl)

theorem carry_eq_sum_mod (N : Nat) (eps choose : Nat → Bool) :
    carry eps choose N = (∑ j ∈ range N, if choose j then bit (eps j) else 0) % 2 := by
  induction N with
  | zero => simp [carry]
  | succ N ih =>
    rw [carry, ih, sum_range_succ]
    omega

/-- Actual finite occurrence counts, derived from the two/four-slot injection. -/
theorem occurrence_card_le (N : Nat) (eps : Nat → Bool) (r : Nat) (a : Atom) :
    ((library N eps r).filter (fun i => a ∈ atoms N eps r i)).card ≤
      (match a with | .old _ => 2 | _ => 4) := by
  let cap : Nat := match a with | .old _ => 2 | _ => 4
  have h := card_le_card_of_injOn (localSlot a)
    (s := (library N eps r).filter (fun i => a ∈ atoms N eps r i)) (t := range cap)
    (fun i hi => mem_range.mpr (localSlot_bound (mem_library.mp (mem_filter.mp hi).1)))
    (by
      intro i hi j hj heq
      have hiv := mem_library.mp (mem_filter.mp hi).1
      have hjv := mem_library.mp (mem_filter.mp hj).1
      exact localSlot_injective hiv hjv
        ((mem_atoms hiv).mp (mem_filter.mp hi).2)
        ((mem_atoms hjv).mp (mem_filter.mp hj).2) heq)
  simpa [cap] using h

/-- Distinguish private tokens from the optional old atom. -/
def isToken : Atom → Bool
  | .old _ => false
  | _ => true

noncomputable def tokenAtoms (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) : Finset Atom :=
  (atoms N eps r i).filter (fun a => isToken a = true)

theorem card_tokenAtoms (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) :
    (tokenAtoms N eps r i).card = tokenCount N eps r i := by
  rcases i with ⟨row, useOld, before⟩
  cases row <;> cases useOld <;>
    unfold tokenAtoms atoms tokenCount <;> dsimp only <;>
    split_ifs <;> simp_all [isToken, filter_insert, filter_singleton]

theorem card_tokenAtoms_le_three {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) : (tokenAtoms N eps r i).card ≤ 3 := by
  rw [card_tokenAtoms]
  exact tokenCount_le_three hi

noncomputable def allAtoms (N r : Nat) : Finset Atom :=
  (range N).image Atom.old ∪ tokens N r

theorem atoms_subset_all {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) : atoms N eps r i ⊆ allAtoms N r := by
  intro a ha
  have h := (mem_atoms hi).mp ha
  have hr := hi.1
  cases a with
  | old j =>
    change i.row = j ∧ _ at h
    exact mem_union_left _ (mem_image.mpr ⟨j, mem_range.mpr (by omega), rfl⟩)
  | wireA j =>
    apply mem_union_right
    apply mem_tokens.mpr
    change i.row = j ∧ i.row + 1 < N at h
    omega
  | wireB j =>
    apply mem_union_right
    apply mem_tokens.mpr
    change (i.row = j ∧ i.row + 1 < N ∧ _) ∨ (i.row = j + 1 ∧ _) at h
    omega
  | tail =>
    apply mem_union_right
    apply mem_tokens.mpr
    change i.row + 1 = N ∧ r = 1 at h
    omega

theorem old_disjoint_tokens (N r : Nat) :
    Disjoint ((range N).image Atom.old) (tokens N r) := by
  rw [disjoint_left]
  intro a ha ht
  obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
  exact (mem_tokens.mp ht)

/-- Double-counting with the explicit local-slot bounds. -/
theorem weighted_incidence_le (N : Nat) (eps : Nat → Bool) (r : Nat) (w : Atom → Nat) :
    ∑ i ∈ library N eps r, ∑ a ∈ atoms N eps r i, w a ≤
      2 * ∑ j ∈ range N, w (.old j) + 4 * ∑ a ∈ tokens N r, w a := by
  classical
  have hdouble :
      (∑ i ∈ library N eps r, ∑ a ∈ atoms N eps r i, w a) =
      ∑ a ∈ allAtoms N r,
        ((library N eps r).filter (fun i => a ∈ atoms N eps r i)).card * w a := by
    calc
      (∑ i ∈ library N eps r, ∑ a ∈ atoms N eps r i, w a) =
          ∑ i ∈ library N eps r, ∑ a ∈ allAtoms N r,
            if a ∈ atoms N eps r i then w a else 0 := by
        apply sum_congr rfl
        intro i hi
        rw [← sum_filter]
        congr 1
        ext a
        simp only [mem_filter]
        exact ⟨fun ha => ⟨atoms_subset_all (mem_library.mp hi) ha, ha⟩, fun ha => ha.2⟩
      _ = ∑ a ∈ allAtoms N r, ∑ i ∈ library N eps r,
            if a ∈ atoms N eps r i then w a else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        rw [← sum_filter]
        simp [sum_const, mul_comm]
  rw [hdouble]
  calc
    (∑ a ∈ allAtoms N r,
        ((library N eps r).filter (fun i => a ∈ atoms N eps r i)).card * w a) ≤
        ∑ a ∈ allAtoms N r, (match a with | .old _ => 2 | _ => 4) * w a := by
      exact sum_le_sum fun a ha => Nat.mul_le_mul_right (w a) (occurrence_card_le N eps r a)
    _ = _ := by
      rw [allAtoms, sum_union (old_disjoint_tokens N r), sum_image]
      · simp only
        rw [← mul_sum]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro a ha
        cases a <;> simp only
        exact False.elim (mem_tokens.mp ha)
      · intro i hi j hj h
        exact Atom.old.inj h

noncomputable def oldAtoms (i : Index) : Finset Atom :=
  if i.useOld then {Atom.old i.row} else ∅

theorem atoms_decomposition {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) : atoms N eps r i = oldAtoms i ∪ tokenAtoms N eps r i := by
  ext a
  constructor
  · intro ha
    cases a with
    | old j =>
      have h := (mem_atoms hi).mp ha
      change i.row = j ∧ i.useOld = true at h
      apply mem_union_left
      simp [oldAtoms, h.2, h.1]
    | wireA j => exact mem_union_right _ (mem_filter.mpr ⟨ha, rfl⟩)
    | wireB j => exact mem_union_right _ (mem_filter.mpr ⟨ha, rfl⟩)
    | tail => exact mem_union_right _ (mem_filter.mpr ⟨ha, rfl⟩)
  · intro ha
    rcases mem_union.mp ha with hold | ht
    · cases hs : i.useOld <;> simp [oldAtoms, hs] at hold
      subst a
      exact (mem_atoms hi).mpr ⟨rfl, hs⟩
    · exact (mem_filter.mp ht).1

theorem oldAtoms_disjoint_tokenAtoms (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) :
    Disjoint (oldAtoms i) (tokenAtoms N eps r i) := by
  rw [disjoint_left]
  intro a ha ht
  cases hs : i.useOld <;> simp [oldAtoms, hs] at ha
  subst a
  have his := (mem_filter.mp ht).2
  simp [isToken] at his

theorem tokenAtoms_subset_tokens {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) : tokenAtoms N eps r i ⊆ tokens N r := by
  intro a ha
  have his := (mem_filter.mp ha).2
  have hmem := atoms_subset_all hi (mem_filter.mp ha).1
  rcases mem_union.mp hmem with hmem | hmem
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hmem
    simp [isToken] at his
  · exact hmem

def atomValue (v : Nat → Nat) : Atom → Nat
  | .old j => v j
  | _ => 1

theorem sum_atoms_value {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) (v : Nat → Nat) :
    (∑ a ∈ atoms N eps r i, atomValue v a) =
      (if i.useOld then v i.row else 0) + tokenCount N eps r i := by
  rw [atoms_decomposition hi, sum_union (oldAtoms_disjoint_tokenAtoms N eps r i)]
  have hold : (∑ a ∈ oldAtoms i, atomValue v a) = if i.useOld then v i.row else 0 := by
    cases hs : i.useOld <;> simp [oldAtoms, hs, atomValue]
  have htok : (∑ a ∈ tokenAtoms N eps r i, atomValue v a) = (tokenAtoms N eps r i).card := by
    calc
      (∑ a ∈ tokenAtoms N eps r i, atomValue v a) = ∑ a ∈ tokenAtoms N eps r i, (1 : Nat) := by
        apply sum_congr rfl
        intro a ha
        have his := (mem_filter.mp ha).2
        cases a <;> simp only [atomValue]
        simp [isToken] at his
      _ = _ := by simp
  rw [hold, htok, card_tokenAtoms]

#print axioms sum_atoms_value

#print axioms card_tokenAtoms
#print axioms weighted_incidence_le

#print axioms card_library_le
#print axioms card_tokens_le
#print axioms biUnion_atoms_selected
#print axioms pairwiseDisjoint_atoms_selected
#print axioms occurrence_card_le

end PaddedF12.TorsionChain
