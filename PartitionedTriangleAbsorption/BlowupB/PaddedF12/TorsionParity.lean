/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TorsionRealization
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ParityEvaluation

@[expose] public section

/-!
# Parity, size and physical incidence of every fixed library member

The disjointness argument is local to each new member: it contains at most one
old piece, so overlapping members of the old library cause no assumption here.
-/

namespace PaddedF12.TorsionChain

open Finset

variable {α : Type*} [DecidableEq α]

theorem eq_old_of_mem_oldAtoms {i : Index} {a : Atom} (ha : a ∈ oldAtoms i) : a = .old i.row := by
  cases hs : i.useOld <;> simp [oldAtoms, hs] at ha
  exact ha

theorem atoms_pairwiseDisjoint_realize {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    {P : Nat → Finset α} {tok : Atom → Finset α} {B : Finset α}
    (hi : Valid N eps r i) (hsub : ∀ j < N, P j ⊆ B)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B) :
    (atoms N eps r i : Set Atom).PairwiseDisjoint (realize P tok) := by
  intro a ha b hb hab
  rw [atoms_decomposition hi] at ha hb
  rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
  · exact False.elim (hab ((eq_old_of_mem_oldAtoms ha).trans (eq_old_of_mem_oldAtoms hb).symm))
  · have hb' := tokenAtoms_subset_tokens hi hb
    rw [eq_old_of_mem_oldAtoms ha]
    change Disjoint (P i.row) (realize P tok b)
    rw [realize_token P tok hb']
    exact ((havoid b hb').mono_right (hsub i.row hi.1)).symm
  · have ha' := tokenAtoms_subset_tokens hi ha
    rw [eq_old_of_mem_oldAtoms hb]
    change Disjoint (realize P tok a) (P i.row)
    rw [realize_token P tok ha']
    exact (havoid a ha').mono_right (hsub i.row hi.1)
  · have ha' := tokenAtoms_subset_tokens hi ha
    have hb' := tokenAtoms_subset_tokens hi hb
    change Disjoint (realize P tok a) (realize P tok b)
    rw [realize_token P tok ha', realize_token P tok hb']
    exact hdis ha' hb' hab

theorem realize_property {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    {P : Nat → Finset α} {tok : Atom → Finset α} {H : Finset α → Prop}
    (hi : Valid N eps r i) (hold : ∀ j < N, H (P j))
    (htok : ∀ a ∈ tokens N r, H (tok a)) {a : Atom} (ha : a ∈ atoms N eps r i) :
    H (realize P tok a) := by
  have hall := atoms_subset_all hi ha
  rcases mem_union.mp hall with ho | ht
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp ho
    exact hold j (mem_range.mp hj)
  · rw [realize_token P tok ht]
    exact htok a ht

theorem physicalPiece_good {Good : Finset α → Prop} (q : ParityEvaluation Good)
    {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    {P : Nat → Finset α} {tok : Atom → Finset α} {B : Finset α}
    (hi : Valid N eps r i) (hsub : ∀ j < N, P j ⊆ B)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B)
    (hold : ∀ j < N, Good (P j)) (htok : ∀ a ∈ tokens N r, Good (tok a)) :
    Good (physicalPiece N eps r P tok i) := by
  exact q.good_biUnion _ _ (atoms_pairwiseDisjoint_realize hi hsub hdis havoid)
    (fun a ha => realize_property hi hold htok ha)

theorem physicalPiece_value_zero {Good : Finset α → Prop} (q : ParityEvaluation Good)
    {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    {P : Nat → Finset α} {tok : Atom → Finset α} {B : Finset α}
    (hi : Valid N eps r i) (hsub : ∀ j < N, P j ⊆ B)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B)
    (hold : ∀ j < N, Good (P j)) (htok : ∀ a ∈ tokens N r, Good (tok a))
    (heps : ∀ j < N, q.value (P j) = bit (eps j))
    (htval : ∀ a ∈ tokens N r, q.value (tok a) = 1) :
    q.value (physicalPiece N eps r P tok i) = 0 := by
  unfold physicalPiece
  rw [q.value_biUnion _ _ (atoms_pairwiseDisjoint_realize hi hsub hdis havoid)
    (fun a ha => realize_property hi hold htok ha)]
  have hs : (∑ a ∈ atoms N eps r i, q.value (realize P tok a)) =
      ∑ a ∈ atoms N eps r i, atomValue (fun j => bit (eps j)) a := by
    apply sum_congr rfl
    intro a ha
    have hall := atoms_subset_all hi ha
    rcases mem_union.mp hall with ho | ht
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp ho
      exact heps j (mem_range.mp hj)
    · rw [realize_token P tok ht, htval a ht]
      cases a <;> simp only [atomValue]
      exact False.elim (mem_tokens.mp ht)
  rw [hs, sum_atoms_value hi]
  exact piece_even hi

theorem physicalPiece_card_le {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    {P : Nat → Finset α} {tok : Atom → Finset α} {K g : Nat}
    (hi : Valid N eps r i) (hold : ∀ j < N, (P j).card ≤ K)
    (htok : ∀ a ∈ tokens N r, (tok a).card ≤ g) :
    (physicalPiece N eps r P tok i).card ≤ K + 3 * g := by
  rw [physicalPiece, atoms_decomposition hi, union_biUnion]
  have ho : ((oldAtoms i).biUnion (realize P tok)).card ≤ K := by
    cases hs : i.useOld
    · simp [oldAtoms, hs]
    · simpa [oldAtoms, hs, realize] using hold i.row hi.1
  have ht : ((tokenAtoms N eps r i).biUnion (realize P tok)).card ≤ 3 * g := by
    calc
      ((tokenAtoms N eps r i).biUnion (realize P tok)).card ≤
          ∑ a ∈ tokenAtoms N eps r i, (realize P tok a).card := card_biUnion_le
      _ ≤ ∑ a ∈ tokenAtoms N eps r i, g := by
        apply sum_le_sum
        intro a ha
        have ht := tokenAtoms_subset_tokens hi ha
        rw [realize_token P tok ht]
        exact htok a ht
      _ = (tokenAtoms N eps r i).card * g := by simp
      _ ≤ 3 * g := Nat.mul_le_mul_right g (card_tokenAtoms_le_three hi)
  exact (card_union_le _ _).trans (Nat.add_le_add ho ht)

/-- Any additive nonnegative physical edge load obeys the 2/4 occurrence bound. -/
theorem physical_weighted_incidence_le (N : Nat) (eps : Nat → Bool) (r : Nat)
    (P : Nat → Finset α) (tok : Atom → Finset α) (B : Finset α) (w : α → Nat)
    (hsub : ∀ j < N, P j ⊆ B)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B) :
    ∑ i ∈ library N eps r, ∑ e ∈ physicalPiece N eps r P tok i, w e ≤
      2 * ∑ j ∈ range N, ∑ e ∈ P j, w e + 4 * ∑ a ∈ tokens N r, ∑ e ∈ tok a, w e := by
  have h := weighted_incidence_le N eps r (fun a => ∑ e ∈ realize P tok a, w e)
  have hl : (∑ i ∈ library N eps r, ∑ e ∈ physicalPiece N eps r P tok i, w e) =
      ∑ i ∈ library N eps r, ∑ a ∈ atoms N eps r i, ∑ e ∈ realize P tok a, w e := by
    apply sum_congr rfl
    intro i hi
    exact sum_biUnion (atoms_pairwiseDisjoint_realize (mem_library.mp hi) hsub hdis havoid)
  rw [hl]
  have ht : (∑ a ∈ tokens N r, ∑ e ∈ realize P tok a, w e) =
      ∑ a ∈ tokens N r, ∑ e ∈ tok a, w e := by
    apply sum_congr rfl
    intro a ha
    rw [realize_token P tok ha]
  rw [ht] at h
  simpa only [realize] using h

#print axioms physicalPiece_good
#print axioms physicalPiece_value_zero
#print axioms physicalPiece_card_le
#print axioms physical_weighted_incidence_le

end PaddedF12.TorsionChain
