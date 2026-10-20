/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TorsionFinite

/-!
# Transport of the fixed torsion chain to physical finite edge sets

Old library pieces may overlap each other: only the pieces selected for one
later leftover must be disjoint. Private token realizations are pairwise
disjoint and avoid the common support of old pieces. Under exactly these
conditions, the fixed refined library yields a genuine physical partition.
-/

namespace PaddedF12.TorsionChain

open Finset

variable {α : Type*} [DecidableEq α]

def realize (P : Nat → Finset α) (tok : Atom → Finset α) : Atom → Finset α
  | .old j => P j
  | a => tok a

noncomputable def physicalPiece (N : Nat) (eps : Nat → Bool) (r : Nat)
    (P : Nat → Finset α) (tok : Atom → Finset α) (i : Index) : Finset α :=
  (atoms N eps r i).biUnion (realize P tok)

noncomputable def chosenOld (N : Nat) (choose : Nat → Bool) : Finset Nat :=
  (range N).filter (fun j => choose j = true)

omit [DecidableEq α] in
theorem realize_token {N r : Nat} {a : Atom} (P : Nat → Finset α) (tok : Atom → Finset α)
    (ha : a ∈ tokens N r) : realize P tok a = tok a := by
  cases a <;> simp only [realize]
  exact False.elim (mem_tokens.mp ha)

omit [DecidableEq α] in
theorem targetAtoms_pairwiseDisjoint_realize {N : Nat} {r : Nat} {choose : Nat → Bool}
    {P : Nat → Finset α} {tok : Atom → Finset α} {B : Finset α}
    (hsub : ∀ j < N, P j ⊆ B)
    (hdisold : (chosenOld N choose : Set Nat).PairwiseDisjoint P)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B) :
    (targetAtoms N r choose : Set Atom).PairwiseDisjoint (realize P tok) := by
  intro a ha b hb hab
  rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hb
    exact hdisold hj hk (fun h => hab (congrArg Atom.old h))
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    change Disjoint (P j) (realize P tok b)
    rw [realize_token P tok hb]
    exact ((havoid b hb).mono_right (hsub j (mem_range.mp (mem_filter.mp hj).1))).symm
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    change Disjoint (realize P tok a) (P j)
    rw [realize_token P tok ha]
    exact (havoid a ha).mono_right (hsub j (mem_range.mp (mem_filter.mp hj).1))
  · change Disjoint (realize P tok a) (realize P tok b)
    rw [realize_token P tok ha, realize_token P tok hb]
    exact hdis ha hb hab

theorem pairwiseDisjoint_physical_selected {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    {P : Nat → Finset α} {tok : Atom → Finset α} {B : Finset α}
    (hfinal : carry eps choose N = r)
    (hsub : ∀ j < N, P j ⊆ B)
    (hdisold : (chosenOld N choose : Set Nat).PairwiseDisjoint P)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B) :
    (selectedLibrary N eps choose : Set Index).PairwiseDisjoint (physicalPiece N eps r P tok) := by
  have hreal := targetAtoms_pairwiseDisjoint_realize hsub hdisold hdis havoid
  have hatoms := pairwiseDisjoint_atoms_selected hfinal
  have htarget : ∀ i ∈ selectedLibrary N eps choose,
      atoms N eps r i ⊆ targetAtoms N r choose := by
    intro i hi a ha
    rw [← biUnion_atoms_selected hfinal]
    exact mem_biUnion.mpr ⟨i, hi, ha⟩
  intro i hi j hj hne
  change Disjoint ((atoms N eps r i).biUnion (realize P tok))
    ((atoms N eps r j).biUnion (realize P tok))
  rw [disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  apply hreal (htarget i hi ha) (htarget j hj hb)
  intro hab
  exact disjoint_left.mp (hatoms hi hj hne) ha (hab ▸ hb)

theorem biUnion_physical_selected {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    (P : Nat → Finset α) (tok : Atom → Finset α)
    (hfinal : carry eps choose N = r) :
    (selectedLibrary N eps choose).biUnion (physicalPiece N eps r P tok) =
      (chosenOld N choose).biUnion P ∪ (tokens N r).biUnion tok := by
  unfold physicalPiece
  rw [← biUnion_biUnion, biUnion_atoms_selected hfinal, targetAtoms, union_biUnion, image_biUnion]
  congr 1
  apply biUnion_congr rfl
  intro a ha
  exact realize_token P tok ha

/-- Physical universality. The library and all its edge sets are fixed before
`choose`; a valid old partition is transported to a valid new partition. -/
theorem fixed_chain_physical_partition (N : Nat) (eps : Nat → Bool) (r : Nat)
    (P : Nat → Finset α) (tok : Atom → Finset α) (B : Finset α)
    (hsub : ∀ j < N, P j ⊆ B)
    (hdis : (tokens N r : Set Atom).PairwiseDisjoint tok)
    (havoid : ∀ a ∈ tokens N r, Disjoint (tok a) B) :
    ∀ choose : Nat → Bool,
      carry eps choose N = r →
      (chosenOld N choose : Set Nat).PairwiseDisjoint P →
      selectedLibrary N eps choose ⊆ library N eps r ∧
      (selectedLibrary N eps choose : Set Index).PairwiseDisjoint (physicalPiece N eps r P tok) ∧
      (selectedLibrary N eps choose).biUnion (physicalPiece N eps r P tok) =
        (chosenOld N choose).biUnion P ∪ (tokens N r).biUnion tok := by
  intro choose hfinal hdisold
  exact ⟨selectedLibrary_subset hfinal,
    pairwiseDisjoint_physical_selected hfinal hsub hdisold hdis havoid,
    biUnion_physical_selected P tok hfinal⟩

#print axioms pairwiseDisjoint_physical_selected
#print axioms biUnion_physical_selected
#print axioms fixed_chain_physical_partition

end PaddedF12.TorsionChain
