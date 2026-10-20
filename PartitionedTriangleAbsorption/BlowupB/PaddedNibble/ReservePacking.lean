/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibbleAdapter
public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveConcentration
public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveDegree
public import PartitionedTriangleAbsorption.ReserveCoverDown

/-!
# Physical blocks for the decomposable reserve

All selected blocks are whole triangles from an edge-disjoint packing. The
lemmas here connect the cube statistics to physical degrees and to witnesses
of common neighbourhoods in prescribed classes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking

open Finset Nibble ReserveTests TypedNibble

variable {V : Type*} [DecidableEq V] {m t : ℕ}

theorem card_star_edgesOf (S : TriSystem V m) (P : Finset (Fin m))
    (hpack : IsPacking S P) (v : V) :
    (star (edgesOf S P) v).card = 2 * (P.filter fun i => v ∈ S.tri i).card := by
  unfold edgesOf
  rw [S.star_biUnion, card_biUnion]
  · rw [sum_congr rfl (fun i hi => S.card_star_triEdges (mem_filter.mp hi).2),
      sum_const, smul_eq_mul, mul_comm]
  · intro i hi j hj hij
    exact (hpack i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij).mono
      (filter_subset _ _) (filter_subset _ _)

theorem packing_subset (S : TriSystem V m) (hpack : IsPacking S univ)
    (P : Finset (Fin m)) : IsPacking S P :=
  fun i _ j _ hij => hpack i (mem_univ _) j (mem_univ _) hij

theorem degree_touched (S : TriSystem V m) (hpack : IsPacking S univ)
    (x : Fin m → Bool) (v : V) :
    ((star (S.touched x) v).card : ℝ) = 2 * blockCount (S.through v) x := by
  have hcard := card_star_edgesOf S (retainedSet x) (packing_subset S hpack _) v
  change (star (S.touched x) v).card = _ at hcard
  rw [hcard, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  have heq : (retainedSet x).filter (fun i => v ∈ S.tri i) =
      (S.through v).filter (fun i => x i = true) := by
    ext i
    simp [retainedSet, TriSystem.through, and_comm]
  rw [heq]
  simp only [blockCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem touched_hasDecomp (S : TriSystem V m) (hpack : IsPacking S univ)
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (htyped : ∀ i, IsTypedTri p F (S.tri i)) (x : Fin m → Bool) :
    HasDecomp p F (S.touched x) := by
  refine ⟨(retainedSet x).image S.tri, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, rfl⟩ := mem_image.mp hT
    exact htyped i
  · intro T hT T' hT' hne
    obtain ⟨i, _, rfl⟩ := mem_image.mp hT
    obtain ⟨j, _, rfl⟩ := mem_image.mp hT'
    exact hpack i (mem_univ _) j (mem_univ _) (fun h => hne (by rw [h]))
  · rw [image_biUnion]
    rfl

theorem exists_block (S : TriSystem V m) {e : Sym2 V} (he : e ∈ edgesOf S univ) :
    ∃ i, e ∈ Nibble.triEdges (S.tri i) := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
  exact ⟨i, hi⟩

noncomputable def blockOf (S : TriSystem V m) (e : Sym2 V) (he : e ∈ edgesOf S univ) : Fin m :=
  Classical.choose (exists_block S he)

theorem blockOf_mem (S : TriSystem V m) (e : Sym2 V) (he : e ∈ edgesOf S univ) :
    e ∈ Nibble.triEdges (S.tri (blockOf S e he)) :=
  Classical.choose_spec (exists_block S he)

/-- One triangle affects at most two different common-neighbour witnesses,
including the case where it contains both roots. -/
theorem block_influence_le_two (S : TriSystem V m) {W : Type*} [DecidableEq W]
    (s : Finset W) (f : W → V) (hf : Function.Injective f) (u v : V)
    (a b : W → Fin m)
    (ha : ∀ w ∈ s, s(u, f w) ∈ Nibble.triEdges (S.tri (a w)))
    (hb : ∀ w ∈ s, s(v, f w) ∈ Nibble.triEdges (S.tri (b w))) (i : Fin m) :
    (s.filter fun w => a w = i ∨ b w = i).card ≤ 2 := by
  let A := s.filter fun w => a w = i ∨ b w = i
  have htri : ∀ w ∈ A, f w ∈ S.tri i := by
    intro w hw
    obtain ⟨hws, hw⟩ := mem_filter.mp hw
    rcases hw with hw | hw
    · have hh := ha w hws
      rw [hw] at hh
      exact (Nibble.mem_triEdges.mp hh).2.1
    · have hh := hb w hws
      rw [hw] at hh
      exact (Nibble.mem_triEdges.mp hh).2.1
  have hroot (r : V) (hr : r ∈ S.tri i) (hne : ∀ w ∈ s, f w ≠ r) : A.card ≤ 2 := by
    calc
      _ ≤ ((S.tri i).erase r).card := card_le_card_of_injOn f
        (fun w hw => mem_erase.mpr ⟨hne w (mem_filter.mp hw).1, htri w hw⟩)
        (fun w _ w' _ h => hf h)
      _ = 2 := by rw [card_erase_of_mem hr, S.card_tri]
  by_cases hA : A.Nonempty
  · obtain ⟨w, hw⟩ := hA
    obtain ⟨hws, hw⟩ := mem_filter.mp hw
    rcases hw with hw | hw
    · have hh := ha w hws
      rw [hw] at hh
      exact hroot u (Nibble.mem_triEdges.mp hh).1
        (fun w hw => (Nibble.mem_triEdges.mp (ha w hw)).2.2.symm)
    · have hh := hb w hws
      rw [hw] at hh
      exact hroot v (Nibble.mem_triEdges.mp hh).1
        (fun w hw => (Nibble.mem_triEdges.mp (hb w hw)).2.2.symm)
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ 2
    rw [he]
    norm_num

variable [Fintype V]

theorem through_card_le (S : TriSystem V m) (hpack : IsPacking S univ) (v : V) :
    2 * (S.through v).card ≤ Fintype.card V := by
  rw [TriSystem.through, ← card_star_edgesOf S univ hpack v]
  exact Nibble.card_star_le _ _

def coveredWitnesses (S : TriSystem V m) (p : V → Fin t) (u v : V) (k : Fin t) : Finset V :=
  univ.filter fun w => s(u, w) ∈ edgesOf S univ ∧ s(v, w) ∈ edgesOf S univ ∧ p w = k

theorem missing_neighbours_card_le (R : Finset (Sym2 V)) (u : V) :
    (univ.filter fun w => s(u, w) ∈ R).card ≤ (star R u).card := by
  apply card_le_card_of_injOn (fun w => s(u, w))
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2, by simp⟩
  · exact fun _ _ _ _ h => Sym2.congr_right.mp h

/-- Removing the uncovered edges loses at most two residual degrees from a
common neighbourhood. -/
theorem coveredWitnesses_card (S : TriSystem V m) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : SimpleGraph V) [DecidableRel J.Adj]
    (ω : ℝ) (hanti : AntiEdgeful p F J ω)
    (hleft : DegBounded (J.edgeFinset \ edgesOf S univ) (ω * Fintype.card V / 8))
    {u v : V} (huv : u ≠ v) {k : Fin t}
    (ht : ({p u, p v, k} : Multiset (Fin t)) ∈ F) :
    3 * ω * Fintype.card V / 4 ≤ (coveredWitnesses S p u v k).card := by
  classical
  let H := univ.filter fun w => J.Adj u w ∧ J.Adj w v ∧ p w = k
  let R := J.edgeFinset \ edgesOf S univ
  let U := univ.filter fun w => s(u, w) ∈ R
  let T := univ.filter fun w => s(v, w) ∈ R
  have hH : ω * Fintype.card V ≤ (H.card : ℝ) :=
    hanti _ ht _ _ _ rfl u v huv rfl rfl
  have hsub : H ⊆ (coveredWitnesses S p u v k ∪ U) ∪ T := by
    intro w hw
    obtain ⟨_, huw, hwv, hpw⟩ := mem_filter.mp hw
    by_cases hu : s(u, w) ∈ edgesOf S univ
    · by_cases hv : s(v, w) ∈ edgesOf S univ
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hu, hv, hpw⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, mem_sdiff.mpr
          ⟨J.mem_edgeFinset.mpr hwv.symm, hv⟩⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, mem_sdiff.mpr
        ⟨J.mem_edgeFinset.mpr huw, hu⟩⟩))
  have hcount : H.card ≤ (coveredWitnesses S p u v k).card + U.card + T.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hU : (U.card : ℝ) ≤ ω * Fintype.card V / 8 := by
    have hh : U.card ≤ (star R u).card := missing_neighbours_card_le R u
    have hhR : (U.card : ℝ) ≤ (star R u).card := by exact_mod_cast hh
    exact hhR.trans (hleft u)
  have hT : (T.card : ℝ) ≤ ω * Fintype.card V / 8 := by
    have hh : T.card ≤ (star R v).card := missing_neighbours_card_le R v
    have hhR : (T.card : ℝ) ≤ (star R v).card := by exact_mod_cast hh
    exact hhR.trans (hleft v)
  have hcountR : (H.card : ℝ) ≤ (coveredWitnesses S p u v k).card + U.card + T.card := by
    exact_mod_cast hcount
  linarith only [hH, hU, hT, hcountR]

#print axioms degree_touched
#print axioms touched_hasDecomp
#print axioms block_influence_le_two
#print axioms coveredWitnesses_card

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
