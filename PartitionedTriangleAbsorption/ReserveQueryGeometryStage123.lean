/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.DisjointQueriesStage123

/-! # Physical dependencies of self-excluding reserve queries -/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveQueryGeometryStage123

open Finset CoverDownStage105 SelectedCoverDownStage122

variable {V : Type*} [DecidableEq V]

def connectors (y z : V) (r : V × V × V) : Finset (Sym2 V) :=
  {s(y, r.2.1), s(r.2.2, z)}

def owners (T : Finset (V × V × V)) (C : Finset (Sym2 V)) : Finset (V × V × V) :=
  T.filter fun r => ¬ Disjoint C (resTri r)

def queryBlock (T : Finset (V × V × V)) (y z : V) (r : V × V × V) :
    Finset (V × V × V) := insert r (owners T (connectors y z r))

theorem owners_card_le (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) (C : Finset (Sym2 V)) :
    (owners T C).card ≤ C.card := by
  classical
  have hex : ∀ r ∈ owners T C, ∃ e ∈ C, e ∈ resTri r := by
    intro r hr
    exact not_disjoint_iff.mp (mem_filter.mp hr).2
  choose f hfC hfr using hex
  let g : {r // r ∈ owners T C} → {e // e ∈ C} :=
    fun r => ⟨f r.val r.property, hfC r.val r.property⟩
  have hg : Function.Injective g := by
    intro r r' heq
    apply Subtype.ext
    have he : f r.val r.property = f r'.val r'.property := congrArg Subtype.val heq
    by_contra hn
    exact disjoint_left.mp
      (hd (mem_filter.mp r.property).1 (mem_filter.mp r'.property).1 hn)
      (hfr r.val r.property) (he ▸ hfr r'.val r'.property)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

theorem queryBlock_card_le (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) (y z : V) (r : V × V × V) :
    (queryBlock T y z r).card ≤ 3 := by
  have h1 := card_insert_le r (owners T (connectors y z r))
  have h2 := owners_card_le T hd (connectors y z r)
  have h3 : (connectors y z r).card ≤ 2 := by
    exact (card_insert_le _ _).trans (by simp)
  change (insert r (owners T (connectors y z r))).card ≤ 3
  omega

theorem owner_meeting (T : Finset (V × V × V)) (y z : V) (r j : V × V × V)
    (hj : j ∈ owners T (connectors y z r)) :
    r.2.1 ∈ ({j.1, j.2.1, j.2.2} : Finset V) ∨
      r.2.2 ∈ ({j.1, j.2.1, j.2.2} : Finset V) := by
  obtain ⟨e, hec, hej⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2
  simp only [connectors, mem_insert, mem_singleton] at hec
  rcases hec with rfl | rfl
  · left
    simp only [resTri, mem_insert, mem_singleton] at hej
    rcases hej with h | h | h <;> rcases Sym2.eq_iff.mp h with h | h <;>
      simp_all
  · right
    simp only [resTri, mem_insert, mem_singleton] at hej
    rcases hej with h | h | h <;> rcases Sym2.eq_iff.mp h with h | h <;>
      simp_all

/-- A coordinate is read by at most four candidates at one fixed root:
it is the candidate itself, or a connector owner meeting its three vertices. -/
theorem queryBlock_read_le (T S : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) (hST : S ⊆ T)
    (x y z : V) (hroot : ∀ r ∈ S, r.1 = x) (j : V × V × V) :
    (S.filter fun r => j ∈ queryBlock T y z r).card ≤ 4 := by
  classical
  let Z : Finset V := {j.1, j.2.1, j.2.2}
  have hsub : (S.filter fun r => j ∈ queryBlock T y z r) ⊆
      {j} ∪ (T.filter fun r => r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)) := by
    intro r hr
    obtain ⟨hrs, hrj⟩ := mem_filter.mp hr
    rcases mem_insert.mp hrj with h | h
    · exact mem_union_left _ (mem_singleton.mpr h.symm)
    · exact mem_union_right _ (mem_filter.mpr
        ⟨hST hrs, hroot r hrs, owner_meeting T y z r j h⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hm := card_meeting_le hd x Z
  have hz : Z.card ≤ 3 := by
    have h1 := card_insert_le j.1 ({j.2.1, j.2.2} : Finset V)
    have h2 := card_insert_le j.2.1 ({j.2.2} : Finset V)
    simp only [card_singleton] at h2
    change Z.card ≤ _ at h1
    omega
  simp only [card_singleton] at hc
  omega

theorem independent_query_subfamily (T S : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) (hST : S ⊆ T)
    (x y z : V) (hroot : ∀ r ∈ S, r.1 = x) :
    ∃ W ⊆ S, (W : Set (V × V × V)).PairwiseDisjoint (queryBlock T y z) ∧
      S.card ≤ 12 * W.card := by
  exact DisjointQueriesStage123.exists_disjoint_of_read S (queryBlock T y z) 3 4
    (fun r _ => ⟨r, mem_insert_self _ _⟩)
    (fun r _ => queryBlock_card_le T hd y z r)
    (queryBlock_read_le T S hd hST x y z hroot)

/-- The trial condition really excludes all edges of the selected reserve,
not just the candidate's own two spokes. -/
theorem clean_connectors (T : Finset (V × V × V)) (y z : V)
    (r : V × V × V) (ω : (V × V × V) → Bool)
    (hself : Disjoint (connectors y z r) (resTri r))
    (hoff : ∀ j ∈ queryBlock T y z r, j ≠ r → ω j = false) :
    Disjoint (connectors y z r) (resEdges (T.filter fun j => ω j = true)) := by
  classical
  rw [disjoint_left]
  intro e he heR
  obtain ⟨j, hj, hej⟩ := mem_biUnion.mp heR
  obtain ⟨hjT, hjω⟩ := mem_filter.mp hj
  have hn : j ≠ r := by
    intro h
    subst j
    exact disjoint_left.mp hself he hej
  have hjb : j ∈ queryBlock T y z r := mem_insert_of_mem
    (mem_filter.mpr ⟨hjT, fun hd => disjoint_left.mp hd he hej⟩)
  have := hoff j hjb hn
  simp_all

end PartitionedTriangleAbsorption.ReserveQueryGeometryStage123
