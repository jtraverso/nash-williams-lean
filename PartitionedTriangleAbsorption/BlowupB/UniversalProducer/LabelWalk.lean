/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ClassRefiner
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.RoutedPath

/-!
# Components of the allowed-label graph and short label walks

`AllowedF F i j := ∃ k, Link F i j k` is symmetric.  `compMap F i` is the least label in the
connected component of `i` for the reflexive-transitive closure of `Allowed F`.  It satisfies
only the FIRST clause of `IsCommonLinkClassMap` (allowed pairs stay in one class,
`compMap_link`); no common-neighbour clause is used anywhere below.

`exists_labelWalk`: two labels in one component, the first active, are joined by a label walk
of length `m` with `2 ≤ m ≤ t + 1` (a shortest path in the component; a single allowed step
is replaced by the other two edges of a permitted triangle, and equal labels use `i, a, i`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption TypedTransformer

variable {t : ℕ}

/-- The allowed-pair relation on labels. -/
def AllowedF (F : Finset (Multiset (Fin t))) (i j : Fin t) : Prop := ∃ k, Link F i j k

theorem allowedF_symm {F : Finset (Multiset (Fin t))} {i j : Fin t} (h : AllowedF F i j) :
    AllowedF F j i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, (link_root_swap F i j k).mp hk⟩

/-- The component representative of a label. -/
noncomputable def compMap (F : Finset (Multiset (Fin t))) (i : Fin t) : Fin t := by
  classical
  exact (univ.filter fun j => Relation.ReflTransGen (AllowedF F) i j).min'
    ⟨i, mem_filter.mpr ⟨mem_univ _, Relation.ReflTransGen.refl⟩⟩

theorem reach_symm {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : Relation.ReflTransGen (AllowedF F) i j) : Relation.ReflTransGen (AllowedF F) j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact (Relation.ReflTransGen.single (allowedF_symm hbc)).trans ih

theorem compMap_eq_of_reach {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : Relation.ReflTransGen (AllowedF F) i j) : compMap F i = compMap F j := by
  classical
  unfold compMap
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun hx => (reach_symm h).trans hx, fun hx => h.trans hx⟩

theorem reach_compMap (F : Finset (Multiset (Fin t))) (i : Fin t) :
    Relation.ReflTransGen (AllowedF F) i (compMap F i) := by
  classical
  have := min'_mem (univ.filter fun j => Relation.ReflTransGen (AllowedF F) i j)
    ⟨i, mem_filter.mpr ⟨mem_univ _, Relation.ReflTransGen.refl⟩⟩
  exact (mem_filter.mp this).2

/-- Allowed pairs stay in one component (the first clause of a class map). -/
theorem compMap_link {F : Finset (Multiset (Fin t))} {i j k : Fin t} (h : Link F i j k) :
    compMap F i = compMap F j :=
  compMap_eq_of_reach (Relation.ReflTransGen.single ⟨k, h⟩)

theorem reach_of_compMap_eq {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : compMap F i = compMap F j) : Relation.ReflTransGen (AllowedF F) i j := by
  have hi := reach_compMap F i
  have hj := reach_compMap F j
  rw [h] at hi
  exact hi.trans (reach_symm hj)

/-- The simple graph of distinct allowed label pairs. -/
def allowedGraph (F : Finset (Multiset (Fin t))) : SimpleGraph (Fin t) :=
  SimpleGraph.fromRel (AllowedF F)

theorem reachable_of_reach {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : Relation.ReflTransGen (AllowedF F) i j) : (allowedGraph F).Reachable i j := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    by_cases hb : b = c
    · subst hb; exact ih
    · refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [allowedGraph, SimpleGraph.fromRel_adj]
      exact ⟨hb, Or.inl hbc⟩

theorem allowed_of_adj {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : (allowedGraph F).Adj i j) : AllowedF F i j := by
  rw [allowedGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact h
  · exact allowedF_symm h

/-- **Short label walks.** -/
theorem exists_labelWalk {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (hi : ActivePart F i) (h : Relation.ReflTransGen (AllowedF F) i j) :
    ∃ (m : ℕ) (lab : ℕ → Fin t), 2 ≤ m ∧ m ≤ t + 1 ∧ lab 0 = i ∧ lab m = j ∧
      ∀ k < m, AllowedF F (lab k) (lab (k + 1)) := by
  classical
  obtain ⟨w, hw⟩ := (reachable_of_reach h).exists_isPath
  have hlen : w.length < t := by
    have := hw.length_lt; simpa using this
  by_cases h0 : w.length = 0
  · -- equal labels: `i, a, i`
    have hij : i = j := SimpleGraph.Walk.eq_of_length_eq_zero h0
    subst hij
    obtain ⟨a, k, hk⟩ := hi
    refine ⟨2, fun n => if n = 1 then a else i, le_rfl, by omega, by simp, by simp, ?_⟩
    intro n hn
    interval_cases n
    · exact ⟨k, hk⟩
    · exact allowedF_symm ⟨k, hk⟩
  · by_cases h1 : w.length = 1
    · -- one step: replace by the other two edges of a permitted triangle
      have hadj : (allowedGraph F).Adj i j := by
        have := w.adj_getVert_succ (i := 0) (by omega)
        rwa [SimpleGraph.Walk.getVert_zero, zero_add, ← h1,
          SimpleGraph.Walk.getVert_length] at this
      obtain ⟨k, hk⟩ := allowed_of_adj hadj
      refine ⟨2, fun n => if n = 0 then i else if n = 1 then k else j, le_rfl, by omega,
        by simp, by simp, ?_⟩
      intro n hn
      interval_cases n
      · exact ⟨j, (link_swap F i j k).mp hk⟩
      · refine ⟨i, ?_⟩
        simp only [one_ne_zero, if_false, if_true, show (1 + 1 = 0) = False by simp,
          show (1 + 1 = 1) = False by simp]
        exact (link_swap F k i j).mp ((link_root_swap F i k j).mp ((link_swap F i j k).mp hk))
    · -- a shortest path of length at least two
      refine ⟨w.length, w.getVert, by omega, by omega, w.getVert_zero, w.getVert_length, ?_⟩
      intro n hn
      exact allowed_of_adj (w.adj_getVert_succ hn)

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
