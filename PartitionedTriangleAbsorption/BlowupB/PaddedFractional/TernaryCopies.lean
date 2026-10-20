/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompletePhysical
import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibbleAdapter

/-!
# Symmetric ternary weights and the original physical copies

This module transports a symmetric function on ordered triples to the existing
`Finset V` representation of typed triangles. Each triangle receives the average
of its six orderings. The edge load is exactly the sum over its third vertex;
there is no factor of two or six in that load identity.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer
open PaddedNibble.TypedNibble

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- Average the ordered triple weights over the six orders of a triangle.
Values on other finite sets are immaterial to the copy sums. -/
noncomputable def ternaryToWeight (w : V → V → V → ℝ) (S : Finset V) : ℝ :=
  (∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, w a b c) / 6

omit [DecidableEq V] in
theorem TernarySupported.diag13 {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {w : V → V → V → ℝ} (h : TernarySupported p F w) (a b : V) : w a b a = 0 :=
  h a b a (fun h' => h'.2.1 rfl)

omit [DecidableEq V] in
theorem TernarySupported.diag23 {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {w : V → V → V → ℝ} (h : TernarySupported p F w) (a b : V) : w a b b = 0 :=
  h a b b (fun h' => h'.2.2.1 rfl)

theorem ternaryToWeight_three {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {w : V → V → V → ℝ} (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ternaryToWeight w {a, b, c} = w a b c := by
  have hbac : w b a c = w a b c := (hsym.1 a b c).symm
  have hacb : w a c b = w a b c := (hsym.2 a b c).symm
  have hbca : w b c a = w a b c := (hsym.2 b a c).symm.trans hbac
  have hcab : w c a b = w a b c := (hsym.1 a c b).symm.trans hacb
  have hcba : w c b a = w a b c := (hsym.2 c a b).symm.trans hcab
  simp only [ternaryToWeight, mem_insert, mem_singleton,
    hab, hac, hbc, or_self, not_false_eq_true, sum_insert, sum_singleton,
    hsup.diag, hsup.diag13, hsup.diag23, hbac, hacb, hbca, hcab, hcba]
  ring

theorem isCopy_activeComplete_of_admissible (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) {a b c : V}
    (h : AdmissibleTriple p F a b c) :
    IsCopy p F (activeCompleteGraph p F) {a, b, c} := by
  obtain ⟨hab, hac, hbc, ht⟩ := h
  have hab' : (activeCompleteGraph p F).Adj a b := ⟨hab, p c, ht⟩
  have hac' : (activeCompleteGraph p F).Adj a c :=
    ⟨hac, p b, (link_swap F _ _ _).mp ht⟩
  have hbc' : (activeCompleteGraph p F).Adj b c :=
    ⟨hbc, p a, (link_swap F _ _ _).mp ((link_root_swap F _ _ _).mp ht)⟩
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isNClique_iff]
    constructor
    · rw [show ({a, b, c} : Finset V) = insert a (insert b {c}) by rfl]
      simp only [coe_insert, coe_singleton, SimpleGraph.isClique_insert,
        SimpleGraph.isClique_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
        true_and]
      exact ⟨fun x hx _ => by subst x; exact hbc',
        fun x hx _ => by rcases hx with rfl | rfl; exact hab'; exact hac'⟩
    · simp [hab, hac, hbc]
  · rw [map_three p hab hac hbc]
    exact ht

theorem admissible_of_isCopy_three (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : IsCopy p F (activeCompleteGraph p F) {a, b, c}) :
    AdmissibleTriple p F a b c := by
  refine ⟨hab, hac, hbc, ?_⟩
  simpa only [Link, map_three p hab hac hbc] using h.2

theorem ternaryToWeight_bound {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {w : V → V → V → ℝ} (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    {M : ℝ} (hM : ∀ a b c, |w a b c| ≤ M) {S : Finset V}
    (hS : IsCopy p F (activeCompleteGraph p F) S) :
    |ternaryToWeight w S| ≤ M := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hS.1.card_eq
  rw [ternaryToWeight_three hsym hsup hab hac hbc]
  exact hM a b c

variable [Fintype V]

/-- The third vertex enumerates the typed copies through a fixed physical edge.
The average over the six orders has exactly the original ternary edge load. -/
theorem ternaryToWeight_load (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    {w : V → V → V → ℝ} (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    {a b : V} (hab : a ≠ b) :
    (∑ S ∈ copies p F (activeCompleteGraph p F) with s(a, b) ∈ triEdges S,
      ternaryToWeight w S) = ternaryLoad w a b := by
  classical
  have hsum : (∑ c ∈ univ with AdmissibleTriple p F a b c, w a b c) =
      ∑ S ∈ copies p F (activeCompleteGraph p F) with s(a, b) ∈ triEdges S,
        ternaryToWeight w S := by
    refine sum_bij (fun c _ => ({a, b, c} : Finset V)) ?_ ?_ ?_ ?_
    · intro c hc
      have hc' := (mem_filter.mp hc).2
      exact mem_filter.mpr ⟨mem_copies_iff.mpr
        (isCopy_activeComplete_of_admissible p F hc'),
        mem_triEdges_iff.mpr ⟨by simp, by simp, hab⟩⟩
    · intro c hc d _ hcd
      have hc' := (mem_filter.mp hc).2
      have hm : c ∈ ({a, b, d} : Finset V) := by
        rw [← hcd]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with hca | hcb | hcd'
      · exact False.elim (hc'.2.1 hca.symm)
      · exact False.elim (hc'.2.2.1 hcb.symm)
      · exact hcd'
    · intro S hS
      obtain ⟨hcopy, hedge⟩ := mem_filter.mp hS
      have hc := mem_copies_iff.mp hcopy
      obtain ⟨ha, hb, _⟩ := mem_triEdges_iff.mp hedge
      obtain ⟨c, hac, hbc, rfl⟩ := exists_third_of_card_three hc.1.card_eq ha hb hab
      exact ⟨c, mem_filter.mpr ⟨mem_univ _,
        admissible_of_isCopy_three p F hab hac hbc hc⟩, rfl⟩
    · intro c hc
      have hc' := (mem_filter.mp hc).2
      exact (ternaryToWeight_three hsym hsup hab hc'.2.1 hc'.2.2.1).symm
  rw [← hsum]
  simp only [sum_filter, ternaryLoad]
  refine sum_congr rfl fun c _ => ?_
  by_cases hc : AdmissibleTriple p F a b c
  · simp only [hc, ite_true]
  · simp only [hc, ite_false, hsup a b c hc]

/-- A signed, bounded ternary weighting gives signed, equally bounded weights
on the original physical typed copies with exactly the same edge loads. -/
theorem exists_copy_weights_of_ternary (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (w : V → V → V → ℝ)
    (hsym : TernarySymmetric w) (hsup : TernarySupported p F w)
    (M : ℝ) (hM : ∀ a b c, |w a b c| ≤ M) :
    ∃ z : Finset V → ℝ,
      (∀ S, IsCopy p F (activeCompleteGraph p F) S → |z S| ≤ M) ∧
      ∀ a b, a ≠ b →
        (∑ S ∈ copies p F (activeCompleteGraph p F) with s(a, b) ∈ triEdges S,
          z S) = ternaryLoad w a b := by
  refine ⟨ternaryToWeight w, ?_, ?_⟩
  · exact fun _ hS => ternaryToWeight_bound hsym hsup hM hS
  · exact fun _ _ hab => ternaryToWeight_load p F hsym hsup hab

#print axioms ternaryToWeight_three
#print axioms ternaryToWeight_bound
#print axioms ternaryToWeight_load
#print axioms exists_copy_weights_of_ternary

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
