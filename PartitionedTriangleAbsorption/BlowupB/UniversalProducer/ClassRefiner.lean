/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ClassLift

/-!
# The ordinary even refiner inside one class of parts

A family has *common-link classes* if there is a class map `cl` on parts such that allowed
pairs lie in one class and any two active parts of one class have a common allowed partner.
For one class `r`, the vertices `classVerts F p cl r` (active part of class `r`) span, by the
guarded two-root supply, an anti-edgeful host for the one-part triangle family.  The existing
heap refiner `exists_universal_refiner_alpha` (`StructuralF3General/OrdinaryHost.lean`), run
on this vertex subtype with rescaled `λ, ρ, α`, gives a fixed remainder and a fixed library of
loopless even pieces of at most `42` edges inside the class, refining every leftover inside
the class with even degrees and a multiple of three edges (`class_refiner`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.OnePart

variable {t : ℕ}

/-- A part with some allowed partner. -/
def ActivePart (F : Finset (Multiset (Fin t))) (i : Fin t) : Prop := ∃ a k, Link F i a k

/-- A class map for which allowed pairs stay in one class and any two active parts of a class
have a common allowed partner. -/
def IsCommonLinkClassMap (F : Finset (Multiset (Fin t))) (cl : Fin t → Fin t) : Prop :=
  (∀ i j k, Link F i j k → cl i = cl j) ∧
    ∀ i j, ActivePart F i → ActivePart F j → cl i = cl j →
      ∃ c, (∃ k, Link F i c k) ∧ (∃ k, Link F j c k)

/-- **Common-link classes**: such a class map exists. -/
def CommonLinkClasses (F : Finset (Multiset (Fin t))) : Prop :=
  ∃ cl : Fin t → Fin t, IsCommonLinkClassMap F cl

/-- The parts of class `r`. -/
noncomputable def classParts (F : Finset (Multiset (Fin t))) (cl : Fin t → Fin t) (r : Fin t) :
    Finset (Fin t) := by
  classical exact univ.filter (fun i => ActivePart F i ∧ cl i = r)

/-- The vertices of class `r`. -/
noncomputable def classVerts {V : Type*} [Fintype V] (F : Finset (Multiset (Fin t)))
    (p : V → Fin t) (cl : Fin t → Fin t) (r : Fin t) : Finset V := by
  classical exact univ.filter (fun v => p v ∈ classParts F cl r)

theorem mem_classParts {F : Finset (Multiset (Fin t))} {cl : Fin t → Fin t} {r i : Fin t} :
    i ∈ classParts F cl r ↔ ActivePart F i ∧ cl i = r := by
  classical
  unfold classParts; simp

theorem mem_classVerts {V : Type*} [Fintype V] {F : Finset (Multiset (Fin t))} {p : V → Fin t}
    {cl : Fin t → Fin t} {r : Fin t} {v : V} :
    v ∈ classVerts F p cl r ↔ p v ∈ classParts F cl r := by
  classical
  unfold classVerts; simp

theorem activePart_of_link {F : Finset (Multiset (Fin t))} {i j k : Fin t} (h : Link F i j k) :
    ActivePart F i ∧ ActivePart F j := by
  refine ⟨⟨j, k, h⟩, ⟨i, k, (link_root_swap F i j k).mp h⟩⟩

/-- Every type lies inside one class of parts or avoids it. -/
theorem type_closed {F : Finset (Multiset (Fin t))} (hF3 : ∀ τ ∈ F, Multiset.card τ = 3)
    {cl : Fin t → Fin t} (hcl : IsCommonLinkClassMap F cl) (r : Fin t) :
    ∀ τ ∈ F, (∀ i ∈ τ, i ∈ classParts F cl r) ∨ (∀ i ∈ τ, i ∉ classParts F cl r) := by
  intro τ hτ
  have key : ∀ i ∈ τ, ∀ j ∈ τ, ActivePart F i ∧ cl i = cl j := by
    intro i hi j hj
    obtain ⟨τ', rfl⟩ := Multiset.exists_cons_of_mem hi
    have hc : Multiset.card τ' = 2 := by
      have := hF3 _ hτ; simp at this; omega
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
    have hl : Link F i a b := by
      change ({i, a, b} : Multiset (Fin t)) ∈ F
      simpa using hτ
    refine ⟨(activePart_of_link hl).1, ?_⟩
    rcases Multiset.mem_cons.mp hj with rfl | hj
    · rfl
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hcl.1 _ _ _ hl
      · exact hcl.1 _ _ _ ((link_swap F i a j).mp hl)
  by_cases h : ∃ i ∈ τ, i ∈ classParts F cl r
  · left
    obtain ⟨i, hi, hir⟩ := h
    intro j hj
    obtain ⟨hj1, hji⟩ := key j hj i hi
    rw [mem_classParts] at hir ⊢
    exact ⟨hj1, hji.trans hir.2⟩
  · right
    push_neg at h
    exact h

/-- Both ends of an allowed host edge lie in the class of either end. -/
theorem mem_classVerts_of_adj {V : Type*} [Fintype V] {F : Finset (Multiset (Fin t))}
    {p : V → Fin t} {cl : Fin t → Fin t} (hcl : IsCommonLinkClassMap F cl) {u v : V}
    (huv : ∃ k, Link F (p u) (p v) k) :
    u ∈ classVerts F p cl (cl (p u)) ∧ v ∈ classVerts F p cl (cl (p u)) := by
  obtain ⟨k, hk⟩ := huv
  obtain ⟨hu, hv⟩ := activePart_of_link hk
  rw [mem_classVerts, mem_classVerts, mem_classParts, mem_classParts]
  exact ⟨⟨hu, rfl⟩, ⟨hv, (hcl.1 _ _ _ hk).symm⟩⟩

theorem classVerts_eq_of_mem {V : Type*} [Fintype V] {F : Finset (Multiset (Fin t))}
    {p : V → Fin t} {cl : Fin t → Fin t} {r r' : Fin t} {v : V}
    (h : v ∈ classVerts F p cl r) (h' : v ∈ classVerts F p cl r') : r = r' := by
  rw [mem_classVerts, mem_classParts] at h h'
  exact h.2.symm.trans h'.2

section ClassRefiner

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The anti-edge supply inside one class. -/
theorem class_antiEdgeful (F : Finset (Multiset (Fin t))) (p : V → Fin t) (cl : Fin t → Fin t)
    (hcl : IsCommonLinkClassMap F cl) (r : Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : ℝ) (hsup : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 2 (ω * Fintype.card V))
    [DecidableRel (G.comap (Subtype.val : classVerts F p cl r → V)).Adj] :
    AntiEdgeful part1 triFam (G.comap (Subtype.val : classVerts F p cl r → V))
      (ω * Fintype.card V / Fintype.card (classVerts F p cl r)) := by
  classical
  intro τ _ i j k _ u v huv _ _
  have hu := u.2
  have hv := v.2
  rw [mem_classVerts, mem_classParts] at hu hv
  obtain ⟨c, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := hcl.2 _ _ hu.1 hv.1 (hu.2.trans hv.2.symm)
  have hS : ({u.1, v.1} : Finset V).card ≤ 2 := card_le_two
  have hn := hsup {u.1, v.1} hS c (by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨k1, hk1⟩
    · rw [mem_singleton.mp hx]; exact ⟨k2, hk2⟩)
  have hWpos : (0 : ℝ) < Fintype.card (classVerts F p cl r) := by
    have : 0 < Fintype.card (classVerts F p cl r) := Fintype.card_pos_iff.mpr ⟨u⟩
    exact_mod_cast this
  rw [div_mul_cancel₀ _ hWpos.ne']
  refine hn.trans ?_
  have hsub : guardedNeighbours p G {u.1, v.1} c ⊆
      (univ.filter (fun w : classVerts F p cl r => (G.comap Subtype.val).Adj u w ∧
        (G.comap Subtype.val).Adj w v ∧ part1 w = k)).image Subtype.val := by
    intro x hx
    obtain ⟨_, hxc, hxa⟩ := mem_filter.mp hx
    have hxW : x ∈ classVerts F p cl r := by
      rw [mem_classVerts, mem_classParts]
      have hl : Link F (p u.1) c k1 := hk1
      obtain ⟨_, hca⟩ := activePart_of_link hl
      refine ⟨hxc ▸ hca, ?_⟩
      rw [hxc, ← hcl.1 _ _ _ hl]; exact hu.2
    refine mem_image.mpr ⟨⟨x, hxW⟩, mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩, rfl⟩
    · exact hxa u.1 (by simp)
    · exact (hxa v.1 (by simp)).symm
    · exact Subsingleton.elim _ _
  have h := (card_le_card hsub).trans card_image_le
  have h' : ((guardedNeighbours p G {u.1, v.1} c).card : ℝ) ≤
      ((univ.filter (fun w : classVerts F p cl r => (G.comap Subtype.val).Adj u w ∧
        (G.comap Subtype.val).Adj w v ∧ part1 w = k)).card : ℝ) := by exact_mod_cast h
  exact h'

end ClassRefiner

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
