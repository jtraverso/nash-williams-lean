/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators

/-! # Integral transport through a finite Hall expansion

All capacities are natural numbers. The cut hypotheses in this file must
still be derived from the graph; an allocation is not a physical packing.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerTransportStage143

open Finset

/-- Weighted Hall, expanded into individual units. -/
theorem unit_matching {A B : Type*} [Finite A] [DecidableEq B]
    (r : A → ℕ) (c : B → ℕ) (nb : A → Finset B)
    (h : ∀ s : Finset A, (∑ a ∈ s, r a) ≤ ∑ b ∈ s.biUnion nb, c b) :
    ∃ f : (Σ a, Fin (r a)) → (Σ b, Fin (c b)),
      Function.Injective f ∧ ∀ u, (f u).1 ∈ nb u.1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let t : (Σ a, Fin (r a)) → Finset (Σ b, Fin (c b)) :=
    fun u => (nb u.1).sigma fun _ => univ
  have hh : ∀ s : Finset (Σ a, Fin (r a)), s.card ≤ (s.biUnion t).card := by
    intro s
    let a := s.image Sigma.fst
    have hs : s ⊆ a.sigma (fun _ => univ) := by
      intro u hu
      simp only [mem_sigma, mem_univ, and_true]
      exact mem_image.mpr ⟨u, hu, rfl⟩
    have he : s.biUnion t = (a.biUnion nb).sigma (fun _ => univ) := by
      ext u
      simp only [t, a, mem_biUnion, mem_sigma, mem_univ, and_true, mem_image]
      aesop
    calc
      s.card ≤ (a.sigma fun _ => univ).card := card_le_card hs
      _ = ∑ v ∈ a, r v := by simp [card_sigma]
      _ ≤ ∑ v ∈ a.biUnion nb, c v := h a
      _ = (s.biUnion t).card := by rw [he]; simp [card_sigma]
  obtain ⟨f, hf, hn⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hh
  exact ⟨f, hf, fun u => (mem_sigma.mp (hn u)).1⟩

/-- Natural allocation matrix obtained from the unit matching. -/
theorem weighted_assignment {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (r : A → ℕ) (c : B → ℕ) (nb : A → Finset B)
    (h : ∀ s : Finset A, (∑ a ∈ s, r a) ≤ ∑ b ∈ s.biUnion nb, c b) :
    ∃ z : A → B → ℕ,
      (∀ a, ∑ b, z a b = r a) ∧
      (∀ b, ∑ a, z a b ≤ c b) ∧
      (∀ a b, b ∉ nb a → z a b = 0) := by
  classical
  obtain ⟨f, hf, hn⟩ := unit_matching r c nb h
  let hit (a : A) (b : B) : Finset (Fin (r a)) :=
    univ.filter fun j => (f ⟨a, j⟩).1 = b
  let z (a : A) (b : B) := (hit a b).card
  refine ⟨z, ?_, ?_, ?_⟩
  · intro a
    have hc := card_eq_sum_card_fiberwise
      (f := fun j : Fin (r a) => (f ⟨a, j⟩).1)
      (s := univ) (t := univ) (fun _ _ => mem_univ _)
    simpa only [card_univ, Fintype.card_fin, z, hit] using hc.symm
  · intro b
    let s : Finset (Σ a, Fin (r a)) := univ.sigma fun a => hit a b
    have hs : s.image f ⊆ ({b} : Finset B).sigma (fun _ => univ) := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
      have hvb : (f v).1 = b := (mem_filter.mp (mem_sigma.mp hv).2).2
      simp [hvb]
    have hc := card_le_card hs
    rw [card_image_of_injective s hf, card_sigma] at hc
    simpa [s, z, card_sigma] using hc
  · intro a b hab
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hjb := (mem_filter.mp hj).2
    exact hab (hjb ▸ hn ⟨a, j⟩)

end PartitionedTriangleAbsorption.IntegerTransportStage143
