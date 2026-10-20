/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply
public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Anti-edge supplies obtained from guarded two-root extensions

The ordinary supply can be obtained even when a pair of endpoint classes is
not itself permitted: it only needs a class which can connect to both roots.
This is exactly the root-root exemption in the extension condition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset OnePart TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem GuardedSupply.to_antiEdgeful {p : V → Fin t} {G : SimpleGraph V}
    [DecidableRel G.Adj] {Allowed : Fin t → Fin t → Prop} {D : ℕ} {γ : ℝ}
    (hs : GuardedSupply p G Allowed D (γ * Fintype.card V)) (hD : 2 ≤ D)
    (F : Finset (Multiset (Fin t)))
    (hallowed : ∀ i j k, ({i, j, k} : Multiset (Fin t)) ∈ F →
      Allowed i k ∧ Allowed j k) : AntiEdgeful p F G γ := by
  intro τ hτ i j k hτeq u v _ hu hv
  subst τ
  obtain ⟨hik, hjk⟩ := hallowed i j k hτ
  have hS : ({u, v} : Finset V).card ≤ D := card_le_two.trans hD
  have hn := hs {u, v} hS k (by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · simpa only [hu] using hik
    · have hxv : x = v := mem_singleton.mp hx
      subst x
      simpa only [hv] using hjk)
  refine hn.trans ?_
  exact_mod_cast card_le_card (fun w hw => by
    obtain ⟨_, hwk, hwa⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨mem_univ _, hwa u (by simp),
      (hwa v (by simp)).symm, hwk⟩)

theorem GuardedSupply.to_ordinaryAntiEdgeful {p : V → Fin t} {G : SimpleGraph V}
    [DecidableRel G.Adj] {Allowed : Fin t → Fin t → Prop} {D : ℕ} {γ : ℝ}
    (hs : GuardedSupply p G Allowed D (γ * Fintype.card V)) (hD : 2 ≤ D)
    (hcommon : ∀ a b : Fin t, ∃ c, Allowed a c ∧ Allowed b c) :
    AntiEdgeful part1 triFam G γ := by
  intro τ _ i j k _ u v _ _ _
  obtain ⟨c, hac, hbc⟩ := hcommon (p u) (p v)
  have hS : ({u, v} : Finset V).card ≤ D := card_le_two.trans hD
  have hn := hs {u, v} hS c (by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hac
    · simpa only [mem_singleton.mp hx] using hbc)
  refine hn.trans ?_
  exact_mod_cast card_le_card (fun w hw => by
    obtain ⟨_, _, hwa⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨mem_univ _, hwa u (by simp),
      (hwa v (by simp)).symm, Subsingleton.elim _ _⟩)

theorem guarded_F3_inputs (cls : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (γ : ℝ)
    (hs : GuardedSupply cls G (fun a b => a ≠ b) 2 (γ * Fintype.card V)) :
    (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => cls v = i).card : ℝ)) ∧
    AntiEdgeful cls F3 G γ ∧ AntiEdgeful part1 triFam G γ := by
  refine ⟨fun i => hs.class_card i, ?_, ?_⟩
  · exact hs.to_antiEdgeful (by omega) F3 (by unfold F3; decide)
  · exact hs.to_ordinaryAntiEdgeful (by omega) (by decide)

#print axioms GuardedSupply.to_antiEdgeful
#print axioms GuardedSupply.to_ordinaryAntiEdgeful
#print axioms guarded_F3_inputs

end PartitionedTriangleAbsorption.StructuralF3General
