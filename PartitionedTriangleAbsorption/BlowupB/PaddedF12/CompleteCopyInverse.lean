/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.CompleteInverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalChains

@[expose] public section

/-! # The complete inverse on the original unordered physical edge and copy types -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks
open PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

def Sym2DemandSupported (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (r : Sym2 V → ℝ) : Prop :=
  ∀ e, e ∉ (activeCompleteGraph p F).edgeFinset → r e = 0

theorem Sym2DemandSupported.diag {p : V → Fin 4} {F : Finset (Multiset (Fin 4))}
    {r : Sym2 V → ℝ} (hr : Sym2DemandSupported p F r) (a : V) : r s(a, a) = 0 := by
  apply hr
  simp

theorem Sym2DemandSupported.edgeSupported {p : V → Fin 4}
    {F : Finset (Multiset (Fin 4))} {r : Sym2 V → ℝ} (hr : Sym2DemandSupported p F r) :
    EdgeSupported p F (fun a b => r s(a, b)) := by
  intro a b hab
  apply hr
  intro he
  exact hab ((SimpleGraph.mem_edgeFinset.mp he).2)

theorem exists_complete_ternary_inverse (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (r : Sym2 V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hs : Sym2DemandSupported p F r) (hr : ∀ e, |r e| ≤ ε)
    (hfamily : (F = F1 ∧ F1RealCompatible p (fun a b => r s(a, b))) ∨
      (F = F2 ∧ F2RealCompatible p (fun a b => r s(a, b)))) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
      (∀ a b, ternaryLoad w a b = r s(a, b)) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  apply exists_complete_inverse_F12 p F (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin _ hs.diag hs.edgeSupported (fun a b => hr s(a, b)) hfamily
  intro a b
  exact congrArg r Sym2.eq_swap

theorem copy_load_diag (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (J : SimpleGraph V) (z : Finset V → ℝ) (a : V) :
    (∑ S ∈ copies p F J with s(a, a) ∈ triEdges S, z S) = 0 := by
  have hnone : ∀ S : Finset V, s(a, a) ∉ triEdges S := by
    intro S hS
    exact (mem_filter.mp hS).2 (by simp)
  simp only [hnone, filter_false, sum_empty]

theorem exists_complete_copy_inverse (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (r : Sym2 V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hs : Sym2DemandSupported p F r) (hr : ∀ e, |r e| ≤ ε)
    (hfamily : (F = F1 ∧ F1RealCompatible p (fun a b => r s(a, b))) ∨
      (F = F2 ∧ F2RealCompatible p (fun a b => r s(a, b)))) :
    ∃ z : Finset V → ℝ,
      (∀ S, IsCopy p F (activeCompleteGraph p F) S →
        |z S| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ))) ∧
      ∀ e : Sym2 V,
        (∑ S ∈ copies p F (activeCompleteGraph p F) with e ∈ triEdges S, z S) = r e := by
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_ternary_inverse p F r ε γ
    hε hγ hγ1 hlarge hmin hs hr hfamily
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p F w hsw htw _ hbw
  refine ⟨z, hbz, ?_⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    by_cases hab : a = b
    · subst b
      rw [copy_load_diag, hs.diag]
    · exact (hlz a b hab).trans (hlw a b)

def copyRestriction {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) : TriangleChain V := by
  classical
  exact fun T => if IsCopy p F G T then z T else 0

theorem copyRestriction_supported {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) (z : TriangleChain V) :
    CopySupported p F G (copyRestriction p F G z) := by
  intro T hT
  simp only [copyRestriction, hT, ite_false]

theorem copyRestriction_boundary {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) (z : TriangleChain V) (e : Sym2 V) :
    boundary (copyRestriction p F G z) e = ∑ T ∈ copies p F G with e ∈ triEdges T, z T := by
  rw [boundary_eq_copy_load p F G _ (copyRestriction_supported p F G z)]
  apply sum_congr rfl
  intro T hT
  simp only [copyRestriction, (mem_copies_iff.mp (mem_filter.mp hT).1), ite_true]

theorem exists_complete_chain_inverse (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (r : Sym2 V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hs : Sym2DemandSupported p F r) (hr : ∀ e, |r e| ≤ ε)
    (hfamily : (F = F1 ∧ F1RealCompatible p (fun a b => r s(a, b))) ∨
      (F = F2 ∧ F2RealCompatible p (fun a b => r s(a, b)))) :
    ∃ z : TriangleChain V, CopySupported p F (activeCompleteGraph p F) z ∧
      boundary z = r ∧
      ∀ T, |z T| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  obtain ⟨z, hbz, hlz⟩ := exists_complete_copy_inverse p F r ε γ
    hε hγ hγ1 hlarge hmin hs hr hfamily
  refine ⟨copyRestriction p F (activeCompleteGraph p F) z,
    copyRestriction_supported p F (activeCompleteGraph p F) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p F (activeCompleteGraph p F) z e).trans (hlz e)
  · intro T
    by_cases hT : IsCopy p F (activeCompleteGraph p F) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

#print axioms exists_complete_ternary_inverse
#print axioms exists_complete_copy_inverse
#print axioms exists_complete_chain_inverse

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
