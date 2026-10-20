/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveChargeStage121
public import PartitionedTriangleAbsorption.UniformPrecoverStage117

/-! # Compatible recut and physical pre-cover with the actual host balanced

The pre-cover supply is selected avoiding the protected reserve. Unused supply
is released to the nibble host; only the actually used spokes are deleted.
This is not yet the nibble/cover-down step or a confinement theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.JointRecutPrecoverStage121

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105
  ReserveAwareRecutStage120 SeedDrivenTrimStage114 ReserveTrimStage109
  F3ReserveTrimStage109

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem spokes_disjoint_outer (W : Finset V) (S J : Finset (Sym2 V))
    (hS : ∀ e ∈ S, IsSpoke W e)
    (hJ : ∀ x y, s(x, y) ∈ J → x ∉ W ∧ y ∉ W) : Disjoint S J := by
  apply disjoint_left.mpr
  intro e he hj
  obtain ⟨x, y, -, hy, rfl⟩ := hS e he
  exact (hJ x y hj).2 hy

omit [Fintype V] in
theorem precover_degree (W : Finset V) (Y S : Finset (Sym2 V)) (d q : ℕ)
    (hd : ∀ v, incidentLoad Y v ≤ d)
    (hroot : ∀ v, v ∉ W → incidentLoad S v = incidentLoad Y v)
    (haux : ∀ v ∈ W, incidentLoad S v ≤ 2 * q) :
    ∀ v, incidentLoad S v ≤ max d (2 * q) := by
  intro v
  by_cases hv : v ∈ W
  · exact (haux v hv).trans (le_max_right _ _)
  · rw [hroot v hv]
    exact (hd v).trans (le_max_left _ _)

omit [Fintype V] in
theorem deletion_degree (S R J : Finset (Sym2 V)) (s r d : ℕ)
    (hS : ∀ v, incidentLoad S v ≤ s) (hR : ∀ v, incidentLoad R v ≤ r)
    (hJ : ∀ v, incidentLoad J v ≤ d) :
    ∀ v, incidentLoad (S ∪ (R ∪ J)) v ≤ s + r + d := by
  intro v
  have h₁ := incidentLoad_union_le S (R ∪ J) v
  have h₂ := incidentLoad_union_le R J v
  have h₃ := hS v
  have h₄ := hR v
  have h₅ := hJ v
  omega

/-- The reserve `R` is protected. The new pre-cover supply `A` is produced
first and avoids `R`; the recut and its used spokes are then produced jointly.
The conclusion includes the literal surviving child and the total deletion
degree, rather than assuming either as a new input. -/
theorem exists_joint_recut_precover (p : V → Fin 4)
    (E J R : Finset (Sym2 V)) (W : Finset V)
    (hcross : ∀ x y, s(x, y) ∈ E → p x ≠ p y)
    (hdiv : IsIntDiv p F3 E) (hbal : ∀ k : Fin 2, bal p k E = 0)
    (hJE : J ⊆ E) (hRE : R ⊆ E) (hRJ : Disjoint R J)
    (hJW : ∀ x y, s(x, y) ∈ J → x ∉ W ∧ y ∉ W)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGE : G.edgeFinset ⊆ E) (hGW : ∀ e ∈ G.edgeFinset, IsSpoke W e)
    (β δ ρ : ℝ) (hdR : DegBounded R (δ * Fintype.card V))
    (hβ : 0 < β - 2 * δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hrich : ∀ x y, s(x, y) ∈ J →
      β * Fintype.card V ≤ (PairReserveStage116.neighbours W G x y).card)
    (hsize : 96 ≤ (β - 2 * δ) ^ 3 * ρ ^ 12 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V)
    (m D P a q r : ℕ) (hP : m < P) (hq : 0 < q)
    (hJdeg : ∀ v, incidentLoad J v ≤ D) (hRdeg : ∀ v, incidentLoad R v ≤ r)
    (hp : ∀ i j, (pool (category p) (R ∪ J) i).card ≤
      (pool (category p) (R ∪ J) j).card + m)
    (hpool : ∀ i, P ≤ (pool (category p) J i).card)
    (ha : (a : ℝ) ≤ (β - 2 * δ) * ρ ^ 2 / 2 * Fintype.card V)
    (hbudget : 6 * quota m D P + (2 * m) / q < a) :
    ∃ A ⊆ G.edgeFinset, Disjoint A R ∧ DegBounded A (2 * ρ * Fintype.card V) ∧
      ∃ Y ⊆ J, ∃ S ⊆ A,
        Disjoint Y R ∧ Disjoint S (R ∪ J) ∧
        Y.card ≤ 2 * m ∧ (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
        HasDecomp p F3 (Y ∪ S) ∧ IsIntDiv p F3 (E \ (Y ∪ S)) ∧
        (J \ (Y ∪ S) = J \ Y) ∧
        (∀ v, incidentLoad S v ≤ max (3 * quota m D P) (2 * q)) ∧
        (∀ v, incidentLoad (S ∪ (R ∪ J)) v ≤
          max (3 * quota m D P) (2 * q) + r + D) ∧
        (∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0) ∧
        (∀ k : Fin 2, bal p k (E \ (S ∪ (R ∪ J))) = 0) := by
  have hb : 2 * (3 * quota m D P) + (2 * m) / q < a := by omega
  obtain ⟨A, hAG, hAR, hAd, hcover⟩ :=
    UniformPrecoverStage117.exists_reserve_for_all_residuals p E J R W
      hcross hdiv hJE hJW hRJ.symm G hGE hGW β δ ρ hdR hβ hρ hρ1
      hn hrich hsize hdegrees (3 * quota m D P) a q (2 * m) hq ha hb
  obtain ⟨Y, hY, hYR, hYcard, hYdeg, hYbal, hconsume⟩ :=
    exists_reserve_aware_recut p E R J m D P hRJ
      (fun x y h => hcross x y ((union_subset hRE hJE) h)) hbal hP hJdeg hp hpool
  obtain ⟨S, hSA, hdec, -, hroot, haux, hdiv'⟩ :=
    hcover Y hY hYcard (fun v _ => hYdeg v)
  have hSJ : Disjoint S J := spokes_disjoint_outer W S J
    (fun e he => hGW e (hAG (hSA he))) hJW
  have hSRJ : Disjoint S (R ∪ J) := disjoint_union_right.mpr
    ⟨hAR.mono_left hSA, hSJ⟩
  have hSE : S ⊆ E := hSA.trans (hAG.trans hGE)
  have hsd : ∀ v, incidentLoad S v ≤ max (3 * quota m D P) (2 * q) :=
    precover_degree W Y S _ q hYdeg hroot haux
  have hdel : ∀ v, incidentLoad (S ∪ (R ∪ J)) v ≤
      max (3 * quota m D P) (2 * q) + r + D :=
    deletion_degree S R J _ r D hsd hRdeg hJdeg
  have hchild : J \ (Y ∪ S) = J \ Y := by
    ext e
    simp only [mem_sdiff, mem_union]
    have hh : e ∈ J → e ∉ S := fun he hs => disjoint_left.mp hSJ hs he
    tauto
  have heq : (Y ∪ S) ∪ (R ∪ (J \ Y)) = S ∪ (R ∪ J) := by
    ext e
    simp only [mem_union, mem_sdiff]
    have := @hY e
    tauto
  have hfinal := hconsume S hSRJ (union_subset hSE (union_subset hRE hJE)) hdec
  rw [heq] at hfinal
  exact ⟨A, hAG, hAR, hAd, Y, hY, S, hSA, hYR, hSRJ, hYcard, hYdeg,
    hdec, hdiv', hchild, hsd, hdel, hYbal, hfinal⟩

end PartitionedTriangleAbsorption.JointRecutPrecoverStage121
