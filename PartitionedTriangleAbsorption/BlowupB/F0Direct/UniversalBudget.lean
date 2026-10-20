/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.CompatibleShared.Host
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.FiniteLibrary

/-!
# Universal F₀ absorption under the explicit shared-refiner budgets

The compatible refiner is constructed here from `AntiEdgeful`; it is not
supplied as an additional hypothesis.  The remaining producer input is the
bounded private placement contract.  A single absorber is returned before
the quantification over all divisible subgraphs of the unbounded reserve.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset AntiEdgeSelection TypedApplicationLinks
open TypedRefinerF0.CompressedHub.CompatibleShared
open TypedRefinerF0
open SharedGreedyPort UniversalRefiner
open StructuralF3General.PrivateFamily StructuralF3General.FiniteLibrary

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem incidentLoad_biUnion_le {I : Type*} (s : Finset I)
    (B : I → Finset (Sym2 V)) (v : V) :
    incidentLoad (s.biUnion B) v ≤ ∑ i ∈ s, incidentLoad (B i) v := by
  classical
  have heq : (s.biUnion B).filter (fun e => v ∈ e) =
      s.biUnion (fun i => (B i).filter fun e => v ∈ e) := by
    ext e
    simp only [mem_filter, mem_biUnion]
    aesop
  unfold incidentLoad
  rw [heq]
  exact card_biUnion_le

theorem universal_of_compatible_budgets
    (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ℕ) (T D a α : ℝ) (power q Lmax Δ : ℕ)
    (hα : 0 < α) (hn : 3 ≤ Fintype.card V) (hanti : AntiEdgeful p F0 G α)
    (hstep : PrivateStep p F0 G 214 C T D a)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hXdeg : ∀ v, incidentLoad X v ≤ Δ)
    (hq : 0 < q) (hLq : Lmax ≤ q) (h99 : 99 * Δ ≤ Lmax)
    (h66 : 66 ≤ Lmax) (h88 : 88 ≤ Lmax)
    (hhub : 330 * ((Fintype.card V / 2 ^ power + 1) * Δ) +
      1452 * 2 ^ power ≤ Lmax)
    (hembed : 2 * (214 : ℝ) * Lmax +
      2 * ((214 * (57635 * (X.card + 2 * (2 ^ power) ^ 2)) : ℕ) : ℝ) / q +
      2 * ((Δ : ℝ) + 2 * q) < α * Fintype.card V)
    (hdegree : max ((Δ : ℝ) + 2 * q) (T + C) + C * (2 * q) ≤ D)
    (hmass : 4 * ((Fintype.card V : ℝ) * ((Δ : ℝ) + 2 * q) +
      ((57635 * (X.card + 2 * (2 ^ power) ^ 2) : ℕ) : ℝ) * C) ≤ T * a) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp p F0 A ∧ DegBounded A D ∧
      ∀ L ⊆ X, IsIntDiv p F0 L → HasDecomp p F0 (A ∪ L) := by
  classical
  have hXloop : ∀ e ∈ X, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))
  obtain ⟨indices, R, _, _, _, _, _, _, _, hcount, hplace⟩ :=
    compatible_shared_host power p X hXloop
  have hforbid : ∀ v, incidentLoad (∅ : Finset (Sym2 V)) v ≤ 0 := by
    intro v
    simp [AntiEdgeSelection.incidentLoad]
  have hbudget : 2 * (214 : ℝ) * Lmax +
      2 * ((214 * (57635 * (X.card + 2 * (2 ^ power) ^ 2)) : ℕ) : ℝ) / q +
      2 * (((0 : ℕ) : ℝ) + Δ + 2 * q) < α * Fintype.card V := by
    simpa using hembed
  obtain ⟨f, _, _, _, _, _, _, hpieces, hRG, hload, href⟩ :=
    hplace G ∅ q Lmax 0 Δ α hα hn hanti hq hLq h99 h66 h88 hhub hforbid hXdeg hbudget
  let R' : Finset (Sym2 V) := mapE f R
  let B := fun i => mapE f (compatB power p X hXloop i)
  have hR'G : R' ⊆ G.edgeFinset := fun e he =>
    SimpleGraph.mem_edgeFinset.mpr (hRG e he).1
  have hRX : Disjoint R' X :=
    disjoint_left.mpr fun e he hx => (hRG e he).2.2 hx
  have hRlib : R' ⊆ indices.biUnion B := by
    obtain ⟨J, hJi, _, hJU⟩ := href ∅ (empty_subset _) RefinerAssembly.empty_isIntDiv
    intro e he
    have heJ : e ∈ J.biUnion B := by
      rw [hJU]
      exact mem_union_left _ he
    obtain ⟨i, hi, hei⟩ := mem_biUnion.mp heJ
    exact mem_biUnion.mpr ⟨i, hJi hi, hei⟩
  have hRdeg : ∀ v, incidentLoad R' v ≤ 2 * q := by
    intro v
    exact (StructuralF3General.PrivateFamily.incidentLoad_mono hRlib v).trans
      ((incidentLoad_biUnion_le indices B v).trans (hload v))
  have hledger : DegBounded (X ∪ R') ((Δ : ℝ) + 2 * q) := by
    intro v
    have hh : incidentLoad (X ∪ R') v = incidentLoad X v + incidentLoad R' v :=
      StructuralF3General.PrivateFamily.incidentLoad_union hRX.symm v
    have hnat : incidentLoad (X ∪ R') v ≤ Δ + 2 * q := by
      rw [hh]
      exact Nat.add_le_add (hXdeg v) (hRdeg v)
    exact_mod_cast hnat
  have hpieces' : ∀ i ∈ indices, B i ⊆ X ∪ R' := by
    intro i hi e he
    exact (union_comm R' X) ▸ (hpieces i hi).2.2.2.2 he
  have hsize : ∀ i ∈ indices, (B i).card ≤ 214 := fun i hi =>
    (hpieces i hi).2.2.2.1
  have hdiv : ∀ i ∈ indices, IsIntDiv p F0 (B i) := fun i hi => (hpieces i hi).1
  have hloadR : ∀ v, ((∑ i ∈ indices, incidentLoad (B i) v : ℕ) : ℝ) ≤ 2 * q := by
    intro v
    exact_mod_cast hload v
  have hmass' : 4 * (((X ∪ R').card : ℝ) + (indices.card : ℝ) * C) ≤ T * a := by
    have hcard := card_le_order_mul_degree (X ∪ R') _ hledger
    have hcountR : (indices.card : ℝ) ≤
        ((57635 * (X.card + 2 * (2 ^ power) ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hmul := mul_le_mul_of_nonneg_right hcountR (Nat.cast_nonneg C)
    linarith
  exact universal_from_finite_library p F0 G 214 C T D (2 * q) ((Δ : ℝ) + 2 * q) a
    hstep X R' hRX hXG hR'G hledger hdegree indices B href hpieces' hsize hdiv hloadR hmass'

#print axioms incidentLoad_biUnion_le
#print axioms universal_of_compatible_budgets

end PartitionedTriangleAbsorption.BlowupB.F0Direct
