/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Family
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # Composing a supplied structural library with simultaneous private absorbers

Library pieces may overlap globally. Only the pieces selected for one leftover
must be disjoint. This consumer does not construct the refiner or fractional input.
The root-load bound may depend on host order; explicit ledger budgets pay for it.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralAbsorberStage70

open Finset TypedApplicationLinks PrivateTemplateStage69 AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A root occurrence costs at least one incident piece edge. This converts the
refiner's summed edge incidence into the private consumer's root-load contract. -/
theorem rootLoad_le_incidence_sum (P : ℕ → Finset (Sym2 V)) (K : ℕ) (v : V) :
    PrivateTemplateStage69.rootLoad P K v ≤ ∑ i ∈ range K, incidentLoad (P i) v := by
  classical
  unfold PrivateTemplateStage69.rootLoad
  rw [card_filter]
  apply sum_le_sum
  intro i _
  split_ifs with hv
  · obtain ⟨_, e, he, hve⟩ := mem_filter.mp hv
    have hpos : 0 < incidentLoad (P i) v := by
      exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hve⟩⟩
    exact hpos
  · exact Nat.zero_le _

/-- A fixed universal absorber from a supplied possibly overlapping library.
There is no global pairwise-disjointness premise on `P`. -/
theorem universal_from_library (m : ℕ) (cls : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    (γ T D Λ ρ : ℝ) (hγ : 0 < γ) (hT : 0 < T)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((ClassRepresentativesStage65.classSet cls i).card : ℝ))
    (h1 : (2 * m + 3 : ℝ) * D < γ ^ 2 * Fintype.card V / 4)
    (h2 : 2 ≤ γ ^ 2 * Fintype.card V / 4)
    (h3 : 56 * D ≤ γ ^ 3 * Fintype.card V / 8)
    (h4 : 4 * D ≤ γ ^ 2 * Fintype.card V / 4)
    (h5 : (SignedHinge.absorberBudget 6 (12 * m) : ℝ) < γ ^ 2 * Fintype.card V / 8)
    (h6 : (2 ^ 21 : ℝ) * SignedHinge.absorberBudget 6 (12 * m) <
      γ ^ 3 * Fintype.card V / 64)
    (X R : Finset (Sym2 V)) (hRX : Disjoint R X)
    (hRG : R ⊆ G.edgeFinset)
    (hledger : DegBounded (X ∪ R) ρ)
    (hD : max ρ (T + templateConst m) + templateConst m * Λ + 2 * m ≤ D)
    (K : ℕ) (P : ℕ → Finset (Sym2 V))
    (href : RefinerAssembly.RefinesReserve (p := cls) (F := F3) (range K) P X R)
    (hpieces : ∀ i < K, P i ⊆ X ∪ R)
    (hPG : ∀ i < K, P i ⊆ G.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m)
    (hdiv : ∀ i < K, IsIntDiv cls F3 (P i))
    (hload : ∀ v, (PrivateTemplateStage69.rootLoad P K v : ℝ) ≤ Λ)
    (hcount : 4 * (((X ∪ R).card : ℝ) + K * templateConst m) ≤ T * γ * Fintype.card V) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp cls F3 A ∧ DegBounded A D ∧
      ∀ L ⊆ X, IsIntDiv cls F3 L → HasDecomp cls F3 (A ∪ L) := by
  obtain ⟨priv, hpriv, hdis, _, hdeg⟩ :=
    family_private_absorbers m cls G hG γ T D Λ ρ hγ hT hsize h1 h2 h3 h4 h5 h6
      (X ∪ R) hledger hD K P hPG hm hdiv hload hcount
  have hcompose := RefinerAssembly.universal_of_refiner (range K) priv P X R hRX href
    (fun i hi => (hpriv i (mem_range.mp hi)).2.2.1)
    (fun i hi => (hpriv i (mem_range.mp hi)).2.2.2.1)
    (fun i hi j hj hij => hdis i (mem_range.mp hi) j (mem_range.mp hj) hij)
    (fun i hi => (hpriv i (mem_range.mp hi)).2.1)
    (fun i hi => hpieces i (mem_range.mp hi))
  refine ⟨R ∪ (range K).biUnion priv, ?_, hcompose.1, hcompose.2.1, ?_, hcompose.2.2⟩
  · exact union_subset hRG (biUnion_subset.mpr fun i hi => (hpriv i (mem_range.mp hi)).1)
  · intro v
    have hmono : (incidentLoad (R ∪ (range K).biUnion priv) v : ℝ) ≤
        incidentLoad ((X ∪ R) ∪ (range K).biUnion priv) v := by
      exact_mod_cast incidentLoad_mono (by
        intro e he
        rcases mem_union.mp he with he | he
        · exact mem_union_left _ (mem_union_right _ he)
        · exact mem_union_right _ he) v
    exact hmono.trans (hdeg v)

/-- Linear-in-order root incidence fits the private-family budget.
The old constant-load asymptotic corollary is not needed. -/
theorem linear_root_budget (C Λ δ n ρ : ℝ)
    (hn : 0 ≤ δ * n) (hρ : ρ ≤ δ * n) (hfixed : C ≤ δ * n / 2)
    (hload : C * Λ + 2 * (1050 : ℝ) ≤ δ * n / 2) :
    max ρ (δ * n + C) + C * Λ + 2 * (1050 : ℝ) ≤ 2 * δ * n := by
  have hmax : max ρ (δ * n + C) ≤ δ * n + δ * n / 2 :=
    max_le (by linarith) (by linarith)
  linarith

/-- A stronger, non-circular scale choice simultaneously pays the refiner
ledger, linear root load, and total private edge count. This is arithmetic,
not a fractional-packing producer or a host-embedding theorem. -/
theorem compatible_scales (C γ δ lam rho : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hγ1 : γ ≤ 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hs : (2 ^ 24 : ℝ) * (C + 1) * lam ≤ γ * δ)
    (hr : (2 ^ 43 : ℝ) * rho ≤ lam ^ 2) :
    8 * lam + 2 * rho ≤ δ ∧
      4200 * C * lam ≤ δ / 4 ∧
      8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho ≤ γ * δ / 4 := by
  have hClam : 0 ≤ C * lam := mul_nonneg hC hlam
  have hγδ : γ * δ ≤ δ := mul_le_of_le_one_left hδ hγ1
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith
  have hCr := mul_le_mul_of_nonneg_left hr hC
  have hClam2 : C * lam ^ 2 ≤ C * lam := mul_le_mul_of_nonneg_left hlam2 hC
  norm_num at hs hr hCr
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end PartitionedTriangleAbsorption.StructuralAbsorberStage70
