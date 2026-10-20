/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.Main
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostSupply
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedLedger
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.FiniteLibrary
public import PartitionedTriangleAbsorption.ColouredHub.Families

/-! # A fixed universal F3 absorber in a guarded extendible host

The refiner, the finite abstract terminal templates, their physical embeddings,
and the complete private family are constructed in this theorem.  The scalar
premises are numerical budgets, with constants chosen before the host.  There
is no completeness, refiner-existence, or absorber-existence premise.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection TypedApplicationLinks TypedTransformer

/-- The full universal quantifier over residues, with explicit density scales. -/
def UniversalAbsorbers {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ρ δ : ℝ) : Prop :=
  ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * ρ * Fintype.card V) →
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)

theorem F3_allowed_iff : ∀ i j : Fin 4, (∃ k, Link F3 i j k) ↔ i ≠ j := by
  unfold Link F3
  decide

theorem universal_F3_budget :
    ∃ S C : ℕ, 2 ≤ S ∧ 1 ≤ C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
        (γ lam rho δ : ℝ),
        (∀ x y, G.Adj x y → cls x ≠ cls y) →
        GuardedSupply cls G (fun i j => i ≠ j) S (γ * Fintype.card V) →
        0 < lam → lam ≤ 1 / 64 → 32 * lam ≤ γ → 0 < rho →
        2 ^ 42 * rho ≤ lam ^ 2 →
        1 ≤ rho * Fintype.card V → 256 ≤ lam * Fintype.card V → 0 < δ →
        (S : ℝ) + S * (2 * δ * Fintype.card V) < γ * Fintype.card V / 2 →
        (C : ℝ) ≤ δ * Fintype.card V / 4 →
        8 * lam + 2 * rho ≤ δ → 4200 * C * lam ≤ δ / 4 →
        8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho ≤ γ * δ / 4 →
        UniversalAbsorbers cls F3 G rho δ := by
  obtain ⟨B, hB⟩ := PrivateFamily.guarded_privateStep F3 ColouredHub.F3_card_three F3_three_step 1050
  let S := terminalOrder 1050 B 4
  let C := terminalSize 1050 B
  have hS : 2 ≤ S := by dsimp [S, terminalOrder]; omega
  have hC : 1 ≤ C := by dsimp [C, terminalSize]; omega
  refine ⟨S, C, hS, hC, fun {V} _ _ cls G _ γ lam rho δ hG hs hlam hlam64 hlamγ hrho
    hscale hn1 hn2 hδ hembed hfixed hledgerScale hrootScale hcountScale => ?_⟩
  classical
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := le_antisymm (le_of_not_gt h) hn0
    change 1 ≤ rho * n at hn1
    rw [heq, mul_zero] at hn1
    norm_num at hn1
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hs2 : GuardedSupply cls G (fun i j => i ≠ j) 2 (γ * Fintype.card V) :=
    hs.mono hS le_rfl
  obtain ⟨hclasses, hanti, hanti1⟩ := guarded_F3_inputs cls G γ hs2
  have hsAllowed : GuardedSupply cls G (fun i j => ∃ k, Link F3 i j k) S
      (γ * Fintype.card V) := by
    intro U hU i hguard
    exact hs U hU i fun u hu => (F3_allowed_iff _ _).mp (hguard u hu)
  have hstep : PrivateFamily.PrivateStep cls F3 G 1050 C
      (δ * n) (2 * δ * n) (γ * n) :=
    hB cls G (γ * n) (δ * n) (2 * δ * n) hsAllowed (by positivity)
      (by positivity) hembed
  intro X hXG hX
  obtain ⟨indices, pieces, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    exists_structural_refiner cls G hG γ lam rho hanti hanti1 hclasses
      hlam hlam64 hlamγ hrho hscale hn1 hn2 X hXG hX
  have hledger : DegBounded (X ∪ R) ((8 * lam + 2 * rho) * n) := by
    have h := degBounded_union hX hRdeg
    convert h using 1
    dsimp [n]
    ring
  have hdegree : max ((8 * lam + 2 * rho) * n) (δ * n + C) +
      C * (4200 * lam * n) ≤ 2 * δ * n := by
    have hledgerN := mul_le_mul_of_nonneg_right hledgerScale hn0
    have hrootN := mul_le_mul_of_nonneg_right hrootScale hn0
    have hmax : max ((8 * lam + 2 * rho) * n) (δ * n + C) ≤ δ * n + C :=
      max_le (by linarith) le_rfl
    change (C : ℝ) ≤ δ * n / 4 at hfixed
    nlinarith
  have hcount : 4 * (((X ∪ R).card : ℝ) + indices.card * C) ≤ (δ * n) * (γ * n) := by
    have hLC := FiniteLibrary.card_le_order_mul_degree (X ∪ R) ((8 * lam + 2 * rho) * n) hledger
    have hKC := mul_le_mul_of_nonneg_right hcard hC0
    change (indices.card : ℝ) * C ≤ (2 ^ 35 * rho * n ^ 2) * C at hKC
    change ((X ∪ R).card : ℝ) ≤ n * ((8 * lam + 2 * rho) * n) at hLC
    calc
      _ ≤ 4 * (n * ((8 * lam + 2 * rho) * n) + (2 ^ 35 * rho * n ^ 2) * C) := by
        linarith
      _ = 4 * (8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho) * n ^ 2 := by ring
      _ ≤ 4 * (γ * δ / 4) * n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountScale (by norm_num))
          (sq_nonneg n)
      _ = (δ * n) * (γ * n) := by ring
  exact FiniteLibrary.universal_from_finite_library cls F3 G 1050 C (δ * n) (2 * δ * n)
    (4200 * lam * n) ((8 * lam + 2 * rho) * n) (γ * n) hstep X R hRX hXG hRG
    hledger hdegree indices pieces href (fun i hi => (hpieces i hi).1)
    (fun i hi => (hpieces i hi).2.2) (fun i hi => (hpieces i hi).2.1) hinc hcount

#print axioms universal_F3_budget

end PartitionedTriangleAbsorption.StructuralF3General
