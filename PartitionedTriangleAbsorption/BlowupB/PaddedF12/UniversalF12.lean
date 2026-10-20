/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.FamilyRefiner
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ExplicitLedger
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.UniformScales

/-!
# Universal F1 and F2 absorbers in guarded extendible hosts

The terminal size and extension order are fixed before the host density, the
host graph and the reserve. The single absorber is then fixed before every
later integrally divisible leftover contained in the reserve.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

/-- The complete universal absorber, with explicit scalar budgets and no
refiner, token or absorber existence premise. -/
theorem universal_F12_budget (kind : Family) :
    ∃ S C : ℕ, S = 2 ^ 21 ∧ C = 2 ^ 21 ∧ 6 ≤ S ∧ 1 ≤ C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
        (γ lam rho δ : ℝ),
        (∀ a b, G.Adj a b → ∃ k, Link kind.types (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) S (γ * Fintype.card V) →
        γ ≤ 1 → 0 < lam → 1024 * lam ≤ γ → 0 < rho →
        2 ^ 32 * rho ≤ lam ^ 2 →
        1 ≤ rho * Fintype.card V → 256 ≤ lam * Fintype.card V → 0 < δ →
        (S : ℝ) + S * (2 * δ * Fintype.card V) < γ * Fintype.card V / 2 →
        (C : ℝ) ≤ δ * Fintype.card V / 4 →
        6 * lam + 2 * rho ≤ δ → (2 ^ 14 : ℝ) * C * lam ≤ δ / 4 →
        6 * lam + 2 * rho + (2 ^ 23 : ℝ) * C * rho ≤ γ * δ / 4 →
        UniversalAbsorbers p kind.types G rho δ := by
  let S : ℕ := 2 ^ 21
  let C : ℕ := 2 ^ 21
  have hS : 6 ≤ S := by norm_num [S]
  have hC : 1 ≤ C := by norm_num [C]
  have hkind : kind.types = F1 ∨ kind.types = F2 := by cases kind <;> simp [Family.types]
  refine ⟨S, C, rfl, rfl, hS, hC, fun {V} _ _ p G _ γ lam rho δ hG hs hγ1 hlam hlamγ hrho
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
  have hs6 : GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) 6
      (γ * Fintype.card V) := hs.mono hS le_rfl
  have hstep : PrivateFamily.PrivateStep p kind.types G 144 C
      (δ * n) (2 * δ * n) (γ * n) :=
    guarded_privateStep_F12 kind.types hkind p G (γ * n) (δ * n) (2 * δ * n) hs
      (by positivity) (by positivity) (by simpa only [S, Nat.cast_pow, Nat.cast_ofNat] using hembed)
  intro X hXG hX
  obtain ⟨indices, pieces, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    exists_F12_refiner kind p G hG γ lam rho hs6 hγ1 hlam hlamγ hrho hscale hn1 hn2 X hXG hX
  have hledger : DegBounded (X ∪ R) ((6 * lam + 2 * rho) * n) := by
    have h := degBounded_union hX hRdeg
    convert h using 1
    dsimp [n]
    ring
  have hdegree : max ((6 * lam + 2 * rho) * n) (δ * n + C) +
      C * ((2 ^ 14 : ℝ) * lam * n) ≤ 2 * δ * n := by
    have hledgerN := mul_le_mul_of_nonneg_right hledgerScale hn0
    have hrootN := mul_le_mul_of_nonneg_right hrootScale hn0
    have hmax : max ((6 * lam + 2 * rho) * n) (δ * n + C) ≤ δ * n + C :=
      max_le (by linarith) le_rfl
    change (C : ℝ) ≤ δ * n / 4 at hfixed
    have hrootN' : C * ((2 ^ 14 : ℝ) * lam * n) ≤ δ * n / 4 := by
      convert hrootN using 1 <;> ring
    calc
      _ ≤ δ * n + C + δ * n / 4 := add_le_add hmax hrootN'
      _ ≤ 2 * δ * n := by nlinarith only [hfixed, mul_nonneg hδ.le hn0]
  have hcount : 4 * (((X ∪ R).card : ℝ) + indices.card * C) ≤ (δ * n) * (γ * n) := by
    have hLC := FiniteLibrary.card_le_order_mul_degree (X ∪ R) ((6 * lam + 2 * rho) * n) hledger
    have hKC := mul_le_mul_of_nonneg_right hcard hC0
    change (indices.card : ℝ) * C ≤ (2 ^ 23 * rho * n ^ 2) * C at hKC
    change ((X ∪ R).card : ℝ) ≤ n * ((6 * lam + 2 * rho) * n) at hLC
    calc
      _ ≤ 4 * (n * ((6 * lam + 2 * rho) * n) + (2 ^ 23 * rho * n ^ 2) * C) := by linarith
      _ = 4 * (6 * lam + 2 * rho + (2 ^ 23 : ℝ) * C * rho) * n ^ 2 := by ring
      _ ≤ 4 * (γ * δ / 4) * n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountScale (by norm_num))
          (sq_nonneg n)
      _ = (δ * n) * (γ * n) := by ring
  exact FiniteLibrary.universal_from_finite_library p kind.types G 144 C (δ * n) (2 * δ * n)
    ((2 ^ 14 : ℝ) * lam * n) ((6 * lam + 2 * rho) * n) (γ * n) hstep X R hRX hXG hRG
    hledger hdegree indices pieces href (fun i hi => (hpieces i hi).1)
    (fun i hi => (hpieces i hi).2.2) (fun i hi => (hpieces i hi).2.1) hinc hcount

/-- The existing explicit scales have enough room for the F1/F2 parity layer. -/
theorem uniform_scalar_budget_F12 (S C γ δ n : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hsmall : 64 * (S + 1) * δ ≤ γ) (hn0 : 0 ≤ n)
    (hn1 : 1 ≤ refinerRho C γ δ * n) :
    let lam := refinerLambda C γ δ
    let rho := refinerRho C γ δ
    0 < lam ∧ 1024 * lam ≤ γ ∧ 0 < rho ∧
      2 ^ 32 * rho ≤ lam ^ 2 ∧ 256 ≤ lam * n ∧
      S + S * (2 * δ * n) < γ * n / 2 ∧ C ≤ δ * n / 4 ∧
      6 * lam + 2 * rho ≤ δ ∧ (2 ^ 14 : ℝ) * C * lam ≤ δ / 4 ∧
      6 * lam + 2 * rho + (2 ^ 23 : ℝ) * C * rho ≤ γ * δ / 4 := by
  dsimp only
  obtain ⟨hlam, hlam64, _, hrho, hscale, hn2, hembed, hfixed, hledger, _, hcount⟩ :=
    uniform_scalar_budget S C γ δ n hS hC hγ hγ1 hδ hsmall hn0 hn1
  let lam := refinerLambda C γ δ
  let rho := refinerRho C γ δ
  have hlamEq : (2 ^ 24 : ℝ) * (C + 1) * lam = γ * δ := by
    dsimp [lam, refinerLambda]
    field_simp
  have hClam : 0 ≤ C * lam := mul_nonneg hC hlam.le
  have hSδ : 0 ≤ S * δ := mul_nonneg hS hδ.le
  have hδ1 : δ ≤ 1 := by nlinarith only [hsmall, hSδ, hγ1]
  have hγδ1 : γ * δ ≤ γ := mul_le_of_le_one_right hγ.le hδ1
  have hγδ : γ * δ ≤ δ := mul_le_of_le_one_left hδ.le hγ1
  have hlam1024 : 1024 * lam ≤ γ := by
    norm_num at hlamEq
    nlinarith only [hlamEq, hClam, hlam.le, hγδ1]
  have hscale32 : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2 := by
    change (2 ^ 42 : ℝ) * rho ≤ lam ^ 2 at hscale
    nlinarith only [hscale, hrho.le]
  have hroot : (2 ^ 14 : ℝ) * C * lam ≤ δ / 4 := by
    norm_num at hlamEq ⊢
    nlinarith only [hlamEq, hClam, hlam.le, hγδ]
  have hledger6 : 6 * lam + 2 * rho ≤ δ := by
    change 8 * lam + 2 * rho ≤ δ at hledger
    linarith only [hledger, hlam.le]
  have hcount23 : 6 * lam + 2 * rho + (2 ^ 23 : ℝ) * C * rho ≤ γ * δ / 4 := by
    change 8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho ≤ γ * δ / 4 at hcount
    have hCrho : 0 ≤ C * rho := mul_nonneg hC hrho.le
    nlinarith only [hcount, hCrho, hlam.le]
  exact ⟨hlam, hlam1024, hrho, hscale32, hn2, hembed, hfixed, hledger6, hroot, hcount23⟩

/-- All density scales and host order requirements are fixed explicitly before
the reserve. The reserve has a degree bound but no cardinality bound. -/
theorem universal_F12_uniform (kind : Family) :
    ∃ S C : ℕ, S = 2 ^ 21 ∧ C = 2 ^ 21 ∧ 6 ≤ S ∧ 1 ≤ C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ),
        (∀ a b, G.Adj a b → ∃ k, Link kind.types (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) S (γ * Fintype.card V) →
        0 < γ → γ ≤ 1 → 0 < δ → 64 * ((S : ℝ) + 1) * δ ≤ γ →
        1 ≤ refinerRho C γ δ * Fintype.card V →
        UniversalAbsorbers p kind.types G (refinerRho C γ δ) δ := by
  obtain ⟨S, C, hSeq, hCeq, hS, hC, hmain⟩ := universal_F12_budget kind
  refine ⟨S, C, hSeq, hCeq, hS, hC, fun {V} _ _ p G _ γ δ hG hs hγ hγ1 hδ hsmall hn1 => ?_⟩
  obtain ⟨hlam, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩ :=
    uniform_scalar_budget_F12 S C γ δ (Fintype.card V) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hγ hγ1 hδ hsmall (Nat.cast_nonneg _) hn1
  exact hmain p G γ (refinerLambda C γ δ) (refinerRho C γ δ) δ hG hs hγ1
    hlam hlamγ hrho hscale hn1 hn2 hδ hembed hfixed hledger hroot hcount

theorem universal_F1_uniform :
    ∃ S C : ℕ, S = 2 ^ 21 ∧ C = 2 ^ 21 ∧ 6 ≤ S ∧ 1 ≤ C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ),
        (∀ a b, G.Adj a b → ∃ k, Link F1 (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F1 i j k) S (γ * Fintype.card V) →
        0 < γ → γ ≤ 1 → 0 < δ → 64 * ((S : ℝ) + 1) * δ ≤ γ →
        1 ≤ refinerRho C γ δ * Fintype.card V →
        UniversalAbsorbers p F1 G (refinerRho C γ δ) δ :=
  universal_F12_uniform .one

theorem universal_F2_uniform :
    ∃ S C : ℕ, S = 2 ^ 21 ∧ C = 2 ^ 21 ∧ 6 ≤ S ∧ 1 ≤ C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ),
        (∀ a b, G.Adj a b → ∃ k, Link F2 (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F2 i j k) S (γ * Fintype.card V) →
        0 < γ → γ ≤ 1 → 0 < δ → 64 * ((S : ℝ) + 1) * δ ≤ γ →
        1 ≤ refinerRho C γ δ * Fintype.card V →
        UniversalAbsorbers p F2 G (refinerRho C γ δ) δ :=
  universal_F12_uniform .two

#print axioms universal_F12_budget
#print axioms uniform_scalar_budget_F12
#print axioms universal_F12_uniform
#print axioms universal_F1_uniform
#print axioms universal_F2_uniform

end PaddedF12
