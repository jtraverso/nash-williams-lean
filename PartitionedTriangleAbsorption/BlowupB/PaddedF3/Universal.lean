/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedScales
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.UniversalF3

@[expose] public section

/-!
# A universal F₃ absorber with explicit budgets

`StructuralF3General.universal_F3_budget` produces the universal absorber with
an existential terminal order. For the padded statement the extension order
must be bounded by `qT * hKT` for every `m`, so it has to be explicit.

The four F₃ types have linearly independent edge vectors and no internal edge,
so the integral witness of a divisible piece is unique:
`c₀₁₂ = (x₀₁ + x₀₂ - x₀₃)/2`, etc. With `0 ≤ x_ij ≤ K` every coefficient is at
least `-K/2`, hence the negative mass is at most `4 K`. With the 1050-edge
structural library this gives terminal order `478804` and size `1445850`, both
below `2^21`, exactly the budgets of the F₁/F₂ assembly.
-/

namespace PaddedF3

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12

universe u

theorem pairVec_cross_bounds {W : Type*} (p : W → Fin 4) (e : Sym2 W) {i j : Fin 4}
    (hij : i ≠ j) : 0 ≤ pairVec p e i j ∧ pairVec p e i j ≤ 1 := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [pairVec, Sym2.lift_mk]
    split_ifs with h1 h2 h2
    · exact absurd (h1.1.symm.trans h2.2) hij
    all_goals norm_num

theorem edgeVec_cross_bounds {W : Type*} [DecidableEq W] (p : W → Fin 4)
    (P : Finset (Sym2 W)) {i j : Fin 4} (hij : i ≠ j) :
    0 ≤ edgeVec p P i j ∧ edgeVec p P i j ≤ P.card := by
  unfold edgeVec
  rw [Finset.sum_apply, Finset.sum_apply]
  refine ⟨sum_nonneg fun e _ => (pairVec_cross_bounds p e hij).1, ?_⟩
  calc
    _ ≤ ∑ _e ∈ P, (1 : ℤ) := sum_le_sum fun e _ => (pairVec_cross_bounds p e hij).2
    _ = P.card := by simp

theorem tev01 : typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 1 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 1 = 1 ∧
    typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) 0 1 = 0 ∧
    typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) 0 1 = 0 := by decide
theorem tev02 : typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 2 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 2 = 0 ∧
    typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) 0 2 = 1 ∧
    typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) 0 2 = 0 := by decide
theorem tev03 : typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 3 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 3 = 1 ∧
    typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) 0 3 = 1 ∧
    typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) 0 3 = 0 := by decide
theorem tev12 : typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 1 2 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 1 2 = 0 ∧
    typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) 1 2 = 0 ∧
    typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) 1 2 = 1 := by decide
theorem tev13 : typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 1 3 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 1 3 = 1 ∧
    typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) 1 3 = 0 ∧
    typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) 1 3 = 1 := by decide
theorem tev23 : typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 2 3 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 2 3 = 0 ∧
    typeEdgeVec ({0, 2, 3} : Multiset (Fin 4)) 2 3 = 1 ∧
    typeEdgeVec ({1, 2, 3} : Multiset (Fin 4)) 2 3 = 1 := by decide

/-- A sum over `F₃` written out on its four types. -/
theorem sum_F3 {β : Type*} [AddCommMonoid β] (f : Multiset (Fin 4) → β) :
    ∑ τ ∈ F3, f τ = f {0, 1, 2} + f {0, 1, 3} + f {0, 2, 3} + f {1, 2, 3} := by
  unfold F3
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  abel

/-- **Explicit F₃ witness.** The unique integral witness has negative mass at most `4 K`. -/
theorem f3_bounded_coefficients (K : ℕ) {W : Type*} [DecidableEq W] (p : W → Fin 4)
    (P : Finset (Sym2 W)) (hK : P.card ≤ K) (hdiv : IsIntDiv p F3 P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ F3, c τ • typeEdgeVec τ ∧
      negativeMass F3 c ≤ 4 * K := by
  obtain ⟨c, hc⟩ := hdiv.1
  refine ⟨c, hc, ?_⟩
  have hent : ∀ i j : Fin 4, edgeVec p P i j =
      c {0, 1, 2} * typeEdgeVec {0, 1, 2} i j + c {0, 1, 3} * typeEdgeVec {0, 1, 3} i j +
      c {0, 2, 3} * typeEdgeVec {0, 2, 3} i j + c {1, 2, 3} * typeEdgeVec {1, 2, 3} i j := by
    intro i j
    rw [hc, Finset.sum_apply, Finset.sum_apply, sum_F3]
    simp only [Pi.smul_apply, smul_eq_mul]
  have e01 := hent 0 1
  have e02 := hent 0 2
  have e03 := hent 0 3
  have e12 := hent 1 2
  have e13 := hent 1 3
  have e23 := hent 2 3
  obtain ⟨a1, a2, a3, a4⟩ := tev01
  rw [a1, a2, a3, a4] at e01
  obtain ⟨a1, a2, a3, a4⟩ := tev02
  rw [a1, a2, a3, a4] at e02
  obtain ⟨a1, a2, a3, a4⟩ := tev03
  rw [a1, a2, a3, a4] at e03
  obtain ⟨a1, a2, a3, a4⟩ := tev12
  rw [a1, a2, a3, a4] at e12
  obtain ⟨a1, a2, a3, a4⟩ := tev13
  rw [a1, a2, a3, a4] at e13
  obtain ⟨a1, a2, a3, a4⟩ := tev23
  rw [a1, a2, a3, a4] at e23
  have b01 := edgeVec_cross_bounds p P (show (0 : Fin 4) ≠ 1 by decide)
  have b02 := edgeVec_cross_bounds p P (show (0 : Fin 4) ≠ 2 by decide)
  have b03 := edgeVec_cross_bounds p P (show (0 : Fin 4) ≠ 3 by decide)
  have b12 := edgeVec_cross_bounds p P (show (1 : Fin 4) ≠ 2 by decide)
  have b13 := edgeVec_cross_bounds p P (show (1 : Fin 4) ≠ 3 by decide)
  have b23 := edgeVec_cross_bounds p P (show (2 : Fin 4) ≠ 3 by decide)
  have hKZ : (P.card : ℤ) ≤ K := by exact_mod_cast hK
  unfold negativeMass
  rw [sum_F3]
  omega

theorem f3_terminal_budgets :
    terminalOrder 1050 (4 * 1050) 4 = 478804 ∧
    terminalSize 1050 (4 * 1050) = 1445850 ∧
    terminalOrder 1050 (4 * 1050) 4 ≤ 2 ^ 21 ∧
    terminalSize 1050 (4 * 1050) ≤ 2 ^ 21 := by decide

/-- A uniform numerical terminal producer for the 1050-edge F₃ library. -/
theorem guarded_terminal_F3 {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) (2 ^ 21) a)
    (hL : DegBounded L d) (hd : 0 ≤ d)
    (hbudget : (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a)
    (P : Finset (Sym2 V)) (hK : P.card ≤ 1050) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hdiv : IsIntDiv p F3 P) :
    ∃ A : Finset (Sym2 V), TerminalAbsorber p F3 G P L Z (2 ^ 21) A := by
  have hq : terminalOrder 1050 (4 * 1050) 4 ≤ 2 ^ 21 := f3_terminal_budgets.2.2.1
  have hqR : (terminalOrder 1050 (4 * 1050) 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hq
  have hbudget' : (terminalOrder 1050 (4 * 1050) 4 : ℝ) + Z.card +
      terminalOrder 1050 (4 * 1050) 4 * d < a := by
    have hm := mul_le_mul_of_nonneg_right hqR hd
    linarith
  obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass F3 ColouredHub.F3_card_three F3_three_step
    1050 (4 * 1050)
    (fun pW PW hKW hdivW => f3_bounded_coefficients 1050 pW PW hKW hdivW)
    p G a d L Z (hs.mono hq le_rfl) hL hd hbudget' P hK hloop hdiv
  exact ⟨A, { hA with card_le := hA.card_le.trans f3_terminal_budgets.2.2.2 }⟩

/-- The private terminal step with the fixed 1050-edge input and `2^21` budgets. -/
theorem guarded_privateStep_F3 {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (a T D : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) (2 ^ 21) a)
    (hD0 : 0 ≤ D) (hT : 0 < T)
    (hbudget : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * D < a / 2) :
    PrivateStep p F3 G 1050 (2 ^ 21) T D a := by
  intro L hL hLc P hPG hm hdiv
  classical
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ a / 2 := by
    have hc := card_highLoad_le L T
    change (High.card : ℝ) * T ≤ 2 * L.card at hc
    nlinarith
  have hbudget' : (2 ^ 21 : ℝ) + High.card + (2 ^ 21 : ℝ) * D < a := by
    linarith
  have hloop : ∀ e ∈ P, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hPG he)
      intro hd
      exact G.ne_of_adj hxy (by simpa using hd)
  obtain ⟨A, hA⟩ := guarded_terminal_F3 p G a D L High hs hL hD0 hbudget' P hm hloop hdiv
  refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
  intro v hv
  rcases hA.vertices v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

/-- `universal_F3_budget` with the explicit budgets `S = C = 2^21`. -/
theorem universal_F3_budget_explicit :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
      (γ lam rho δ : ℝ),
      (∀ x y, G.Adj x y → cls x ≠ cls y) →
      GuardedSupply cls G (fun i j => i ≠ j) (2 ^ 21) (γ * Fintype.card V) →
      0 < lam → lam ≤ 1 / 64 → 32 * lam ≤ γ → 0 < rho →
      2 ^ 42 * rho ≤ lam ^ 2 →
      1 ≤ rho * Fintype.card V → 256 ≤ lam * Fintype.card V → 0 < δ →
      ((2 ^ 21 : ℕ) : ℝ) + ((2 ^ 21 : ℕ) : ℝ) * (2 * δ * Fintype.card V) <
        γ * Fintype.card V / 2 →
      ((2 ^ 21 : ℕ) : ℝ) ≤ δ * Fintype.card V / 4 →
      8 * lam + 2 * rho ≤ δ → 4200 * ((2 ^ 21 : ℕ) : ℝ) * lam ≤ δ / 4 →
      8 * lam + 2 * rho + (2 ^ 35 : ℝ) * ((2 ^ 21 : ℕ) : ℝ) * rho ≤ γ * δ / 4 →
      UniversalAbsorbers cls F3 G rho δ := by
  intro V _ _ cls G _ γ lam rho δ hG hs hlam hlam64 hlamγ hrho hscale hn1 hn2 hδ hembed hfixed
    hledgerScale hrootScale hcountScale
  classical
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ 21 := ⟨_, rfl⟩
  rw [← hCdef] at hs hembed hfixed hrootScale hcountScale
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
    hs.mono (by rw [hCdef]; norm_num) le_rfl
  obtain ⟨hclasses, hanti, hanti1⟩ := guarded_F3_inputs cls G γ hs2
  have hsAllowed : GuardedSupply cls G (fun i j => ∃ k, Link F3 i j k) (2 ^ 21)
      (γ * Fintype.card V) := by
    rw [← hCdef]
    intro U hU i hguard
    exact hs U hU i fun u hu => (F3_allowed_iff _ _).mp (hguard u hu)
  have hembed' : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n / 2 := by
    rw [hCdef] at hembed
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hembed
  have hstep : PrivateFamily.PrivateStep cls F3 G 1050 C
      (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    exact guarded_privateStep_F3 cls G (γ * n) (δ * n) (2 * δ * n) hsAllowed (by positivity)
      (by positivity) hembed'
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
    have h1 : (C : ℝ) * (4200 * lam * n) = 4200 * C * lam * n := by ring
    have h2 : 0 ≤ δ * n := mul_nonneg hδ.le hn0
    linarith [hmax, hfixed, hrootN, h1, h2]
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

/-- The uniform version, with the explicit query order and terminal size `2^21`. -/
theorem universal_F3_uniform_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ)
    (hG : ∀ x y, G.Adj x y → cls x ≠ cls y)
    (hs : GuardedSupply cls G (fun i j => i ≠ j) (2 ^ 21) (γ * Fintype.card V))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hsmall : 64 * (((2 ^ 21 : ℕ) : ℝ) + 1) * δ ≤ γ)
    (hn1 : 1 ≤ refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ * Fintype.card V) :
    UniversalAbsorbers cls F3 G (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ := by
  obtain ⟨hlam, hlam64, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩ :=
    uniform_scalar_budget ((2 ^ 21 : ℕ) : ℝ) ((2 ^ 21 : ℕ) : ℝ) γ δ (Fintype.card V)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hγ hγ1 hδ hsmall (Nat.cast_nonneg _) hn1
  exact universal_F3_budget_explicit cls G γ (refinerLambda ((2 ^ 21 : ℕ) : ℝ) γ δ)
    (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ hG hs hlam hlam64 hlamγ hrho hscale hn1 hn2 hδ
    hembed hfixed hledger hroot hcount

/-- The F₃ analogue of `Family.universal_simple`, at the padded scales. -/
theorem universal_simple_F3 {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link F3 (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) (2 ^ 21) (ω * Fintype.card V))
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 1 ≤ paddedRho ω * Fintype.card V) :
    UniversalAbsorbers p F3 G (paddedRho ω) (paddedAbsDelta ω) := by
  have hsmall : 64 * ((((2 ^ 21 : ℕ) : ℝ)) + 1) * paddedAbsDelta ω ≤ ω := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using padded_delta_small hω.le hω1
  have hρ : paddedRho ω ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using paddedRho_le_refiner hω.le
  have hn' : 1 ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) *
      Fintype.card V := hn.trans (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
  have hG' : ∀ x y, G.Adj x y → p x ≠ p y := fun x y h => (F3_allowed_iff _ _).mp (hG x y h)
  have hs' : GuardedSupply p G (fun i j => i ≠ j) (2 ^ 21) (ω * Fintype.card V) := by
    intro U hU i hguard
    exact hs U hU i fun u hu => (F3_allowed_iff _ _).mpr (hguard u hu)
  exact universalAbsorbers_mono_rho p F3 G
    (universal_F3_uniform_explicit p G ω (paddedAbsDelta ω) hG' hs' hω hω1
      (paddedAbsDelta_pos hω) hsmall hn') hρ

#print axioms f3_bounded_coefficients
#print axioms guarded_terminal_F3
#print axioms universal_F3_budget_explicit
#print axioms universal_simple_F3

end PaddedF3
