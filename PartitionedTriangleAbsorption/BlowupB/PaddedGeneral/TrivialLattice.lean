/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Universal
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

/-!
# Universal absorbers for every family with a trivial lattice

`TrivialLattice F`: on loopless active edge sets, ordinary divisibility (`Even3`) already implies
`IsIntDiv p F`. For such F with `ThreeStepLinks`, common neighbour classes, and an explicit
witness bound `B` for 42-edge pieces with terminal order and size `≤ 2^21`, the ORDINARY refiner
gives `UniversalCert F`. The proof is the F* argument with F as a parameter.
-/

namespace PaddedGeneral

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12

universe u

/-- Trivial lattice: on loopless sets, F-divisibility is ordinary divisibility of active sets. -/
def TrivialLattice (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V)),
    (∀ e ∈ E, ¬ e.IsDiag) → (IsIntDiv p F E ↔ ActiveEdges F p E ∧ OnePart.Even3 E)

/-- Explicit witness bound `B` for pieces of at most 42 edges. -/
def WitnessBound (F : Finset (Multiset (Fin 4))) (B : ℕ) : Prop :=
  ∀ {W : Type} [DecidableEq W] (p : W → Fin 4) (P : Finset (Sym2 W)),
    P.card ≤ 42 → IsIntDiv p F P → ∃ c : Multiset (Fin 4) → ℤ,
      edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ negativeMass F c ≤ B

theorem universal_budget_of_trivial (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (hcommon : ∀ a b : Fin 4, ∃ c, (∃ k, Link F a c k) ∧ (∃ k, Link F b c k))
    (htriv : TrivialLattice F) (B : ℕ) (hB : WitnessBound F B)
    (hord : terminalOrder 42 B 4 ≤ 2 ^ 21) (hsize : terminalSize 42 B ≤ 2 ^ 21) :
    ∀ {V : Type} [Fintype V] [DecidableEq V]
      (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
      (γ lam rho δ : ℝ),
      (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (γ * Fintype.card V) →
      0 < lam → lam ≤ 1 / 64 → 32 * lam ≤ γ → 0 < rho →
      2 ^ 42 * rho ≤ lam ^ 2 →
      1 ≤ rho * Fintype.card V → 256 ≤ lam * Fintype.card V → 0 < δ →
      ((2 ^ 21 : ℕ) : ℝ) + ((2 ^ 21 : ℕ) : ℝ) * (2 * δ * Fintype.card V) <
        γ * Fintype.card V / 2 →
      ((2 ^ 21 : ℕ) : ℝ) ≤ δ * Fintype.card V / 4 →
      8 * lam + 2 * rho ≤ δ → 4200 * ((2 ^ 21 : ℕ) : ℝ) * lam ≤ δ / 4 →
      8 * lam + 2 * rho + (2 ^ 35 : ℝ) * ((2 ^ 21 : ℕ) : ℝ) * rho ≤ γ * δ / 4 →
      UniversalAbsorbers p F G rho δ := by
  intro V _ _ p G _ γ lam rho δ hG hs hlam hlam64 hlamγ hrho hscale hn1 hn2 hδ hembed hfixed
    hledgerScale hrootScale hcountScale
  classical
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ 21 := ⟨_, rfl⟩
  rw [← hCdef] at hembed hfixed hrootScale hcountScale
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := le_antisymm (le_of_not_gt h) hn0
    change 1 ≤ rho * n at hn1
    rw [heq, mul_zero] at hn1
    norm_num at hn1
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hanti : AntiEdgeful OnePart.part1 OnePart.triFam G γ :=
    hs.to_ordinaryAntiEdgeful (by norm_num) hcommon
  have hembed' : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n / 2 := by
    rw [hCdef] at hembed
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hembed
  -- the terminal step
  have hterminal : ∀ (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V),
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a →
      DegBounded L d → 0 ≤ d → (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a →
      ∀ P : Finset (Sym2 V), P.card ≤ 42 → (∀ e ∈ P, ¬ e.IsDiag) → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (2 ^ 21) A := by
    intro a d L Z hsa hL hd hbudget P hK hloop hdiv
    have hqR : (terminalOrder 42 B 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hord
    have hbudget' : (terminalOrder 42 B 4 : ℝ) + Z.card + terminalOrder 42 B 4 * d < a := by
      have hm := mul_le_mul_of_nonneg_right hqR hd
      linarith
    obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass F hcard hthree 42 B
      (fun pW PW hKW hdivW => hB pW PW hKW hdivW)
      p G a d L Z (hsa.mono hord le_rfl) hL hd hbudget' P hK hloop hdiv
    exact ⟨A, { hA with card_le := hA.card_le.trans hsize }⟩
  have hstep : PrivateFamily.PrivateStep p F G 42 C (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    intro L hL hLc P hPG hm hdiv
    let High : Finset V := univ.filter fun v => (δ * n) < (incidentLoad L v : ℝ)
    have hHigh : (High.card : ℝ) ≤ γ * n / 2 := by
      have hc := card_highLoad_le L (δ * n)
      change (High.card : ℝ) * (δ * n) ≤ 2 * L.card at hc
      have hδn : 0 < δ * n := by positivity
      nlinarith
    have hbudget' : (2 ^ 21 : ℝ) + High.card + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n := by
      linarith
    have hloop : ∀ e ∈ P, ¬ e.IsDiag := by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hPG he)
        intro hd
        exact G.ne_of_adj hxy (by simpa using hd)
    obtain ⟨A, hA⟩ := hterminal (γ * n) (2 * δ * n) L High hs hL (by positivity) hbudget' P hm
      hloop hdiv
    refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
    intro v hv
    rcases hA.vertices v hv with hp | hz
    · exact Or.inl hp
    · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))
  intro X hXG hX
  obtain ⟨indices, pieces, R, hRG, hRX, href, hpieces, hRdeg, hcard', hinc⟩ :=
    exists_universal_refiner_alpha G X hXG lam rho hlam hlam64 hrho
      (by nlinarith only [hscale, hrho.le]) hn1 hn2 hX γ (by linarith) hanti
  have hactG : ∀ P ⊆ G.edgeFinset, ActiveEdges F p P := fun P hP a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hP hab))
  have hloopG : ∀ P ⊆ G.edgeFinset, ∀ e ∈ P, ¬ e.IsDiag :=
    fun P hP e he => G.not_isDiag_of_mem_edgeFinset (hP he)
  have href' : RefinerAssembly.RefinesReserve (p := p) (F := F) indices pieces X R := by
    intro L hL hdivL
    have hloop := hloopG L (hL.trans hXG)
    have h3 : OnePart.Even3 L := ((htriv p L hloop).mp hdivL).2
    exact href L hL ((OnePart.isIntDiv_part1_iff L hloop).mpr h3)
  have hledger : DegBounded (X ∪ R) ((8 * lam + 2 * rho) * n) := by
    intro v
    have h := degBounded_union hX hRdeg v
    have h4 : 2 * rho * Fintype.card V + 4 * lam * Fintype.card V ≤ (8 * lam + 2 * rho) * n := by
      have := mul_le_mul_of_nonneg_right (show 4 * lam ≤ 8 * lam by linarith) hn0
      dsimp only [n]; nlinarith
    linarith
  have hinc' : ∀ v, ((∑ i ∈ indices, incidentLoad (pieces i) v : ℕ) : ℝ) ≤ 4200 * lam * n := by
    intro v
    have := hinc v
    have h2 : 4096 * lam * Fintype.card V ≤ 4200 * lam * n := by
      dsimp only [n]
      have := mul_le_mul_of_nonneg_right (show 4096 * lam ≤ 4200 * lam by linarith) hn0
      nlinarith
    linarith
  have hcard'' : (indices.card : ℝ) ≤ 2 ^ 35 * rho * n ^ 2 := by
    have h2 : (1224 : ℝ) * rho * (Fintype.card V : ℝ) ^ 2 ≤ 2 ^ 35 * rho * n ^ 2 := by
      dsimp only [n]
      have := mul_le_mul_of_nonneg_right (show (1224 : ℝ) * rho ≤ 2 ^ 35 * rho by nlinarith)
        (sq_nonneg (Fintype.card V : ℝ))
      linarith
    linarith
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
    have hKC := mul_le_mul_of_nonneg_right hcard'' hC0
    change ((X ∪ R).card : ℝ) ≤ n * ((8 * lam + 2 * rho) * n) at hLC
    calc
      _ ≤ 4 * (n * ((8 * lam + 2 * rho) * n) + (2 ^ 35 * rho * n ^ 2) * C) := by
        linarith
      _ = 4 * (8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho) * n ^ 2 := by ring
      _ ≤ 4 * (γ * δ / 4) * n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountScale (by norm_num))
          (sq_nonneg n)
      _ = (δ * n) * (γ * n) := by ring
  exact FiniteLibrary.universal_from_finite_library p F G 42 C (δ * n) (2 * δ * n)
    (4200 * lam * n) ((8 * lam + 2 * rho) * n) (γ * n) hstep X R hRX hXG hRG
    hledger hdegree indices pieces href' (fun i hi => (hpieces i hi).1)
    (fun i hi => (hpieces i hi).2.2.2.2)
    (fun i hi => (htriv p (pieces i)
      (hloopG _ ((hpieces i hi).1.trans (union_subset hXG hRG)))).mpr
      ⟨hactG _ ((hpieces i hi).1.trans (union_subset hXG hRG)),
        (hpieces i hi).2.2.2.1, (hpieces i hi).2.2.1⟩)
    hinc' hcount

/-- **`UniversalCert` for every family with a trivial lattice** (and the finite side conditions). -/
theorem universalCert_of_trivial (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (hcommon : ∀ a b : Fin 4, ∃ c, (∃ k, Link F a c k) ∧ (∃ k, Link F b c k))
    (htriv : TrivialLattice F) (B : ℕ) (hB : WitnessBound F B)
    (hord : terminalOrder 42 B 4 ≤ 2 ^ 21) (hsize : terminalSize 42 B ≤ 2 ^ 21) :
    UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  have hsmall : 64 * ((((2 ^ 21 : ℕ) : ℝ)) + 1) * paddedAbsDelta ω ≤ ω := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using padded_delta_small hω.le hω1
  have hρ : paddedRho ω ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using paddedRho_le_refiner hω.le
  have hn' : 1 ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) *
      Fintype.card V := hn.trans (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
  obtain ⟨hlam, hlam64, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩ :=
    uniform_scalar_budget ((2 ^ 21 : ℕ) : ℝ) ((2 ^ 21 : ℕ) : ℝ) ω (paddedAbsDelta ω)
      (Fintype.card V) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hω hω1 (paddedAbsDelta_pos hω)
      hsmall (Nat.cast_nonneg _) hn'
  exact universalAbsorbers_mono_rho p F G
    (universal_budget_of_trivial F hcard hthree hcommon htriv B hB hord hsize p G ω
      (refinerLambda ((2 ^ 21 : ℕ) : ℝ) ω (paddedAbsDelta ω))
      (refinerRho ((2 ^ 21 : ℕ) : ℝ) ω (paddedAbsDelta ω)) (paddedAbsDelta ω) hG hs
      hlam hlam64 hlamγ hrho hscale hn' hn2 (paddedAbsDelta_pos hω) hembed hfixed hledger hroot
      hcount) hρ

/-- Sanity check: F* is an instance. -/
theorem universalCert_Fstar_via_trivial : UniversalCert PaddedFstar.Fstar :=
  universalCert_of_trivial PaddedFstar.Fstar PaddedFstar.Fstar_card PaddedFstar.Fstar_three_step
    PaddedFstar.fstar_common (fun p E hloop => PaddedFstar.isIntDiv_Fstar_iff p E hloop)
    (8 * 42 + 40) (fun p P hK hdiv => PaddedFstar.fstar_bounded_coefficients 42 p P hK hdiv)
    PaddedFstar.fstar_terminal_budgets.2.2.1 PaddedFstar.fstar_terminal_budgets.2.2.2

#print axioms universalCert_of_trivial
#print axioms universalCert_Fstar_via_trivial

end PaddedGeneral
