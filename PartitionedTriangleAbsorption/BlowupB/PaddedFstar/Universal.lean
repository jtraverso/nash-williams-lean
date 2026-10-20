/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Lattice
import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Universal

/-!
# A universal F* absorber from the ORDINARY refiner

F* has a trivial lattice (`isIntDiv_Fstar_iff`). Hence the ordinary universal refiner
(`exists_universal_refiner_alpha`, pieces even with `3 ∣ |P|`, at most 42 edges) already refines
F*-divisible leftovers into F*-divisible pieces. No charge or torsion layer is needed. Terminal
absorbers for the 42-edge pieces use the explicit witness bound `8·42 + 40 = 376`: order 40996 and
size 123978, both below `2^21`.
-/

namespace PaddedFstar

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12

universe u

theorem fstar_common : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link Fstar a c k) ∧ (∃ k, Link Fstar b c k) := by
  unfold Link Fstar
  decide

theorem fstar_terminal_budgets :
    terminalOrder 42 (8 * 42 + 40) 4 = 40996 ∧
    terminalSize 42 (8 * 42 + 40) = 123978 ∧
    terminalOrder 42 (8 * 42 + 40) 4 ≤ 2 ^ 21 ∧
    terminalSize 42 (8 * 42 + 40) ≤ 2 ^ 21 := by decide

theorem guarded_terminal_Fstar {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fstar i j k) (2 ^ 21) a)
    (hL : DegBounded L d) (hd : 0 ≤ d)
    (hbudget : (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a)
    (P : Finset (Sym2 V)) (hK : P.card ≤ 42) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hdiv : IsIntDiv p Fstar P) :
    ∃ A : Finset (Sym2 V), TerminalAbsorber p Fstar G P L Z (2 ^ 21) A := by
  have hq : terminalOrder 42 (8 * 42 + 40) 4 ≤ 2 ^ 21 := fstar_terminal_budgets.2.2.1
  have hqR : (terminalOrder 42 (8 * 42 + 40) 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hq
  have hbudget' : (terminalOrder 42 (8 * 42 + 40) 4 : ℝ) + Z.card +
      terminalOrder 42 (8 * 42 + 40) 4 * d < a := by
    have hm := mul_le_mul_of_nonneg_right hqR hd
    linarith
  obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass Fstar Fstar_card Fstar_three_step
    42 (8 * 42 + 40)
    (fun pW PW hKW hdivW => fstar_bounded_coefficients 42 pW PW hKW hdivW)
    p G a d L Z (hs.mono hq le_rfl) hL hd hbudget' P hK hloop hdiv
  exact ⟨A, { hA with card_le := hA.card_le.trans fstar_terminal_budgets.2.2.2 }⟩

theorem guarded_privateStep_Fstar {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (a T D : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fstar i j k) (2 ^ 21) a)
    (hD0 : 0 ≤ D) (hT : 0 < T)
    (hbudget : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * D < a / 2) :
    PrivateStep p Fstar G 42 (2 ^ 21) T D a := by
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
  obtain ⟨A, hA⟩ := guarded_terminal_Fstar p G a D L High hs hL hD0 hbudget' P hm hloop hdiv
  refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
  intro v hv
  rcases hA.vertices v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

/-- Pieces and leftovers in an F*-host: ordinary divisibility is F*-divisibility. -/
theorem isIntDiv_Fstar_of_even3 {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Fstar (p a) (p b) k)
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset) (h3 : OnePart.Even3 P) :
    IsIntDiv p Fstar P := by
  have hloop : ∀ e ∈ P, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeFinset (hPG he)
  refine (isIntDiv_Fstar_iff p P hloop).mpr ⟨fun a b hab => hG a b ?_, h3⟩
  exact SimpleGraph.mem_edgeFinset.mp (hPG hab)

/-- `universal_F3_budget_explicit` with the ordinary refiner, for F*. -/
theorem universal_Fstar_budget :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
      (γ lam rho δ : ℝ),
      (∀ a b, G.Adj a b → ∃ k, Link Fstar (p a) (p b) k) →
      GuardedSupply p G (fun i j => ∃ k, Link Fstar i j k) (2 ^ 21) (γ * Fintype.card V) →
      0 < lam → lam ≤ 1 / 64 → 32 * lam ≤ γ → 0 < rho →
      2 ^ 42 * rho ≤ lam ^ 2 →
      1 ≤ rho * Fintype.card V → 256 ≤ lam * Fintype.card V → 0 < δ →
      ((2 ^ 21 : ℕ) : ℝ) + ((2 ^ 21 : ℕ) : ℝ) * (2 * δ * Fintype.card V) <
        γ * Fintype.card V / 2 →
      ((2 ^ 21 : ℕ) : ℝ) ≤ δ * Fintype.card V / 4 →
      8 * lam + 2 * rho ≤ δ → 4200 * ((2 ^ 21 : ℕ) : ℝ) * lam ≤ δ / 4 →
      8 * lam + 2 * rho + (2 ^ 35 : ℝ) * ((2 ^ 21 : ℕ) : ℝ) * rho ≤ γ * δ / 4 →
      UniversalAbsorbers p Fstar G rho δ := by
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
    hs.to_ordinaryAntiEdgeful (by norm_num) fstar_common
  have hembed' : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n / 2 := by
    rw [hCdef] at hembed
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hembed
  have hstep : PrivateFamily.PrivateStep p Fstar G 42 C (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    exact guarded_privateStep_Fstar p G (γ * n) (δ * n) (2 * δ * n) hs (by positivity)
      (by positivity) hembed'
  intro X hXG hX
  obtain ⟨indices, pieces, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    exists_universal_refiner_alpha G X hXG lam rho hlam hlam64 hrho
      (by nlinarith only [hscale, hrho.le]) hn1 hn2 hX γ (by linarith) hanti
  have href' : RefinerAssembly.RefinesReserve (p := p) (F := Fstar) indices pieces X R := by
    intro L hL hdivL
    have hloop : ∀ e ∈ L, ¬ e.IsDiag :=
      fun e he => G.not_isDiag_of_mem_edgeFinset (hXG (hL he))
    have h3 := ((isIntDiv_Fstar_iff p L hloop).mp hdivL).2
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
  have hcard' : (indices.card : ℝ) ≤ 2 ^ 35 * rho * n ^ 2 := by
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
    have hKC := mul_le_mul_of_nonneg_right hcard' hC0
    change ((X ∪ R).card : ℝ) ≤ n * ((8 * lam + 2 * rho) * n) at hLC
    calc
      _ ≤ 4 * (n * ((8 * lam + 2 * rho) * n) + (2 ^ 35 * rho * n ^ 2) * C) := by
        linarith
      _ = 4 * (8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho) * n ^ 2 := by ring
      _ ≤ 4 * (γ * δ / 4) * n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountScale (by norm_num))
          (sq_nonneg n)
      _ = (δ * n) * (γ * n) := by ring
  exact FiniteLibrary.universal_from_finite_library p Fstar G 42 C (δ * n) (2 * δ * n)
    (4200 * lam * n) ((8 * lam + 2 * rho) * n) (γ * n) hstep X R hRX hXG hRG
    hledger hdegree indices pieces href' (fun i hi => (hpieces i hi).1)
    (fun i hi => (hpieces i hi).2.2.2.2)
    (fun i hi => isIntDiv_Fstar_of_even3 p G hG (pieces i)
      ((hpieces i hi).1.trans (union_subset hXG hRG))
      ⟨(hpieces i hi).2.2.2.1, (hpieces i hi).2.2.1⟩)
    hinc' hcount

/-- The uniform version at the refiner scales. -/
theorem universal_Fstar_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Fstar (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fstar i j k) (2 ^ 21) (γ * Fintype.card V))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hsmall : 64 * (((2 ^ 21 : ℕ) : ℝ) + 1) * δ ≤ γ)
    (hn1 : 1 ≤ refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ * Fintype.card V) :
    UniversalAbsorbers p Fstar G (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ := by
  obtain ⟨hlam, hlam64, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩ :=
    uniform_scalar_budget ((2 ^ 21 : ℕ) : ℝ) ((2 ^ 21 : ℕ) : ℝ) γ δ (Fintype.card V)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hγ hγ1 hδ hsmall (Nat.cast_nonneg _) hn1
  exact universal_Fstar_budget p G γ (refinerLambda ((2 ^ 21 : ℕ) : ℝ) γ δ)
    (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ hG hs hlam hlam64 hlamγ hrho hscale hn1 hn2 hδ
    hembed hfixed hledger hroot hcount

/-- **`UniversalCert Fstar`** at the padded scales. -/
theorem universal_simple_Fstar {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link Fstar (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fstar i j k) (2 ^ 21) (ω * Fintype.card V))
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 1 ≤ paddedRho ω * Fintype.card V) :
    UniversalAbsorbers p Fstar G (paddedRho ω) (paddedAbsDelta ω) := by
  have hsmall : 64 * ((((2 ^ 21 : ℕ) : ℝ)) + 1) * paddedAbsDelta ω ≤ ω := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using padded_delta_small hω.le hω1
  have hρ : paddedRho ω ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using paddedRho_le_refiner hω.le
  have hn' : 1 ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) *
      Fintype.card V := hn.trans (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
  exact universalAbsorbers_mono_rho p Fstar G
    (universal_Fstar_uniform p G ω (paddedAbsDelta ω) hG hs hω hω1
      (paddedAbsDelta_pos hω) hsmall hn') hρ

#print axioms universal_Fstar_budget
#print axioms universal_simple_Fstar

end PaddedFstar
