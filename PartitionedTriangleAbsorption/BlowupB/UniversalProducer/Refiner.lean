/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Target
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.UniversalF3

/-!
# General assembly: a shared refiner producer gives the universal-absorber target

This module isolates the geometric input that is still missing for a general
family.  It is NOT an absorber premise: `SharedRefiner` asks only for a fixed
remainder `R` and a fixed library of bounded, integrally divisible pieces of
`X ∪ R` that exactly partition `R ∪ L` for every divisible `L ⊆ X`
(`RefinerAssembly.RefinesReserve`), with explicit degree / count / load budgets.
No decomposition, absorber or `HasDecomp` statement occurs in it.

The private terminal step is produced by the existing
`PrivateFamily.guarded_privateStep`, which needs `ThreeStepLinks F` and
card-three types; the ledger induction and the composition are the existing
`FiniteLibrary.universal_from_finite_library`.

Order of choices in `producerTarget_of_refinerProducer`:
`F` (card three, `ThreeStepLinks`), refiner data `I, Sref, m, K, c` ↦
`B` (private library), `St = terminalOrder m B 4`, `C = terminalSize m B`,
`S = max (max St Sref) 4` ↦ `ω` ↦ `δ₀ = ω/(8(St+1))` ↦ `δ ≤ δ₀` ↦
`λ = min c 1 · ω δ / (16 (K+1)(C+1))`, `ρ = min c 1 · λ² / (16 (K+1)(C+1))`,
`N = ⌈1/ρ⌉ + ⌈1/(cλ)⌉ + ⌈2C/δ⌉ + ⌈4(St+1)/ω⌉` ↦ host ↦ `X` ↦ refiner `(s, B, R)`
↦ absorber `A` ↦ every divisible `L ⊆ X`.
Budgets: terminal threshold `T = δ n`, running degree `D = 2 δ n`, supply `a = ω n`,
ledger degree `(2ρ + Kλ) n`, library load `Λ = K λ n`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General

/-- **Shared refiner contract** (geometric, no absorber): for every reserve `X` of
maximum degree at most `2 ρ n` there are a remainder `R` disjoint from `X` and a
fixed library of pieces of `X ∪ R`, each integrally divisible with at most `m`
edges, refining `R ∪ L` for every divisible `L ⊆ X`, with `Δ(R) ≤ K λ n`,
at most `K ρ n²` pieces and total library load at most `K λ n` at every vertex. -/
def SharedRefiner {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Type*) (m : ℕ) (K lam rho : ℝ) : Prop :=
  ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
    ∃ (indices : Finset I) (B : I → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := p) (F := F) indices B X R ∧
      (∀ j ∈ indices, B j ⊆ X ∪ R ∧ IsIntDiv p F (B j) ∧ (B j).card ≤ m) ∧
      DegBounded R (K * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ K * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ indices, incidentLoad (B j) v : ℕ) : ℝ) ≤ K * lam * Fintype.card V

/-- **Refiner producer** for a family: in every host with active edges and guarded
supply of order `Sref` at `ω n`, and for all small `λ ≤ c ω`, `ρ ≤ c λ²` with
`ρ n ≥ 1`, `c λ n ≥ 1`, a shared refiner with constants `m, K` exists. -/
def RefinerProducer {t : ℕ} (F : Finset (Multiset (Fin t))) (I : Type*)
    (Sref m : ℕ) (K c : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) Sref (ω * Fintype.card V) →
    0 < lam → lam ≤ c * ω → 0 < rho → rho ≤ c * lam ^ 2 →
    1 ≤ rho * Fintype.card V → 1 ≤ c * lam * Fintype.card V →
    SharedRefiner p F G I m K lam rho

/-- The refiner scale `λ`. -/
noncomputable def asmLam (K C c ω δ : ℝ) : ℝ :=
  min c 1 * ω * δ / (16 * ((K + 1) * (C + 1)))

/-- The reserve scale `ρ`. -/
noncomputable def asmRho (K C c ω δ : ℝ) : ℝ :=
  min c 1 * (asmLam K C c ω δ) ^ 2 / (16 * ((K + 1) * (C + 1)))

theorem asm_core (St C K c c' κ lam rho ω δ n : ℝ) (hSt : 0 ≤ St) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1) (hc'c : c' ≤ c)
    (hκ : κ = 16 * ((K + 1) * (C + 1)))
    (hlamκ : lam * κ = c' * ω * δ) (hrhoκ : rho * κ = c' * lam ^ 2)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hδ : 0 < δ)
    (hδ0 : 8 * (St + 1) * δ ≤ ω)
    (hn3 : 2 * C ≤ δ * n) (hn4 : 4 * (St + 1) ≤ ω * n) :
    0 < lam ∧ lam ≤ c * ω ∧ 0 < rho ∧ rho ≤ c * lam ^ 2 ∧
    St + St * (2 * δ * n) < ω * n / 2 ∧
    max ((2 * rho + K * lam) * n) (δ * n + C) + C * (K * lam * n) ≤ 2 * δ * n ∧
    4 * ((2 * rho + K * lam) + K * rho * C) ≤ δ * ω := by
  set P := (K + 1) * (C + 1) with hP
  have hKC : 1 ≤ P := by nlinarith
  have hKP : K ≤ P := by nlinarith
  have hCKP : C * K ≤ P := by nlinarith
  have hκpos : 0 < κ := by rw [hκ]; linarith
  have hδ8 : 8 * δ ≤ ω := by nlinarith
  have hδ1 : δ ≤ 1 := by linarith
  have hωδ : 0 < ω * δ := mul_pos hω hδ
  have hlam0 : 0 < lam := by
    have : 0 < lam * κ := by rw [hlamκ]; positivity
    exact pos_of_mul_pos_left this hκpos.le
  have hrho0 : 0 < rho := by
    have : 0 < rho * κ := by rw [hrhoκ]; positivity
    exact pos_of_mul_pos_left this hκpos.le
  have hlamκ' : lam * κ ≤ ω * δ := by
    rw [hlamκ]
    have := mul_le_mul_of_nonneg_right hc'1 hωδ.le
    linarith [show c' * ω * δ = c' * (ω * δ) by ring]
  have hPlam : P * lam ≤ ω * δ / 16 := by
    rw [hκ] at hlamκ'; linarith
  have hlam16 : lam ≤ ω * δ / 16 := by
    have := mul_le_mul_of_nonneg_right hKC hlam0.le
    linarith
  have hKlam : K * lam ≤ ω * δ / 16 := by
    have := mul_le_mul_of_nonneg_right hKP hlam0.le
    linarith
  have hCKlam : C * K * lam ≤ ω * δ / 16 := by
    have := mul_le_mul_of_nonneg_right hCKP hlam0.le
    linarith
  have hωδ1 : ω * δ ≤ 1 := by nlinarith
  have hlamsmall : lam ≤ 1 := by linarith
  have hrhoκ' : rho * κ ≤ lam ^ 2 := by
    rw [hrhoκ]
    have := mul_le_mul_of_nonneg_right hc'1 (sq_nonneg lam)
    linarith
  have hPrho : P * rho ≤ lam ^ 2 / 16 := by
    rw [hκ] at hrhoκ'; linarith
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith
  have hrho1 : rho ≤ lam / 16 := by
    have := mul_le_mul_of_nonneg_right hKC hrho0.le
    linarith
  have hKCrho : K * rho * C ≤ lam / 16 := by
    have := mul_le_mul_of_nonneg_right hCKP hrho0.le
    linarith
  refine ⟨hlam0, ?_, hrho0, ?_, ?_, ?_, ?_⟩
  · have hκ1 : 1 ≤ κ := by rw [hκ]; linarith
    have hc'ω : 0 ≤ c' * ω := (mul_pos hc'0 hω).le
    have h4 : c' * ω * δ ≤ c' * ω := mul_le_of_le_one_right hc'ω hδ1
    have h5 : c' * ω ≤ c' * ω * κ := le_mul_of_one_le_right hc'ω hκ1
    have h6 : lam * κ ≤ c' * ω * κ := by linarith
    have h3 : lam ≤ c' * ω := le_of_mul_le_mul_right h6 hκpos
    have := mul_le_mul_of_nonneg_right hc'c hω.le
    linarith
  · have hκ1 : 1 ≤ κ := by rw [hκ]; linarith
    have hcl : 0 ≤ c' * lam ^ 2 := mul_nonneg hc'0.le (sq_nonneg lam)
    have h5 : c' * lam ^ 2 ≤ c' * lam ^ 2 * κ := le_mul_of_one_le_right hcl hκ1
    have h6 : rho * κ ≤ c' * lam ^ 2 * κ := by linarith
    have h7 := le_of_mul_le_mul_right h6 hκpos
    have := mul_le_mul_of_nonneg_right hc'c (sq_nonneg lam)
    linarith
  · have hn0 : 0 < n := pos_of_mul_pos_right (by linarith) hω.le
    have h1 : 8 * St * δ ≤ ω := by
      have : 8 * (St + 1) * δ = 8 * St * δ + 8 * δ := by ring
      linarith
    have h2 : St * (2 * δ * n) * 4 ≤ ω * n := by
      have := mul_le_mul_of_nonneg_right h1 hn0.le
      calc St * (2 * δ * n) * 4 = (8 * St * δ) * n := by ring
        _ ≤ ω * n := this
    linarith
  · have hn0 : 0 < n := pos_of_mul_pos_right (by linarith) hω.le
    have hωδδ : ω * δ ≤ δ := mul_le_of_le_one_left hδ.le hω1
    have hA : (2 * rho + K * lam) * n ≤ δ * n + C := by
      have h1 : 2 * rho + K * lam ≤ δ := by linarith
      have := mul_le_mul_of_nonneg_right h1 hn0.le
      linarith
    have hB : C * (K * lam * n) ≤ δ * n / 2 := by
      have h1 : C * K * lam ≤ δ / 2 := by linarith
      have := mul_le_mul_of_nonneg_right h1 hn0.le
      calc C * (K * lam * n) = (C * K * lam) * n := by ring
        _ ≤ δ / 2 * n := this
        _ = δ * n / 2 := by ring
    rw [max_eq_right hA]
    linarith
  · linarith

theorem asm_scales (St C K c ω δ n : ℝ) (hSt : 0 ≤ St) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hc : 0 < c) (hω : 0 < ω) (hω1 : ω ≤ 1) (hδ : 0 < δ)
    (hδ0 : 8 * (St + 1) * δ ≤ ω)
    (hn3 : 2 * C ≤ δ * n) (hn4 : 4 * (St + 1) ≤ ω * n) :
    0 < asmLam K C c ω δ ∧ asmLam K C c ω δ ≤ c * ω ∧
    0 < asmRho K C c ω δ ∧ asmRho K C c ω δ ≤ c * (asmLam K C c ω δ) ^ 2 ∧
    St + St * (2 * δ * n) < ω * n / 2 ∧
    max ((2 * asmRho K C c ω δ + K * asmLam K C c ω δ) * n) (δ * n + C) +
      C * (K * asmLam K C c ω δ * n) ≤ 2 * δ * n ∧
    4 * ((2 * asmRho K C c ω δ + K * asmLam K C c ω δ) +
      K * asmRho K C c ω δ * C) ≤ δ * ω := by
  have hκ : (16 * ((K + 1) * (C + 1)) : ℝ) ≠ 0 := by positivity
  exact asm_core St C K c (min c 1) (16 * ((K + 1) * (C + 1))) (asmLam K C c ω δ)
    (asmRho K C c ω δ) ω δ n hSt hC hK (lt_min hc one_pos) (min_le_right _ _)
    (min_le_left _ _) rfl (by rw [asmLam, div_mul_cancel₀ _ hκ])
    (by rw [asmRho, div_mul_cancel₀ _ hκ]) hω hω1 hδ hδ0 hn3 hn4

/-- **General assembly.** For a card-three family with `ThreeStepLinks`, a refiner
producer implies the producer target, with `S = max (max St Sref) 4`. -/
theorem producerTarget_of_refinerProducer (F : Finset (Multiset (Fin 4)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (I : Type) (Sref m : ℕ) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c)
    (href : RefinerProducer F I Sref m K c) :
    ∃ S : ℕ, 4 ≤ S ∧ Sref ≤ S ∧ ProducerTarget F S := by
  obtain ⟨B, hB⟩ := PrivateFamily.guarded_privateStep F hF3 hthree m
  set St := terminalOrder m B 4 with hSt
  set C := terminalSize m B with hCdef
  refine ⟨max (max St Sref) 4, le_max_right _ _,
    (le_max_right St Sref).trans (le_max_left _ _), ?_⟩
  apply producerTarget_of_small
  intro ω hω hω1
  have hSt1 : (0 : ℝ) < 8 * ((St : ℝ) + 1) := by positivity
  refine ⟨ω / (8 * ((St : ℝ) + 1)), div_pos hω hSt1, fun δ hδ hδ₀ => ?_⟩
  have hδ0 : 8 * ((St : ℝ) + 1) * δ ≤ ω := by
    rw [le_div_iff₀ hSt1] at hδ₀; linarith
  set lam := asmLam K C c ω δ with hlam
  set rho := asmRho K C c ω δ with hrho
  -- positivity of λ, ρ does not depend on n
  obtain ⟨hlam0, hlamc, hrho0, hrhoc, -, -, -⟩ :=
    asm_scales St C K c ω δ (max (2 * C / δ) (4 * (St + 1) / ω)) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hK hc hω hω1 hδ hδ0
      ((div_le_iff₀' hδ).mp (le_max_left _ _))
      ((div_le_iff₀' hω).mp (le_max_right _ _))
  refine ⟨rho, hrho0, ⌈1 / rho⌉₊ + ⌈1 / (c * lam)⌉₊ + ⌈2 * (C : ℝ) / δ⌉₊ +
    ⌈4 * ((St : ℝ) + 1) / ω⌉₊, fun V _ _ p G _ hN hG hs => ?_⟩
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hNr : ⌈1 / rho⌉₊ ≤ Fintype.card V := by omega
  have hNl : ⌈1 / (c * lam)⌉₊ ≤ Fintype.card V := by omega
  have hNc : ⌈2 * (C : ℝ) / δ⌉₊ ≤ Fintype.card V := by omega
  have hNs : ⌈4 * ((St : ℝ) + 1) / ω⌉₊ ≤ Fintype.card V := by omega
  have hn1 : 1 ≤ rho * n := one_le_mul_of_ceil_le hrho0 hNr
  have hn2 : 1 ≤ c * lam * n := one_le_mul_of_ceil_le (mul_pos hc hlam0) hNl
  have hn3 : 2 * (C : ℝ) ≤ δ * n := by
    have h : 2 * (C : ℝ) / δ ≤ n :=
      (Nat.le_ceil _).trans (show ((⌈2 * (C : ℝ) / δ⌉₊ : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) from
        Nat.cast_le.mpr hNc)
    rw [div_le_iff₀ hδ] at h; linarith
  have hn4 : 4 * ((St : ℝ) + 1) ≤ ω * n := by
    have h : 4 * ((St : ℝ) + 1) / ω ≤ n :=
      (Nat.le_ceil _).trans
        (show ((⌈4 * ((St : ℝ) + 1) / ω⌉₊ : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) from
          Nat.cast_le.mpr hNs)
    rw [div_le_iff₀ hω] at h; linarith
  obtain ⟨-, -, -, -, hbudget, hdeg, hcnt⟩ :=
    asm_scales St C K c ω δ n (Nat.cast_nonneg _) (Nat.cast_nonneg _) hK hc hω hω1 hδ hδ0
      hn3 hn4
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  -- private terminal step
  have hsSt : GuardedSupply p G (fun i j => ∃ k, Link F i j k) St (ω * n) :=
    hs.mono ((le_max_left St Sref).trans (le_max_left _ _)) le_rfl
  have hstep : PrivateFamily.PrivateStep p F G m C (δ * n) (2 * δ * n) (ω * n) :=
    hB p G (ω * n) (δ * n) (2 * δ * n) hsSt (by positivity) (by nlinarith)
      (by simpa only [hSt] using hbudget)
  -- refiner
  have hsRef : GuardedSupply p G (fun i j => ∃ k, Link F i j k) Sref (ω * n) :=
    hs.mono ((le_max_right St Sref).trans (le_max_left _ _)) le_rfl
  have hR := href V p G ω lam rho hω hω1 hG hsRef hlam0 hlamc hrho0 hrhoc hn1 hn2
  have hρδ : rho ≤ δ := by
    have := hdeg
    have h1 : (2 * rho + K * lam) * n ≤ 2 * δ * n := (le_max_left _ _).trans
      (le_trans (le_add_of_nonneg_right (by positivity)) hdeg)
    have hnpos : 0 < n := by nlinarith
    have : 2 * rho + K * lam ≤ 2 * δ := le_of_mul_le_mul_right (by linarith) hnpos
    nlinarith
  apply universalAbsorbers_mono_delta p F G _ (le_refl δ)
  intro X hXG hX
  obtain ⟨indices, Bp, R, hRG, hRX, hrefines, hpieces, hRdeg, hcard, hload⟩ := hR X hXG hX
  have hledger : DegBounded (X ∪ R) ((2 * rho + K * lam) * n) := by
    intro v
    have h1 := hX v
    have h2 := hRdeg v
    have hsub : (X ∪ R).filter (fun e => v ∈ e) ⊆
        X.filter (fun e => v ∈ e) ∪ R.filter (fun e => v ∈ e) := by
      intro e he
      simp only [mem_filter, mem_union] at he ⊢
      tauto
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    have hcR : (((X ∪ R).filter (fun e => v ∈ e)).card : ℝ) ≤
        ((X.filter (fun e => v ∈ e)).card : ℝ) + ((R.filter (fun e => v ∈ e)).card : ℝ) := by
      exact_mod_cast hc
    change _ ≤ 2 * rho * n at h1
    change _ ≤ K * lam * n at h2
    nlinarith
  have hcount : 4 * (((X ∪ R).card : ℝ) + indices.card * C) ≤ (δ * n) * (ω * n) := by
    have hLC := FiniteLibrary.card_le_order_mul_degree (X ∪ R) _ hledger
    have hKC := mul_le_mul_of_nonneg_right hcard hC0
    change ((X ∪ R).card : ℝ) ≤ n * ((2 * rho + K * lam) * n) at hLC
    calc
      _ ≤ 4 * (n * ((2 * rho + K * lam) * n) + (K * rho * n ^ 2) * C) := by linarith
      _ = 4 * ((2 * rho + K * lam) + K * rho * C) * n ^ 2 := by ring
      _ ≤ (δ * ω) * n ^ 2 := mul_le_mul_of_nonneg_right hcnt (sq_nonneg n)
      _ = (δ * n) * (ω * n) := by ring
  exact FiniteLibrary.universal_from_finite_library p F G m C (δ * n) (2 * δ * n)
    (K * lam * n) ((2 * rho + K * lam) * n) (ω * n) hstep X R hRX hXG hRG hledger hdeg
    indices Bp hrefines (fun j hj => (hpieces j hj).1) (fun j hj => (hpieces j hj).2.2)
    (fun j hj => (hpieces j hj).2.1) hload hcount

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
