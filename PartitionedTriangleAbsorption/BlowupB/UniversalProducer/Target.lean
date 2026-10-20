/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.UniversalF12

@[expose] public section

/-!
# The universal-absorber producer target

`ProducerTarget F S` is the requested quantifier order, stated with the EXISTING
`StructuralF3General.UniversalAbsorbers`:

for every `0 < ω ≤ 1` and every `δ > 0` there are `ρ > 0` and `N`, chosen before
the host, such that every host `(V, p, G)` with `N ≤ |V|`, active edges and
`GuardedSupply p G (∃ k, Link F · · k) S (ω |V|)` satisfies
`UniversalAbsorbers p F G ρ δ`.

This file only contains the target, the monotonicity facts in `ρ`, `δ` and the
supply order, and the reduction "small `δ` suffices".  Nothing here assumes an
absorber.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

/-- The requested producer statement for a family `F` on four labels, with
supply order `S`.  Order of choices: `S` (outside), then `ω`, `δ`, then `ρ, N`,
then the host `V, p, G`; the reserve `X`, the absorber `A` and the leftovers `L`
are quantified inside `UniversalAbsorbers`. -/
def ProducerTarget (F : Finset (Multiset (Fin 4))) (S : ℕ) : Prop :=
  ∀ ω : ℝ, 0 < ω → ω ≤ 1 → ∀ δ : ℝ, 0 < δ →
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F i j k) S (ω * Fintype.card V) →
        UniversalAbsorbers p F G ρ δ

/-- The same statement, but only for `δ` in a small positive interval `(0, δ₀(ω)]`. -/
def SmallDeltaTarget (F : Finset (Multiset (Fin 4))) (S : ℕ) : Prop :=
  ∀ ω : ℝ, 0 < ω → ω ≤ 1 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F i j k) S (ω * Fintype.card V) →
        UniversalAbsorbers p F G ρ δ

section Mono

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- A larger absorber degree budget is easier. -/
theorem universalAbsorbers_mono_delta (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ δ δ' : ℝ}
    (h : UniversalAbsorbers p F G ρ δ) (hδ : δ ≤ δ') :
    UniversalAbsorbers p F G ρ δ' := by
  intro X hX hdeg
  obtain ⟨A, hAG, hAX, hA, hAdeg, hAL⟩ := h X hX hdeg
  refine ⟨A, hAG, hAX, hA, fun v => (hAdeg v).trans ?_, hAL⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ (by norm_num))
    (Nat.cast_nonneg _)

/-- A smaller reserve degree is easier. -/
theorem universalAbsorbers_mono (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ ρ' δ δ' : ℝ}
    (h : UniversalAbsorbers p F G ρ δ) (hρ : ρ' ≤ ρ) (hδ : δ ≤ δ') :
    UniversalAbsorbers p F G ρ' δ' :=
  universalAbsorbers_mono_delta p F G (PaddedF12.universalAbsorbers_mono_rho p F G h hρ) hδ

end Mono

/-- Small `δ` suffices: larger `δ` follows by monotonicity, with the same `ρ, N`
as for `min δ δ₀`. -/
theorem producerTarget_of_small {F : Finset (Multiset (Fin 4))} {S : ℕ}
    (h : SmallDeltaTarget F S) : ProducerTarget F S := by
  intro ω hω hω1 δ hδ
  obtain ⟨δ₀, hδ₀, hsmall⟩ := h ω hω hω1
  obtain ⟨ρ, hρ, N, hN⟩ := hsmall (min δ δ₀) (lt_min hδ hδ₀) (min_le_right _ _)
  refine ⟨ρ, hρ, N, fun V _ _ p G _ hn hG hs => ?_⟩
  exact universalAbsorbers_mono_delta p F G (hN V p G hn hG hs) (min_le_left _ _)

/-- A higher supply order is a stronger host hypothesis. -/
theorem producerTarget_mono_order {F : Finset (Multiset (Fin 4))} {S S' : ℕ}
    (h : ProducerTarget F S) (hS : S ≤ S') : ProducerTarget F S' := by
  intro ω hω hω1 δ hδ
  obtain ⟨ρ, hρ, N, hN⟩ := h ω hω hω1 δ hδ
  exact ⟨ρ, hρ, N, fun V _ _ p G _ hn hG hs => hN V p G hn hG (hs.mono hS le_rfl)⟩

/-- `n ≥ ⌈1/ρ⌉` gives `1 ≤ ρ n`. -/
theorem one_le_mul_of_ceil_le {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : ⌈1 / ρ⌉₊ ≤ n) :
    1 ≤ ρ * n := by
  have h1 : 1 / ρ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [div_le_iff₀ hρ] at h1
  linarith

/-- **Parameter bridge for the existing "uniform" absorber theorems.**
If a family has universal absorbers at `ρ = refinerRho C γ δ` whenever
`64 (S+1) δ ≤ γ` and `1 ≤ ρ n` (the shape of `universal_F3_uniform` and
`universal_F12_uniform`), then it satisfies the producer target with order `S`. -/
theorem producerTarget_of_uniform (F : Finset (Multiset (Fin 4))) (S C : ℕ)
    (huni : ∀ (V : Type) [Fintype V] [DecidableEq V]
        (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ),
        (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F i j k) S (γ * Fintype.card V) →
        0 < γ → γ ≤ 1 → 0 < δ → 64 * ((S : ℝ) + 1) * δ ≤ γ →
        1 ≤ refinerRho C γ δ * Fintype.card V →
        UniversalAbsorbers p F G (refinerRho C γ δ) δ) :
    ProducerTarget F S := by
  apply producerTarget_of_small
  intro ω hω hω1
  have hS1 : (0 : ℝ) < 64 * ((S : ℝ) + 1) := by positivity
  refine ⟨ω / (64 * ((S : ℝ) + 1)), div_pos hω hS1, fun δ hδ hδ₀ => ?_⟩
  have hρ : 0 < refinerRho C ω δ := refinerRho_pos (Nat.cast_nonneg _) hω hδ
  refine ⟨refinerRho C ω δ, hρ, ⌈1 / refinerRho C ω δ⌉₊, fun V _ _ p G _ hn hG hs => ?_⟩
  have hsmall : 64 * ((S : ℝ) + 1) * δ ≤ ω := by
    rw [le_div_iff₀ hS1] at hδ₀
    linarith
  exact huni V p G ω δ hG hs hω hω1 hδ hsmall (one_le_mul_of_ceil_le hρ hn)

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
