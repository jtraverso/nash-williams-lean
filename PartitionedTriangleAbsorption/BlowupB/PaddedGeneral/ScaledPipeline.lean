/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.InverseScales

/-! The reserve/repair/nibble pipeline with family-dependent inverse scales.
Unlike the old NumericInputs, no bound C <= 2^20 is hidden here. The two
geometric producers (inverse and universal absorber) remain explicit inputs. -/
namespace PaddedGeneral
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble (packingThreshold)
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer
open PaddedF12 KeevashQuantitative

structure ScaledNumericInputs (n : ℕ) (C ω ε ρ δ : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  omega_pos : 0 < ω
  omega_le_one : ω ≤ 1
  error_nonneg : 0 ≤ ε
  rho_pos : 0 < ρ
  rho_le_one : ρ ≤ 1
  class_n : 8 ≤ ω * n
  reserve_n : (2 : ℝ) ^ 27 * ρ⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ n
  initial_n : packingThreshold (27 / ω) (min (ω / 8) (min 1 (ω ^ 2))) ≤ n
  final_n : coverDownThreshold (54 / ω) (ρ ^ 2 * ω / 12) ≤ n
  initial_tolerance : ε ≤ loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))
  initial_repair : ε ≤ inverseEpsilon C ω
  deletion_cap : 2 * δ + 2 * ρ ≤ inverseKappa C ω

/-- Threshold fixed from the parameters, before choosing a host graph. -/
noncomputable def scaledOrder (ω ρ : ℝ) : ℕ :=
  max (max ⌈8 / ω⌉₊ ⌈(2 : ℝ)^27 * ρ⁻¹^9 * ω⁻¹^6⌉₊)
    (max (packingThreshold (27 / ω) (min (ω / 8) (min 1 (ω^2))))
      (coverDownThreshold (54 / ω) (ρ^2 * ω / 12)))

theorem scaled_numeric_inputs_of_order (C ω ε ρ δ : ℝ)
    (hC : 0 ≤ C) (hω : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 ≤ ε)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (he : ε ≤ min (inverseEpsilon C ω)
      (loadTolerance (min (ω / 8) (min 1 (ω^2)))))
    (hd : 2 * δ + 2 * ρ ≤ inverseKappa C ω)
    (n : ℕ) (hn : scaledOrder ω ρ ≤ n) : ScaledNumericInputs n C ω ε ρ δ := by
  have hn' := hn
  simp only [scaledOrder,max_le_iff] at hn'
  refine ⟨hC,hω,hω1,hε,hρ,hρ1,?_,?_,hn'.2.1,hn'.2.2,
    he.trans (min_le_right _ _),he.trans (min_le_left _ _),hd⟩
  · have h : 8 / ω ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn'.1.1)
    have hh := (div_le_iff₀ hω).mp h
    nlinarith
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hn'.1.2)

theorem decomposition_local_scaled (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (C ω ε ρ δ : ℝ) (hI : CompleteInverseCertLocalBound F C)
    (V : Type) [Fintype V] [DecidableEq V]
    (hn : ScaledNumericInputs (Fintype.card V) C ω ε ρ δ)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hU : UniversalAbsorbers p F G ρ δ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V))
    (hdiv : IsIntDiv p F G.edgeFinset) (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p F G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) :
    HasDecomp p F G.edgeFinset := by
  classical
  have hω := hn.omega_pos
  have hρ := hn.rho_pos
  have hw0 : ∀ T, IsCopy p F G T →
      0 ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  obtain ⟨X,hX,hXdec,hXdeg,hXanti⟩ :=
    exists_decomposable_reserve_effective (27 / ω) ρ ω
      (by positivity) hn.rho_pos hn.rho_le_one hω hn.omega_le_one
      V hn.reserve_n hn.initial_n 4 p F le_rfl G φ
      (hs.to_antiEdgeful (by norm_num) F hF.allowed_of_triangle) hw0
      (degree_gap_of_guarded p G _ ω hG hF.forbidden hs)
      (fun e he => (hload e he).trans hn.initial_tolerance)
  obtain ⟨A,hA,hAX,hAdec,hAdeg,habs⟩ := hU X hX hXdeg
  have hBdeg : DegBounded (A ∪ X) (inverseKappa C ω * Fintype.card V) := by
    intro v
    calc
      _ ≤ 2 * δ * Fintype.card V + 2 * ρ * Fintype.card V :=
        degBounded_union hAdeg hXdeg v
      _ = (2 * δ + 2 * ρ) * Fintype.card V := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hn.deletion_cap (Nat.cast_nonneg _)
  have hk := inverse_kappa_budget hn.constant_nonneg hω (le_refl (inverseKappa C ω))
  obtain ⟨ψ,hψ,hψload⟩ := hostRepair_local_bound F C hn.constant_nonneg hI V p G
    (A ∪ X) ω ε (inverseKappa C ω) φ hω hn.omega_le_one hn.error_nonneg
    hn.class_n hG hs hdiv (union_subset hA hX) (hAdec.union hXdec hAX) hBdeg hw hload
    (inverse_epsilon_budget hn.constant_nonneg hω hn.initial_repair)
    (inverse_scales_pos hn.constant_nonneg hω).1.le hk.1 hk.2
  have ha : 0 < ρ ^ 2 * ω / 12 := by positivity
  have ha1 : ρ ^ 2 * ω / 12 ≤ 1 := by
    have hp : ρ ^ 2 ≤ 1 := pow_le_one₀ hn.rho_pos.le hn.rho_le_one
    have hm : ρ ^ 2 * ω ≤ 1 := calc
      _ ≤ 1 * ω := mul_le_mul_of_nonneg_right hp hω.le
      _ ≤ 1 := by simpa using hn.omega_le_one
    linarith
  apply typed_cover_down_absorption_effective (54 / ω) (ρ ^ 2 * ω / 12)
    (by positivity) ha ha1 V hn.final_n 4 p F G A X ψ
    hA hX hAX hdiv habs hXanti hψ
  intro e he
  have heH : e ∈ (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset := by
    rwa [SimpleGraph.edgeFinset_deleteEdges]
  rw [hψload e heH, sub_self, abs_zero]
  have hζ : 0 < min ((ρ ^ 2 * ω / 12) ^ 2 / 256) (min 1 ((ρ ^ 2 * ω / 12) ^ 2)) := by
    positivity
  exact (loadTolerance_pos _ hζ ((min_le_right _ _).trans (min_le_left _ _))).le

#print axioms decomposition_local_scaled
#print axioms scaled_numeric_inputs_of_order
end PaddedGeneral
