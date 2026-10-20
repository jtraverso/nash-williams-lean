/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedThresholds
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedParameters
import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveConstruction

/-! # Assembly of the exact padded statement from physical host repair

The only intermediate premise in this file is the signed fractional repair
theorem for the actual graph after a sparse decomposable edge set is removed.
The reserve, the universal absorber, their quantifier order, and every order
and density requirement are discharged by previously proved constructions.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer
open PaddedThresholds KeevashQuantitative

/-- The physical fractional repair used between absorption and cover-down.
The input weights and all loads are indexed by the original physical copies.
-/
def HostRepairSpec (kind : Family) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (ω ε : ℝ) (φ : Finset V → ℝ),
    0 < ω → ω ≤ 1 → 0 ≤ ε → 4 ≤ ω * Fintype.card V →
    (∀ a b, G.Adj a b → ∃ k, Link kind.types (p a) (p b) k) →
    GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) 4
      (ω * Fintype.card V) →
    IsIntDiv p kind.types G.edgeFinset →
    B ⊆ G.edgeFinset → HasDecomp p kind.types B →
    DegBounded B (paddedKappa ω * Fintype.card V) →
    (∀ T, IsCopy p kind.types G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
    (∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p kind.types G with e ∈ triEdges T, φ T) - 1| ≤ ε) →
    ((2 : ℝ) ^ 32 / ω ^ 9) * ε ≤ ω ^ 2 / 4 →
    let H := G.deleteEdges (B : Set (Sym2 V))
    ∃ ψ : Finset V → ℝ,
      (∀ T, IsCopy p kind.types H T →
        0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ H.edgeFinset,
        (∑ T ∈ copies p kind.types H with e ∈ triEdges T, ψ T) = 1

theorem Family.allowed_of_triangle (kind : Family) :
    ∀ i j k : Fin 4, ({i, j, k} : Multiset (Fin 4)) ∈ kind.types →
      (∃ a, Link kind.types i k a) ∧ (∃ a, Link kind.types j k a) := by
  cases kind
  · exact f1_allowed_of_triangle
  · exact f2_allowed_of_triangle

/-- The graph-level construction chooses the reserve, then one absorber
valid for every divisible subgraph of that reserve, before cover-down.
-/
theorem decomposition_of_numeric_inputs (kind : Family)
    (hrepair : HostRepairSpec kind) (V : Type) [Fintype V] [DecidableEq V]
    (m : ℕ) (ω : ℝ) (hn : NumericInputs m (Fintype.card V) ω)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link kind.types (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) (2 ^ 21)
      (ω * Fintype.card V))
    (hdiv : IsIntDiv p kind.types G.edgeFinset) (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p kind.types G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p kind.types G with e ∈ triEdges T, φ T) - 1| ≤
        ω ^ (PaddedInputs.hKT 4 m ^ 20)) :
    HasDecomp p kind.types G.edgeFinset := by
  classical
  have hω := hn.omega_pos
  have hw0 : ∀ T, IsCopy p kind.types G T →
      0 ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  obtain ⟨X, hX, hXdec, hXdeg, hXanti⟩ :=
    exists_decomposable_reserve_effective (27 / ω) (paddedRho ω) ω
      (by positivity) (paddedRho_pos hω) hn.rho_le_one hω hn.omega_le_one
      V hn.reserve_n hn.initial_n 4 p kind.types le_rfl G φ
      (hs.to_antiEdgeful (by norm_num) kind.types kind.allowed_of_triangle) hw0
      (kind.host_degree_gap p G ω hG hs)
      (fun e he => (hload e he).trans hn.initial_tolerance)
  obtain ⟨A, hA, hAX, hAdec, hAdeg, habs⟩ :=
    kind.universal_simple p G ω hG hs hω hn.omega_le_one hn.rho_n X hX hXdeg
  have hBdeg : DegBounded (A ∪ X) (paddedKappa ω * Fintype.card V) := by
    have hsmall : 2 * paddedAbsDelta ω + 2 * paddedRho ω ≤ paddedKappa ω := by
      have hk := paddedKappa_pos hω
      linarith [hn.deletion_cap]
    intro v
    calc
      _ ≤ 2 * paddedAbsDelta ω * Fintype.card V +
          2 * paddedRho ω * Fintype.card V := degBounded_union hAdeg hXdeg v
      _ = (2 * paddedAbsDelta ω + 2 * paddedRho ω) * Fintype.card V := by ring
      _ ≤ paddedKappa ω * Fintype.card V :=
        mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)
  obtain ⟨ψ, hψ, hψload⟩ := hrepair V p G (A ∪ X) ω
    (ω ^ (PaddedInputs.hKT 4 m ^ 20)) φ hω hn.omega_le_one (by positivity)
    hn.class_n hG (hs.mono (by norm_num) le_rfl) hdiv
    (union_subset hA hX) (hAdec.union hXdec hAX) hBdeg hw hload hn.initial_repair
  apply typed_cover_down_absorption_effective (54 / ω) (reserveAlpha ω)
    (by positivity) hn.alpha_pos hn.alpha_le_one V hn.final_n 4 p kind.types G A X ψ
    hA hX hAX hdiv habs hXanti hψ
  intro e he
  have heH : e ∈ (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset := by
    rwa [SimpleGraph.edgeFinset_deleteEdges]
  rw [hψload e heH, sub_self, abs_zero]
  have hζ : 0 < min (reserveAlpha ω ^ 2 / 256) (min 1 (reserveAlpha ω ^ 2)) := by
    have ha := hn.alpha_pos
    positivity
  have hζ1 : min (reserveAlpha ω ^ 2 / 256) (min 1 (reserveAlpha ω ^ 2)) ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  exact (loadTolerance_pos _ hζ hζ1).le

/-- The exact supplied padded statement, with its original order of
quantifiers, follows from physical host repair for the chosen family.
-/
theorem keevasPaddedSpec_of_hostRepair (kind : Family) (hrepair : HostRepairSpec kind) :
    PaddedInputs.KeevashPaddedSpec kind.types := by
  intro m
  refine ⟨1 / 8, by norm_num, orderThreshold, ?_⟩
  intro V _ _ hlarge ω hdensity hω8 p J hloop hallowed _hclasses hdiv hreg hext
  classical
  have hn := numeric_inputs m (Fintype.card V) hlarge ω hdensity hω8
  have hn0 : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    have hb := hn.class_n
    simp only [hz, Nat.cast_zero, mul_zero] at hb
    norm_num at hb
  obtain ⟨hq, hqK, hguardK⟩ := PaddedInputs.padded_query_bounds m
  obtain ⟨φ, hw, hload⟩ := PaddedInputs.physical_weights_of_padded m p kind.types
    kind.card_three J hloop ω (ω ^ (PaddedInputs.hKT 4 m ^ 20)) hn.omega_pos hn0
    hq hqK hreg hext
  let : Fintype (PaddedInputs.edgeGraph J).edgeSet :=
    (PaddedInputs.edgeGraph J).fintypeEdgeSet
  have hJ : (PaddedInputs.edgeGraph J).edgeFinset = J :=
    PaddedInputs.edgeGraph_edges J hloop
  rw [← hJ] at hdiv ⊢
  exact decomposition_of_numeric_inputs kind hrepair V m ω hn p (PaddedInputs.edgeGraph J)
    (PaddedInputs.edgeGraph_allowed p kind.types J hallowed)
    (PaddedInputs.guardedSupply_of_padded p kind.types J hloop ω (2 ^ 21) hguardK hext)
    hdiv φ (fun T hT => ⟨(hw T hT).1, by simpa only [div_div] using (hw T hT).2⟩)
    (fun e he => hload e (hJ ▸ he))

#print axioms decomposition_of_numeric_inputs
#print axioms keevasPaddedSpec_of_hostRepair

end PaddedF12
