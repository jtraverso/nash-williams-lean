/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.FractionalRepair
import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Inverse

/-!
# The padded Keevash statement for F₃

The assembly of `PaddedF12.PaddedAssembly` is family-agnostic except for the universal absorber,
the complete inverse and a few finite facts about the allowed pairs. With the F₃ versions of
those (`PaddedF3.Universal`, `PaddedF3.Inverse`), the same numeric inputs, reserve, nibble,
cover-down and repair give `PaddedInputs.KeevashPaddedSpec F3`.
-/

namespace PaddedF3

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer
open PaddedF12 PaddedF12.PaddedThresholds KeevashQuantitative

theorem f3_allowed_of_triangle : ∀ i j k : Fin 4,
    ({i, j, k} : Multiset (Fin 4)) ∈ F3 →
      (∃ a, Link F3 i k a) ∧ (∃ a, Link F3 j k a) := by
  unfold Link F3
  decide

theorem f3_forbidden (i : Fin 4) : ∃ j, ¬ ∃ k, Link F3 i j k :=
  ⟨i, by fin_cases i <;> (unfold Link F3; decide)⟩

theorem host_degree_gap_F3 {V : Type*} [Fintype V] [DecidableEq V] {D : ℕ}
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link F3 (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) D (ω * Fintype.card V)) :
    DegBounded G.edgeFinset ((1 - ω) * Fintype.card V) :=
  degree_gap_of_guarded p G _ ω hG f3_forbidden hs

/-- `HostRepairSpec` for F₃. -/
def HostRepairSpecF3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (ω ε : ℝ) (φ : Finset V → ℝ),
    0 < ω → ω ≤ 1 → 0 ≤ ε → 4 ≤ ω * Fintype.card V →
    (∀ a b, G.Adj a b → ∃ k, Link F3 (p a) (p b) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) 4
      (ω * Fintype.card V) →
    IsIntDiv p F3 G.edgeFinset →
    B ⊆ G.edgeFinset → HasDecomp p F3 B →
    DegBounded B (paddedKappa ω * Fintype.card V) →
    (∀ T, IsCopy p F3 G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
    (∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F3 G with e ∈ triEdges T, φ T) - 1| ≤ ε) →
    ((2 : ℝ) ^ 32 / ω ^ 9) * ε ≤ ω ^ 2 / 4 →
    let H := G.deleteEdges (B : Set (Sym2 V))
    ∃ ψ : Finset V → ℝ,
      (∀ T, IsCopy p F3 H T →
        0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ H.edgeFinset,
        (∑ T ∈ copies p F3 H with e ∈ triEdges T, ψ T) = 1

theorem hostRepair_F3 : HostRepairSpecF3 := by
  intro V _ _ p G _ B ω ε φ hω hω1 hε hlarge hallowed hs hdiv hBG hBdec hBdeg hw hload hεbudget
  classical
  let H := G.deleteEdges (B : Set (Sym2 V))
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hκ := paddedKappa_pos hω
  have hκcap := PaddedThresholds.kappa_small hω hω1
  have hguardH : GuardedSupply p H (fun i j => ∃ k, Link F3 i j k) 4
      (ω * Fintype.card V / 2) := by
    have hdelete := guardedSupply_deleteEdges p G (fun i j => ∃ k, Link F3 i j k)
      4 (ω * Fintype.card V) (paddedKappa ω * Fintype.card V) hs B hBdeg (by positivity)
    apply hdelete.mono le_rfl
    have hb := mul_le_mul_of_nonneg_right hκcap hnR.le
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i := by
    intro i
    simpa only [classSize, classVertices] using hs.class_card i
  have hdivH : IsIntDiv p F3 H.edgeFinset := by
    rw [show H.edgeFinset = G.edgeFinset \ B from SimpleGraph.edgeFinset_deleteEdges _]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hBdec hBG
  have hw0 : ∀ T, IsCopy p F3 G T → 0 ≤ φ T ∧
      φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  let θ : ℝ := ε + 2 * (27 / ω) * paddedKappa ω
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hloadH : ∀ e ∈ H.edgeFinset,
      |(∑ T ∈ copies p F3 H with e ∈ triEdges T, φ T) - 1| ≤ θ := by
    have hr := nearLoads_deleteEdges p F3 G B (27 / ω) ε
      (paddedKappa ω * Fintype.card V) (by positivity) hn hBdeg φ hw0 hload
    have heq : ε + 2 * (27 / ω) * (paddedKappa ω * Fintype.card V) / Fintype.card V = θ := by
      dsimp only [θ]
      field_simp
    rwa [heq] at hr
  have hactive : H ≤ activeCompleteGraph p F3 := by
    intro a b hab
    exact ⟨hab.ne, hallowed a b (hHG hab)⟩
  obtain ⟨w, hws, hwe, hwb⟩ := exists_host_chain_inverse_F3 p H
    (loadDefect p F3 H φ) θ ω hθ hω hω1 hlarge hmin hguardH
    (loadDefect_supported p F3 H φ hactive)
    (loadDefect_zero p F3 H φ)
    (loadDefect_bound p F3 H φ θ hθ (by
      intro e he
      rw [abs_sub_comm]
      exact hloadH e he))
    (loadDefect_F3 p H φ hdivH)
  apply exactWeights_of_bounded_correction p F3 H ω hω hω1 hn φ w
    (fun T hT => hw T ⟨hT.1.mono hHG, hT.2⟩) hws
  · intro T hT
    exact (hwb T hT).trans (correction_budget ((2 : ℝ) ^ 32 / ω ^ 9)
      ε (27 / ω) (paddedKappa ω) ω (Fintype.card V) hnR.le hεbudget (padded_repair_budget hω))
  · intro e he
    rw [hwe]
    simp only [loadDefect, he, ite_true]

theorem decomposition_of_numeric_inputs_F3 (V : Type) [Fintype V] [DecidableEq V]
    (m : ℕ) (ω : ℝ) (hn : NumericInputs m (Fintype.card V) ω)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F3 (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) (2 ^ 21)
      (ω * Fintype.card V))
    (hdiv : IsIntDiv p F3 G.edgeFinset) (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p F3 G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F3 G with e ∈ triEdges T, φ T) - 1| ≤
        ω ^ (PaddedInputs.hKT 4 m ^ 20)) :
    HasDecomp p F3 G.edgeFinset := by
  classical
  have hω := hn.omega_pos
  have hw0 : ∀ T, IsCopy p F3 G T →
      0 ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  obtain ⟨X, hX, hXdec, hXdeg, hXanti⟩ :=
    exists_decomposable_reserve_effective (27 / ω) (paddedRho ω) ω
      (by positivity) (paddedRho_pos hω) hn.rho_le_one hω hn.omega_le_one
      V hn.reserve_n hn.initial_n 4 p F3 le_rfl G φ
      (hs.to_antiEdgeful (by norm_num) F3 f3_allowed_of_triangle) hw0
      (host_degree_gap_F3 p G ω hG hs)
      (fun e he => (hload e he).trans hn.initial_tolerance)
  obtain ⟨A, hA, hAX, hAdec, hAdeg, habs⟩ :=
    universal_simple_F3 p G ω hG hs hω hn.omega_le_one hn.rho_n X hX hXdeg
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
  obtain ⟨ψ, hψ, hψload⟩ := hostRepair_F3 V p G (A ∪ X) ω
    (ω ^ (PaddedInputs.hKT 4 m ^ 20)) φ hω hn.omega_le_one (by positivity)
    hn.class_n hG (hs.mono (by norm_num) le_rfl) hdiv
    (union_subset hA hX) (hAdec.union hXdec hAX) hBdeg hw hload hn.initial_repair
  apply typed_cover_down_absorption_effective (54 / ω) (reserveAlpha ω)
    (by positivity) hn.alpha_pos hn.alpha_le_one V hn.final_n 4 p F3 G A X ψ
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

/-- **The padded Keevash statement for F₃**, unconditional. -/
theorem keevashPaddedSpec_F3 : PaddedInputs.KeevashPaddedSpec F3 := by
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
  obtain ⟨φ, hw, hload⟩ := PaddedInputs.physical_weights_of_padded m p F3
    ColouredHub.F3_card_three J hloop ω (ω ^ (PaddedInputs.hKT 4 m ^ 20)) hn.omega_pos hn0
    hq hqK hreg hext
  let : Fintype (PaddedInputs.edgeGraph J).edgeSet :=
    (PaddedInputs.edgeGraph J).fintypeEdgeSet
  have hJ : (PaddedInputs.edgeGraph J).edgeFinset = J :=
    PaddedInputs.edgeGraph_edges J hloop
  rw [← hJ] at hdiv ⊢
  exact decomposition_of_numeric_inputs_F3 V m ω hn p (PaddedInputs.edgeGraph J)
    (PaddedInputs.edgeGraph_allowed p F3 J hallowed)
    (PaddedInputs.guardedSupply_of_padded p F3 J hloop ω (2 ^ 21) hguardK hext)
    hdiv φ (fun T hT => ⟨(hw T hT).1, by simpa only [div_div] using (hw T hT).2⟩)
    (fun e he => hload e (hJ ▸ he))

#print axioms hostRepair_F3
#print axioms keevashPaddedSpec_F3

end PaddedF3
