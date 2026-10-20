/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

@[expose] public section

/-!
# The reduction with an inverse certificate for classes of size at least 8

`CompleteInverseCert F` asks for the signed inverse on every complete allowed blowup with
`4 ≤ γ n`. For families with an isolated monochromatic class this is false
(`PaddedComponents.not_completeInverseCert_of_isolatedMono`: classes of four vertices). In the
reduction the inverse is only used with `γ = ω`, where `ω n ≥ 2^262` (`paddedRho ω n ≥ 1`).

`CompleteInverseCert₈ F` is the same certificate under `8 ≤ γ n`; it is implied by
`CompleteInverseCert F`. `keevashPaddedSpec_of_certs₈` is the reduction
`PaddedGeneral.keevashPaddedSpec_of_certs` with `CompleteInverseCert₈` in place of
`CompleteInverseCert`; its proof is the same, with `8 ≤ ω n` from `NumericInputs`.
-/

namespace PaddedGeneral

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer
open PaddedF12 PaddedF12.PaddedThresholds KeevashQuantitative

/-- Certificate 2 for classes of size at least `8`. -/
def CompleteInverseCert₈ (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (r : Sym2 V → ℝ) (ε γ : ℝ),
    0 ≤ ε → 0 < γ → γ ≤ 1 → 8 ≤ γ * (Fintype.card V : ℝ) →
    (∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i) →
    Sym2DemandSupported p F r → (∀ e, |r e| ≤ ε) → SpanCompat p F r →
    ∃ z : TriangleChain V, CopySupported p F (activeCompleteGraph p F) z ∧
      boundary z = r ∧
      ∀ T, |z T| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ))

theorem completeInverseCert₈_of_cert {F : Finset (Multiset (Fin 4))}
    (h : CompleteInverseCert F) : CompleteInverseCert₈ F := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge
  exact h V p r ε γ hε hγ hγ1 (by linarith)

/-- `8 ≤ ω n` in the numeric regime. -/
theorem eight_le_omega_n {m n : ℕ} {ω : ℝ} (hn : NumericInputs m n ω) :
    8 ≤ ω * (n : ℝ) := by
  have hω := hn.omega_pos
  have hω1 := hn.omega_le_one
  have hr := hn.rho_n
  have hle : paddedRho ω ≤ ω / 8 := by
    unfold paddedRho
    have h25 : ω ^ 25 ≤ 1 := pow_le_one₀ hω.le hω1
    have h8 : (8 : ℝ) ≤ 2 ^ 262 :=
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 262 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hA : ω ^ 26 ≤ ω :=
      calc ω ^ 26 = ω * ω ^ 25 := by ring
        _ ≤ ω * 1 := mul_le_mul_of_nonneg_left h25 hω.le
        _ = ω := mul_one ω
    calc ω ^ 26 / 2 ^ 262 ≤ ω / 2 ^ 262 := div_le_div_of_nonneg_right hA (by positivity)
      _ ≤ ω / 8 := div_le_div_of_nonneg_left hω.le (by norm_num) h8
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 1 ≤ ω / 8 * n := hr.trans (mul_le_mul_of_nonneg_right hle hn0)
  linarith

theorem exists_host_chain_inverse_gen₈ (F : Finset (Multiset (Fin 4)))
    (hI : CompleteInverseCert₈ F) {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Sym2 V → ℝ) (ε ω : ℝ) (hε : 0 ≤ ε) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : 8 ≤ ω * (Fintype.card V : ℝ))
    (hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i)
    (hguard : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4
      (ω * Fintype.card V / 2))
    (hs : Sym2DemandSupported p F r) (hzero : ∀ e, e ∉ G.edgeFinset → r e = 0)
    (hr : ∀ e, |r e| ≤ ε) (hc : SpanCompat p F r) :
    ∃ w : TriangleChain V, CopySupported p F G w ∧ boundary w = r ∧
      ∀ T, IsCopy p F G T →
        |w T| ≤ ((2 : ℝ) ^ 32 / ω ^ 9) * ε / Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  obtain ⟨z, hzs, hzr, hzb⟩ := hI V p r ε ω hε hω hω1 hlarge hmin hs hr hc
  let M : ℝ := (2 : ℝ) ^ 20 * ε / (ω ^ 6 * Fintype.card V)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hS := total_mass_bound p F (activeCompleteGraph p F) z M hM (fun T _ => hzb T)
  have hU := vertex_mass_bound p F (activeCompleteGraph p F) z M hM (fun T _ => hzb T)
  obtain ⟨w, hws, hwr, hwb⟩ := SignedTransfer.exists_signed_transfer p F G
    (ω * Fintype.card V / 2) ε ((Fintype.card V : ℝ) ^ 3 * M)
    ((Fintype.card V : ℝ) ^ 2 * M) (by positivity) hguard z hzs
    (by intro e he; rw [hzr]; exact hzero e he)
    (by intro e; rw [hzr]; exact hr e) hS hU
  refine ⟨w, hws, hwr.trans hzr, ?_⟩
  intro T hT
  exact (hwb T hT.1.card_eq).trans (transferred_inverse_bound ε ω (Fintype.card V)
    hε hω hω1 hnR)

theorem hostRepair_gen₈ (F : Finset (Multiset (Fin 4))) (hI : CompleteInverseCert₈ F)
    (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (ω ε : ℝ) (φ : Finset V → ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 ≤ ε) (hlarge : 8 ≤ ω * Fintype.card V)
    (hallowed : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V))
    (hdiv : IsIntDiv p F G.edgeFinset)
    (hBG : B ⊆ G.edgeFinset) (hBdec : HasDecomp p F B)
    (hBdeg : DegBounded B (paddedKappa ω * Fintype.card V))
    (hw : ∀ T, IsCopy p F G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε)
    (hεbudget : ((2 : ℝ) ^ 32 / ω ^ 9) * ε ≤ ω ^ 2 / 4) :
    ∃ ψ : Finset V → ℝ,
      (∀ T, IsCopy p F (G.deleteEdges (B : Set (Sym2 V))) T →
        0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        (∑ T ∈ copies p F (G.deleteEdges (B : Set (Sym2 V))) with e ∈ triEdges T, ψ T) = 1 := by
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
  have hguardH : GuardedSupply p H (fun i j => ∃ k, Link F i j k) 4
      (ω * Fintype.card V / 2) := by
    have hdelete := guardedSupply_deleteEdges p G (fun i j => ∃ k, Link F i j k)
      4 (ω * Fintype.card V) (paddedKappa ω * Fintype.card V) hs B hBdeg (by positivity)
    apply hdelete.mono le_rfl
    have hb := mul_le_mul_of_nonneg_right hκcap hnR.le
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i := by
    intro i
    simpa only [classSize, classVertices] using hs.class_card i
  have hdivH : IsIntDiv p F H.edgeFinset := by
    rw [show H.edgeFinset = G.edgeFinset \ B from SimpleGraph.edgeFinset_deleteEdges _]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hBdec hBG
  have hw0 : ∀ T, IsCopy p F G T → 0 ≤ φ T ∧
      φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  let θ : ℝ := ε + 2 * (27 / ω) * paddedKappa ω
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hloadH : ∀ e ∈ H.edgeFinset,
      |(∑ T ∈ copies p F H with e ∈ triEdges T, φ T) - 1| ≤ θ := by
    have hr := nearLoads_deleteEdges p F G B (27 / ω) ε
      (paddedKappa ω * Fintype.card V) (by positivity) hn hBdeg φ hw0 hload
    have heq : ε + 2 * (27 / ω) * (paddedKappa ω * Fintype.card V) / Fintype.card V = θ := by
      dsimp only [θ]
      field_simp
    rwa [heq] at hr
  have hactive : H ≤ activeCompleteGraph p F := by
    intro a b hab
    exact ⟨hab.ne, hallowed a b (hHG hab)⟩
  obtain ⟨w, hws, hwe, hwb⟩ := exists_host_chain_inverse_gen₈ F hI p H
    (loadDefect p F H φ) θ ω hθ hω hω1 hlarge hmin hguardH
    (loadDefect_supported p F H φ hactive)
    (loadDefect_zero p F H φ)
    (loadDefect_bound p F H φ θ hθ (by
      intro e he
      rw [abs_sub_comm]
      exact hloadH e he))
    (loadDefect_span p F H φ hdivH)
  apply exactWeights_of_bounded_correction p F H ω hω hω1 hn φ w
    (fun T hT => hw T ⟨hT.1.mono hHG, hT.2⟩) hws
  · intro T hT
    exact (hwb T hT).trans (correction_budget ((2 : ℝ) ^ 32 / ω ^ 9)
      ε (27 / ω) (paddedKappa ω) ω (Fintype.card V) hnR.le hεbudget (padded_repair_budget hω))
  · intro e he
    rw [hwe]
    simp only [loadDefect, he, ite_true]

theorem decomposition_gen₈ (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hU : UniversalCert F) (hI : CompleteInverseCert₈ F)
    (V : Type) [Fintype V] [DecidableEq V]
    (m : ℕ) (ω : ℝ) (hn : NumericInputs m (Fintype.card V) ω)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21)
      (ω * Fintype.card V))
    (hdiv : IsIntDiv p F G.edgeFinset) (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p F G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤
        ω ^ (PaddedInputs.hKT 4 m ^ 20)) :
    HasDecomp p F G.edgeFinset := by
  classical
  have hω := hn.omega_pos
  have hw0 : ∀ T, IsCopy p F G T →
      0 ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  obtain ⟨X, hX, hXdec, hXdeg, hXanti⟩ :=
    exists_decomposable_reserve_effective (27 / ω) (paddedRho ω) ω
      (by positivity) (paddedRho_pos hω) hn.rho_le_one hω hn.omega_le_one
      V hn.reserve_n hn.initial_n 4 p F le_rfl G φ
      (hs.to_antiEdgeful (by norm_num) F hF.allowed_of_triangle) hw0
      (degree_gap_of_guarded p G _ ω hG hF.forbidden hs)
      (fun e he => (hload e he).trans hn.initial_tolerance)
  obtain ⟨A, hA, hAX, hAdec, hAdeg, habs⟩ :=
    hU V p G ω hG hs hω hn.omega_le_one hn.rho_n X hX hXdeg
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
  obtain ⟨ψ, hψ, hψload⟩ := hostRepair_gen₈ F hI V p G (A ∪ X) ω
    (ω ^ (PaddedInputs.hKT 4 m ^ 20)) φ hω hn.omega_le_one (by positivity)
    (eight_le_omega_n hn) hG (hs.mono (by norm_num) le_rfl) hdiv
    (union_subset hA hX) (hAdec.union hXdec hAX) hBdeg hw hload hn.initial_repair
  apply typed_cover_down_absorption_effective (54 / ω) (reserveAlpha ω)
    (by positivity) hn.alpha_pos hn.alpha_le_one V hn.final_n 4 p F G A X ψ
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

/-- **Reduction**: the two certificates and the finite facts give the padded Keevash statement. -/
theorem keevashPaddedSpec_of_certs₈ (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hU : UniversalCert F) (hI : CompleteInverseCert₈ F) :
    PaddedInputs.KeevashPaddedSpec F := by
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
  obtain ⟨φ, hw, hload⟩ := PaddedInputs.physical_weights_of_padded m p F
    hF.card_three J hloop ω (ω ^ (PaddedInputs.hKT 4 m ^ 20)) hn.omega_pos hn0
    hq hqK hreg hext
  let : Fintype (PaddedInputs.edgeGraph J).edgeSet :=
    (PaddedInputs.edgeGraph J).fintypeEdgeSet
  have hJ : (PaddedInputs.edgeGraph J).edgeFinset = J :=
    PaddedInputs.edgeGraph_edges J hloop
  rw [← hJ] at hdiv ⊢
  exact decomposition_gen₈ F hF hU hI V m ω hn p (PaddedInputs.edgeGraph J)
    (PaddedInputs.edgeGraph_allowed p F J hallowed)
    (PaddedInputs.guardedSupply_of_padded p F J hloop ω (2 ^ 21) hguardK hext)
    hdiv φ (fun T hT => ⟨(hw T hT).1, by simpa only [div_div] using (hw T hT).2⟩)
    (fun e he => hload e (hJ ▸ he))

end PaddedGeneral

#print axioms PaddedGeneral.completeInverseCert₈_of_cert
#print axioms PaddedGeneral.keevashPaddedSpec_of_certs₈
