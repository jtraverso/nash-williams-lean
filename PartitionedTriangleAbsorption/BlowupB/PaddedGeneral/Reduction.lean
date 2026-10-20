/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Assembly

/-!
# The padded Keevash statement from two family certificates (t = 4)

The assembly of PaddedF12/PaddedF3 is family-agnostic except for

* `UniversalCert F`: universal absorbers at the padded scales, in hosts with guarded supply of
  order `2^21`;
* `CompleteInverseCert F`: a signed inverse on the complete allowed blowup, with the bound
  `2^20 ε / (γ^6 n)`, for every demand in the real span of the type edge vectors;
* three finite, decidable facts about `F`: card three, `allowed_of_triangle`, and a forbidden class
  for every class.

The real compatibility is the span condition `SpanCompat`, which holds for the load defect of any
integrally divisible host (`loadDefect_span`), for every `F`.

**`keevashPaddedSpec_of_certs`**: the certificates give `PaddedInputs.KeevashPaddedSpec F`.
F₁, F₂ and F₃ are instances (`universalCert_F1/F2/F3`, `completeInverseCert_F1/F2/F3`).
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

/-! ### Certificates -/

/-- Real compatibility: the class totals lie in the real span of the type edge vectors. -/
def SpanCompat {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (r : Sym2 V → ℝ) : Prop :=
  ∃ c : Multiset (Fin 4) → ℝ,
    classTotal p (fun a b => r s(a, b)) = ∑ τ ∈ F, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))

/-- Certificate 1: universal absorbers at the padded scales. -/
def UniversalCert (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ),
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    0 < ω → ω ≤ 1 → 1 ≤ paddedRho ω * Fintype.card V →
    UniversalAbsorbers p F G (paddedRho ω) (paddedAbsDelta ω)

/-- Certificate 2: the bounded signed inverse on the complete allowed blowup. -/
def CompleteInverseCert (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (r : Sym2 V → ℝ) (ε γ : ℝ),
    0 ≤ ε → 0 < γ → γ ≤ 1 → 4 ≤ γ * (Fintype.card V : ℝ) →
    (∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i) →
    Sym2DemandSupported p F r → (∀ e, |r e| ≤ ε) → SpanCompat p F r →
    ∃ z : TriangleChain V, CopySupported p F (activeCompleteGraph p F) z ∧
      boundary z = r ∧
      ∀ T, |z T| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ))

/-- The finite facts about `F` used by the assembly. -/
structure FamilyFacts (F : Finset (Multiset (Fin 4))) : Prop where
  card_three : ∀ τ ∈ F, Multiset.card τ = 3
  allowed_of_triangle : ∀ i j k : Fin 4, ({i, j, k} : Multiset (Fin 4)) ∈ F →
    (∃ a, Link F i k a) ∧ (∃ a, Link F j k a)
  forbidden : ∀ i : Fin 4, ∃ j, ¬ ∃ k, Link F i j k

/-! ### The load defect is span compatible, for every family -/

theorem loadDefect_span {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : TriangleChain V) (hdiv : IsIntDiv p F G.edgeFinset) :
    SpanCompat p F (loadDefect p F G φ) := by
  have hloop : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag :=
    fun _ he => G.not_isDiag_of_mem_edgeFinset he
  obtain ⟨c1, hc1⟩ := PaddedF12.RealTypeTotals.real_span_of_isIntDiv p F G.edgeFinset hdiv
  obtain ⟨c2, hc2⟩ := real_span_boundary p F G (copyRestriction p F G φ)
    (copyRestriction_supported p F G φ)
  rw [← classTotal_edgeIndicator p G.edgeFinset hloop] at hc1
  refine ⟨fun τ => c1 τ - c2 τ, ?_⟩
  rw [loadDefect_eq_indicator_sub_boundary]
  funext i j
  have h1 := congrFun (congrFun hc1 i) j
  have h2 := congrFun (congrFun hc2 i) j
  simp only [classTotal_sub, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    sum_sub_distrib] at h1 h2 ⊢
  rw [h1, h2]

/-! ### Generic host inverse and repair -/

theorem exists_host_chain_inverse_gen (F : Finset (Multiset (Fin 4)))
    (hI : CompleteInverseCert F) {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Sym2 V → ℝ) (ε ω : ℝ) (hε : 0 ≤ ε) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω * (Fintype.card V : ℝ))
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

theorem hostRepair_gen (F : Finset (Multiset (Fin 4))) (hI : CompleteInverseCert F)
    (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (ω ε : ℝ) (φ : Finset V → ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 ≤ ε) (hlarge : 4 ≤ ω * Fintype.card V)
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
  obtain ⟨w, hws, hwe, hwb⟩ := exists_host_chain_inverse_gen F hI p H
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

theorem decomposition_gen (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hU : UniversalCert F) (hI : CompleteInverseCert F)
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
  obtain ⟨ψ, hψ, hψload⟩ := hostRepair_gen F hI V p G (A ∪ X) ω
    (ω ^ (PaddedInputs.hKT 4 m ^ 20)) φ hω hn.omega_le_one (by positivity)
    hn.class_n hG (hs.mono (by norm_num) le_rfl) hdiv
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
theorem keevashPaddedSpec_of_certs (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hU : UniversalCert F) (hI : CompleteInverseCert F) :
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
  exact decomposition_gen F hF hU hI V m ω hn p (PaddedInputs.edgeGraph J)
    (PaddedInputs.edgeGraph_allowed p F J hallowed)
    (PaddedInputs.guardedSupply_of_padded p F J hloop ω (2 ^ 21) hguardK hext)
    hdiv φ (fun T hT => ⟨(hw T hT).1, by simpa only [div_div] using (hw T hT).2⟩)
    (fun e he => hload e (hJ ▸ he))

/-! ### Instances: F₁, F₂, F₃ -/

theorem familyFacts_F1 : FamilyFacts F1 :=
  ⟨Family.card_three .one, Family.allowed_of_triangle .one, Family.forbidden .one⟩
theorem familyFacts_F2 : FamilyFacts F2 :=
  ⟨Family.card_three .two, Family.allowed_of_triangle .two, Family.forbidden .two⟩
theorem familyFacts_F3 : FamilyFacts F3 :=
  ⟨ColouredHub.F3_card_three, PaddedF3.f3_allowed_of_triangle, PaddedF3.f3_forbidden⟩

theorem universalCert_F1 : UniversalCert F1 :=
  fun V _ _ p G _ ω hG hs hω hω1 hn => Family.universal_simple .one p G ω hG hs hω hω1 hn
theorem universalCert_F2 : UniversalCert F2 :=
  fun V _ _ p G _ ω hG hs hω hω1 hn => Family.universal_simple .two p G ω hG hs hω hω1 hn
theorem universalCert_F3 : UniversalCert F3 :=
  fun V _ _ p G _ ω hG hs hω hω1 hn => PaddedF3.universal_simple_F3 p G ω hG hs hω hω1 hn

theorem completeInverseCert_F1 : CompleteInverseCert F1 :=
  fun V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hc =>
    exists_complete_chain_inverse p F1 r ε γ hε hγ hγ1 hlarge hmin hs hr
      (Or.inl ⟨rfl, F1RealCompatible.of_span p _ hc⟩)
theorem completeInverseCert_F2 : CompleteInverseCert F2 :=
  fun V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hc =>
    exists_complete_chain_inverse p F2 r ε γ hε hγ hγ1 hlarge hmin hs hr
      (Or.inr ⟨rfl, F2RealCompatible.of_span p _ hc⟩)
theorem completeInverseCert_F3 : CompleteInverseCert F3 :=
  fun V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hc =>
    PaddedF3.exists_complete_chain_inverse_F3 p r ε γ hε hγ hγ1 hlarge hmin hs hr
      (PaddedF3.F3RealCompatible.of_span p _ hc)

/-- Sanity check: the reduction recovers F₁, F₂, F₃. -/
theorem keevashPaddedSpec_F123_via_certs (F : Finset (Multiset (Fin 4)))
    (hF : F = F1 ∨ F = F2 ∨ F = F3) : PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with rfl | rfl | rfl
  · exact keevashPaddedSpec_of_certs F1 familyFacts_F1 universalCert_F1 completeInverseCert_F1
  · exact keevashPaddedSpec_of_certs F2 familyFacts_F2 universalCert_F2 completeInverseCert_F2
  · exact keevashPaddedSpec_of_certs F3 familyFacts_F3 universalCert_F3 completeInverseCert_F3

#print axioms loadDefect_span
#print axioms keevashPaddedSpec_of_certs
#print axioms keevashPaddedSpec_F123_via_certs

end PaddedGeneral
