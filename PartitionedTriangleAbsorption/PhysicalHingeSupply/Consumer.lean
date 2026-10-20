/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Supply
public import PartitionedTriangleAbsorption.SignedAbsorberAPIStage57
public import PartitionedTriangleAbsorption.TypedEmbeddingSelection

/-! # Interface bridges and the native consumer of the physical hinge supplier

**Bridges to existing host interfaces.** The primitive three/four-root queries of the
supplier are exactly `CommonNbrRich 4`. Among the existing interfaces:

* `TypedEmbeddingSelection.Supply p G 4 (ρ n)` is *the same* statement
  (`commonNbrRich_iff_supply`); it is already a hypothesis of
  `ColouredHub.OrderedEmbedding`;
* `CN6 = CommonNbrRich 6` implies it (`commonNbrRich_four_of_cn6`);
* `AntiEdgeful` does **not** imply it (`HingeSupplyFamilyStage58` refutes even the
  weaker conclusion `HingeSupply`), and `Supply p G 2 a` (used by `SharedF0.Host`) only
  controls two roots.

All of these that do imply it are themselves explicit hypotheses; none is derived from the
application host. The application gap is recorded in the Stage 59 report.

**Native consumer.** `signed_absorber_of_commonNbrRich` feeds the supplier into the
already verified signed absorber (`SignedHinge.signed_hinge_absorber`), with
`α = ρ`, `β = ρ^2/4`, `C0 = 6`; anti-edgefulness and non-empty parts are derived from
`CommonNbrRich 4` too, so the only host hypothesis is `CommonNbrRich 4 p G ρ`.
`absorber_of_commonNbrRich_api` is the fixed-host form in the Stage 57 API.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalHingeSupply

open Finset SignedHinge SignedCertificate F0Geometric TypedApplicationLinks

section Bridges

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `CommonNbrRich 4 p G ρ` is literally the existing `Supply p G 4 (ρ n)`. -/
theorem commonNbrRich_iff_supply {r : ℕ} (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (ρ : ℝ) :
    CommonNbrRich r p G ρ ↔ TypedEmbeddingSelection.Supply p G r (ρ * Fintype.card V) :=
  Iff.rfl

/-- Common-neighbour richness is monotone in the number of roots. -/
theorem commonNbrRich_mono {r r' : ℕ} (hr : r ≤ r') {p : V → Fin 2} {G : SimpleGraph V}
    [DecidableRel G.Adj] {ρ : ℝ} (h : CommonNbrRich r' p G ρ) : CommonNbrRich r p G ρ :=
  fun R hR i => h R (hR.trans hr) i

/-- The six-root hypothesis `CN6` gives the four-root queries. -/
theorem commonNbrRich_four_of_cn6 {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {ρ : ℝ} (h : CN6 p G ρ) : CommonNbrRich 4 p G ρ :=
  commonNbrRich_mono (by norm_num) h

/-- With `ρ n > 0`, common-neighbour richness makes both parts non-empty (empty root set). -/
theorem parts_of_commonNbrRich {r : ℕ} {p : V → Fin 2} {G : SimpleGraph V}
    [DecidableRel G.Adj] {ρ : ℝ} (hpos : 0 < ρ * Fintype.card V)
    (h : CommonNbrRich r p G ρ) : ∀ j : Fin 2, ∃ v, p v = j := by
  intro j
  have h1 := h ∅ (by simp) j
  have h2 : 0 < (univ.filter (fun w => p w = j ∧ ∀ u ∈ (∅ : Finset V), G.Adj u w)).card := by
    exact_mod_cast hpos.trans_le h1
  obtain ⟨v, hv⟩ := card_pos.mp h2
  exact ⟨v, (mem_filter.mp hv).2.1⟩

end Bridges

section Consumer

/-- **Fixed-host native consumer (Stage 57 API).** `CommonNbrRich 4 p G ρ`, `8 ≤ ρ n` and the
two budget inequalities for `C0 = 6`, `β = ρ^2/4` give the signed absorber with the
unchanged physical contract. -/
theorem absorber_of_commonNbrRich_api (ρ : ℝ) (K : ℕ) {V : Type*}
    [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : CommonNbrRich 4 p G ρ) (hn : 8 ≤ ρ * Fintype.card V)
    {ι : Type*} [Fintype ι] (P : Finset (Sym2 V)) (t : ι → Finset V)
    (c : ι → ℤ) (Z : Finset V) (hcert : IsSignedCert p G P t c)
    (hK : certWeight c ≤ K) (hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z)
    (hZ : Z.card ≤ 3 * K)
    (hαM : (absorberBudget 6 K : ℝ) < ρ * Fintype.card V)
    (hβM : (2 ^ Nat.choose (6 + 1) 2 : ℝ) * absorberBudget 6 K <
      ρ ^ 2 / 4 * Fintype.card V) :
    ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
      IsAbsorber p P A ∧ IsTwoMode p P A Q ∧ IsTransformer (p := p) (F := F0) A P Q ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
      (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
      A.card ≤ absorberConst 6 * K ∧ Q.card ≤ absorberConst 6 * K ∧
      (vertSet (A ∪ Q)).card ≤ absorberConst 6 * K ∧
      pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
      pairCount p Q 0 1 = pairCount p P 0 1 :=
  SignedAbsorberAPIStage57.absorber_of_budget_api ρ (ρ ^ 2 / 4) 6 K p G
    (parts_of_commonNbrRich (by linarith) hG)
    (antiEdgeful_of_commonNbrRich (by norm_num) p G hG)
    (hingeSupply_of_budget hn hG) P t c Z hcert hK hPZ hZ hαM hβM

/-- **Asymptotic native consumer.** For `ρ > 0` and certificate weight `K`, constants `C, N`
(chosen before the host) give the signed absorber for every host of order `≥ N` whose only
geometric hypothesis is `CommonNbrRich 4 p G ρ`. -/
theorem signed_absorber_of_commonNbrRich (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    ∃ C N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
        CommonNbrRich 4 p G ρ →
        ∀ {ι : Type} [Fintype ι] (P : Finset (Sym2 V)) (t : ι → Finset V) (c : ι → ℤ)
          (Z : Finset V), IsSignedCert p G P t c → certWeight c ≤ K →
          (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → Z.card ≤ 3 * K →
          ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
            Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧ (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
            (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
            HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q) ∧
            A.card ≤ C * K ∧ Q.card ≤ C * K ∧ (vertSet (A ∪ Q)).card ≤ C * K ∧
            pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
            pairCount p Q 0 1 = pairCount p P 0 1 := by
  obtain ⟨C, N0, hN0⟩ := signed_hinge_absorber ρ (ρ ^ 2 / 4) hρ (by positivity) 6 K
  refine ⟨C, max N0 (Nat.ceil (8 / ρ)), ?_⟩
  intro V _ _ hN p G _ hG
  have hn : 8 ≤ ρ * Fintype.card V := by
    have h1 : 8 / ρ ≤ (Fintype.card V : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
    rw [div_le_iff₀ hρ] at h1
    linarith
  intro ι _ P t c Z hcert hK hPZ hZ
  exact hN0 V ((le_max_left _ _).trans hN) p G (parts_of_commonNbrRich (by linarith) hG)
    (antiEdgeful_of_commonNbrRich (by norm_num) p G hG) (hingeSupply_of_budget hn hG)
    P t c Z hcert hK hPZ hZ

end Consumer

end PartitionedTriangleAbsorption.PhysicalHingeSupply
