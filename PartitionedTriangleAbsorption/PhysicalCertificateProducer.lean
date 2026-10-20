/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Defs
public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Consumer

/-! # From a bounded physical certificate to an F0 absorber

The support bounds hold for every family of partitioned triangles. Only the last two
theorems specialize to F0 and use the existing common-neighbour/physical-hinge producer.
They require a bound on physical certificate cost and common-neighbour richness of
order four. They do not establish the general candidate for Theorem 13.16 or [17].
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalCertificateProducer

open Finset BlowupB SignedCertificate SignedHinge TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  {ι : Type*} [Fintype ι] {P : Finset (Sym2 V)} {T : ι → Finset V} {c : ι → ℤ}

omit [Fintype V] in
/-- Every source edge occurs in a certificate triangle with nonzero coefficient. -/
theorem edge_covered_of_physCert (h : PhysCert p F G P T c) {e : Sym2 V}
    (he : e ∈ P) : ∃ j, c j ≠ 0 ∧ e ∈ triEdges (T j) := by
  have hsum : (∑ j, c j * indZ (triEdges (T j)) e) ≠ 0 := by
    rw [← h.2 e, indZ_mem he]
    norm_num
  obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨j, fun hc => hj (by simp [hc]), ?_⟩
  by_contra hn
  exact hj (by simp [indZ, hn])

/-- The source is contained in the union of the nonzero certificate triangles. -/
theorem support_subset_of_physCert (h : PhysCert p F G P T c) :
    vertSet P ⊆ univ.biUnion (fun j => if c j = 0 then ∅ else T j) := by
  classical
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_vertSet.mp hv
  obtain ⟨j, hj, hej⟩ := edge_covered_of_physCert h he
  refine mem_biUnion.mpr ⟨j, mem_univ j, ?_⟩
  rw [ite_eq_right hj]
  exact mem_sym2_iff.mp (mem_filter.mp hej).1 v hve

/-- Three vertices per nonzero triangle, charged to its absolute integer coefficient. -/
theorem support_card_le_of_physCert (h : PhysCert p F G P T c) :
    ((vertSet P).card : ℤ) ≤ 3 * ∑ j, |c j| := by
  classical
  have hcard : (vertSet P).card ≤ 3 * ∑ j, (c j).natAbs := by
    calc
      (vertSet P).card ≤
          (univ.biUnion (fun j => if c j = 0 then ∅ else T j)).card :=
        card_le_card (support_subset_of_physCert h)
      _ ≤ ∑ j, (if c j = 0 then ∅ else T j).card := card_biUnion_le
      _ ≤ ∑ j, 3 * (c j).natAbs := by
        refine sum_le_sum fun j _ => ?_
        by_cases hj : c j = 0
        · simp [hj]
        · rw [ite_eq_right hj, (h.1 j).1.card_eq]
          have hpos : 0 < (c j).natAbs := Int.natAbs_pos.mpr hj
          omega
      _ = 3 * ∑ j, (c j).natAbs := (mul_sum _ _ _).symm
  have hcast : ((vertSet P).card : ℤ) ≤ 3 * (∑ j, (c j).natAbs : ℕ) := by
    exact_mod_cast hcard
  simpa using hcast

/-- A physical certificate already guarantees that all source edges lie in the host. -/
theorem subset_host_of_physCert [DecidableRel G.Adj] (h : PhysCert p F G P T c) :
    P ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨j, _, hej⟩ := edge_covered_of_physCert h he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hxy, hnd⟩ := mem_filter.mp hej
    have hx := mem_sym2_iff.mp hxy x (Sym2.mem_mk_left x y)
    have hy := mem_sym2_iff.mp hxy y (Sym2.mem_mk_right x y)
    rw [Sym2.mk_isDiag_iff] at hnd
    exact SimpleGraph.mem_edgeFinset.mpr ((h.1 j).1.isClique hx hy hnd)

/-- Cost at most K supplies the formerly explicit source-anchor bound. -/
theorem support_card_le_of_physDivCost {K : ℕ} (h : PhysDivCost p F G P K) :
    (vertSet P).card ≤ 3 * K := by
  obtain ⟨ι, _, T, c, hc, hK⟩ := h
  have hcard := (support_card_le_of_physCert hc).trans (mul_le_mul_of_nonneg_left hK
    (by norm_num : (0 : ℤ) ≤ 3))
  exact_mod_cast hcard

end PartitionedTriangleAbsorption.PhysicalCertificateProducer

namespace PartitionedTriangleAbsorption.PhysicalCertificateProducer

open Finset BlowupB SignedCertificate SignedHinge TypedApplicationLinks PhysicalHingeSupply
  F0Geometric

/-- Fixed-host producer: the physical cost bound supplies both the certificate and its
anchor set. The returned destination avoids every vertex of the source. -/
theorem absorber_of_physDivCost_budget (ρ : ℝ) (K : ℕ) {V : Type*}
    [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : CommonNbrRich 4 p G ρ) (hn : 8 ≤ ρ * Fintype.card V)
    (P : Finset (Sym2 V)) (hP : PhysDivCost p F0 G P K)
    (hαM : (absorberBudget 6 K : ℝ) < ρ * Fintype.card V)
    (hβM : (2 ^ Nat.choose (6 + 1) 2 : ℝ) * absorberBudget 6 K <
      ρ ^ 2 / 4 * Fintype.card V) :
    ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
      IsAbsorber p P A ∧ IsTwoMode p P A Q ∧ IsTransformer (p := p) (F := F0) A P Q ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ vertSet P) ∧
      (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
      A.card ≤ absorberConst 6 * K ∧ Q.card ≤ absorberConst 6 * K ∧
      (vertSet (A ∪ Q)).card ≤ absorberConst 6 * K ∧
      pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
      pairCount p Q 0 1 = pairCount p P 0 1 := by
  have hZ := support_card_le_of_physDivCost hP
  obtain ⟨ι, _, T, c, hc, hK⟩ := hP
  exact absorber_of_commonNbrRich_api ρ K p G hG hn P T c (vertSet P)
    hc hK (fun _ he _ hv => mem_vertSet.mpr ⟨_, he, hv⟩) hZ hαM hβM

/-- Uniform producer: C and N precede the host and source; only bounded physical lattice
membership and common-neighbour richness are required as input. -/
theorem absorber_of_physDivCost (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    ∃ C N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
        CommonNbrRich 4 p G ρ → ∀ (P : Finset (Sym2 V)), PhysDivCost p F0 G P K →
          ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
            Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧
            (∀ e ∈ Q, ∀ v ∈ e, v ∉ vertSet P) ∧
            (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
            HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q) ∧
            A.card ≤ C * K ∧ Q.card ≤ C * K ∧ (vertSet (A ∪ Q)).card ≤ C * K ∧
            pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
            pairCount p Q 0 1 = pairCount p P 0 1 := by
  obtain ⟨C, N, h⟩ := signed_absorber_of_commonNbrRich ρ hρ K
  refine ⟨C, N, ?_⟩
  intro V _ _ hN p G _ hG P hP
  have hZ := support_card_le_of_physDivCost hP
  obtain ⟨ι, _, T, c, hc, hK⟩ := hP
  exact h V hN p G hG P T c (vertSet P) hc hK
    (fun _ he _ hv => mem_vertSet.mpr ⟨_, he, hv⟩) hZ

end PartitionedTriangleAbsorption.PhysicalCertificateProducer
