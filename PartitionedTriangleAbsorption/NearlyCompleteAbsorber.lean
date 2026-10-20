/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Nearly
public import PartitionedTriangleAbsorption.PhysicalCertificateProducer

/-! # Absorption from aggregate divisibility in a nearly complete F0 host

The query estimate works for every triangle family and every compatible root set.
The absorber theorem specializes to F0: bounded aggregate divisibility is converted
to a bounded physical certificate, and common-neighbour richness is derived from
the missing-degree bound. The constants precede the host and the source.
This is a bounded-source result under explicit density hypotheses, not general [17].
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NearlyCompleteAbsorber

open Finset BlowupB F0Geometric TypedApplicationLinks PhysicalCertificateProducer SignedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- A compatible query loses at most d+1 vertices per root, including the root itself. -/
theorem card_query_ge (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hmiss : ∀ v, missDeg p F G v ≤ d) (R : Finset V) (i : Fin t)
    (hcompat : ∀ u ∈ R, AllowedPair F (p u) i) :
    (univ.filter fun v => p v = i).card ≤
      (univ.filter fun v => p v = i ∧ ∀ u ∈ R, G.Adj u v).card + R.card * (d + 1) := by
  classical
  let Q := univ.filter fun v => p v = i ∧ ∀ u ∈ R, G.Adj u v
  have hsub : (univ.filter fun v => p v = i) ⊆ Q ∪ (R ∪ R.biUnion (missSet p F G)) := by
    intro v hv
    have hpi := (mem_filter.mp hv).2
    by_cases hq : ∀ u ∈ R, G.Adj u v
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hpi, hq⟩)
    · push Not at hq
      obtain ⟨u, hu, huv⟩ := hq
      refine mem_union_right _ ?_
      by_cases heq : u = v
      · exact mem_union_left _ (heq ▸ hu)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨u, hu,
          mem_filter.mpr ⟨mem_univ _, heq,
            by simpa only [hpi] using hcompat u hu, huv⟩⟩)
  have hbad : (R.biUnion (missSet p F G)).card ≤ R.card * d := by
    calc
      (R.biUnion (missSet p F G)).card ≤ ∑ u ∈ R, (missSet p F G u).card :=
        card_biUnion_le
      _ ≤ ∑ _u ∈ R, d := sum_le_sum fun u _ => hmiss u
      _ = R.card * d := by rw [sum_const, smul_eq_mul]
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 := card_union_le R (R.biUnion (missSet p F G))
  dsimp [Q] at h1
  nlinarith

/-- All colour pairs are allowed for F0. -/
theorem allowedPair_F0 (i j : Fin 2) : AllowedPair F0 i j := by
  revert i j
  decide

/-- Missing degree and class sizes supply the four-root queries used by the hinges. -/
theorem commonNbrRich_of_missing (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hmiss : ∀ v, missDeg p F0 G v ≤ d) (ρ : ℝ)
    (hcls : ∀ i, ρ * Fintype.card V + 4 * (d + 1) ≤
      ((univ.filter fun v => p v = i).card : ℝ)) : CommonNbrRich 4 p G ρ := by
  intro R hR i
  have hq := card_query_ge p F0 G hmiss R i (fun u _ => allowedPair_F0 (p u) i)
  have hq' : ((univ.filter fun v => p v = i).card : ℝ) ≤
      (univ.filter fun v => p v = i ∧ ∀ u ∈ R, G.Adj u v).card +
        (R.card : ℝ) * (d + 1) := by exact_mod_cast hq
  have hR' : (R.card : ℝ) ≤ 4 := by exact_mod_cast hR
  have hloss : (R.card : ℝ) * (d + 1) ≤ 4 * (d + 1) :=
    mul_le_mul_of_nonneg_right hR' (by positivity)
  linarith [hcls i]

/-- No physical certificate is assumed: the source only supplies aggregate divisibility.
The bound B depends on the source size cap K and rho, never on the host or missing degree. -/
theorem absorber_of_aggregate_nearly (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    ∃ B N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
        (∀ v, missDeg p F0 G v ≤ d) →
        (∀ i, (2 * K + 10) * (d + 1) < (univ.filter fun v => p v = i).card) →
        (∀ i, ρ * Fintype.card V + 4 * (d + 1) ≤
          ((univ.filter fun v => p v = i).card : ℝ)) →
        ∀ (P : Finset (Sym2 V)), P ⊆ G.edgeFinset → IsIntDiv p F0 P → P.card ≤ K →
          ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
            Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧
            (∀ e ∈ Q, ∀ v ∈ e, v ∉ vertSet P) ∧
            (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
            HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q) ∧
            A.card ≤ B ∧ Q.card ≤ B ∧ (vertSet (A ∪ Q)).card ≤ B ∧
            pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
            pairCount p Q 0 1 = pairCount p P 0 1 := by
  obtain ⟨C, hC⟩ := physDivCost_nearly F0 (by decide) K
  obtain ⟨D, N, hA⟩ := absorber_of_physDivCost ρ hρ C.toNat
  refine ⟨D * C.toNat, N, ?_⟩
  intro V _ _ hN p G _ d hmiss hcls hgeom P hP hdiv hK
  have hphys := hC (fun u v _ => allowedPair_F0 (p u) (p v)) hmiss
    (by simpa using hcls) hP hdiv hK
  obtain ⟨ι, hι, T, c, hc, hcost⟩ := hphys
  have hbudget : PhysDivCost p F0 G P C.toNat :=
    ⟨ι, hι, T, c, hc, hcost.trans (Int.self_le_toNat C)⟩
  exact hA V hN p G (commonNbrRich_of_missing p G hmiss ρ hgeom) P hbudget

end PartitionedTriangleAbsorption.NearlyCompleteAbsorber
