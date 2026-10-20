/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TorsionRefiner
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostLayer

/-!
# The ordinary, integer-charge and torsion layers with closed quantitative bounds

This assembly constructs the full shared refiner. Its two physical supply
arguments are quantitative token producers; the concrete guarded template
producer discharges them for F1 and F2 in the family-specific assembly.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.OnePart

abbrev OrdinaryIndex := ℕ × Bool × Fin 3 × Fin 3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The proved physical algebra needed by the two families. -/
structure R2Algebra (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (χ : Fin 4 → Fin 4 → ℤ) (Good : Finset (Sym2 V) → Prop)
    (q : ParityEvaluation Good) : Prop where
  chi_bound : ∀ i j, |χ i j| ≤ 2
  charge_dvd : ∀ A, (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → Even3 A →
    (12 : ℤ) ∣ charge χ p A
  good_iff : ∀ A, Good A ↔ (∀ e ∈ A, ¬ e.IsDiag) ∧ ActiveEdges F p A ∧
    (∀ v, Even (incidentLoad A v)) ∧ charge χ p A = 0
  div_iff : ∀ A, (∀ e ∈ A, ¬ e.IsDiag) →
    (IsIntDiv p F A ↔ Good A ∧ q.value A = 0)
  ordinary : ∀ A, (∀ e ∈ A, ¬ e.IsDiag) → IsIntDiv p F A → IsIntDiv part1 triFam A

theorem demand_le_fourteen (χ : Fin 4 → Fin 4 → ℤ) (p : V → Fin 4)
    (hχ : ∀ i j, |χ i j| ≤ 2) (A : Finset (Sym2 V))
    (hdvd : (12 : ℤ) ∣ charge χ p A) (hcard : A.card ≤ 42) :
    (charge χ p A / 12).natAbs ≤ 14 := by
  have hb := abs_charge_le p (fun e => abs_pair_pairVec_le hχ p e) A
  have hc : (A.card : ℤ) ≤ 42 := by exact_mod_cast hcard
  have heq : charge χ p A = 12 * (charge χ p A / 12) :=
    (Int.mul_ediv_cancel' hdvd).symm
  rw [heq, abs_mul] at hb
  norm_num at hb
  have hnat : ((charge χ p A / 12).natAbs : ℤ) ≤ 14 := by
    rw [Int.natCast_natAbs]
    omega
  exact_mod_cast hnat

theorem degree_biUnion_of_sum {I : Type*} (S : Finset I) (P : I → Finset (Sym2 V))
    (d : ℝ) (h : ∀ v, ((∑ i ∈ S, incidentLoad (P i) v : ℕ) : ℝ) ≤ d) :
    DegBounded (S.biUnion P) d := by
  intro v
  have hn : (incidentLoad (S.biUnion P) v : ℝ) ≤
      ((∑ i ∈ S, incidentLoad (P i) v : ℕ) : ℝ) := by
    exact_mod_cast incidentLoad_biUnion_le S P v
  exact hn.trans (h v)

theorem active_of_host (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) : ActiveEdges F p A :=
  fun a b hab => hG a b (SimpleGraph.mem_edgeFinset.mp (hA hab))

theorem loopless_of_host (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) : ∀ e ∈ A, ¬ e.IsDiag :=
  fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hA he))

/-- The complete shared refiner: pieces have at most 144 edges, there are at
most `2^23 rho n^2` pieces and the total incidence is at most `2^14 lam n`. -/
theorem exists_r2_refiner
    (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (χ : Fin 4 → Fin 4 → ℤ)
    (Good : Finset (Sym2 V) → Prop) (q : ParityEvaluation Good)
    (alg : R2Algebra p F χ Good q)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (γ lam rho : ℝ) (hanti : AntiEdgeful part1 triFam G γ)
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hantiScale : 8 * lam ≤ γ)
    (hrho : 0 < rho) (hscale : 2 ^ 32 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (chargeSupply : ∀ B : Finset (Sym2 V), DegBounded B (6 * lam * Fintype.card V) →
      ∀ S : Finset (Tok OrdinaryIndex),
      (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2 →
      ∃ tok, TokReal χ (fun _ _ => 0) p 12 6 B S tok ∧
        (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
        ∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lam * Fintype.card V)
    (paritySupply : ∀ B : Finset (Sym2 V), DegBounded B (6 * lam * Fintype.card V) →
      ∀ S : Finset TorsionChain.Atom,
      (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2 →
      ∃ tok, ParityTokenReal q B S tok ∧ (∀ a ∈ S, (tok a).card ≤ 6) ∧
        (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
        ∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lam * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset TorsionChain.Index) (P : TorsionChain.Index → Finset (Sym2 V))
      (R : Finset (Sym2 V)), R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := p) (F := F) indices P X R ∧
      (∀ i ∈ indices, P i ⊆ X ∪ R ∧ IsIntDiv p F (P i) ∧ (P i).card ≤ 144) ∧
      DegBounded R (6 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 2 ^ 23 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) ≤
        2 ^ 14 * lam * Fintype.card V := by
  classical
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hscale24 : 2 ^ 24 * rho ≤ lam ^ 2 := by nlinarith
  have hrholam : 2 * rho ≤ lam := by nlinarith
  have hQ0 : IsIntDiv (part1 : V → Fin 1) triFam ∅ :=
    isIntDiv_of_hasDecomp hasDecomp_empty
  obtain ⟨I0, P0, R0, hR0G, hR0X, href0, hp0, hR0deg, hcard0, hinc0⟩ :=
    exists_universal_refiner_alpha G X hXG lam rho hlam hlam64 hrho hscale24
      hn1 hn2 hX γ hantiScale hanti
  let E0 : PredRefiner OrdinaryIndex X (IsIntDiv part1 triFam) :=
    { lib := I0
      P := P0
      R0 := R0
      loopP := fun j hj => (hp0 j hj).2.1
      evenP := fun j hj => (hp0 j hj).2.2.1
      subP := fun j hj => by rw [union_comm]; exact (hp0 j hj).1
      disjRX := hR0X
      refines := href0 }
  have hactive0 : ∀ i ∈ E0.lib, ActiveEdges F p (E0.P i) := by
    intro i hi
    exact active_of_host p F G hG ((E0.subP i hi).trans (union_subset hR0G hXG))
  have hdvd : ∀ i ∈ E0.lib, (12 : ℤ) ∣ charge χ p (E0.P i) := by
    intro i hi
    exact alg.charge_dvd _ (E0.loopP i hi) (hactive0 i hi)
      ⟨(hp0 i hi).2.2.2.1, E0.evenP i hi⟩
  have habs : ∀ i ∈ E0.lib, (charge χ p (E0.P i) / 12).natAbs ≤ 14 := by
    intro i hi
    exact demand_le_fourteen χ p alg.chi_bound _ (hdvd i hi) (hp0 i hi).2.2.2.2
  have hsum : ∑ i ∈ E0.lib, (charge χ p (E0.P i) / 12).natAbs ≤ 14 * E0.lib.card := by
    calc
      _ ≤ ∑ _i ∈ E0.lib, 14 := sum_le_sum habs
      _ = _ := by simp [mul_comm]
  have hledger0 : DegBounded (E0.R0 ∪ X) (6 * lam * Fintype.card V) := by
    intro v
    have h := degBounded_union hR0deg hX v
    have hnum := mul_le_mul_of_nonneg_right hrholam hn0
    change (incidentLoad (E0.R0 ∪ X) v : ℝ) ≤ _
    dsimp [E0]
    change (incidentLoad (R0 ∪ X) v : ℝ) ≤ 4 * lam * n + 2 * rho * n at h
    change (incidentLoad (R0 ∪ X) v : ℝ) ≤ 6 * lam * n
    nlinarith
  let ExtraC : Finset (Tok OrdinaryIndex) → (Tok OrdinaryIndex → Finset (Sym2 V)) → Prop :=
    fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lam * n
  obtain ⟨SC, tokC, E1, hrealC, hextraC, hSC, hE1R, hzero1, _, hsize1, hload1, hlib1⟩ :=
    token_layer E0 hQ0 χ (fun _ _ => 0) p 12 (by norm_num) hdvd 6 ExtraC (by
      intro S hS
      have hsN : S.card ≤ 126 * E0.lib.card := by omega
      have hsR : (S.card : ℝ) ≤ 126 * (I0.card : ℝ) := by exact_mod_cast hsN
      have hSbound : (S.card : ℝ) ≤ 2 ^ 22 * rho * n ^ 2 := by
        change (I0.card : ℝ) ≤ 1224 * rho * n ^ 2 at hcard0
        nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
      exact chargeSupply _ hledger0 S hSbound)
  have hTCG : SC.biUnion tokC ⊆ G.edgeFinset := biUnion_subset.mpr hextraC.1
  have hR1G : E1.R0 ⊆ G.edgeFinset := by rw [hE1R]; exact union_subset hR0G hTCG
  have hTCdegree : DegBounded (SC.biUnion tokC) (lam * n) :=
    degree_biUnion_of_sum SC tokC _ hextraC.2
  have hR1degree : DegBounded E1.R0 (5 * lam * n) := by
    rw [hE1R]
    convert degBounded_union hR0deg hTCdegree using 1
    dsimp [n]
    ring
  have hsize126 : ∀ i ∈ E1.lib, (E1.P i).card ≤ 126 := by
    intro i hi
    rcases hsize1 i hi with h | ⟨j, hj, h⟩
    · omega
    · have hP := (hp0 j hj).2.2.2.2
      have hA := habs j hj
      change (P0 j).card ≤ 42 at hP
      change (E0.P j).card ≤ 42 at hP
      omega
  have hgood1 : ∀ i ∈ E1.lib, Good (E1.P i) := by
    intro i hi
    exact (alg.good_iff _).mpr ⟨E1.loopP i hi,
      active_of_host p F G hG ((E1.subP i hi).trans (union_subset hR1G hXG)),
      E1.evenP i hi, hzero1 i hi⟩
  have hlib1N : E1.lib.card ≤ 1359 * E0.lib.card := by omega
  have hcard1 : (E1.lib.card : ℝ) ≤ 2 ^ 21 * rho * n ^ 2 := by
    have hN : (E1.lib.card : ℝ) ≤ 1359 * (I0.card : ℝ) := by exact_mod_cast hlib1N
    change (I0.card : ℝ) ≤ 1224 * rho * n ^ 2 at hcard0
    nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
  have hinc1 : ∀ v, ((∑ i ∈ E1.lib, incidentLoad (E1.P i) v : ℕ) : ℝ) ≤ 4140 * lam * n := by
    intro v
    have h1 : ((∑ i ∈ E1.lib, incidentLoad (E1.P i) v : ℕ) : ℝ) ≤
        ((∑ i ∈ I0, incidentLoad (P0 i) v : ℕ) : ℝ) +
          44 * ((∑ a ∈ SC, incidentLoad (tokC a) v : ℕ) : ℝ) := by exact_mod_cast hload1 v
    have h2 := hextraC.2 v
    have h3 := hinc0 v
    change ((∑ i ∈ I0, incidentLoad (P0 i) v : ℕ) : ℝ) ≤ 4096 * lam * n at h3
    linarith
  have hledger1 : DegBounded (E1.R0 ∪ X) (6 * lam * Fintype.card V) := by
    intro v
    have h := degBounded_union hR1degree hX v
    have hnum := mul_le_mul_of_nonneg_right hrholam hn0
    change (incidentLoad (E1.R0 ∪ X) v : ℝ) ≤ 5 * lam * n + 2 * rho * n at h
    change (incidentLoad (E1.R0 ∪ X) v : ℝ) ≤ 6 * lam * n
    linarith
  let ExtraP : Finset TorsionChain.Atom → (TorsionChain.Atom → Finset (Sym2 V)) → Prop :=
    fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lam * n
  have hQ1good : ∀ L ⊆ X, IsIntDiv part1 triFam L ∧ charge χ p L = 0 → Good L := by
    rintro L hLX ⟨hL, hc⟩
    have hLG := hLX.trans hXG
    have hloop := loopless_of_host G hLG
    exact (alg.good_iff L).mpr ⟨hloop, active_of_host p F G hG hLG,
      ((isIntDiv_part1_iff L hloop).mp hL).2, hc⟩
  obtain ⟨SP, tokP, E2, hrealP, hextraP, hSP, hE2R, hpieces2, hlib2, hload2⟩ :=
    torsion_layer E1 q ⟨hQ0, charge_empty _ _⟩ hgood1 hQ1good
      (fun A hA => ((alg.good_iff A).mp hA).1)
      (fun A hA => ((alg.good_iff A).mp hA).2.2.1) 126 6 hsize126 ExtraP (by
        intro S hS
        have hsR : (S.card : ℝ) ≤ 2 * (E1.lib.card : ℝ) := by exact_mod_cast hS
        have hbound : (S.card : ℝ) ≤ 2 ^ 22 * rho * n ^ 2 := by nlinarith
        exact paritySupply _ hledger1 S hbound)
  have hR2G : E2.R0 ⊆ G.edgeFinset := by
    rw [hE2R]
    exact union_subset hR1G (biUnion_subset.mpr hextraP.1)
  refine ⟨E2.lib, E2.P, E2.R0, hR2G, E2.disjRX, ?_, ?_, ?_, ?_, ?_⟩
  · apply E2.refinesReserve
    intro L hLX hL
    have hloop := loopless_of_host G (hLX.trans hXG)
    have hgoodbit := (alg.div_iff L hloop).mp hL
    exact ⟨⟨alg.ordinary L hloop hL, ((alg.good_iff L).mp hgoodbit.1).2.2.2⟩, hgoodbit.2⟩
  · intro i hi
    have hp := hpieces2 i hi
    refine ⟨?_, (alg.div_iff _ (E2.loopP i hi)).mpr ⟨hp.1, hp.2.1⟩, hp.2.2⟩
    simpa only [union_comm] using E2.subP i hi
  · rw [hE2R]
    have hTPdegree := degree_biUnion_of_sum SP tokP (lam * n) hextraP.2
    convert degBounded_union hR1degree hTPdegree using 1
    dsimp [n]
    ring
  · have h2 : (E2.lib.card : ℝ) ≤ 4 * (E1.lib.card : ℝ) := by exact_mod_cast hlib2
    change (E2.lib.card : ℝ) ≤ 2 ^ 23 * rho * n ^ 2
    nlinarith
  · intro v
    have h2 : ((∑ i ∈ E2.lib, incidentLoad (E2.P i) v : ℕ) : ℝ) ≤
        2 * ((∑ i ∈ E1.lib, incidentLoad (E1.P i) v : ℕ) : ℝ) +
          4 * ((∑ a ∈ SP, incidentLoad (tokP a) v : ℕ) : ℝ) := by exact_mod_cast hload2 v
    have h1 := hinc1 v
    have ht := hextraP.2 v
    change ((∑ i ∈ E2.lib, incidentLoad (E2.P i) v : ℕ) : ℝ) ≤ 2 ^ 14 * lam * n
    nlinarith

#print axioms demand_le_fourteen
#print axioms exists_r2_refiner

end PaddedF12
