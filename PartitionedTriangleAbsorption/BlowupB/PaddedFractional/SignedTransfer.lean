/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.OctahedronKernel
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.SignedEdgeTransfer

/-!
# Global signed transfer from the complete allowed graph to the host

Each physical complete triangle contributes its octahedral base and three
rooted sides. All occurrences of a fixed unordered edge are oriented to
one pair of endpoints and repaired together. This preserves the original
boundary, removes every unavailable old edge, and retains the polynomial
coefficient bound.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer StructuralF3General PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : ℝ}

namespace ThirdDistribution

def swapped {a b : V} (μ : ThirdDistribution p F G a b s) :
    ThirdDistribution p F G b a s where
  law := μ.law
  completion := μ.completion
  typed := (link_root_swap F _ _ _).mp μ.typed
  support c hc := ⟨(μ.support c hc).1, (μ.support c hc).2.2, (μ.support c hc).2.1⟩
  cap := μ.cap

omit [DecidableRel G.Adj] in
theorem swapped_chain {a b : V} (μ : ThirdDistribution p F G a b s) :
    μ.swapped.chain = μ.chain := by
  funext Q
  unfold chain swapped
  apply μ.law.average_congr
  intro c _
  congr 1
  ext v
  simp only [mem_insert, mem_singleton, or_left_comm]

omit [DecidableRel G.Adj] in
theorem exists_reindexed {a b c d : V} (μ : ThirdDistribution p F G a b s)
    (hac : a = c) (hbd : b = d) :
    ∃ ν : ThirdDistribution p F G c d s, ν.chain = μ.chain := by
  subst c
  subst d
  exact ⟨μ, rfl⟩

end ThirdDistribution

omit [Fintype V] [DecidableEq V] in
theorem mk_out_eq (e : Sym2 V) : s(e.out.1, e.out.2) = e := by
  exact e.out_eq

namespace RootedSide

omit [DecidableRel G.Adj] in
theorem exists_oriented (R : RootedSide p F G s) (e : Sym2 V)
    (he : R.edge p F G = e) :
    ∃ μ : ThirdDistribution p F G e.out.1 e.out.2 s, μ.chain = R.distribution.chain := by
  have hp : s(R.left, R.right) = s(e.out.1, e.out.2) := he.trans (mk_out_eq e).symm
  rcases Sym2.eq_iff.mp hp with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact R.distribution.exists_reindexed hl hr
  · obtain ⟨μ, hμ⟩ := R.distribution.swapped.exists_reindexed hr hl
    exact ⟨μ, hμ.trans R.distribution.swapped_chain⟩

noncomputable def oriented (R : RootedSide p F G s) (e : Sym2 V)
    (he : R.edge p F G = e) : ThirdDistribution p F G e.out.1 e.out.2 s :=
  Classical.choose (R.exists_oriented e he)

omit [DecidableRel G.Adj] in
theorem oriented_chain (R : RootedSide p F G s) (e : Sym2 V)
    (he : R.edge p F G = e) : (R.oriented e he).chain = R.distribution.chain :=
  Classical.choose_spec (R.exists_oriented e he)

omit [DecidableRel G.Adj] [DecidableEq V] in
theorem out_distinct (R : RootedSide p F G s) (e : Sym2 V)
    (he : R.edge p F G = e) : e.out.1 ≠ e.out.2 := by
  have hp : s(R.left, R.right) = s(e.out.1, e.out.2) := he.trans (mk_out_eq e).symm
  intro hh
  apply R.distinct
  rcases Sym2.eq_iff.mp hp with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact hl.trans (hh.trans hr.symm)
  · exact hl.trans (hh.symm.trans hr.symm)

end RootedSide

namespace SignedTransfer

noncomputable def outFlag (Q : Finset V) (e : Sym2 V) : ℝ :=
  vertexIndicator Q e.out.1 + vertexIndicator Q e.out.2

omit [Fintype V] in
theorem outFlag_nonneg (Q : Finset V) (e : Sym2 V) : 0 ≤ outFlag Q e :=
  add_nonneg (vertexIndicator_nonneg Q _) (vertexIndicator_nonneg Q _)

omit [Fintype V] in
theorem outFlag_mk (Q : Finset V) (a b : V) :
    outFlag Q s(a, b) = vertexIndicator Q a + vertexIndicator Q b := by
  have hh := mk_out_eq s(a, b)
  rcases Sym2.eq_iff.mp hh with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [outFlag, ha, hb]
  · simp only [outFlag, ha, hb, add_comm]

omit [Fintype V] in
theorem sum_outFlag_triangle {T : Finset V} (hT : T.card = 3) (Q : Finset V) :
    (∑ e ∈ triEdges T, outFlag Q e) = 2 * ∑ v ∈ T, vertexIndicator Q v := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hT
  rw [sum_triEdges_three _ hab hac hbc]
  simp only [outFlag_mk]
  simp [hab, hac, hbc]
  ring

abbrev CompleteCopies (p : V → Fin t) (F : Finset (Multiset (Fin t))) :=
  {T : Finset V // T ∈ copies p F (activeCompleteGraph p F)}

abbrev KernelFamily (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℝ) :=
  (T : CompleteCopies p F) → OctKernel p F G s T.val

abbrev SideIndex (p : V → Fin t) (F : Finset (Multiset (Fin t))) :=
  CompleteCopies p F × Fin 3

def occurrenceEdge (K : KernelFamily p F G s) (i : SideIndex p F) : Sym2 V :=
  ((K i.1).side i.2).edge p F G

abbrev EdgeFiber (K : KernelFamily p F G s) (e : Sym2 V) :=
  {i : SideIndex p F // occurrenceEdge K i = e}

noncomputable def fiberDistribution (K : KernelFamily p F G s) (e : Sym2 V)
    (i : EdgeFiber K e) : ThirdDistribution p F G e.out.1 e.out.2 s :=
  ((K i.val.1).side i.val.2).oriented e i.property

theorem fiberDistribution_chain (K : KernelFamily p F G s) (e : Sym2 V)
    (i : EdgeFiber K e) :
    (fiberDistribution K e i).chain = ((K i.val.1).side i.val.2).distribution.chain :=
  ((K i.val.1).side i.val.2).oriented_chain e i.property

theorem fiber_distinct (K : KernelFamily p F G s) (e : Sym2 V) (i : EdgeFiber K e) :
    e.out.1 ≠ e.out.2 :=
  ((K i.val.1).side i.val.2).out_distinct e i.property

theorem side_sum (K : KernelFamily p F G s) (T : CompleteCopies p F)
    (f : Sym2 V → ℝ) :
    (∑ i : Fin 3, f (((K T).side i).edge p F G)) = ∑ e ∈ triEdges T.val, f e := by
  rw [← (K T).side_edges, sum_image]
  intro i _ j _ hij
  exact (K T).side_injective hij

omit [DecidableEq V] in
theorem complete_sum (f : Finset V → ℝ) :
    (∑ T : CompleteCopies p F, f T.val) = ∑ T ∈ copies p F (activeCompleteGraph p F), f T :=
  (sum_subtype _ (fun _ => Iff.rfl) _).symm

theorem fiber_sum (K : KernelFamily p F G s) (e : Sym2 V) (f : SideIndex p F → ℝ) :
    (∑ i : EdgeFiber K e, f i.val) =
      ∑ i : SideIndex p F, if occurrenceEdge K i = e then f i else 0 := by
  classical
  rw [← sum_filter]
  exact (sum_subtype _ (by simp) _).symm

theorem fiber_weight_sum (K : KernelFamily p F G s) (f : Finset V → ℝ) (e : Sym2 V) :
    (∑ i : EdgeFiber K e, f i.val.1.val) =
      ∑ T ∈ copies p F (activeCompleteGraph p F) with e ∈ triEdges T, f T := by
  classical
  rw [fiber_sum K e (fun i => f i.1.val), Fintype.sum_prod_type]
  have hi (T : CompleteCopies p F) :
      (∑ j : Fin 3, if occurrenceEdge K (T, j) = e then f T.val else 0) =
        if e ∈ triEdges T.val then f T.val else 0 := by
    change (∑ j : Fin 3, (fun d => if d = e then f T.val else 0)
      (((K T).side j).edge p F G)) = _
    rw [side_sum K T (fun d => if d = e then f T.val else 0)]
    simp
  simp_rw [hi]
  rw [complete_sum (fun T => if e ∈ triEdges T then f T else 0), sum_filter]

theorem fiber_balance (K : KernelFamily p F G s) (z : TriangleChain V)
    (hz : CopySupported p F (activeCompleteGraph p F) z) (e : Sym2 V) :
    (∑ i : EdgeFiber K e, z i.val.1.val) = boundary z e := by
  rw [fiber_weight_sum, boundary_eq_copy_load p F (activeCompleteGraph p F) z hz]

theorem fiber_mass (K : KernelFamily p F G s) (z : TriangleChain V) (e : Sym2 V) :
    (∑ i : EdgeFiber K e, |z i.val.1.val|) = edgeMass p F (activeCompleteGraph p F) z e :=
  fiber_weight_sum K (fun T => |z T|) e

theorem fiber_total (K : KernelFamily p F G s) (f : SideIndex p F → ℝ) :
    (∑ e : Sym2 V, ∑ i : EdgeFiber K e, f i.val) = ∑ i : SideIndex p F, f i :=
  Fintype.sum_fiberwise (occurrenceEdge K) f

noncomputable def transferredChain (K : KernelFamily p F G s) (z : TriangleChain V) :
    TriangleChain V := fun Q =>
  (∑ T : CompleteCopies p F, z T.val * (K T).base Q) +
  ∑ e : Sym2 V, SignedEdgeTransfer.repairedFamily
    (fun i : EdgeFiber K e => z i.val.1.val) (fiberDistribution K e) Q

theorem transferredChain_supported (K : KernelFamily p F G s) (z : TriangleChain V)
    (hz : CopySupported p F (activeCompleteGraph p F) z)
    (hzero : ∀ e, e ∉ G.edgeFinset → boundary z e = 0) :
    CopySupported p F G (transferredChain K z) := by
  classical
  unfold transferredChain
  apply CopySupported.add
  · apply CopySupported.sum univ
    intro T _
    exact (K T).base_supported.smul (z T.val)
  · apply CopySupported.sum univ
    intro e _
    apply SignedEdgeTransfer.repairedFamily_supported
    intro hab
    rw [fiber_balance K z hz]
    apply hzero
    intro he
    apply hab
    have he' : s(e.out.1, e.out.2) ∈ G.edgeFinset := by rw [mk_out_eq]; exact he
    exact G.mem_edgeFinset.mp he'

theorem transferredChain_boundary (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (K : KernelFamily p F G s) (z : TriangleChain V)
    (hz : CopySupported p F (activeCompleteGraph p F) z) (e : Sym2 V) :
    boundary (transferredChain K z) e = boundary z e := by
  classical
  have hlocal (d : Sym2 V) :
      boundary (SignedEdgeTransfer.repairedFamily
        (fun i : EdgeFiber K d => z i.val.1.val) (fiberDistribution K d)) e =
      ∑ i : EdgeFiber K d, z i.val.1.val *
        boundary ((K i.val.1).side i.val.2).distribution.chain e := by
    rw [SignedEdgeTransfer.repairedFamily_boundary hs0 hs _ _ (fiber_distinct K d)]
    apply sum_congr rfl
    intro i _
    rw [fiberDistribution_chain]
  unfold transferredChain
  simp only [boundary_add, boundary_sum, boundary_smul, hlocal]
  rw [fiber_total K (fun i => z i.1.val * boundary ((K i.1).side i.2).distribution.chain e),
    Fintype.sum_prod_type, ← sum_add_distrib]
  calc
    _ = ∑ T : CompleteCopies p F, z T.val * boundary (triangleBasis T.val) e := by
      apply sum_congr rfl
      intro T _
      rw [(K T).boundary_identity, mul_add, mul_sum]
    _ = boundary z e := by
      simp only [boundary_basis, mul_ite, mul_one, mul_zero]
      rw [complete_sum (fun T => if e ∈ triEdges T then z T else 0),
        boundary_eq_copy_load p F (activeCompleteGraph p F) z hz, sum_filter]

noncomputable def overlapMass (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (z : TriangleChain V) (Q : Finset V) : ℝ :=
  ∑ T ∈ copies p F (activeCompleteGraph p F), |z T| * ∑ v ∈ T, vertexIndicator Q v

theorem weighted_edgeMass (z : TriangleChain V) (g : Sym2 V → ℝ) :
    (∑ e : Sym2 V, edgeMass p F (activeCompleteGraph p F) z e * g e) =
      ∑ T ∈ copies p F (activeCompleteGraph p F), |z T| * ∑ e ∈ triEdges T, g e := by
  classical
  unfold edgeMass
  simp only [sum_filter, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  rw [mul_sum]
  simp only [sum_ite_mem, univ_inter]

theorem weighted_outFlag_mass (z : TriangleChain V) (Q : Finset V) :
    (∑ e : Sym2 V, edgeMass p F (activeCompleteGraph p F) z e * outFlag Q e) =
      2 * overlapMass p F z Q := by
  rw [weighted_edgeMass]
  unfold overlapMass
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [sum_outFlag_triangle (mem_copies_iff.mp hT).1.card_eq]
  ring

theorem overlapMass_eq_vertex (z : TriangleChain V) (Q : Finset V) :
    overlapMass p F z Q =
      ∑ v ∈ Q, ∑ T ∈ copies p F (activeCompleteGraph p F) with v ∈ T, |z T| := by
  classical
  have hswap (T : Finset V) :
      (∑ v ∈ T, vertexIndicator Q v) = ∑ v ∈ Q, if v ∈ T then (1 : ℝ) else 0 := by
    simp only [vertexIndicator, sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
    rw [inter_comm]
  unfold overlapMass
  simp_rw [hswap, mul_sum, mul_ite, mul_one, mul_zero]
  rw [sum_comm]
  simp only [sum_filter]

theorem overlapMass_bound (z : TriangleChain V) (U : ℝ)
    (hU : ∀ v, (∑ T ∈ copies p F (activeCompleteGraph p F) with v ∈ T, |z T|) ≤ U)
    (Q : Finset V) (hQ : Q.card = 3) : overlapMass p F z Q ≤ 3 * U := by
  rw [overlapMass_eq_vertex]
  calc
    _ ≤ ∑ _v ∈ Q, U := sum_le_sum fun v _ => hU v
    _ = _ := by simp only [sum_const, hQ, nsmul_eq_mul, Nat.cast_ofNat]

theorem base_sum_bound (K : KernelFamily p F G s) (z : TriangleChain V)
    (Q : Finset V) (hQ : Q.card = 3) :
    |∑ T : CompleteCopies p F, z T.val * (K T).base Q| ≤
      (∑ T ∈ copies p F (activeCompleteGraph p F), |z T|) * (3 / s) ^ 3 +
        overlapMass p F z Q * (3 / s) ^ 2 := by
  calc
    _ ≤ ∑ T : CompleteCopies p F, |z T.val| *
        ((3 / s) ^ 3 + (∑ v ∈ T.val, vertexIndicator Q v) * (3 / s) ^ 2) :=
      SignedEdgeTransfer.abs_sum_mul_bound univ _ _ _ (fun T _ => (K T).base_bound Q hQ)
    _ = _ := by
      rw [complete_sum (fun T => |z T| *
        ((3 / s) ^ 3 + (∑ v ∈ T, vertexIndicator Q v) * (3 / s) ^ 2))]
      simp only [overlapMass, mul_add, ← mul_assoc, sum_add_distrib, ← sum_mul]

theorem fiber_repair_bound (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (K : KernelFamily p F G s) (z : TriangleChain V)
    (hz : CopySupported p F (activeCompleteGraph p F) z)
    (e : Sym2 V) (Q : Finset V) (hQ : Q.card = 3) :
    |SignedEdgeTransfer.repairedFamily
      (fun i : EdgeFiber K e => z i.val.1.val) (fiberDistribution K e) Q| ≤
      |boundary z e| * (if e ∈ triEdges Q then (1 : ℝ) else 0) * (3 / s) +
        edgeMass p F (activeCompleteGraph p F) z e *
          (outFlag Q e * (3 / s) ^ 2 + (3 / s) ^ 3) := by
  have hh := SignedEdgeTransfer.repairedFamily_bound hs0 hs
    (fun i : EdgeFiber K e => z i.val.1.val) (fiberDistribution K e) (fiber_distinct K e) Q hQ
  rw [fiber_balance K z hz, fiber_mass K z, mk_out_eq] at hh
  exact hh

theorem residual_sum_bound (hs0 : 0 < s) (z : TriangleChain V) (ε : ℝ)
    (hε : ∀ e, |boundary z e| ≤ ε) (Q : Finset V) (hQ : Q.card = 3) :
    (∑ e : Sym2 V, |boundary z e| *
      (if e ∈ triEdges Q then (1 : ℝ) else 0) * (3 / s)) ≤ 3 * ε * (3 / s) := by
  classical
  have hsum : (∑ e ∈ triEdges Q, |boundary z e|) ≤ 3 * ε := by
    calc
      _ ≤ ∑ _e ∈ triEdges Q, ε := sum_le_sum fun e _ => hε e
      _ = _ := by simp only [sum_const, physical_triEdges_card hQ, nsmul_eq_mul, Nat.cast_ofNat]
  calc
    _ = (∑ e ∈ triEdges Q, |boundary z e|) * (3 / s) := by
      simp only [← sum_mul, mul_ite, mul_one, mul_zero, sum_ite_mem, univ_inter]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)

theorem paired_sum_identity (z : TriangleChain V) (Q : Finset V) :
    (∑ e : Sym2 V, edgeMass p F (activeCompleteGraph p F) z e *
      (outFlag Q e * (3 / s) ^ 2 + (3 / s) ^ 3)) =
    2 * overlapMass p F z Q * (3 / s) ^ 2 +
      3 * (∑ T ∈ copies p F (activeCompleteGraph p F), |z T|) * (3 / s) ^ 3 := by
  simp only [mul_add, ← mul_assoc, sum_add_distrib, ← sum_mul]
  rw [weighted_outFlag_mass, sum_edgeMass]

theorem repaired_sum_bound (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (K : KernelFamily p F G s) (z : TriangleChain V)
    (hz : CopySupported p F (activeCompleteGraph p F) z) (ε : ℝ)
    (hε : ∀ e, |boundary z e| ≤ ε) (Q : Finset V) (hQ : Q.card = 3) :
    |∑ e : Sym2 V, SignedEdgeTransfer.repairedFamily
      (fun i : EdgeFiber K e => z i.val.1.val) (fiberDistribution K e) Q| ≤
      3 * ε * (3 / s) + 2 * overlapMass p F z Q * (3 / s) ^ 2 +
        3 * (∑ T ∈ copies p F (activeCompleteGraph p F), |z T|) * (3 / s) ^ 3 := by
  calc
    _ ≤ ∑ e : Sym2 V, |SignedEdgeTransfer.repairedFamily
        (fun i : EdgeFiber K e => z i.val.1.val) (fiberDistribution K e) Q| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : Sym2 V, (|boundary z e| *
        (if e ∈ triEdges Q then (1 : ℝ) else 0) * (3 / s) +
        edgeMass p F (activeCompleteGraph p F) z e *
          (outFlag Q e * (3 / s) ^ 2 + (3 / s) ^ 3)) :=
      sum_le_sum fun e _ => fiber_repair_bound hs0 hs K z hz e Q hQ
    _ ≤ _ := by
      rw [sum_add_distrib, paired_sum_identity]
      have hh := residual_sum_bound hs0 z ε hε Q hQ
      linarith only [hh]

theorem transferredChain_bound (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (K : KernelFamily p F G s) (z : TriangleChain V)
    (hz : CopySupported p F (activeCompleteGraph p F) z) (ε S U : ℝ)
    (hε : ∀ e, |boundary z e| ≤ ε)
    (hS : (∑ T ∈ copies p F (activeCompleteGraph p F), |z T|) ≤ S)
    (hU : ∀ v, (∑ T ∈ copies p F (activeCompleteGraph p F) with v ∈ T, |z T|) ≤ U)
    (Q : Finset V) (hQ : Q.card = 3) :
    |transferredChain K z Q| ≤ 9 * ε / s + 81 * U / s ^ 2 + 108 * S / s ^ 3 := by
  have hbase := base_sum_bound K z Q hQ
  have hrepair := repaired_sum_bound hs0 hs K z hz ε hε Q hQ
  have hmass := mul_le_mul_of_nonneg_right hS (show 0 ≤ (3 / s) ^ 3 by positivity)
  have hoverlap := mul_le_mul_of_nonneg_right (overlapMass_bound z U hU Q hQ)
    (sq_nonneg (3 / s))
  unfold transferredChain
  calc
    _ ≤ |∑ T : CompleteCopies p F, z T.val * (K T).base Q| +
        |∑ e : Sym2 V, SignedEdgeTransfer.repairedFamily
          (fun i : EdgeFiber K e => z i.val.1.val) (fiberDistribution K e) Q| :=
      abs_add_le _ _
    _ ≤ 3 * ε * (3 / s) + 9 * U * (3 / s) ^ 2 + 4 * S * (3 / s) ^ 3 := by
      nlinarith only [hbase, hrepair, hmass, hoverlap]
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- A completely constructed signed transfer, with uniform edge, vertex, and
total mass budgets. No auxiliary choice or coupling hypothesis is required. -/
theorem exists_signed_transfer (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (s ε S U : ℝ) (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (z : TriangleChain V) (hz : CopySupported p F (activeCompleteGraph p F) z)
    (hzero : ∀ e, e ∉ G.edgeFinset → boundary z e = 0)
    (hε : ∀ e, |boundary z e| ≤ ε)
    (hS : (∑ T ∈ copies p F (activeCompleteGraph p F), |z T|) ≤ S)
    (hU : ∀ v, (∑ T ∈ copies p F (activeCompleteGraph p F) with v ∈ T, |z T|) ≤ U) :
    ∃ w : TriangleChain V, CopySupported p F G w ∧ boundary w = boundary z ∧
      ∀ Q : Finset V, Q.card = 3 →
        |w Q| ≤ 9 * ε / s + 81 * U / s ^ 2 + 108 * S / s ^ 3 := by
  classical
  let K : KernelFamily p F G s := fun T =>
    Classical.choice (exists_octKernel p F G s hs0 hs T.val (mem_copies_iff.mp T.property))
  refine ⟨transferredChain K z, transferredChain_supported K z hz hzero, ?_, ?_⟩
  · exact funext (transferredChain_boundary hs0 hs K z hz)
  · exact transferredChain_bound hs0 hs K z hz ε S U hε hS hU

#print axioms RootedSide.oriented_chain
#print axioms fiber_balance
#print axioms fiber_mass
#print axioms transferredChain_supported
#print axioms transferredChain_boundary
#print axioms weighted_outFlag_mass
#print axioms overlapMass_eq_vertex
#print axioms transferredChain_bound
#print axioms exists_signed_transfer

end SignedTransfer

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
