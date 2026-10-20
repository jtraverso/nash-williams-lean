/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1PositiveStage166
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # Physical F1 quota repair through the one-dimensional kernel

This constructs a subpacking, not a new packing producer. The loss bound is
global cardinality only: no vertex-degree or confinement claim is made.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1ResidualQuotasStage169

open Finset TypedApplicationLinks F1PositiveStage166

variable {V : Type} [DecidableEq V]

theorem residual_representation {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (hQE : Q ⊆ E)
    (c : Multiset (Fin t) → ℤ)
    (hc : edgeVec p E = ∑ tau ∈ F, c tau • typeEdgeVec tau) :
    edgeVec p (E \ Q) = ∑ tau ∈ F,
      (c tau - ((D.filter fun s => triType p s = tau).card : ℤ)) • typeEdgeVec tau := by
  have h := edgeVec_union p (disjoint_sdiff : Disjoint Q (E \ Q))
  rw [union_sdiff_of_subset hQE, hc, hD.edgeVec_eq] at h
  rw [eq_sub_of_add_eq' h.symm, ← sum_sub_distrib]
  exact sum_congr rfl fun tau _ => by rw [sub_smul]

omit [DecidableEq V] in
theorem edge_coordinate_bounds {t : ℕ} (p : V → Fin t)
    (P : Finset (Sym2 V)) (i j : Fin t) :
    0 ≤ edgeVec p P i j ∧ edgeVec p P i j ≤ 2 * (P.card : ℤ) := by
  have he (e : Sym2 V) : 0 ≤ pairVec p e i j ∧ pairVec p e i j ≤ 2 := by
    induction e using Sym2.ind with
    | _ u v =>
      simp only [pairVec, Sym2.lift_mk]
      split_ifs <;> norm_num
  constructor
  · simp only [edgeVec, Finset.sum_apply]
    exact sum_nonneg fun e _ => (he e).1
  · simp only [edgeVec, Finset.sum_apply]
    calc
      _ ≤ ∑ _e ∈ P, (2 : ℤ) := sum_le_sum fun e _ => (he e).2
      _ = 2 * (P.card : ℤ) := by simp only [sum_const, nsmul_eq_mul]; ring

omit [DecidableEq V] in
/-- Fixing the first coefficient kills the kernel and bounds every coordinate
by the size of the physical residual, even when its cone is not feasible. -/
theorem zero_first_coefficients_bounded (p : V → Fin 4) (P : Finset (Sym2 V))
    (r : Multiset (Fin 4) → ℤ)
    (hr : edgeVec p P = ∑ tau ∈ F1, r tau • typeEdgeVec tau)
    (hzero : r {0, 0, 2} = 0) :
    ∀ tau ∈ F1, -4 * (P.card : ℤ) ≤ r tau ∧ r tau ≤ 4 * (P.card : ℤ) := by
  have h00 := congrFun (congrFun hr 0) 0
  have h11 := congrFun (congrFun hr 1) 1
  have h22 := congrFun (congrFun hr 2) 2
  have h33 := congrFun (congrFun hr 3) 3
  have h02 := congrFun (congrFun hr 0) 2
  have h03 := congrFun (congrFun hr 0) 3
  have h12 := congrFun (congrFun hr 1) 2
  simp only [F1] at h00 h11 h22 h33 h02 h03 h12
  repeat rw [sum_insert (by decide)] at h00 h11 h22 h33 h02 h03 h12
  simp [typeEdgeVec, sum_singleton]
    at h00 h11 h22 h33 h02 h03 h12
  have b00 := edge_coordinate_bounds p P 0 0
  have b11 := edge_coordinate_bounds p P 1 1
  have b22 := edge_coordinate_bounds p P 2 2
  have b33 := edge_coordinate_bounds p P 3 3
  have b02 := edge_coordinate_bounds p P 0 2
  have b03 := edge_coordinate_bounds p P 0 3
  have b12 := edge_coordinate_bounds p P 1 2
  intro tau htau
  simp only [F1, mem_insert, mem_singleton] at htau
  rcases htau with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Multiset.insert_eq_cons] at *; omega

/-- Clipping a feasible kernel shift preserves nonnegativity and bounds the
distance from the packing counts. This is an integer calculation, not LP rounding. -/
theorem clipped_shift (n r z s L : ℤ) (hn : 0 ≤ n) (hL : 0 ≤ L)
    (hr : -L ≤ r ∧ r ≤ L) (hs : s = 1 ∨ s = -1)
    (hfeasible : 0 ≤ n + r + z * s) :
    0 ≤ n + r + max (-L) (min L z) * s ∧
      n - (n + r + max (-L) (min L z) * s) ≤ 2 * L := by
  rcases hs with rfl | rfl
  all_goals simp only [mul_one, mul_neg] at *; omega

/-- Re-choose the feasible original coefficients along the kernel. At most
eight missing-edge units of capacity per type are lost. -/
theorem coefficients_near_packing (p : V → Fin 4) (E Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hI : IsIntDiv p F1 E) (hR : IsFracDiv p F1 E)
    (hD : IsDecomp p F1 Q D) (hQE : Q ⊆ E) :
    ∃ c : Multiset (Fin 4) → ℕ,
      (edgeVec p E = ∑ tau ∈ F1, (c tau : ℤ) • typeEdgeVec tau) ∧
      ∀ tau ∈ F1, (D.filter fun s => triType p s = tau).card - c tau ≤
        8 * (E \ Q).card := by
  obtain ⟨c0, hc0⟩ := F1_coefficients_of_divisibility p E hI hR
  let count (tau : Multiset (Fin 4)) : ℕ := (D.filter fun s => triType p s = tau).card
  let z : ℤ := (c0 {0, 0, 2} : ℤ) - count {0, 0, 2}
  let r (tau : Multiset (Fin 4)) : ℤ := (c0 tau : ℤ) - count tau - z * kernelSign tau
  let L : ℤ := 4 * (E \ Q).card
  let shift : ℤ := max (-L) (min L z)
  have hr : edgeVec p (E \ Q) = ∑ tau ∈ F1, r tau • typeEdgeVec tau := by
    rw [residual_representation p F1 E Q D hD hQE (fun tau => (c0 tau : ℤ)) hc0]
    simp only [r, count, sub_smul, mul_smul]
    simp only [sum_sub_distrib, ← smul_sum, F1_kernel_zero, smul_zero, sub_zero]
  have hzero : r {0, 0, 2} = 0 := by
    have hs : kernelSign {0, 0, 2} = 1 := by decide
    simp only [r, z, hs, mul_one, sub_self]
  have hb := zero_first_coefficients_bounded p (E \ Q) r hr hzero
  have hsign (tau : Multiset (Fin 4)) : kernelSign tau = 1 ∨ kernelSign tau = -1 := by
    unfold kernelSign
    split_ifs <;> simp
  have hn (tau : Multiset (Fin 4)) (htau : tau ∈ F1) :
      0 ≤ (count tau : ℤ) + r tau + shift * kernelSign tau ∧
        (count tau : ℤ) - ((count tau : ℤ) + r tau + shift * kernelSign tau) ≤ 2 * L := by
    apply clipped_shift (count tau) (r tau) z (kernelSign tau) L
      (Int.natCast_nonneg _) (by dsimp [L]; positivity) (hb tau htau) (hsign tau)
    dsimp [r]
    have hc : 0 ≤ (c0 tau : ℤ) := Int.natCast_nonneg _
    linarith
  let c (tau : Multiset (Fin 4)) : ℕ :=
    ((count tau : ℤ) + r tau + shift * kernelSign tau).toNat
  have hcast (tau : Multiset (Fin 4)) (htau : tau ∈ F1) :
      (c tau : ℤ) = (c0 tau : ℤ) + (shift - z) * kernelSign tau := by
    dsimp [c]
    rw [Int.toNat_of_nonneg (hn tau htau).1]
    dsimp [r]
    ring
  refine ⟨c, ?_, ?_⟩
  · rw [hc0]
    have hsum : (∑ tau ∈ F1, (c tau : ℤ) • typeEdgeVec tau) =
        ∑ tau ∈ F1, ((c0 tau : ℤ) + (shift - z) * kernelSign tau) • typeEdgeVec tau :=
      sum_congr rfl fun tau htau => by rw [hcast tau htau]
    rw [hsum]
    simp only [add_smul, mul_smul]
    rw [sum_add_distrib, ← smul_sum, F1_kernel_zero, smul_zero, add_zero]
  · intro tau htau
    have hh := (hn tau htau).2
    have hcn : (c tau : ℤ) = (count tau : ℤ) + r tau + shift * kernelSign tau := by
      dsimp [c]
      rw [Int.toNat_of_nonneg (hn tau htau).1]
    dsimp [L, count] at hh hcn
    omega

/-- Select actual triangles of each type up to its capacity. -/
theorem trim_type_caps {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (c : Multiset (Fin t) → ℕ) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F Q' D' ∧
      (∀ tau ∈ F, (D'.filter fun s => triType p s = tau).card ≤ c tau) ∧
      D'.card + (∑ tau ∈ F, ((D.filter fun s => triType p s = tau).card - c tau)) = D.card := by
  classical
  have hs : ∀ tau : Multiset (Fin t), ∃ S ⊆ D.filter (fun s => triType p s = tau),
      S.card = min (c tau) (D.filter fun s => triType p s = tau).card := fun tau =>
    exists_subset_card_eq (Nat.min_le_right _ _)
  choose S hS hSc using hs
  let D' := F.biUnion S
  have hsub : D' ⊆ D := by
    intro s hs
    obtain ⟨tau, _, hs⟩ := mem_biUnion.mp hs
    exact (mem_filter.mp (hS tau hs)).1
  have hfilt (tau : Multiset (Fin t)) (htau : tau ∈ F) :
      D'.filter (fun s => triType p s = tau) = S tau := by
    ext s
    constructor
    · intro hs
      obtain ⟨hs, heq⟩ := mem_filter.mp hs
      obtain ⟨sigma, _, hs⟩ := mem_biUnion.mp hs
      have heq' := (mem_filter.mp (hS sigma hs)).2
      have hsame : sigma = tau := heq'.symm.trans heq
      simpa only [hsame] using hs
    · intro hs
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨tau, htau, hs⟩,
        (mem_filter.mp (hS tau hs)).2⟩
  have hcap (tau : Multiset (Fin t)) (htau : tau ∈ F) :
      (D'.filter fun s => triType p s = tau).card ≤ c tau := by
    rw [hfilt tau htau, hSc tau]
    exact Nat.min_le_left _ _
  have hcard : D'.card = ∑ tau ∈ F,
      min (c tau) (D.filter fun s => triType p s = tau).card := by
    rw [card_eq_sum_card_fiberwise (f := triType p) (t := F)
      (fun s hs => (hD.1 s (hsub hs)).2)]
    exact sum_congr rfl fun tau htau => by rw [hfilt tau htau, hSc tau]
  refine ⟨D', D'.biUnion triEdges, hsub, ?_,
    ⟨fun s hs => hD.1 s (hsub hs), hD.2.1.subset hsub, rfl⟩, hcap, ?_⟩
  · rw [← hD.2.2]
    exact biUnion_subset_biUnion_of_subset_left triEdges hsub
  · rw [hcard, ← sum_add_distrib,
      card_eq_sum_card_fiberwise (f := triType p) (t := F)
        (fun s hs => (hD.1 s hs).2)]
    apply sum_congr rfl
    intro tau _
    omega

theorem residual_card_after_subpacking {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q Q' : Finset (Sym2 V))
    (D D' : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (hD' : IsDecomp p F Q' D') (hsub : D' ⊆ D) :
    (E \ Q').card ≤ (E \ Q).card + 3 * (D.card - D'.card) := by
  have hcover : Q ⊆ Q' ∪ (D \ D').biUnion triEdges := by
    rw [← hD'.2.2, ← union_biUnion, union_sdiff_of_subset hsub, hD.2.2]
  have hedge : E \ Q' ⊆ (E \ Q) ∪ (D \ D').biUnion triEdges := by
    intro e he
    obtain ⟨heE, heQ'⟩ := mem_sdiff.mp he
    by_cases heQ : e ∈ Q
    · rcases mem_union.mp (hcover heQ) with he | he
      · exact (heQ' he).elim
      · exact mem_union_right _ he
    · exact mem_union_left _ (mem_sdiff.mpr ⟨heE, heQ⟩)
  have hsize : ((D \ D').biUnion triEdges).card ≤ 3 * (D \ D').card := by
    calc
      _ ≤ ∑ s ∈ D \ D', (triEdges s).card := card_biUnion_le
      _ ≤ ∑ _s ∈ D \ D', 3 := sum_le_sum fun s hs => by
        obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ :=
          card_eq_three.mp (hD.1 s (mem_sdiff.mp hs).1).1
        rw [triEdges_three huv huw hvw]
        exact card_le_three
      _ = 3 * (D \ D').card := by
        norm_num [sum_const, nsmul_eq_mul, mul_comm]
  exact (card_le_card hedge).trans ((card_union_le _ _).trans (by
    rw [card_sdiff_of_subset hsub] at hsize
    omega))

/-- A physical quota repair with a global loss proportional to uncovered edges.
No residual cone is received as a premise. -/
theorem repair_F1_packing (p : V → Fin 4) (E Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hI : IsIntDiv p F1 E) (hR : IsFracDiv p F1 E)
    (hD : IsDecomp p F1 Q D) (hQE : Q ⊆ E) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F1 Q' D' ∧
      IsIntDiv p F1 (E \ Q') ∧
      (∃ b : Multiset (Fin 4) → ℕ,
        edgeVec p (E \ Q') = ∑ tau ∈ F1, (b tau : ℤ) • typeEdgeVec tau) ∧
      D.card - D'.card ≤ 64 * (E \ Q).card ∧
      (E \ Q').card ≤ 193 * (E \ Q).card := by
  obtain ⟨c, hc, hbound⟩ := coefficients_near_packing p E Q D hI hR hD hQE
  obtain ⟨D', Q', hsub, hQsub, hD', hcap, hloss⟩ := trim_type_caps p F1 Q D hD c
  have hQ'E := hQsub.trans hQE
  have hexcess : (∑ tau ∈ F1, ((D.filter fun s => triType p s = tau).card - c tau)) ≤
      64 * (E \ Q).card := by
    calc
      _ ≤ ∑ _tau ∈ F1, 8 * (E \ Q).card := sum_le_sum hbound
      _ = 64 * (E \ Q).card := by
        rw [sum_const, nsmul_eq_mul]
        have hF : F1.card = 8 := by decide
        rw [hF]
        omega
  have hsize := residual_card_after_subpacking p F1 E Q Q' D D' hD hD' hsub
  refine ⟨D', Q', hsub, hQsub, hD',
    isIntDiv_sdiff_of_hasDecomp hI ⟨D', hD'⟩ hQ'E, ?_, by omega, by omega⟩
  refine ⟨fun tau => (c tau - (D'.filter fun s => triType p s = tau).card), ?_⟩
  rw [residual_representation p F1 E Q' D' hD' hQ'E (fun tau => (c tau : ℤ)) hc]
  apply sum_congr rfl
  intro tau htau
  rw [Nat.cast_sub (hcap tau htau)]

end PartitionedTriangleAbsorption.F1ResidualQuotasStage169

end

