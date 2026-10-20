/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedNibbleAdapter
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-!
# The balance gate for damage-robust F1 loads

Every physical F1 triangle has two cross edges and one internal edge in
the coarsening {0,1}|{2,3}. Thus near-unit loads require near-zero signed
edge balance. This necessary condition is independent of the weights' cap.
It is not a construction of a robust weighting or an absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1BalanceGateStage228

open Finset TypedApplicationLinks TypedNibble

def pairCharge (i j : Fin 4) : ℤ :=
  if (i.val < 2 ↔ j.val < 2) then -2 else 1

theorem pairCharge_symm (i j : Fin 4) : pairCharge i j = pairCharge j i := by
  simp [pairCharge, iff_comm]

theorem allowed_triangle_charge : ∀ i j k : Fin 4,
    ({i, j, k} : Multiset (Fin 4)) ∈ F1 →
      pairCharge i j + pairCharge i k + pairCharge j k = 0 := by decide

variable {V : Type*} [DecidableEq V]

def charge (p : V → Fin 4) (e : Sym2 V) : ℝ :=
  (Sym2.lift ⟨fun x y => pairCharge (p x) (p y),
    fun x y => pairCharge_symm (p x) (p y)⟩ e : ℤ)

noncomputable def balance (p : V → Fin 4) (E : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ E, charge p e

theorem physical_triangle_balance (p : V → Fin 4) (s : Finset V)
    (hs : IsTypedTri p F1 s) : balance p (triEdges s) = 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hs.1
  have htype : ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1 := by
    simpa only [map_three p hxy hxz hyz] using hs.2
  unfold balance
  rw [sum_triEdges_three _ hxy hxz hyz]
  simp only [charge, Sym2.lift_mk]
  exact_mod_cast allowed_triangle_charge (p x) (p y) (p z) htype

noncomputable def load (D : Finset (Finset V)) (w : Finset V → ℝ)
    (e : Sym2 V) : ℝ := ∑ s ∈ D with e ∈ triEdges s, w s

theorem weighted_balance_zero (p : V → Fin 4) (E : Finset (Sym2 V))
    (D : Finset (Finset V)) (w : Finset V → ℝ)
    (hsub : ∀ s ∈ D, triEdges s ⊆ E)
    (htype : ∀ s ∈ D, IsTypedTri p F1 s) :
    ∑ e ∈ E, charge p e * load D w e = 0 := by
  unfold load
  simp_rw [sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  have hcolumn : ∀ s ∈ D,
      (∑ e ∈ E, if e ∈ triEdges s then charge p e * w s else 0) = 0 := by
    intro s hs
    rw [← sum_filter]
    have he : E.filter (fun e => e ∈ triEdges s) = triEdges s :=
      filter_mem_eq_inter.trans (inter_eq_right.mpr (hsub s hs))
    rw [he, ← sum_mul]
    change balance p (triEdges s) * w s = 0
    rw [physical_triangle_balance p s (htype s hs), zero_mul]
  exact (sum_congr rfl hcolumn).trans (by simp)

theorem near_load_requires_balance (p : V → Fin 4) (E : Finset (Sym2 V))
    (D : Finset (Finset V)) (w : Finset V → ℝ) (τ : ℝ)
    (hsub : ∀ s ∈ D, triEdges s ⊆ E)
    (htype : ∀ s ∈ D, IsTypedTri p F1 s)
    (hload : ∀ e ∈ E, |load D w e - 1| ≤ τ) :
    |balance p E| ≤ τ * ∑ e ∈ E, |charge p e| := by
  have hzero := weighted_balance_zero p E D w hsub htype
  have hid : (∑ e ∈ E, charge p e * (load D w e - 1)) = -balance p E := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib, hzero]
    simp [balance]
  calc
    |balance p E| = |∑ e ∈ E, charge p e * (load D w e - 1)| := by
      rw [hid, abs_neg]
    _ ≤ ∑ e ∈ E, |charge p e * (load D w e - 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ E, |charge p e| * τ := by
      apply sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hload e he) (abs_nonneg _)
    _ = τ * ∑ e ∈ E, |charge p e| := by rw [← sum_mul, mul_comm]

theorem graph_near_load_requires_balance [Fintype V] (p : V → Fin 4)
    (H : SimpleGraph V) [DecidableRel H.Adj] (w : Finset V → ℝ) (τ : ℝ)
    (hload : ∀ e ∈ H.edgeFinset,
      |load (copies p F1 H) w e - 1| ≤ τ) :
    |balance p H.edgeFinset| ≤ τ * ∑ e ∈ H.edgeFinset, |charge p e| := by
  apply near_load_requires_balance p H.edgeFinset (copies p F1 H) w τ
  · intro s hs
    exact triEdges_subset_of_isCopy (mem_copies_iff.mp hs)
  · intro s hs
    exact isTypedTri_of_isCopy (mem_copies_iff.mp hs)
  · exact hload

theorem decomposition_balance_zero (p : V → Fin 4) (E : Finset (Sym2 V))
    (hE : HasDecomp p F1 E) : balance p E = 0 := by
  obtain ⟨D, hD⟩ := hE
  obtain ⟨htype, hdisjoint, hUnion⟩ := hD
  unfold balance
  rw [← hUnion, sum_biUnion hdisjoint]
  have hs : ∀ s ∈ D, (∑ e ∈ triEdges s, charge p e) = 0 :=
    fun s hs => physical_triangle_balance p s (htype s hs)
  exact (sum_congr rfl hs).trans (by simp)

theorem arbitrary_accuracy_requires_balance (p : V → Fin 4) (E : Finset (Sym2 V))
    (D : Finset (Finset V))
    (hsub : ∀ s ∈ D, triEdges s ⊆ E)
    (htype : ∀ s ∈ D, IsTypedTri p F1 s)
    (hweights : ∀ τ : ℝ, 0 < τ → ∃ w : Finset V → ℝ,
      ∀ e ∈ E, |load D w e - 1| ≤ τ) : balance p E = 0 := by
  by_contra hne
  have hpos : 0 < |balance p E| := abs_pos.mpr hne
  let M : ℝ := ∑ e ∈ E, |charge p e|
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => abs_nonneg _)
  let τ : ℝ := |balance p E| / (2 * (M + 1))
  have ht : 0 < τ := div_pos hpos (by positivity)
  obtain ⟨w, hw⟩ := hweights τ ht
  have hh := near_load_requires_balance p E D w τ hsub htype hw
  change |balance p E| ≤ τ * M at hh
  have he : τ * (2 * (M + 1)) = |balance p E| := by
    dsimp [τ]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

theorem balance_sdiff (p : V → Fin 4) (E R : Finset (Sym2 V)) (hR : R ⊆ E) :
    balance p (E \ R) = balance p E - balance p R := by
  unfold balance
  exact sum_sdiff_eq_sub hR

theorem balanced_puncture_reserve_ledger (p : V → Fin 4)
    (E I R : Finset (Sym2 V)) (hI : I ⊆ E) (hR : R ⊆ E \ I)
    (hE : balance p E = 0) :
    balance p ((E \ I) \ R) = -balance p I - balance p R := by
  rw [balance_sdiff p (E \ I) R hR, balance_sdiff p E I hI, hE]
  ring

theorem deleted_cross_edges_tolerance (t k τ : ℝ) (ht : 0 < t)
    (hcount : |4 * t - k * t| ≤ τ * (8 * t ^ 2 - 4 * t - k * t)) :
    |4 - k| ≤ τ * (8 * t - 4 - k) := by
  have he : 4 * t - k * t = (4 - k) * t := by ring
  rw [he, abs_mul, abs_of_pos ht] at hcount
  have he' : 8 * t ^ 2 - 4 * t - k * t = (8 * t - 4 - k) * t := by ring
  rw [he', ← mul_assoc] at hcount
  exact (mul_le_mul_iff_of_pos_right ht).mp hcount

end PartitionedTriangleAbsorption.F1BalanceGateStage228
