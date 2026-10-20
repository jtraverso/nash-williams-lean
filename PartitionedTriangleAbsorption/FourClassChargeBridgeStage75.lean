/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
public import PartitionedTriangleAbsorption.TypedRefinerCharge

/-! # Charge balance as the physical inverse's coordinate condition

Class labels fix the orientation of an unordered edge. The finite bijection
below therefore counts each cross-class edge once, even for empty classes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassChargeBridgeStage75

open Finset TypedLoadNecessity FourClassCopyAdapterStage74 FourClassInverseStage73

variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem pairVec_mk (p : V → Fin 4) (u v : V) (i j : Fin 4) :
    pairVec p s(u,v) i j =
      (if p u = i ∧ p v = j then 1 else 0) +
      (if p v = i ∧ p u = j then 1 else 0) := rfl

theorem pair_total (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (d : Sym2 V → ℝ)
    {i j : Fin 4} (hij : i ≠ j) :
    (∑ e ∈ G.edgeFinset, (pairVec p e i j : ℝ) * d e) =
      ∑ a : Class p i, ∑ b : Class p j, d s(a.val,b.val) := by
  classical
  have hval (e : Sym2 V) : pairVec p e i j = 0 ∨ pairVec p e i j = 1 := by
    induction e using Sym2.ind with
    | _ u v =>
      rw [pairVec_mk]
      split_ifs with h h'
      · exact False.elim (hij (h.1.symm.trans h'.2))
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
  have hs : (∑ e ∈ G.edgeFinset, (pairVec p e i j : ℝ) * d e) =
      ∑ e ∈ G.edgeFinset.filter (fun e => pairVec p e i j = 1), d e := by
    rw [sum_filter]
    apply sum_congr rfl
    intro e _
    rcases hval e with h | h
    · simp [h]
    · simp [h]
  rw [hs, ← Fintype.sum_prod_type
    (fun ab : Class p i × Class p j => d s(ab.1.val,ab.2.val))]
  symm
  apply sum_bij (fun ab _ => s(ab.1.val,ab.2.val))
  · intro ab _
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr
        ((hG _ _).mpr (by simpa only [class_label] using hij)))
    · simp [pairVec_mk, class_label, hij, hij.symm]
  · intro ab _ cd _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · exact False.elim (class_ne hij ab.1 cd.2 h.1)
  · intro e he
    obtain ⟨_, h⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ u v =>
      rw [pairVec_mk] at h
      by_cases h1 : p u = i ∧ p v = j
      · exact ⟨(⟨u,h1.1⟩,⟨v,h1.2⟩), mem_univ _, rfl⟩
      · have h2 : p v = i ∧ p u = j := by
          by_contra h2
          simp [h1, h2] at h
        exact ⟨(⟨v,h2.1⟩,⟨u,h2.2⟩), mem_univ _, Sym2.eq_swap⟩
  · intro ab _
    rfl

omit [Fintype V] in
theorem pairFun_mk (p : V → Fin 4) (l : Fin 4 → Fin 4 → ℤ) (u v : V) :
    pairFun l (pairVec p s(u,v)) = l (p u) (p v) + l (p v) (p u) := by
  simp [pairFun, pairVec, mul_add, sum_add_distrib, ite_and]

omit [Fintype V] in
theorem chi3a_pair (p : V → Fin 4) (e : Sym2 V) :
    pairFun TypedRefinerCharge.chi3a (pairVec p e) =
      2 * (pairVec p e 0 1 + pairVec p e 2 3 -
        pairVec p e 0 2 - pairVec p e 1 3) := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [pairFun_mk]
    simp only [pairVec_mk]
    generalize p u = i
    generalize p v = j
    fin_cases i <;> fin_cases j <;> decide

omit [Fintype V] in
theorem chi3b_pair (p : V → Fin 4) (e : Sym2 V) :
    pairFun TypedRefinerCharge.chi3b (pairVec p e) =
      2 * (pairVec p e 0 1 + pairVec p e 2 3 -
        pairVec p e 0 3 - pairVec p e 1 2) := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [pairFun_mk]
    simp only [pairVec_mk]
    generalize p u = i
    generalize p v = j
    fin_cases i <;> fin_cases j <;> decide

theorem rawBalanced_of_charges (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (d : Sym2 V → ℝ)
    (ha : ∑ e ∈ G.edgeFinset,
      (pairFun TypedRefinerCharge.chi3a (pairVec p e) : ℝ) * d e = 0)
    (hb : ∑ e ∈ G.edgeFinset,
      (pairFun TypedRefinerCharge.chi3b (pairVec p e) : ℝ) * d e = 0) :
    RawBalanced (demandCoordinates p d) := by
  simp only [chi3a_pair, Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat,
    mul_assoc, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, ← mul_sum] at ha
  simp only [chi3b_pair, Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat,
    mul_assoc, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, ← mul_sum] at hb
  rw [pair_total p G hG d (by decide : (0 : Fin 4) ≠ 1),
    pair_total p G hG d (by decide : (2 : Fin 4) ≠ 3),
    pair_total p G hG d (by decide : (0 : Fin 4) ≠ 2),
    pair_total p G hG d (by decide : (1 : Fin 4) ≠ 3)] at ha
  rw [pair_total p G hG d (by decide : (0 : Fin 4) ≠ 1),
    pair_total p G hG d (by decide : (2 : Fin 4) ≠ 3),
    pair_total p G hG d (by decide : (0 : Fin 4) ≠ 3),
    pair_total p G hG d (by decide : (1 : Fin 4) ≠ 2)] at hb
  constructor <;> dsimp [RawBalanced, demandCoordinates] <;> linarith

theorem rawBalanced_of_supported_charges (p : V → Fin 4) (G J : SimpleGraph V)
    [DecidableRel J.Adj]
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (hJG : J ≤ G)
    (d : Sym2 V → ℝ) (hz : ∀ e ∉ J.edgeFinset, d e = 0)
    (ha : ∑ e ∈ J.edgeFinset,
      (pairFun TypedRefinerCharge.chi3a (pairVec p e) : ℝ) * d e = 0)
    (hb : ∑ e ∈ J.edgeFinset,
      (pairFun TypedRefinerCharge.chi3b (pairVec p e) : ℝ) * d e = 0) :
    RawBalanced (demandCoordinates p d) := by
  classical
  apply rawBalanced_of_charges p G hG d
  all_goals
    rw [← sum_subset (SimpleGraph.edgeFinset_mono hJG)
      (fun e _ he => by rw [hz e he, mul_zero])]
    assumption

end PartitionedTriangleAbsorption.FourClassChargeBridgeStage75
