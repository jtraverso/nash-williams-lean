/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1PhysicalConeRepairStage183

/-! # Root supply from host surplus and the actual residual degree

No triangle-family abundance is assumed here. The host surplus margin remains
explicit; deriving that margin from the near-unit fractional loads is separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1RootSupplyStage184

open Finset TypedApplicationLinks F1RootCountsStage182 F1PhysicalConeRepairStage183

variable {V : Type} [DecidableEq V]

theorem edge_charge_le (p : V → Fin 4) (v : V) (e : Sym2 V) (he : ¬ e.IsDiag) :
    degContrib p v e (first1 (p v)) + degContrib p v e (second1 (p v)) -
      degContrib p v e (p v) ≤ if v ∈ e then 1 else 0 := by
  have hlabel : ∀ r l : Fin 4,
      (if l = first1 r then (1 : ℤ) else 0) +
        (if l = second1 r then 1 else 0) - (if l = r then 1 else 0) ≤ 1 := by decide
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := hab.symm
      simpa [degContrib, hb] using hlabel (p v) (p b)
    · by_cases hb : b = v
      · subst b
        simpa [degContrib, ha] using hlabel (p v) (p a)
      · simp [degContrib, ha, hb, Ne.symm ha, Ne.symm hb]

theorem surplus_le_degree (p : V → Fin 4) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, ¬ e.IsDiag) (v : V) :
    surplus p R v ≤ ((R.filter fun e => v ∈ e).card : ℤ) := by
  simp only [surplus, degVec, Finset.sum_apply]
  rw [← sum_add_distrib, ← sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ R, if v ∈ e then (1 : ℤ) else 0 :=
      sum_le_sum fun e he => edge_charge_le p v e (hR e he)
    _ = _ := by simp

theorem singleton_supply_from_margin (p : V → Fin 4) (E Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F1 Q D) (hQ : Q ⊆ E)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (v : V) (σ ξ n : ℝ)
    (hmargin : σ * n ≤ (surplus p E v : ℝ))
    (hres : ((E \ Q).filter fun e => v ∈ e).card ≤ ξ * n) :
    (σ - ξ) * n / 2 ≤ ((singletonFamily p D v).card : ℝ) := by
  have hpart := surplus_partition p E Q hQ v
  have hcounts := (packing_root_counts p Q D hD v).1
  have hr := surplus_le_degree p (E \ Q) (fun e he => hE e (mem_sdiff.mp he).1) v
  have hpart' : (surplus p E v : ℝ) = (surplus p Q v : ℝ) + surplus p (E \ Q) v :=
    by exact_mod_cast hpart
  have hcounts' : (surplus p Q v : ℝ) = 2 * (singletonFamily p D v).card :=
    by exact_mod_cast hcounts
  have hr' : (surplus p (E \ Q) v : ℝ) ≤ ((E \ Q).filter fun e => v ∈ e).card :=
    by exact_mod_cast hr
  nlinarith

end PartitionedTriangleAbsorption.F1RootSupplyStage184

