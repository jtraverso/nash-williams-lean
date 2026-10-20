/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1RootSupplyStage184
public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse

/-! # Selection budgets from the actual residual

The debt of a root is bounded by its residual degree. Handshake gives a total
request budget of twice the residual edge count. Only root supply remains as
a separate quantitative premise of the physical cone repair.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1RootDebtStage185

open Finset TypedApplicationLinks F1RootCountsStage182 F1PhysicalConeRepairStage183

variable {V : Type} [DecidableEq V]

theorem root_debt_le_degree (p : V → Fin 4) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, ¬ e.IsDiag) (v : V) :
    (-surplus p R v).toNat ≤ (R.filter fun e => v ∈ e).card := by
  have hn : ∀ j, 0 ≤ degVec p R v j := by
    intro j
    simp only [degVec, Finset.sum_apply]
    exact sum_nonneg fun e _ => TypedDivisibilityCollapse.degContrib_nonneg p v e j
  have hs := TypedDivisibilityCollapse.sum_degVec p R hR v
  have hown := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) => hn j)
    (mem_univ (p v))
  rw [hs] at hown
  have hcharge : -surplus p R v ≤ degVec p R v (p v) := by
    dsimp [surplus]
    linarith [hn (first1 (p v)), hn (second1 (p v))]
  change (-surplus p R v).toNat ≤ _
  dsimp [AntiEdgeSelection.incidentLoad] at hown
  omega

theorem total_root_debt [Fintype V] (p : V → Fin 4) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, ¬ e.IsDiag) :
    (∑ v : V, (-surplus p R v).toNat) ≤ 2 * R.card := by
  calc
    _ ≤ ∑ v : V, (R.filter fun e => v ∈ e).card :=
      sum_le_sum fun v _ => root_debt_le_degree p R hR v
    _ = _ := TypedCoverDown.sum_degrees_eq_two_mul_card R hR

theorem physical_cone_repair_from_residual [Finite V] (p : V → Fin 4)
    (E Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F1 Q D) (hQE : Q ⊆ E) (hI : IsIntDiv p F1 E)
    (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (hpos : ∃ a : Multiset (Fin 4) → ℕ,
      edgeVec p (E \ Q) = ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ)
    (d K : ℕ) (hd : 0 < d)
    (hdeg : ∀ v, ((E \ Q).filter fun e => v ∈ e).card ≤ K)
    (hsupply : ∀ v,
      d * (d + K) + 6 * (E \ Q).card < d * (singletonFamily p D v).card) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p F1 Q' D' ∧
      IsIntDiv p F1 (E \ Q') ∧
      (∃ a : Multiset (Fin 4) → ℕ,
        edgeVec p (E \ Q') = ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ) ∧
      (∀ v, 0 ≤ surplus p (E \ Q') v) ∧
      (∀ v, ((E \ Q').filter fun e => v ∈ e).card ≤
        ((E \ Q).filter fun e => v ∈ e).card + 2 * (d + K)) := by
  let := Fintype.ofFinite V
  have hR : ∀ e ∈ E \ Q, ¬ e.IsDiag := fun e he => hE e (mem_sdiff.mp he).1
  exact physical_cone_repair p E Q D hD hQE hI hpos d K (2 * (E \ Q).card) hd
    (fun v => (root_debt_le_degree p (E \ Q) hR v).trans (hdeg v))
    (total_root_debt p (E \ Q) hR) (by
      intro v
      convert hsupply v using 1
      ring)

end PartitionedTriangleAbsorption.F1RootDebtStage185

