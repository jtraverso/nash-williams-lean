/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SmallTrimStage118

/-! # Reserve-aware balance for the actual nibble host

`R` is a protected reserve, not the supply used to pre-cover `Y`. The latter
uses `S`, disjoint from `R ∪ J`. Balancing just the surviving child `J \ Y`
does not balance the nibble host unless `R` is already balanced.

The producer below trims inside `J`, keeping `R` untouched. Its capacity and
category-discrepancy premises remain explicit; it is not a vortex theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveAwareRecutStage120

open Finset TypedApplicationLinks CoverDownStage105 AntiEdgeSelection F3ReserveTrimStage109
  ReserveTrimStage109 SeedDrivenTrimStage114

variable {V : Type*} [DecidableEq V]

theorem bal_union (p : V → Fin 4) (k : Fin 2) {A B : Finset (Sym2 V)}
    (h : Disjoint A B) : bal p k (A ∪ B) = bal p k A + bal p k B :=
  sum_union h

theorem bal_sdiff (p : V → Fin 4) (k : Fin 2) {A B : Finset (Sym2 V)}
    (h : B ⊆ A) : bal p k (A \ B) = bal p k A - bal p k B := by
  have hh := sum_sdiff (f := balEdge p k) h
  unfold bal
  omega

theorem bal_zero_of_hasDecomp (p : V → Fin 4) (k : Fin 2)
    {A : Finset (Sym2 V)} (h : HasDecomp p F3 A) : bal p k A = 0 := by
  obtain ⟨D, hT, hdisj, rfl⟩ := h
  rw [bal, sum_biUnion hdisj]
  exact sum_eq_zero fun s hs => bal_triEdges p k (hT s hs)

/-- Exact bookkeeping after pre-covering a child recut and withholding both
the protected reserve and the surviving child. -/
theorem actual_host_balance (p : V → Fin 4) (k : Fin 2)
    (E R J Y S : Finset (Sym2 V))
    (hRJ : Disjoint R J) (hY : Y ⊆ J) (hS : Disjoint S (R ∪ J))
    (hsub : S ∪ (R ∪ J) ⊆ E) (hE : bal p k E = 0)
    (hdec : HasDecomp p F3 (Y ∪ S)) :
    bal p k (E \ ((Y ∪ S) ∪ (R ∪ (J \ Y)))) =
      -bal p k ((R ∪ J) \ Y) := by
  have heq : (Y ∪ S) ∪ (R ∪ (J \ Y)) = S ∪ (R ∪ J) := by
    ext e
    simp only [mem_union, mem_sdiff]
    have := @hY e
    tauto
  have hYS : Disjoint Y S :=
    (hS.mono_right (hY.trans subset_union_right)).symm
  have hzero := bal_zero_of_hasDecomp p k hdec
  rw [bal_union p k hYS] at hzero
  rw [heq, bal_sdiff p k hsub, bal_union p k hS,
    bal_sdiff p k (hY.trans subset_union_right), bal_union p k hRJ, hE]
  omega

/-- Construct a bounded recut in the child for the correct combined target.
Any subsequent disjoint physical pre-cover then leaves a balanced nibble host.
No exact fractional seed or positivity is claimed here. -/
theorem exists_reserve_aware_recut [Finite V] (p : V → Fin 4)
    (E R J : Finset (Sym2 V)) (m D P : ℕ)
    (hRJ : Disjoint R J)
    (hcross : ∀ x y, s(x, y) ∈ R ∪ J → p x ≠ p y)
    (hE : ∀ k : Fin 2, bal p k E = 0)
    (hP : m < P) (hdeg : ∀ v, incidentLoad J v ≤ D)
    (hp : ∀ i j, (pool (category p) (R ∪ J) i).card ≤
      (pool (category p) (R ∪ J) j).card + m)
    (hpool : ∀ i, P ≤ (pool (category p) J i).card) :
    ∃ Y ⊆ J, Disjoint Y R ∧ Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      (∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0) ∧
      ∀ S : Finset (Sym2 V), Disjoint S (R ∪ J) → S ∪ (R ∪ J) ⊆ E →
        HasDecomp p F3 (Y ∪ S) →
        ∀ k : Fin 2, bal p k (E \ ((Y ∪ S) ∪ (R ∪ (J \ Y)))) = 0 := by
  have hdiff : J \ R = J := by
    ext e
    simp only [mem_sdiff]
    exact ⟨And.left, fun he => ⟨he, fun hr => disjoint_left.mp hRJ hr he⟩⟩
  have hloop : ∀ e ∈ J, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      intro hd
      exact hcross x y (mem_union_right R he)
        (congrArg p (Sym2.mk_isDiag_iff.mp hd))
  obtain ⟨Y, hY, hc, hd, heq⟩ := SmallTrimStage118.exists_small_trim
    (category p) R J m D P hP hloop hdeg hp (fun i => by rw [hdiff]; exact hpool i)
  rw [hdiff] at hY
  have hb : ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0 := by
    intro k
    rw [bal_eq_category_counts p k _ (fun x y he => hcross x y (mem_sdiff.mp he).1),
      heq, heq]
    exact sub_self _
  refine ⟨Y, hY, hRJ.symm.mono_left hY, hc, hd, hb, ?_⟩
  intro S hS hsub hdec k
  rw [actual_host_balance p k E R J Y S hRJ hY hS hsub (hE k) hdec, hb k, neg_zero]

end PartitionedTriangleAbsorption.ReserveAwareRecutStage120
