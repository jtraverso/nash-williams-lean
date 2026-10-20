/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveTrimStage109
public import PartitionedTriangleAbsorption.SeedBalanceStage105

/-! # Physical reserve trimming cancels the two F3 balance charges

The protected edge set is not modified. Category capacity remains an explicit
premise, not a claim about arbitrary pair-rich hosts. Zero balance is necessary
for seed repair; this module does not promote it to sufficient positivity.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F3ReserveTrimStage109

open Finset AntiEdgeSelection CoverDownStage105 ReserveTrimStage109

variable {V : Type*}

def categoryTab (i j : Fin 4) : Fin 3 :=
  if ({i, j} : Finset (Fin 4)) = {0, 1} ∨ ({i, j} : Finset (Fin 4)) = {2, 3} then 0
  else if ({i, j} : Finset (Fin 4)) = {0, 2} ∨ ({i, j} : Finset (Fin 4)) = {1, 3} then 1
  else 2

theorem categoryTab_symm (i j : Fin 4) : categoryTab i j = categoryTab j i := by
  revert i j; decide

def category (p : V → Fin 4) (e : Sym2 V) : Fin 3 :=
  Sym2.lift ⟨fun u v => categoryTab (p u) (p v),
    fun u v => categoryTab_symm (p u) (p v)⟩ e

theorem balEdge_category (p : V → Fin 4) (k : Fin 2) (u v : V) (h : p u ≠ p v) :
    balEdge p k s(u, v) =
      (if category p s(u, v) = 0 then 1 else 0) -
      (if category p s(u, v) = (if k = 0 then 1 else 2) then 1 else 0) := by
  simp only [balEdge, category, Sym2.lift_mk]
  have htab : ∀ (k : Fin 2) (i j : Fin 4), i ≠ j → balTab k i j =
      (if categoryTab i j = 0 then 1 else 0) -
      (if categoryTab i j = (if k = 0 then 1 else 2) then 1 else 0) := by decide
  exact htab k (p u) (p v) h

/-- Opposite-pair counts express exactly the returned seed's balance functionals. -/
theorem bal_eq_category_counts (p : V → Fin 4) (k : Fin 2) (E : Finset (Sym2 V))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v) :
    bal p k E = ((pool (category p) E 0).card : ℤ) -
      ((pool (category p) E (if k = 0 then 1 else 2)).card : ℤ) := by
  classical
  have heq : ∀ e ∈ E, balEdge p k e =
      (if category p e = 0 then 1 else 0) -
      (if category p e = (if k = 0 then 1 else 2) then 1 else 0) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v => exact balEdge_category p k u v (hcross u v he)
  rw [bal, sum_congr rfl heq, sum_sub_distrib]
  simp [pool, sum_boole]

variable [DecidableEq V]

/-- Deleting a degree-`q` edge set loses at most `2*q` common reserve neighbors.
This is the same two-root quantity used by the returned inner cover-down. -/
theorem two_root_loss (U : Finset V) (R Y : Finset (Sym2 V)) (x y : V) (a q : ℕ)
    (hload : ∀ v, incidentLoad Y v ≤ q)
    (hrich : a ≤ (U.filter (fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R)).card) :
    a ≤ (U.filter (fun z => s(x, z) ∈ R \ Y ∧ s(y, z) ∈ R \ Y)).card + 2 * q := by
  let Bad := (U.filter fun z => s(x, z) ∈ Y) ∪ (U.filter fun z => s(y, z) ∈ Y)
  have hb : Bad.card ≤ 2 * q := by
    have hx := (card_spoke_filter_le U Y x).trans (hload x)
    have hy := (card_spoke_filter_le U Y y).trans (hload y)
    exact (card_union_le _ _).trans (by omega)
  have hs : U.filter (fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R) ⊆
      (U.filter (fun z => s(x, z) ∈ R \ Y ∧ s(y, z) ∈ R \ Y)) ∪ Bad := by
    intro z hz
    simp only [mem_filter, mem_union, mem_sdiff, Bad] at hz ⊢
    tauto
  exact hrich.trans ((card_le_card hs).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left hb _)))

variable [Finite V]

/-- A checkable physical trimming producer. The surviving protected+reserve
system has both F3 charges zero, with at most `3*q` deletions at any vertex. -/
theorem exists_balanced_trim (p : V → Fin 4) (X R : Finset (Sym2 V)) (t q D : ℕ)
    (hcross : ∀ u v, s(u, v) ∈ X ∪ R → p u ≠ p v)
    (hdeg : ∀ v, incidentLoad R v ≤ D)
    (ht : ∀ i, t ≤ (pool (category p) (X ∪ R) i).card)
    (hcap : ∀ i, let M := (pool (category p) (X ∪ R) i).card - t
      M = 0 ∨ 2 * M * D + M * q < q * (pool (category p) (R \ X) i).card) :
    ∃ Y ⊆ R \ X, (∀ v, incidentLoad Y v ≤ 3 * q) ∧
      ∀ k : Fin 2, bal p k ((X ∪ R) \ Y) = 0 := by
  have hloop : ∀ e ∈ R, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      intro hd
      exact hcross u v (mem_union_right X he) (congrArg p (Sym2.mk_isDiag_iff.mp hd))
  obtain ⟨Y, hY, hd, hc⟩ := trim_to_equal_counts (category p) X R t q D hloop hdeg ht hcap
  refine ⟨Y, hY, hd, fun k => ?_⟩
  rw [bal_eq_category_counts p k _ (fun u v he => hcross u v (mem_sdiff.mp he).1), hc, hc]
  exact sub_self _

end PartitionedTriangleAbsorption.F3ReserveTrimStage109
