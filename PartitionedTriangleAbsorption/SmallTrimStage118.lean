/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SampledReserveTrimStage115

/-! # Keep the cardinality bound of the balanced recut

The recut equalizes three category counts to their minimum. One surplus
vanishes, so pairwise differences at most `m` imply at most `2*m` removals.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SmallTrimStage118

open Finset AntiEdgeSelection ReserveTrimStage109 SeedDrivenTrimStage114
  F3ReserveTrimStage109 CoverDownStage105 TypedNibble TypedApplicationLinks
  TypedLoadNecessity ApproximateBalanceStage114 NeighbourPoolCapacityStage114

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem card_eq_pools (c : Sym2 V → Fin 3) (E : Finset (Sym2 V)) :
    E.card = (pool c E 0).card + (pool c E 1).card + (pool c E 2).card := by
  have hh : E.card = ∑ i : Fin 3, (pool c E i).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using hh

theorem card_trim_le (c : Sym2 V → Fin 3) (E Y : Finset (Sym2 V)) (m : ℕ)
    (hY : Y ⊆ E)
    (hp : ∀ i j, (pool c E i).card ≤ (pool c E j).card + m)
    (hc : ∀ i, (pool c (E \ Y) i).card =
      min (pool c E 0).card (min (pool c E 1).card (pool c E 2).card)) :
    Y.card ≤ 2 * m := by
  have hE := card_eq_pools c E
  have hR := card_eq_pools c (E \ Y)
  rw [hc 0, hc 1, hc 2] at hR
  have hsub := card_sdiff_add_card_eq_card hY
  have h01 := hp 0 1
  have h02 := hp 0 2
  have h10 := hp 1 0
  have h12 := hp 1 2
  have h20 := hp 2 0
  have h21 := hp 2 1
  omega

variable [Finite V]

theorem exists_small_trim (c : Sym2 V → Fin 3) (X R : Finset (Sym2 V))
    (m D P : ℕ) (hP : m < P) (hloop : ∀ e ∈ R, ¬ e.IsDiag)
    (hdeg : ∀ v, incidentLoad R v ≤ D)
    (hp : ∀ i j, (pool c (X ∪ R) i).card ≤ (pool c (X ∪ R) j).card + m)
    (hpool : ∀ i, P ≤ (pool c (R \ X) i).card) :
    ∃ Y ⊆ R \ X, Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ i, (pool c ((X ∪ R) \ Y) i).card =
        min (pool c (X ∪ R) 0).card
          (min (pool c (X ∪ R) 1).card (pool c (X ∪ R) 2).card) := by
  let a := fun i => (pool c (X ∪ R) i).card
  let t := min (a 0) (min (a 1) (a 2))
  have ht : ∀ i, t ≤ a i := by
    intro i
    fin_cases i <;> dsimp [t] <;> omega
  have hs : ∀ i, a i - t ≤ m := by
    intro i
    have h0 := hp i 0
    have h1 := hp i 1
    have h2 := hp i 2
    dsimp [a, t]
    omega
  have hcap : ∀ i, let M := (pool c (X ∪ R) i).card - t
      M = 0 ∨ 2 * M * D + M * quota m D P <
        quota m D P * (pool c (R \ X) i).card := by
    intro i
    right
    have hsmall : 2 * (a i - t) * D + (a i - t) * quota m D P ≤
        2 * m * D + m * quota m D P := by gcongr <;> exact hs i
    exact hsmall.trans_lt ((quota_capacity m D P hP).trans_le
      (Nat.mul_le_mul_left _ (hpool i)))
  obtain ⟨Y, hY, hd, hc⟩ := trim_to_equal_counts c X R t (quota m D P) D
    hloop hdeg ht hcap
  refine ⟨Y, hY, card_trim_le c (X ∪ R) Y m ?_ hp hc, hd, hc⟩
  exact hY.trans (sdiff_subset.trans subset_union_right)

variable [Fintype V]

theorem exists_small_trim_of_seed (p : V → Fin 4)
    (J : SimpleGraph V) [DecidableRel J.Adj] (R : Finset (Sym2 V)) (hR : R ⊆ J.edgeFinset)
    (φ : Finset V → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hl : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε)
    (hcross : ∀ x y, J.Adj x y → p x ≠ p y)
    (m D P : ℕ) (hm : 2 * ε * J.edgeFinset.card ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad R v ≤ D)
    (hpool : ∀ i, P ≤ (pool (category p) R i).card) :
    ∃ Y ⊆ R, Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k (J.edgeFinset \ Y) = 0 := by
  let X := J.edgeFinset \ R
  have hhost : X ∪ R = J.edgeFinset := sdiff_union_of_subset hR
  have hdiff : R \ X = R := by ext e; simp only [X, mem_sdiff]; tauto
  have hp : ∀ i j, (pool (category p) (X ∪ R) i).card ≤
      (pool (category p) (X ∪ R) j).card + m := by
    intro i j
    rw [hhost]
    have hh := (abs_le.mp (category_difference p J φ ε hε hcross hl i j)).2
    have hh' : ((pool (category p) J.edgeFinset i).card : ℝ) ≤
        (pool (category p) J.edgeFinset j).card + m := by linarith
    exact_mod_cast hh'
  have hloop : ∀ e ∈ R, ¬ e.IsDiag := by
    intro e he
    exact J.not_isDiag_of_mem_edgeFinset (hR he)
  obtain ⟨Y, hY, hcard, hd, hc⟩ := exists_small_trim (category p) X R m D P hP
    hloop hdeg hp (fun i => by rw [hdiff]; exact hpool i)
  refine ⟨Y, hdiff ▸ hY, hcard, hd, fun k => ?_⟩
  rw [bal_eq_category_counts p k _ (fun x y he =>
    hcross x y (SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1))]
  rw [hhost] at hc
  rw [hc, hc]
  exact sub_self _

end PartitionedTriangleAbsorption.SmallTrimStage118
