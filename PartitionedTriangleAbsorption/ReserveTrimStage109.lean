/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PoolQuotaStage109

/-! # Balance a reserve by deleting bounded-degree surplus edges

`X` is protected: only edges of the supplied physical reserve `R` may be
deleted. The three categories are the opposite-pair classes of F3, but the
selection theorem works for any edge classification. Its capacity condition
is checkable before choosing the deletions. It does not assert the existence
of a vortex, or of an exact fractional seed on its complement.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveTrimStage109

open Finset AntiEdgeSelection

variable {V : Type*} [Finite V] [DecidableEq V]

def pool (c : Sym2 V → Fin 3) (E : Finset (Sym2 V)) (i : Fin 3) :=
  E.filter (fun e => c e = i)

/-- Equalize all three category counts without deleting protected edges.
Every vertex loses at most `3*q` reserve edges. -/
theorem trim_to_equal_counts (c : Sym2 V → Fin 3) (X R : Finset (Sym2 V))
    (t q D : ℕ) (hR : ∀ e ∈ R, ¬ e.IsDiag)
    (hdeg : ∀ v, incidentLoad R v ≤ D)
    (ht : ∀ i, t ≤ (pool c (X ∪ R) i).card)
    (hcap : ∀ i, let M := (pool c (X ∪ R) i).card - t
      M = 0 ∨ 2 * M * D + M * q < q * (pool c (R \ X) i).card) :
    ∃ Y ⊆ R \ X,
      (∀ v, incidentLoad Y v ≤ 3 * q) ∧
      (∀ i, (pool c ((X ∪ R) \ Y) i).card = t) := by
  have select : ∀ i : Fin 3, ∃ Y ⊆ pool c (R \ X) i,
      Y.card = (pool c (X ∪ R) i).card - t ∧
      ∀ v, incidentLoad Y v ≤ q := by
    intro i
    rcases hcap i with hz | hb
    · exact ⟨∅, empty_subset _, by simp [hz], by simp [incidentLoad]⟩
    · apply PoolQuotaStage109.exists_subpool (pool c (R \ X) i)
        ((pool c (X ∪ R) i).card - t) q D ?_ ?_ hb _ le_rfl
      · intro e he
        exact hR e (mem_sdiff.mp (mem_filter.mp he).1).1
      · intro v
        exact (card_le_card (by
          intro e he
          exact mem_filter.mpr ⟨(mem_sdiff.mp (mem_filter.mp
            (mem_filter.mp he).1).1).1, (mem_filter.mp he).2⟩)).trans (hdeg v)
  choose Y hsub hcard hload using select
  let Z := univ.biUnion Y
  have hZsub : Z ⊆ R \ X := by
    intro e he
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
    exact (mem_filter.mp (hsub i hei)).1
  have hZi : ∀ i, pool c Z i = Y i := by
    intro i
    ext e
    simp only [pool, mem_filter]
    constructor
    · rintro ⟨he, hc⟩
      obtain ⟨j, _, hej⟩ := mem_biUnion.mp he
      have hcji := (mem_filter.mp (hsub j hej)).2.symm.trans hc
      simpa only [hcji] using hej
    · intro he
      exact ⟨mem_biUnion.mpr ⟨i, mem_univ i, he⟩,
        (mem_filter.mp (hsub i he)).2⟩
  refine ⟨Z, hZsub, ?_, ?_⟩
  · intro v
    have hbi : Z.filter (fun e => v ∈ e) =
        univ.biUnion (fun i => (Y i).filter (fun e => v ∈ e)) := by
      ext e
      simp [Z, exists_and_right]
    calc incidentLoad Z v = (Z.filter (fun e => v ∈ e)).card := rfl
      _ ≤ ∑ i : Fin 3, ((Y i).filter (fun e => v ∈ e)).card := by
        rw [hbi]
        exact card_biUnion_le
      _ ≤ ∑ _i : Fin 3, q := sum_le_sum (fun i _ => hload i v)
      _ = 3 * q := by simp
  · intro i
    have heq : pool c ((X ∪ R) \ Z) i = pool c (X ∪ R) i \ Y i := by
      rw [← hZi i]
      ext e
      simp only [pool, mem_filter, mem_sdiff]
      tauto
    have hYi : Y i ⊆ pool c (X ∪ R) i := by
      intro e he
      obtain ⟨heRX, hc⟩ := mem_filter.mp (hsub i he)
      exact mem_filter.mpr ⟨mem_union_right X (mem_sdiff.mp heRX).1, hc⟩
    rw [heq, card_sdiff_of_subset hYi, hcard i]
    exact Nat.sub_sub_self (ht i)

end PartitionedTriangleAbsorption.ReserveTrimStage109
