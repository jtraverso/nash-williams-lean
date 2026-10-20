/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.LocalMin
public import PartitionedTriangleAbsorption.ExceptionalQuotaStage142

@[expose] public section

/-!
# Case (5): the quota ledger of a family of edge-disjoint triangles

For a partition `p` into four classes and a pairing index `i`, the integer
`sixQuota p E i = 2|E| − 3·cut_i(E)` is six times the number of `i`-matched triangles still
needed (Proposition 15.21).  Removing a triangle whose three vertices lie on the same side of
the `i`-th bipartition lowers it by `6`; removing any other triangle leaves it unchanged.
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 ExceptionalQuotaStage142

variable {V : Type*} [DecidableEq V]

/-- All vertices of `t` lie on the same side of the `i`-th bipartition. -/
def SameSide (p : V → Fin 4) (i : Fin 3) (t : Finset V) : Prop :=
  ∀ a ∈ t, ∀ b ∈ t, side i (p a) = side i (p b)

instance (p : V → Fin 4) (i : Fin 3) : DecidablePred (SameSide p i) := fun t => by
  unfold SameSide; infer_instance

lemma sameSide_three_iff (p : V → Fin 4) (i : Fin 3) (a b c : V) :
    SameSide p i {a, b, c} ↔
      side i (p a) = side i (p b) ∧ side i (p a) = side i (p c) := by
  constructor
  · intro h
    exact ⟨h a (by simp) b (by simp), h a (by simp) c (by simp)⟩
  · rintro ⟨h1, h2⟩ x hx y hy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | exact h1 | exact h2 | exact h1.symm | exact h2.symm |
        exact h1.symm.trans h2 | exact h2.symm.trans h1

/-- The six-fold quota consumed by a family of edge-disjoint triangles. -/
theorem sixQuota_family (p : V → Fin 4) (D : Finset (Finset V)) (h3 : ∀ t ∈ D, t.card = 3)
    (hdisj : (D : Set (Finset V)).PairwiseDisjoint triEdges) (i : Fin 3) :
    sixQuota p (D.biUnion triEdges) i = 6 * ((D.filter (SameSide p i)).card : ℤ) := by
  classical
  have he : (D.biUnion triEdges).card = ∑ t ∈ D, (triEdges t).card := card_biUnion hdisj
  have hc : (cuts p (D.biUnion triEdges) i).card = ∑ t ∈ D, (cuts p (triEdges t) i).card := by
    unfold cuts
    rw [filter_biUnion]
    exact card_biUnion (fun s hs t ht hst =>
      (hdisj hs ht hst).mono (filter_subset _ _) (filter_subset _ _))
  have hsum : sixQuota p (D.biUnion triEdges) i = ∑ t ∈ D, sixQuota p (triEdges t) i := by
    unfold sixQuota
    rw [he, hc]
    simp only [Nat.cast_sum, mul_sum, sum_sub_distrib]
  rw [hsum]
  have ht : ∀ t ∈ D, sixQuota p (triEdges t) i = if SameSide p i t then 6 else 0 := by
    intro t htD
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (h3 t htD)
    have hE : triEdges ({a, b, c} : Finset V) = TypedCorrectionFamily.edges a b c := by
      rw [triEdges_three hab hac hbc]
      rfl
    rw [hE, sixQuota_triangle p a b c hab hac hbc i]
    have hiff := sameSide_three_iff p i a b c
    by_cases h : SameSide p i {a, b, c}
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  rw [sum_congr rfl ht, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  ring

/-- A family of edge-disjoint triangles is a `{K₃}`-decomposition of its edge set. -/
theorem hasDecomp_of_family (D : Finset (Finset V)) (h3 : ∀ t ∈ D, t.card = 3)
    (hdisj : (D : Set (Finset V)).PairwiseDisjoint triEdges) :
    HasDecomp OnePart.part1 OnePart.triFam (D.biUnion triEdges) := by
  refine ⟨D, fun s hs => ⟨h3 s hs, ?_⟩, hdisj, rfl⟩
  simp only [OnePart.triFam, Finset.mem_singleton]
  have hm : s.val.map OnePart.part1 = Multiset.replicate 3 (0 : Fin 1) := by
    rw [Multiset.eq_replicate]
    exact ⟨by simpa using h3 s hs, fun _ _ => Subsingleton.elim _ _⟩
  exact hm.trans rfl

/-- Removing a decomposable subset preserves the six-fold quota identity shape. -/
theorem sixQuota_sdiff_family (p : V → Fin 4) (E : Finset (Sym2 V)) (D : Finset (Finset V))
    (h3 : ∀ t ∈ D, t.card = 3) (hdisj : (D : Set (Finset V)).PairwiseDisjoint triEdges)
    (hsub : D.biUnion triEdges ⊆ E) (i : Fin 3) :
    sixQuota p (E \ D.biUnion triEdges) i =
      sixQuota p E i - 6 * ((D.filter (SameSide p i)).card : ℤ) := by
  rw [sixQuota_sdiff p E _ hsub i, sixQuota_family p D h3 hdisj i]

end NashWilliams18.C128
