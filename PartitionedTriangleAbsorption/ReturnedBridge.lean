/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import PartitionedTriangleAbsorption.PhysicalHinge

/-! # Consume Aristotle's actual decomposition definitions

No incomplete main theorem is imported. The physical-support lemmas apply to
the supplied `HasDecomp` directly, via forgetting labels and disjointness.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption

variable {V : Type*} [DecidableEq V] {t : ℕ}

theorem triangleCovered_of_hasDecomp (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E : Finset (Sym2 V))
    (h : HasDecomp p F E) : PhysicalHinge.TriangleCovered E := by
  obtain ⟨D, hcard, _, hunion⟩ := h
  apply PhysicalHinge.triangleCovered_of_decomposition E D
  · exact fun s hs => (hcard s hs).1
  · exact hunion

/-- The two physical residuals in an actual returned hinge are triangle-covered. -/
theorem IsHinge.triangleCovered {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {S S' : Finset V} {H : Finset (Sym2 V)} (h : IsHinge p F S S' H) :
    PhysicalHinge.TriangleCovered (H ∪ (triEdges S \ triEdges S')) ∧
    PhysicalHinge.TriangleCovered (H ∪ (triEdges S' \ triEdges S)) :=
  ⟨triangleCovered_of_hasDecomp p F _ h.2.1,
    triangleCovered_of_hasDecomp p F _ h.2.2⟩

/-- This helper proof is reused from the returned `Divisibility.lean`. -/
lemma triEdges_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
      Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]

/-- Four-root support for the actual `IsHinge` predicate supplied by Aristotle. -/
theorem IsHinge.four_roots {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (H : Finset (Sym2 V)) (u v w z : V)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (h : IsHinge p F {u, v, w} {u, v, z} H) :
    ({u, v, w, z} : Finset V) ⊆ PhysicalHinge.support H := by
  have heW := triEdges_three huv huw hvw
  have heZ := triEdges_three huv huz hvz
  have hdiffW : triEdges ({u, v, w} : Finset V) \ triEdges {u, v, z} =
      {s(u, w), s(v, w)} := by
    simp [heW, heZ, huv, huw, hvw, hwz.symm]
  have hdiffZ : triEdges ({u, v, z} : Finset V) \ triEdges {u, v, w} =
      {s(u, z), s(v, z)} := by
    simp [heW, heZ, huv, huz, hvz, hwz]
  have hcovW := h.triangleCovered.1
  have hcovZ := h.triangleCovered.2
  rw [hdiffW] at hcovW
  rw [hdiffZ] at hcovZ
  apply PhysicalHinge.four_roots_forced H u v w z huv huw huz hvw hvz
  · simpa only [heW] using h.1.mono_right Finset.subset_union_left
  · simpa only [heZ] using h.1.mono_right Finset.subset_union_right
  · exact hcovW
  · exact hcovZ

end PartitionedTriangleAbsorption
