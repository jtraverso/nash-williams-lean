/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedNibbleAdapter
public import PartitionedTriangleAbsorption.F3ParityStage105

/-! # Stage105: an exact F3 seed forces two balance functionals to vanish

For `F3` on four classes, the two edge functionals
`Φ₁ = e₀₁ + e₂₃ - e₀₂ - e₁₃` and `Φ₂ = e₀₁ + e₂₃ - e₀₃ - e₁₂`
annihilate every allowed triangle. Hence:

* every edge set carrying an exact fractional `F3` seed (the input format of
  `TypedNibble.typed_nibble_packing`) has `Φ₁ = Φ₂ = 0`;
* if `J` and a subgraph `J'` both carry exact seeds then the deleted edges `R`
  satisfy `Φ₁(R) = Φ₂(R) = 0`. So an exact seed for `G` never restricts to an
  exact seed of `G - R` when the deleted reserve `R` is unbalanced; balancing
  the reserve is a NECESSARY, explicitly verifiable condition of any
  seed-compatibility lemma (obligation B).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

/-- The two balance tables on class pairs. -/
def balTab (k : Fin 2) (i j : Fin 4) : ℤ :=
  if k = 0 then
    (if ({i, j} : Finset (Fin 4)) = {0, 1} ∨ ({i, j} : Finset (Fin 4)) = {2, 3} then 1 else 0) -
    (if ({i, j} : Finset (Fin 4)) = {0, 2} ∨ ({i, j} : Finset (Fin 4)) = {1, 3} then 1 else 0)
  else
    (if ({i, j} : Finset (Fin 4)) = {0, 1} ∨ ({i, j} : Finset (Fin 4)) = {2, 3} then 1 else 0) -
    (if ({i, j} : Finset (Fin 4)) = {0, 3} ∨ ({i, j} : Finset (Fin 4)) = {1, 2} then 1 else 0)

theorem balTab_symm (k : Fin 2) (i j : Fin 4) : balTab k i j = balTab k j i := by
  revert k i j; decide

theorem balTab_triangle (k : Fin 2) (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) : balTab k i j + balTab k i l + balTab k j l = 0 := by
  revert k i j l; decide

/-- The balance functional of one edge. -/
def balEdge (p : V → Fin 4) (k : Fin 2) (e : Sym2 V) : ℤ :=
  Sym2.lift ⟨fun a b => balTab k (p a) (p b), fun a b => balTab_symm k (p a) (p b)⟩ e

/-- The balance functional of an edge set. -/
def bal (p : V → Fin 4) (k : Fin 2) (E : Finset (Sym2 V)) : ℤ := ∑ e ∈ E, balEdge p k e

theorem bal_triEdges (p : V → Fin 4) (k : Fin 2) {s : Finset V} (hs : IsTypedTri p F3 s) :
    bal p k (triEdges s) = 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs.1
  have hmap := hs.2
  have hval : ({a, b, c} : Finset V).val.map p = {p a, p b, p c} := by
    simp [hab, hac, hbc]
  rw [hval] at hmap
  have hd : p a ≠ p b ∧ p a ≠ p c ∧ p b ≠ p c := by
    revert hmap
    generalize p a = i
    generalize p b = j
    generalize p c = l
    revert i j l
    decide
  rw [bal, triEdges_three hab hac hbc, sum_insert, sum_insert, sum_singleton]
  · simpa [balEdge, add_assoc] using balTab_triangle k _ _ _ hd.1 hd.2.1 hd.2.2
  · simp only [mem_singleton, Sym2.eq_iff]; tauto
  · simp only [mem_insert, mem_singleton, Sym2.eq_iff]; tauto

variable [Fintype V]

/-- **Necessary condition for an exact seed.** -/
theorem bal_eq_zero_of_exact_seed (p : V → Fin 4) (k : Fin 2) (J : SimpleGraph V)
    [DecidableRel J.Adj] (φ : Finset V → ℝ)
    (hload : ∀ e ∈ J.edgeFinset, ∑ s ∈ copies p F3 J with e ∈ triEdges s, φ s = 1) :
    bal p k J.edgeFinset = 0 := by
  have key : ((bal p k J.edgeFinset : ℤ) : ℝ) =
      ∑ s ∈ copies p F3 J, φ s * ((bal p k (triEdges s) : ℤ) : ℝ) := by
    rw [bal, Int.cast_sum]
    calc ∑ e ∈ J.edgeFinset, ((balEdge p k e : ℤ) : ℝ)
        = ∑ e ∈ J.edgeFinset, ∑ s ∈ copies p F3 J with e ∈ triEdges s,
            φ s * ((balEdge p k e : ℤ) : ℝ) := by
          refine sum_congr rfl fun e he => ?_
          rw [← sum_mul, hload e he, one_mul]
      _ = ∑ s ∈ copies p F3 J, ∑ e ∈ J.edgeFinset with e ∈ triEdges s,
            φ s * ((balEdge p k e : ℤ) : ℝ) := by
          rw [sum_comm']
          intro e s
          simp only [mem_filter]
          tauto
      _ = ∑ s ∈ copies p F3 J, φ s * ((bal p k (triEdges s) : ℤ) : ℝ) := by
          refine sum_congr rfl fun s hs => ?_
          have hsub := TypedNibble.triEdges_subset_of_isCopy (TypedNibble.mem_copies_iff.mp hs)
          rw [bal, Int.cast_sum, mul_sum, filter_mem_eq_inter, inter_eq_right.mpr hsub]
  have hz : ∑ s ∈ copies p F3 J, φ s * ((bal p k (triEdges s) : ℤ) : ℝ) = 0 := by
    refine sum_eq_zero fun s hs => ?_
    rw [bal_triEdges p k (TypedNibble.isTypedTri_of_isCopy (TypedNibble.mem_copies_iff.mp hs))]
    simp
  exact_mod_cast key.trans hz

/-- **Exact seeds do not restrict through unbalanced deletions.** If both `J` and a
subgraph `J'` carry exact seeds, the deleted edge set is balanced. -/
theorem bal_deleted_eq_zero (p : V → Fin 4) (k : Fin 2) (J J' : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel J'.Adj] (hle : J' ≤ J) (φ φ' : Finset V → ℝ)
    (hload : ∀ e ∈ J.edgeFinset, ∑ s ∈ copies p F3 J with e ∈ triEdges s, φ s = 1)
    (hload' : ∀ e ∈ J'.edgeFinset, ∑ s ∈ copies p F3 J' with e ∈ triEdges s, φ' s = 1) :
    bal p k (J.edgeFinset \ J'.edgeFinset) = 0 := by
  have h1 := bal_eq_zero_of_exact_seed p k J φ hload
  have h2 := bal_eq_zero_of_exact_seed p k J' φ' hload'
  have hsub : J'.edgeFinset ⊆ J.edgeFinset := SimpleGraph.edgeFinset_mono hle
  have := sum_sdiff (f := balEdge p k) hsub
  unfold bal at h1 h2 ⊢
  linarith

/-- Contrapositive form: deleting an unbalanced reserve destroys every exact seed. -/
theorem no_exact_seed_after_unbalanced_deletion (p : V → Fin 4) (k : Fin 2)
    (J J' : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel J'.Adj] (hle : J' ≤ J)
    (φ : Finset V → ℝ)
    (hload : ∀ e ∈ J.edgeFinset, ∑ s ∈ copies p F3 J with e ∈ triEdges s, φ s = 1)
    (hunbal : bal p k (J.edgeFinset \ J'.edgeFinset) ≠ 0) :
    ¬ ∃ φ' : Finset V → ℝ,
      ∀ e ∈ J'.edgeFinset, ∑ s ∈ copies p F3 J' with e ∈ triEdges s, φ' s = 1 :=
  fun ⟨φ', h'⟩ => hunbal (bal_deleted_eq_zero p k J J' hle φ φ' hload h')

end PartitionedTriangleAbsorption.CoverDownStage105
