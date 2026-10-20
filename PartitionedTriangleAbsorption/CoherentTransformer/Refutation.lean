/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoherentTransformer.BipartiteLinkHost
public import Mathlib.Algebra.BigOperators.Fin

/-! # Refutation of the two-root coherent transformer target

In the six-class host `BipartiteLinkHost.host (k+2)`, take the two disjoint
physical 4-cycles

  `Hx = (A,0)(P,0)(Z,0)(X,0)`,  `Hy = (A,1)(P,1)(Z,1)(X,1)`.

All hypotheses of the candidate hold with `α = 1/6`, `β = 1/3`, `|I| = 4`,
for every size `n = 6(k+2)`. The star charge at `v = (A,0)` annihilates
every F0 triangle, equals `2` on `Hx` and `0` on `Hy`. By charge invariance
NO physical transformer exists, of any size.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer.Refutation

open Finset TypedApplicationLinks BipartiteLinkHost

/-- Classes along the 4-cycle: `A, P, Z, X`. -/
def cls : Fin 4 → Fin 6 := ![0, 3, 5, 1]

/-- The successor permutation of the positions. -/
def succ4 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

theorem cls_trail : ∀ i : Fin 4, cls i ≠ cls (succ4 i) ∧ R (cls i) (cls (succ4 i)) = true := by
  decide

theorem cls_edge_inj : ∀ i j : Fin 4,
    ((cls i = cls j ∧ cls (succ4 i) = cls (succ4 j)) ∨
      (cls i = cls (succ4 j) ∧ cls (succ4 i) = cls j)) → i = j := by
  decide

theorem cls_used : ∀ i : Fin 4, cls i = 0 ∨ cls i = 3 ∨ cls i = 5 ∨ cls i = 1 := by
  decide

variable (L : ℕ)

/-- Roots of the trail with index `m`: position `i` goes to `(cls i, m)`. -/
def rootMap (m : Fin L) : Fin 4 → Fin 6 × Fin L := fun i => (cls i, m)

theorem physicalTrail (m : Fin L) : PhysicalTrail (host L) succ4 (rootMap L m) := by
  refine ⟨fun i h => (cls_trail i).1 (congrArg Prod.fst h), ?_, fun i => ?_⟩
  · intro i j h
    apply cls_edge_inj
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩
    · exact Or.inr ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩
  · exact ⟨fun h => (cls_trail i).1 (congrArg Prod.fst h), (cls_trail i).2⟩

theorem trailEdges_subset (m : Fin L) :
    trailEdges succ4 (rootMap L m) ⊆ (host L).edgeFinset := by
  intro e he
  simp only [trailEdges, mem_image, mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (physicalTrail L m).2.2 i

theorem sum_trailEdges (m : Fin L) (f : Sym2 (Fin 6 × Fin L) → ℤ) :
    ∑ e ∈ trailEdges succ4 (rootMap L m), f e =
      ∑ i, f s(rootMap L m i, rootMap L m (succ4 i)) := by
  rw [trailEdges, sum_image]
  intro i _ j _ h
  exact (physicalTrail L m).2.1 h

/-- Two clone roots in the same used class have `2L` common neighbours in each part. -/
theorem clone_pair (a b : Fin 6 × Fin L) (hab : a.1 = b.1)
    (hc : a.1 = 0 ∨ a.1 = 3 ∨ a.1 = 5 ∨ a.1 = 1) (j : Fin 2) :
    2 * L ≤ (univ.filter fun w => hp L w = j ∧ (host L).Adj a w ∧ (host L).Adj b w).card := by
  obtain ⟨e₁, e₂, h12, hp1, hp2, h1c, h2c, hR1, hR2⟩ := clone_class a.1 hc j
  have hsub : block L e₁ ∪ block L e₂ ⊆
      univ.filter fun w => hp L w = j ∧ (host L).Adj a w ∧ (host L).Adj b w := by
    intro w hw
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hw with hw | hw <;> rw [mem_block] at hw
    · refine ⟨by change part w.1 = j; rw [hw]; exact hp1, ⟨?_, by rw [hw]; exact hR1⟩,
        ⟨?_, by rw [hw, ← hab]; exact hR1⟩⟩
      · intro h; apply h1c; rw [← hw, ← h]
      · intro h; apply h1c; rw [← hw, ← h, hab]
    · refine ⟨by change part w.1 = j; rw [hw]; exact hp2, ⟨?_, by rw [hw]; exact hR2⟩,
        ⟨?_, by rw [hw, ← hab]; exact hR2⟩⟩
      · intro h; apply h2c; rw [← hw, ← h]
      · intro h; apply h2c; rw [← hw, ← h, hab]
  have hdisj : Disjoint (block L e₁) (block L e₂) := by
    rw [disjoint_left]
    intro w h1 h2
    rw [mem_block] at h1 h2
    exact h12 (h1.symm.trans h2)
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_block, card_block] at this
  omega

theorem cloneCondition (m m' : Fin L) :
    CloneCondition (hp L) (host L) (1 / 3) (rootMap L m) (rootMap L m') := by
  intro i j
  have h := clone_pair L (rootMap L m i) (rootMap L m' i) rfl (cls_used i) j
  have h2 : ((2 * L : ℕ) : ℝ) ≤ ((univ.filter fun w => hp L w = j ∧
      (host L).Adj (rootMap L m i) w ∧ (host L).Adj (rootMap L m' i) w).card : ℝ) := by
    exact_mod_cast h
  rw [card_host]
  push_cast at h2 ⊢
  linarith

/-- The source and target root sets are disjoint when the indices differ. -/
theorem roots_disjoint {m m' : Fin L} (hm : m ≠ m') :
    Disjoint (univ.image (rootMap L m)) (univ.image (rootMap L m')) := by
  rw [disjoint_left]
  intro a ha hb
  simp only [mem_image, mem_univ, true_and] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact hm (congrArg Prod.snd hj).symm

/-- The star charge at `(A,0)` is `2` on the source cycle. -/
theorem charge_source (k : ℕ) :
    ∑ e ∈ trailEdges succ4 (rootMap (k + 2) 0), starCharge (k + 2) (0, 0) e = 2 := by
  rw [sum_trailEdges]
  simp [Fin.sum_univ_four, starCharge_mk, rootMap, cls, succ4, sgn]

/-- The star charge at `(A,0)` is `0` on the target cycle. -/
theorem charge_target (k : ℕ) :
    ∑ e ∈ trailEdges succ4 (rootMap (k + 2) 1), starCharge (k + 2) (0, 0) e = 0 := by
  rw [sum_trailEdges]
  simp [starCharge_mk, rootMap]

/-- **No physical coherent transformer exists** for the two 4-cycles, of any size. -/
theorem no_transformer (k : ℕ) (T : Finset (Sym2 (Fin 6 × Fin (k + 2)))) :
    ¬ IsCoherentTransformer (hp (k + 2)) (host (k + 2)) succ4
      (rootMap (k + 2) 0) (rootMap (k + 2) 1) T := by
  rintro ⟨hT, hd, hx, hy⟩
  have h := charge_eq_of_transformer (starCharge_annihilating (k + 2) (0, 0) rfl) hT
    (trailEdges_subset _ _) (trailEdges_subset _ _)
    (disjoint_of_subset_right subset_union_left hd)
    (disjoint_of_subset_right subset_union_right hd) hx hy
  rw [charge_source, charge_target] at h
  omega

theorem antiEdgeful_of_le {α : ℝ} (hα : α ≤ 1 / 6) : AntiEdgeful (hp L) F0 (host L) α := by
  intro τ hτ i j k hτeq u v huv hu hv
  have h := antiEdgeful L τ hτ i j k hτeq u v huv hu hv
  have hn : (0 : ℝ) ≤ Fintype.card (Fin 6 × Fin L) := Nat.cast_nonneg _
  nlinarith

theorem cloneCondition_of_le {β : ℝ} (hβ : β ≤ 1 / 3) (m m' : Fin L) :
    CloneCondition (hp L) (host L) β (rootMap L m) (rootMap L m') := by
  intro i j
  have h := cloneCondition L m m' i j
  have hn : (0 : ℝ) ≤ Fintype.card (Fin 6 × Fin L) := Nat.cast_nonneg _
  nlinarith

/-- **Headline refutation.** For `α ≤ 1/6`, `β ≤ 1/3` and every size bound
`K ≥ 4`, the candidate coherent F0 transformer target is false: whatever
`C, N` are chosen first, the host `host (N+2)` (with `6(N+2) ≥ N` vertices)
and the two 4-cycles satisfy every hypothesis, yet admit no physical
transformer at all. -/
theorem not_candidateTarget {α β : ℝ} (hα : α ≤ 1 / 6) (hβ : β ≤ 1 / 3) {K : ℕ}
    (hK : 4 ≤ K) : ¬ CandidateTarget α β K := by
  rintro ⟨C, N, h⟩
  obtain ⟨T, hT, -⟩ := h (Fin 6 × Fin (N + 2)) (hp (N + 2)) (host (N + 2)) (Fin 4) succ4
    (rootMap (N + 2) 0) (rootMap (N + 2) 1)
    (by rw [card_host]; omega) ⟨(0, 0), rfl⟩ ⟨(3, 0), rfl⟩
    (antiEdgeful_of_le (N + 2) hα) (by simpa using hK)
    (physicalTrail _ _) (physicalTrail _ _)
    (roots_disjoint _ (by simp)) (fun _ => rfl) (cloneCondition_of_le (N + 2) hβ 0 1)
  exact no_transformer N T hT

end PartitionedTriangleAbsorption.CoherentTransformer.Refutation
