/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Setup
import RequestProject.NW18.Case127.IntDivF2

/-!
# Setting of the proof of Theorem 12.7

Notation for a graph `G` with a four-partition `p : V → Fin 4` (the classes `0, 1, 2, 3` are
the paper's `V₁', …, V₄'`) which is close to an `F₂`-blowup, i.e. to `T̄₂(n/2) + T₂(n/2)`
(classes `0, 1` are cliques not joined to each other, classes `2, 3` are independent and
completely joined, and the two halves are completely joined):

* `abnSet G p v` — the *abnormal* pairs at `v` with respect to `F₂`;
* `partner2 i` — the only class not allowed for the class `i` in `F₂`
  (`0 ↔ 1`, and `2`, `3` are not allowed with themselves);
* `newPart G p A` — the partition `P` of the paper: vertices outside `A` keep their class, a
  vertex `v ∈ A` is moved to the side where it has fewer neighbours; on the side `{0, 1}` into
  the class where it has more neighbours, on the side `{2, 3}` into the class where it has fewer
  neighbours (so that, in both cases, it has many neighbours in the allowed classes);
* `Setup127 G p A s` — the hypotheses used throughout: `δ(G) ≥ 3n/4`, the classes have sizes
  in `[n/4 − 1, n/4 + 1]`, `|A| ≤ 2 s n` and every vertex outside `A` has at most `s n`
  abnormal pairs.

The side map `side4` (the bipartition `P* = (V₁ ∪ V₂, V₃ ∪ V₄)`) is the one of Theorem 12.6.
All declarations of the proof of Theorem 12.7 live in the namespace `NashWilliams18.C127`.
-/

namespace NashWilliams18.C127

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The abnormal pairs at `v` with respect to `F₂`. -/
def abnSet (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (v : V) : Finset V :=
  univ.filter (fun w => w ≠ v ∧ ¬ (G.Adj v w ↔ AllowedT F2 (p v) (p w)))

/-- The class not allowed for the class `i` in `F₂`. -/
def partner2 (i : Fin 4) : Fin 4 := ![1, 0, 2, 3] i

lemma allowedT_F2_iff_partner (i j : Fin 4) : AllowedT F2 i j ↔ j ≠ partner2 i := by
  revert i j; decide

lemma allowedT_F2_of_side_ne {i j : Fin 4} (h : side4 i ≠ side4 j) : AllowedT F2 i j := by
  revert i j; decide

lemma side_eq_of_not_allowedT_F2 {i j : Fin 4} (h : ¬ AllowedT F2 i j) : side4 i = side4 j := by
  by_contra h'; exact h (allowedT_F2_of_side_ne h')

lemma allowedT_F2_comm (i j : Fin 4) : AllowedT F2 i j ↔ AllowedT F2 j i := by
  revert i j; decide

/-- The partition `P` of the paper (proof of Theorem 12.7). -/
def newPart (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (A : Finset V) (v : V) :
    Fin 4 :=
  if v ∈ A then
    (if degT G p v 0 + degT G p v 1 ≤ degT G p v 2 + degT G p v 3 then
      (if degT G p v 1 ≤ degT G p v 0 then 0 else 1)
    else (if degT G p v 2 ≤ degT G p v 3 then 2 else 3))
  else p v

/-- The hypotheses of the proof of Theorem 12.7. -/
structure Setup127 (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (A : Finset V)
    (s : ℝ) : Prop where
  deg : 3 * Fintype.card V ≤ 4 * G.minDegree
  cls_lo : ∀ i, (Fintype.card V : ℝ) / 4 - 1 ≤ ((clsT p i).card : ℝ)
  cls_hi : ∀ i, ((clsT p i).card : ℝ) ≤ (Fintype.card V : ℝ) / 4 + 1
  A_card : (A.card : ℝ) ≤ 2 * s * Fintype.card V
  normal : ∀ v, v ∉ A → ((abnSet G p v).card : ℝ) ≤ s * Fintype.card V

section basic

variable (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)

/-- A vertex sees all of an allowed class except its abnormal pairs (and itself). -/
lemma card_clsT_le_degT_allowed (v : V) (j : Fin 4) (hj : AllowedT F2 (p v) j) :
    (clsT p j).card ≤ degT G p v j + (abnSet G p v).card + 1 := by
  have hsub : clsT p j ⊆ (univ.filter (fun w => G.Adj v w ∧ p w = j)) ∪ abnSet G p v ∪ {v} := by
    intro w hw
    simp only [clsT, mem_filter, mem_univ, true_and] at hw
    simp only [abnSet, mem_union, mem_filter, mem_univ, true_and, mem_singleton]
    by_cases hwv : w = v
    · exact Or.inr hwv
    · by_cases hadj : G.Adj v w
      · exact Or.inl (Or.inl ⟨hadj, hw⟩)
      · exact Or.inl (Or.inr ⟨hwv, fun h => hadj (h.mpr (by rw [hw]; exact hj))⟩)
  calc (clsT p j).card ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by
      have := card_union_le (univ.filter (fun w => G.Adj v w ∧ p w = j)) (abnSet G p v)
      simp only [card_singleton]; unfold degT; omega

/-- A vertex has at most its abnormal pairs as neighbours in a forbidden class. -/
lemma degT_le_abn_forbidden (v : V) (j : Fin 4) (hj : ¬ AllowedT F2 (p v) j) :
    degT G p v j ≤ (abnSet G p v).card := by
  apply card_le_card
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw
  simp only [abnSet, mem_filter, mem_univ, true_and]
  refine ⟨fun h => G.ne_of_adj hw.1 h.symm, fun h => hj ?_⟩
  · rw [← hw.2]; exact h.mp hw.1

end basic

section newpart

variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V} {s : ℝ}

lemma newPart_of_not_mem {v : V} (hv : v ∉ A) : newPart G p A v = p v := by
  simp [newPart, hv]

/-- Every vertex has at least `n/10` neighbours (in the old partition) in every class allowed
for its new class (Claim 12.7.2). -/
lemma newPart_big (h : Setup127 G p A s) (hs : s ≤ 1 / 100)
    (hn : 100 ≤ (Fintype.card V : ℝ)) (v : V) (j : Fin 4)
    (hj : AllowedT F2 (newPart G p A v) j) :
    (Fintype.card V : ℝ) / 10 ≤ (degT G p v j : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hsum := sum_degT_eq_degree G p v
  rw [Fin.sum_univ_four] at hsum
  have hdeg : 3 * Fintype.card V ≤ 4 * G.degree v :=
    h.deg.trans (by have := G.minDegree_le_degree v; omega)
  have hle : ∀ i, (degT G p v i : ℝ) ≤ n / 4 + 1 := fun i =>
    (Nat.cast_le.mpr (degT_le_class G p v i)).trans (h.cls_hi i)
  have hsumR : (degT G p v 0 : ℝ) + degT G p v 1 + degT G p v 2 + degT G p v 3 =
      G.degree v := by exact_mod_cast hsum
  have hdegR : 3 * n ≤ 4 * (G.degree v : ℝ) := by rw [hndef]; exact_mod_cast hdeg
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  by_cases hv : v ∈ A
  · simp only [newPart, hv, if_true] at hj
    split_ifs at hj with c1 c2 c2
    · have c1R : (degT G p v 0 : ℝ) + degT G p v 1 ≤ degT G p v 2 + degT G p v 3 := by
        exact_mod_cast c1
      have c2R : (degT G p v 1 : ℝ) ≤ degT G p v 0 := by exact_mod_cast c2
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp) with
        rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hj; decide) | linarith
    · have c1R : (degT G p v 0 : ℝ) + degT G p v 1 ≤ degT G p v 2 + degT G p v 3 := by
        exact_mod_cast c1
      have c2R : (degT G p v 0 : ℝ) < degT G p v 1 := by exact_mod_cast not_le.mp c2
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp) with
        rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hj; decide) | linarith
    · have c1R : (degT G p v 2 : ℝ) + degT G p v 3 < degT G p v 0 + degT G p v 1 := by
        exact_mod_cast not_le.mp c1
      have c2R : (degT G p v 2 : ℝ) ≤ degT G p v 3 := by exact_mod_cast c2
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp) with
        rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hj; decide) | linarith
    · have c1R : (degT G p v 2 : ℝ) + degT G p v 3 < degT G p v 0 + degT G p v 1 := by
        exact_mod_cast not_le.mp c1
      have c2R : (degT G p v 3 : ℝ) < degT G p v 2 := by exact_mod_cast not_le.mp c2
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp) with
        rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hj; decide) | linarith
  · rw [newPart_of_not_mem hv] at hj
    have h1 := card_clsT_le_degT_allowed G p v j hj
    have h1R : ((clsT p j).card : ℝ) ≤ degT G p v j + (abnSet G p v).card + 1 := by
      exact_mod_cast h1
    have := h.normal v hv
    have := h.cls_lo j
    nlinarith

/-- A vertex of `A` has at most as many old-partition neighbours on its new side as on the
other side. -/
lemma newPart_side_le {v : V} (hv : v ∈ A) :
    (if side4 (newPart G p A v) = 0 then degT G p v 0 + degT G p v 1
      else degT G p v 2 + degT G p v 3) ≤
    (if side4 (newPart G p A v) = 0 then degT G p v 2 + degT G p v 3
      else degT G p v 0 + degT G p v 1) := by
  simp only [newPart, hv, if_true]
  split_ifs <;> simp_all [side4] <;> omega

end newpart

end NashWilliams18.C127
