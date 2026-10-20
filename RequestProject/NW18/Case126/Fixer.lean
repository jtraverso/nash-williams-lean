/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.Setup

@[expose] public section

/-!
# The parity-fixer (Definition 15.18, Claim 12.6.3)

A parity-fixer is a vertex `v` adjacent to four vertices `w₀, w₁, w₂, w₃` outside `A`, with
`w_i` in the class `i`, such that `w₀ w₂ w₁ w₃` is a cycle (i.e. all four cross pairs between
`{w₀, w₁}` and `{w₂, w₃}` are edges).  It provides the two triangle pairs
`{v w₀ w₂, v w₁ w₃}` and `{v w₀ w₃, v w₁ w₂}`, which cover the same spokes and the two
complementary perfect matchings of the cycle; swapping them changes the parity of all four
cross edge counts.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class not joined to the class `i` in `F₁` (`0 ↔ 1`, `2 ↔ 3`). -/
def partner4 (i : Fin 4) : Fin 4 := ![1, 0, 3, 2] i

lemma allowedT_F1_iff_partner (i j : Fin 4) : AllowedT F1 i j ↔ j ≠ partner4 i := by
  revert i j; decide

/-- A parity-fixer with center `v` and spokes `w₀, …, w₃`. -/
structure Fixer126 (G : SimpleGraph V) (p : V → Fin 4) (A : Finset V) (v w0 w1 w2 w3 : V) :
    Prop where
  n0 : w0 ∉ A
  n1 : w1 ∉ A
  n2 : w2 ∉ A
  n3 : w3 ∉ A
  c0 : p w0 = 0
  c1 : p w1 = 1
  c2 : p w2 = 2
  c3 : p w3 = 3
  a0 : G.Adj v w0
  a1 : G.Adj v w1
  a2 : G.Adj v w2
  a3 : G.Adj v w3
  e02 : G.Adj w0 w2
  e03 : G.Adj w0 w3
  e12 : G.Adj w1 w2
  e13 : G.Adj w1 w3

section

variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V} {s : ℝ}

omit [DecidableEq V] in
lemma degT_eq_card_filter_cls (v : V) (j : Fin 4) :
    degT G p v j = ((clsT p j).filter (fun w => G.Adj v w)).card := by
  unfold degT clsT
  rw [filter_filter]
  congr 1; ext w; simp [and_comm]

/-- The non-neighbours of `v` in an allowed class are abnormal (or `v` itself). -/
lemma card_nonadj_cls_le (v : V) (j : Fin 4) (hj : AllowedT F1 (p v) j) :
    ((clsT p j).filter (fun w => ¬ G.Adj v w)).card ≤ (abnSet G p v).card + 1 := by
  have hsub : (clsT p j).filter (fun w => ¬ G.Adj v w) ⊆ abnSet G p v ∪ {v} := by
    intro w hw
    simp only [clsT, mem_filter, mem_univ, true_and] at hw
    simp only [abnSet, mem_union, mem_filter, mem_univ, true_and, mem_singleton]
    by_cases hwv : w = v
    · exact Or.inr hwv
    · exact Or.inl ⟨hwv, fun h => hw.2 (h.mpr (by rw [hw.1]; exact hj))⟩
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by simp))

/-- A common neighbour in a class: if `x` has `n/10` neighbours in the class `j`, then two
normal vertices allowed with `j` have a common neighbour with `x` in `V_j ∖ A`. -/
lemma pick_common (h : Setup126 G p A s) (hs : s ≤ 1 / 100)
    (hn : 100 ≤ (Fintype.card V : ℝ)) (x : V) (j : Fin 4)
    (hx : (Fintype.card V : ℝ) / 10 ≤ (degT G p x j : ℝ)) (y1 y2 : V) (hy1 : y1 ∉ A)
    (hy2 : y2 ∉ A) (ha1 : AllowedT F1 (p y1) j) (ha2 : AllowedT F1 (p y2) j) :
    ∃ u, u ∉ A ∧ p u = j ∧ G.Adj x u ∧ G.Adj y1 u ∧ G.Adj y2 u := by
  by_contra hne
  push_neg at hne
  have hsub : (clsT p j).filter (fun w => G.Adj x w) ⊆
      A ∪ (clsT p j).filter (fun w => ¬ G.Adj y1 w) ∪
        (clsT p j).filter (fun w => ¬ G.Adj y2 w) := by
    intro u hu
    simp only [clsT, mem_filter, mem_univ, true_and] at hu
    simp only [clsT, mem_union, mem_filter, mem_univ, true_and]
    by_cases huA : u ∈ A
    · exact Or.inl (Or.inl huA)
    · by_cases h1 : G.Adj y1 u
      · by_cases h2 : G.Adj y2 u
        · exact absurd h2 (hne u huA hu.1 hu.2 h1)
        · exact Or.inr ⟨hu.1, h2⟩
      · exact Or.inl (Or.inr ⟨hu.1, h1⟩)
  have hc0 := card_le_card hsub
  have hc1 := card_union_le (A ∪ (clsT p j).filter (fun w => ¬ G.Adj y1 w))
    ((clsT p j).filter (fun w => ¬ G.Adj y2 w))
  have hc2 := card_union_le A ((clsT p j).filter (fun w => ¬ G.Adj y1 w))
  rw [← degT_eq_card_filter_cls] at hc0
  have hb1 := card_nonadj_cls_le (G := G) y1 j ha1
  have hb2 := card_nonadj_cls_le (G := G) y2 j ha2
  have hcR : (degT G p x j : ℝ) ≤ A.card + ((abnSet G p y1).card + 1) +
      ((abnSet G p y2).card + 1) := by
    have : degT G p x j ≤ A.card + ((abnSet G p y1).card + 1) + ((abnSet G p y2).card + 1) := by
      omega
    exact_mod_cast this
  have := h.A_card
  have := h.normal y1 hy1
  have := h.normal y2 hy2
  nlinarith

/-- A parity-fixer from a center `v` adjacent to a normal vertex `w` and with `n/10` neighbours
in each of the other three classes. -/
lemma fixer_of_center (h : Setup126 G p A s) (hs : s ≤ 1 / 100)
    (hn : 100 ≤ (Fintype.card V : ℝ)) (v w : V) (hw : w ∉ A) (hvw : G.Adj v w)
    (hbig : ∀ j, j ≠ p w → (Fintype.card V : ℝ) / 10 ≤ (degT G p v j : ℝ)) :
    ∃ v w0 w1 w2 w3, Fixer126 G p A v w0 w1 w2 w3 := by
  have hcases : p w = 0 ∨ p w = 1 ∨ p w = 2 ∨ p w = 3 := by
    rcases p w with ⟨k, hk⟩; interval_cases k <;> simp
  rcases hcases with hc | hc | hc | hc
  · obtain ⟨u2, n2, c2, a2, e2, -⟩ := pick_common h hs hn v 2 (hbig 2 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u3, n3, c3, a3, e3, -⟩ := pick_common h hs hn v 3 (hbig 3 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u1, n1, c1, a1, f2, f3⟩ := pick_common h hs hn v 1 (hbig 1 (by rw [hc]; decide))
      u2 u3 n2 n3 (by rw [c2]; decide) (by rw [c3]; decide)
    exact ⟨v, w, u1, u2, u3, hw, n1, n2, n3, hc, c1, c2, c3, hvw, a1, a2, a3, e2, e3, f2.symm,
      f3.symm⟩
  · obtain ⟨u2, n2, c2, a2, e2, -⟩ := pick_common h hs hn v 2 (hbig 2 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u3, n3, c3, a3, e3, -⟩ := pick_common h hs hn v 3 (hbig 3 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u0, n0, c0, a0, f2, f3⟩ := pick_common h hs hn v 0 (hbig 0 (by rw [hc]; decide))
      u2 u3 n2 n3 (by rw [c2]; decide) (by rw [c3]; decide)
    exact ⟨v, u0, w, u2, u3, n0, hw, n2, n3, c0, hc, c2, c3, a0, hvw, a2, a3, f2.symm, f3.symm,
      e2, e3⟩
  · obtain ⟨u0, n0, c0, a0, e0, -⟩ := pick_common h hs hn v 0 (hbig 0 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u1, n1, c1, a1, e1, -⟩ := pick_common h hs hn v 1 (hbig 1 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u3, n3, c3, a3, f0, f1⟩ := pick_common h hs hn v 3 (hbig 3 (by rw [hc]; decide))
      u0 u1 n0 n1 (by rw [c0]; decide) (by rw [c1]; decide)
    exact ⟨v, u0, u1, w, u3, n0, n1, hw, n3, c0, c1, hc, c3, a0, a1, hvw, a3, e0.symm, f0,
      e1.symm, f1⟩
  · obtain ⟨u0, n0, c0, a0, e0, -⟩ := pick_common h hs hn v 0 (hbig 0 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u1, n1, c1, a1, e1, -⟩ := pick_common h hs hn v 1 (hbig 1 (by rw [hc]; decide))
      w w hw hw (by rw [hc]; decide) (by rw [hc]; decide)
    obtain ⟨u2, n2, c2, a2, f0, f1⟩ := pick_common h hs hn v 2 (hbig 2 (by rw [hc]; decide))
      u0 u1 n0 n1 (by rw [c0]; decide) (by rw [c1]; decide)
    exact ⟨v, u0, u1, u2, w, n0, n1, n2, hw, c0, c1, c2, hc, a0, a1, a2, hvw, f0, e0.symm, f1,
      e1.symm⟩

/-- **Claim 12.6.3**: a parity-fixer exists. -/
lemma exists_fixer (h : Setup126 G p A s) (hs : s ≤ 1 / 100)
    (hn : 100 ≤ (Fintype.card V : ℝ)) : ∃ v w0 w1 w2 w3, Fixer126 G p A v w0 w1 w2 w3 := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set P := newPart G p A with hPdef
  have hsum := sum_card_clsT P
  rw [Fin.sum_univ_four] at hsum
  obtain ⟨c, hc⟩ : ∃ c, n / 4 ≤ ((clsT P c).card : ℝ) := by
    by_contra hne
    push_neg at hne
    have hR : ((clsT P 0).card : ℝ) + (clsT P 1).card + (clsT P 2).card + (clsT P 3).card =
        n := by rw [hndef]; exact_mod_cast hsum
    linarith [hne 0, hne 1, hne 2, hne 3]
  obtain ⟨w, hwcls, hwA⟩ : ∃ w, p w = partner4 c ∧ w ∉ A := by
    by_contra hne
    push_neg at hne
    have hsub : clsT p (partner4 c) ⊆ A := by
      intro w hw
      simp only [clsT, mem_filter, mem_univ, true_and] at hw
      exact hne w hw
    have h1 : ((clsT p (partner4 c)).card : ℝ) ≤ A.card := by exact_mod_cast card_le_card hsub
    have := h.cls_lo (partner4 c)
    have := h.A_card
    nlinarith
  obtain ⟨v, hvc, hwv⟩ : ∃ v, P v = c ∧ G.Adj w v := by
    by_contra hne
    push_neg at hne
    have hwc : w ∉ clsT P c := by
      simp only [clsT, mem_filter, mem_univ, true_and, hPdef, newPart_of_not_mem hwA, hwcls]
      have : ∀ c : Fin 4, partner4 c ≠ c := by decide
      exact this c
    have hdisj1 : Disjoint (G.neighborFinset w) (clsT P c) := by
      rw [disjoint_left]
      intro y hy hyc
      simp only [clsT, mem_filter, mem_univ, true_and] at hyc
      exact hne y hyc ((G.mem_neighborFinset _ _).mp hy)
    have hdisj2 : Disjoint (G.neighborFinset w ∪ clsT P c) {w} := by
      rw [disjoint_singleton_right, mem_union, not_or]
      exact ⟨fun h => G.irrefl ((G.mem_neighborFinset _ _).mp h), hwc⟩
    have hcard := card_le_univ (G.neighborFinset w ∪ clsT P c ∪ {w})
    rw [card_union_of_disjoint hdisj2, card_union_of_disjoint hdisj1, card_singleton,
      G.card_neighborFinset_eq_degree] at hcard
    have hdeg : 3 * Fintype.card V ≤ 4 * G.degree w :=
      h.deg.trans (by have := G.minDegree_le_degree w; omega)
    have h1 : (G.degree w : ℝ) + (clsT P c).card + 1 ≤ n := by rw [hndef]; exact_mod_cast hcard
    have h2 : 3 * n ≤ 4 * (G.degree w : ℝ) := by rw [hndef]; exact_mod_cast hdeg
    linarith
  refine fixer_of_center h hs hn v w hwA hwv.symm fun j hj => newPart_big h hs hn v j ?_
  rw [← hPdef, hvc, allowedT_F1_iff_partner]
  rwa [hwcls] at hj

end

end NashWilliams18
