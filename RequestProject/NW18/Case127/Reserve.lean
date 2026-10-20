/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Reserve126
import RequestProject.NW18.Case127.FixerEdges
import RequestProject.NW18.Case127.Extremal

/-!
# The reserve of interior triangles (Claim 12.7.6)

Inside `D = V₀ ∖ (A ∪ {v})` every vertex misses at most `s n` vertices (the class `0` is a clique
in `F₂`, so the missing pairs inside it are abnormal), so `G[D]` has a packing of at least
`n²/700` triangles.  These triangles are interior for `P*`, avoid `A`, and avoid the edges of the
parity-fixer.
-/

namespace NashWilliams18.C127

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V} {s : ℝ}
  {v w0 w1 w2 w3 : V}

/-- **Claim 12.7.6**: a reserve of interior triangles. -/
lemma reserve_127 (h : Setup127 G p A s) (hs : s ≤ 1 / 1000)
    (hsn : 10 ≤ s * (Fintype.card V : ℝ)) (hF : Fixer126 G p A v w0 w1 w2 w3) :
    ∃ T₀ : Finset (Finset V), IsTrianglePacking G T₀ ∧
      (∀ t ∈ T₀, ∃ i, ∀ x ∈ t, sideP G p A x = i) ∧ (∀ t ∈ T₀, ∀ x ∈ t, x ∉ A) ∧
      Disjoint (T₀.biUnion triEdges) (fixW v w0 w1 w2 w3) ∧
      (Fintype.card V : ℝ) ^ 2 / 700 ≤ (T₀.card : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by by_contra hneg; push_neg at hneg; nlinarith
  set D : Finset V := (clsT p 0 \ A).erase v with hD
  have hDmem : ∀ x ∈ D, x ≠ v ∧ x ∉ A ∧ p x = 0 := by
    intro x hx
    simp only [hD, mem_erase, mem_sdiff, clsT, mem_filter, mem_univ, true_and] at hx
    exact ⟨hx.1, hx.2.2, hx.2.1⟩
  set k : ℕ := ⌊s * n⌋₊ with hk
  have hkle : (k : ℝ) ≤ s * n := Nat.floor_le (by positivity)
  have hkD : ∀ x ∈ D, (D.filter (fun y => y ≠ x ∧ ¬ G.Adj x y)).card ≤ k := by
    intro x hx
    obtain ⟨-, hxA, hx0⟩ := hDmem x hx
    have hsub : D.filter (fun y => y ≠ x ∧ ¬ G.Adj x y) ⊆ abnSet G p x := by
      intro y hy
      simp only [mem_filter] at hy
      obtain ⟨-, -, hy0⟩ := hDmem y hy.1
      simp only [abnSet, mem_filter, mem_univ, true_and]
      refine ⟨hy.2.1, fun hiff => hy.2.2 (hiff.mpr ?_)⟩
      rw [hx0, hy0]; decide
    have h1 : ((D.filter (fun y => y ≠ x ∧ ¬ G.Adj x y)).card : ℝ) ≤ s * n :=
      (Nat.cast_le.mpr (card_le_card hsub)).trans (h.normal x hxA)
    exact Nat.le_floor h1
  obtain ⟨T, hT, hTD, hTc⟩ := dense_packing G D k hkD
  refine ⟨T, hT, fun t ht => ⟨0, fun x hx => ?_⟩, fun t ht x hx => (hDmem x (hTD t ht hx)).2.1,
    ?_, ?_⟩
  · obtain ⟨-, hxA, hx0⟩ := hDmem x (hTD t ht hx)
    rw [sideP_of_not_mem hxA, hx0]; decide
  · rw [disjoint_left]
    intro e he heW
    obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
    have hall : ∀ a ∈ e, a ∈ D := fun a ha =>
      hTD t ht (mem_sym2_iff.mp (mem_filter.mp het).1 a ha)
    rcases fixW_mem_cases e heW with h' | h' | h'
    · exact (hDmem v (hall v h')).1 rfl
    · have := (hDmem w2 (hall w2 h')).2.2; rw [hF.c2] at this; exact absurd this (by decide)
    · have := (hDmem w3 (hall w3 h')).2.2; rw [hF.c3] at this; exact absurd this (by decide)
  · have h1 : (clsT p 0).card ≤ (clsT p 0 \ A).card + A.card := card_le_card_sdiff_add_card
    have h2 := pred_card_le_card_erase (s := clsT p 0 \ A) (a := v)
    have h3 : ((clsT p 0).card : ℝ) ≤ D.card + 1 + A.card := by
      have : (clsT p 0).card ≤ D.card + 1 + A.card := by rw [hD]; omega
      exact_mod_cast this
    have hc := h.cls_lo 0
    have hA := h.A_card
    have hDlo : n / 5 ≤ (D.card : ℝ) := by nlinarith
    have hk2 : n / 11 ≤ (D.card : ℝ) / 2 - 1 - k := by nlinarith
    have hprod : n / 5 * (n / 11) ≤ (D.card : ℝ) * ((D.card : ℝ) / 2 - 1 - k) :=
      mul_le_mul hDlo hk2 (by positivity) (by positivity)
    nlinarith

end NashWilliams18.C127
