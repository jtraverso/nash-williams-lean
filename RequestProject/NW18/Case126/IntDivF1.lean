/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.FracDivF1

@[expose] public section

/-!
# Integral `F₁`-divisibility

An `F₁`-blowup (no edges between parts `0, 1` nor between parts `2, 3`) with all degrees even
is integrally `F₁`-divisible as soon as the four cross edge counts `e(V₀, V₂)`, `e(V₀, V₃)`,
`e(V₁, V₂)`, `e(V₁, V₃)` are even and the ordered edge counts satisfy
`E₀₀ + E₁₁ + E₂₂ + E₃₃ = E₀₂ + E₀₃ + E₁₂ + E₁₃` (twice the number of interior edges equals the
number of cross edges).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An integer degree vector lies in the `F₁` degree lattice of part `a` when it vanishes on the
part paired with `a` and has even sum. -/
lemma vertex_lattice_F1 (d : Fin 4 → ℤ) (a : Fin 4)
    (h01 : a.val < 2 → d (if a = 0 then 1 else 0) = 0)
    (h23 : 2 ≤ a.val → d (if a = 2 then 3 else 2) = 0)
    (hev : Even (d 0 + d 1 + d 2 + d 3)) :
    ∃ c : Multiset (Fin 4) → ℤ, d = ∑ τ ∈ F1 with a ∈ τ, c τ • typeDegVec τ a := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16⟩ :=
    typeDegVec_F1_vals
  obtain ⟨k, hk⟩ := hev
  rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) a with rfl | rfl | rfl | rfl
  · have hz := h01 (by decide)
    simp at hz
    refine ⟨fun τ => if τ = {0, 0, 2} then d 2 else if τ = {0, 0, 3} then d 0 - d 2 else
      if τ = {0, 2, 2} then 0 else if τ = {0, 3, 3} then k - d 0 else 0, ?_⟩
    rw [show F1.filter (fun τ => ((0 : Fin 4) ∈ τ)) = {{0, 0, 2}, {0, 0, 3}, {0, 2, 2}, {0, 3, 3}}
      by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1, w2, w3, w4]
    fin_cases i <;> simp +decide <;> omega
  · have hz := h01 (by decide)
    simp at hz
    refine ⟨fun τ => if τ = {1, 1, 2} then d 2 else if τ = {1, 1, 3} then d 1 - d 2 else
      if τ = {1, 2, 2} then 0 else if τ = {1, 3, 3} then k - d 1 else 0, ?_⟩
    rw [show F1.filter (fun τ => ((1 : Fin 4) ∈ τ)) = {{1, 1, 2}, {1, 1, 3}, {1, 2, 2}, {1, 3, 3}}
      by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w5, w6, w7, w8]
    fin_cases i <;> simp +decide <;> omega
  · have hz := h23 (by decide)
    simp at hz
    refine ⟨fun τ => if τ = {0, 2, 2} then d 0 else if τ = {1, 2, 2} then d 2 - d 0 else
      if τ = {0, 0, 2} then 0 else if τ = {1, 1, 2} then k - d 2 else 0, ?_⟩
    rw [show F1.filter (fun τ => ((2 : Fin 4) ∈ τ)) = {{0, 0, 2}, {1, 1, 2}, {0, 2, 2}, {1, 2, 2}}
      by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w9, w10, w11, w12]
    fin_cases i <;> simp +decide <;> omega
  · have hz := h23 (by decide)
    simp at hz
    refine ⟨fun τ => if τ = {0, 3, 3} then d 0 else if τ = {1, 3, 3} then d 3 - d 0 else
      if τ = {0, 0, 3} then 0 else if τ = {1, 1, 3} then k - d 3 else 0, ?_⟩
    rw [show F1.filter (fun τ => ((3 : Fin 4) ∈ τ)) = {{0, 0, 3}, {1, 1, 3}, {0, 3, 3}, {1, 3, 3}}
      by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w13, w14, w15, w16]
    fin_cases i <;> simp +decide <;> omega

omit [DecidableEq V] in
/-- The degree is the sum of the degrees into the parts. -/
lemma sum_degT_eq_degree {t : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (v : V) : ∑ j, degT G p v j = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    card_eq_sum_card_fiberwise (f := p) (t := univ) (fun _ _ => by simp)]
  refine sum_congr rfl fun j _ => ?_
  unfold degT
  congr 1
  ext w
  simp

omit [DecidableEq V] in
/-- An edge vector entry of a pair of parts not allowed by `F` vanishes in an `F`-blowup. -/
lemma edgeVec_eq_zero_of_not_allowed {t : ℕ} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin t}
    (hbl : ∀ u v, G.Adj u v → AllowedT F (p u) (p v)) {i j : Fin t} (hij : ¬ AllowedT F i j) :
    edgeVec p G.edgeFinset i j = 0 := by
  classical
  rw [edgeVec_eq_sum_degT]
  refine sum_eq_zero fun v hv => ?_
  have hv' : p v = i := (mem_filter.mp hv).2
  rw [degT_eq_zero_of_not_allowed hbl (by rw [hv']; exact hij)]
  simp

/-- **Integral `F₁`-divisibility** of an Eulerian `F₁`-blowup with even cross edge counts and
balanced interior/cross edge counts. -/
theorem isIntDiv_F1 {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4}
    (hbl : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v))
    (hev : ∀ v, Even (G.degree v))
    (h02 : Even (edgeVec p G.edgeFinset 0 2)) (h03 : Even (edgeVec p G.edgeFinset 0 3))
    (h12 : Even (edgeVec p G.edgeFinset 1 2)) (h13 : Even (edgeVec p G.edgeFinset 1 3))
    (hsum : edgeVec p G.edgeFinset 0 0 + edgeVec p G.edgeFinset 1 1 +
      edgeVec p G.edgeFinset 2 2 + edgeVec p G.edgeFinset 3 3 =
      edgeVec p G.edgeFinset 0 2 + edgeVec p G.edgeFinset 0 3 +
      edgeVec p G.edgeFinset 1 2 + edgeVec p G.edgeFinset 1 3) :
    IsIntDiv p F1 G.edgeFinset := by
  set E := G.edgeFinset with hE
  have hdiag : ∀ i, Even (edgeVec p E i i) := by
    intro i
    unfold edgeVec
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.even_sum _ fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y =>
      simp only [pairVec, Sym2.lift_mk]
      by_cases h : p x = i ∧ p y = i
      · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; decide
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; decide
  have hsym := PartitionedTriangleAbsorption.TypedLoadFamilies.edgeVec_symm p E
  have hz01 : edgeVec p E 0 1 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by rw [allowedT_F1_iff]; decide)
  have hz23 : edgeVec p E 2 3 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by rw [allowedT_F1_iff]; decide)
  refine ⟨?_, fun v => ?_⟩
  · obtain ⟨y0, hy0⟩ := hdiag 0
    obtain ⟨y1, hy1⟩ := hdiag 1
    obtain ⟨y2, hy2⟩ := hdiag 2
    obtain ⟨y3, hy3⟩ := hdiag 3
    obtain ⟨x02, hx02⟩ := h02
    obtain ⟨x03, hx03⟩ := h03
    obtain ⟨x12, hx12⟩ := h12
    obtain ⟨x13, hx13⟩ := h13
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := typeEdgeVec_F1_vals
    set f := y2 - x02
    set c := x12 - f
    set dd := y1 - c
    set h := x13 - dd
    refine ⟨fun τ => if τ = {0, 0, 2} then 0 else if τ = {0, 0, 3} then y0 else
      if τ = {0, 2, 2} then x02 else if τ = {1, 2, 2} then f else
      if τ = {1, 1, 2} then c else if τ = {1, 1, 3} then dd else
      if τ = {1, 3, 3} then h else if τ = {0, 3, 3} then y3 - h else 0, ?_⟩
    rw [F1_sum]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1, w2, w3, w4, w5, w6, w7, w8]
    have s01 := hsym 0 1
    have s02 := hsym 0 2
    have s03 := hsym 0 3
    have s12 := hsym 1 2
    have s13 := hsym 1 3
    have s23 := hsym 2 3
    fin_cases i <;> fin_cases j <;> simp +decide <;> omega
  · have hd : degVec p E v = fun j => (degT G p v j : ℤ) := by
      funext j; exact degVec_eq_degT p G v j
    rw [hd]
    refine vertex_lattice_F1 _ (p v) (fun ha => ?_) (fun ha => ?_) ?_
    · rw [degT_eq_zero_of_not_allowed hbl]
      · simp
      rw [allowedT_F1_iff]
      rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) (p v) with h' | h' | h' | h' <;>
        rw [h'] at ha ⊢ <;> simp at ha ⊢
    · rw [degT_eq_zero_of_not_allowed hbl]
      · simp
      rw [allowedT_F1_iff]
      rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) (p v) with h' | h' | h' | h' <;>
        rw [h'] at ha ⊢ <;> simp at ha ⊢
    · have h1 := sum_degT_eq_degree G p v
      rw [Fin.sum_univ_four] at h1
      have h2 := hev v
      rw [← h1] at h2
      exact_mod_cast h2

omit [DecidableEq V] in
/-- The row sums of the edge vector of an Eulerian graph are even. -/
lemma even_row_edgeVec {t : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj] (p : V → Fin t)
    (hev : ∀ v, Even (G.degree v)) (i : Fin t) :
    Even (∑ j, edgeVec p G.edgeFinset i j) := by
  classical
  simp_rw [edgeVec_eq_sum_degT]
  rw [sum_comm]
  refine Finset.even_sum _ fun v _ => ?_
  have := sum_degT_eq_degree G p v
  have h2 : (∑ j, (degT G p v j : ℤ)) = (G.degree v : ℤ) := by exact_mod_cast this
  rw [h2]
  exact_mod_cast hev v

omit [DecidableEq V] in
/-- **Parity of the cross edge counts** of an Eulerian `F₁`-blowup: the four cross edge counts
`E₀₂, E₀₃, E₁₂, E₁₃` all have the same parity. -/
theorem cross_parity_F1 {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4}
    (hbl : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) (hev : ∀ v, Even (G.degree v)) :
    Even (edgeVec p G.edgeFinset 0 2 + edgeVec p G.edgeFinset 0 3) ∧
      Even (edgeVec p G.edgeFinset 0 2 + edgeVec p G.edgeFinset 1 2) ∧
      Even (edgeVec p G.edgeFinset 1 2 + edgeVec p G.edgeFinset 1 3) := by
  set E := G.edgeFinset with hE
  have hdiag : ∀ i, Even (edgeVec p E i i) := by
    intro i
    unfold edgeVec
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.even_sum _ fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y =>
      simp only [pairVec, Sym2.lift_mk]
      by_cases h : p x = i ∧ p y = i
      · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; decide
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; decide
  have hsym := PartitionedTriangleAbsorption.TypedLoadFamilies.edgeVec_symm p E
  have hz01 : edgeVec p E 0 1 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by rw [allowedT_F1_iff]; decide)
  have hz10 : edgeVec p E 1 0 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by rw [allowedT_F1_iff]; decide)
  have hz23 : edgeVec p E 2 3 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by rw [allowedT_F1_iff]; decide)
  have r0 := even_row_edgeVec p hev 0
  have r1 := even_row_edgeVec p hev 1
  have r2 := even_row_edgeVec p hev 2
  rw [Fin.sum_univ_four, ← hE] at r0 r1 r2
  have s02 := hsym 0 2
  have s12 := hsym 1 2
  obtain ⟨a0, ha0⟩ := hdiag 0
  obtain ⟨a1, ha1⟩ := hdiag 1
  obtain ⟨a2, ha2⟩ := hdiag 2
  obtain ⟨k0, hk0⟩ := r0
  obtain ⟨k1, hk1⟩ := r1
  obtain ⟨k2, hk2⟩ := r2
  refine ⟨⟨k0 - a0, by omega⟩, ⟨k2 - a2, by omega⟩, ⟨k1 - a1, by omega⟩⟩

end NashWilliams18
