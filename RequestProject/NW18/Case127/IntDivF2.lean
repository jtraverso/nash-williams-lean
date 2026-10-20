/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.IntDivF1
public import RequestProject.NW18.Case127.FracDivF2

@[expose] public section

/-!
# Integral `F₂`-divisibility (Lemma 13.20)

An `F₂`-blowup (no edges between the parts `0, 1` and no edges inside the parts `2, 3`) is
integrally `F₂`-divisible as soon as it is Eulerian, the ordered edge counts satisfy
`E₀₀ + E₁₁ + 2 E₂₃ = E₀₂ + E₀₃ + E₁₂ + E₁₃` (condition (i') of Lemma 13.20: the cross edges are
twice the interior edges), and `E₀₀ + E₀₂ − E₀₃ ≡ 0 (mod 4)` (condition (iii'),
`2 e₁₁ + e₁₃ ≡ e₁₄ (mod 4)` in the paper's notation; recall `E₀₀ = 2 e₁₁`).

`even_parity_F2`: in an Eulerian `F₂`-blowup the quantity `E₀₀ + E₀₂ − E₀₃` is always even.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An integer degree vector lies in the `F₂` degree lattice of part `a` when it vanishes on the
parts not allowed for `a` and has even sum. -/
lemma vertex_lattice_F2 (d : Fin 4 → ℤ) (a : Fin 4)
    (hz : ∀ j, ¬ AllowedT F2 a j → d j = 0)
    (hev : Even (d 0 + d 1 + d 2 + d 3)) :
    ∃ c : Multiset (Fin 4) → ℤ, d = ∑ τ ∈ F2 with a ∈ τ, c τ • typeDegVec τ a := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := typeDegVec_F2_vals
  obtain ⟨k, hk⟩ := hev
  rcases (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) a with rfl | rfl | rfl | rfl
  · have hz1 := hz 1 (by decide)
    refine ⟨fun τ => if τ = {0, 0, 2} then d 2 - k + d 0 else if τ = {0, 0, 3} then k - d 2 else
      if τ = {0, 2, 3} then k - d 0 else 0, ?_⟩
    rw [show F2.filter (fun τ => ((0 : Fin 4) ∈ τ)) = {{0, 0, 2}, {0, 0, 3}, {0, 2, 3}}
      by decide]
    rw [sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1, w2, w3]
    fin_cases i <;> simp +decide <;> omega
  · have hz0 := hz 0 (by decide)
    refine ⟨fun τ => if τ = {1, 1, 2} then d 2 - k + d 1 else if τ = {1, 1, 3} then k - d 2 else
      if τ = {1, 2, 3} then k - d 1 else 0, ?_⟩
    rw [show F2.filter (fun τ => ((1 : Fin 4) ∈ τ)) = {{1, 1, 2}, {1, 1, 3}, {1, 2, 3}}
      by decide]
    rw [sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w4, w5, w6]
    fin_cases i <;> simp +decide <;> omega
  · have hz2 := hz 2 (by decide)
    refine ⟨fun τ => if τ = {0, 2, 3} then d 0 else if τ = {1, 2, 3} then d 3 - d 0 else
      if τ = {0, 0, 2} then 0 else if τ = {1, 1, 2} then k - d 3 else 0, ?_⟩
    rw [show F2.filter (fun τ => ((2 : Fin 4) ∈ τ)) = {{0, 0, 2}, {1, 1, 2}, {0, 2, 3}, {1, 2, 3}}
      by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w7, w8, w9, w10]
    fin_cases i <;> simp +decide <;> omega
  · have hz3 := hz 3 (by decide)
    refine ⟨fun τ => if τ = {0, 2, 3} then d 0 else if τ = {1, 2, 3} then d 2 - d 0 else
      if τ = {0, 0, 3} then 0 else if τ = {1, 1, 3} then k - d 2 else 0, ?_⟩
    rw [show F2.filter (fun τ => ((3 : Fin 4) ∈ τ)) = {{0, 0, 3}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}}
      by decide]
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w11, w12, w13, w14]
    fin_cases i <;> simp +decide <;> omega

omit [Fintype V] [DecidableEq V] in
/-- The diagonal entries of an edge vector are even. -/
lemma even_edgeVec_diag {t : ℕ} (p : V → Fin t) (E : Finset (Sym2 V)) (i : Fin t) :
    Even (edgeVec p E i i) := by
  unfold edgeVec
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.even_sum _ fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y =>
    simp only [pairVec, Sym2.lift_mk]
    by_cases h : p x = i ∧ p y = i
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; decide
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; decide

/-- **Lemma 13.20** (integral part, sufficiency): integral `F₂`-divisibility of an Eulerian
`F₂`-blowup satisfying (i') and (iii'). -/
theorem isIntDiv_F2 {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4}
    (hbl : ∀ u v, G.Adj u v → AllowedT F2 (p u) (p v))
    (hev : ∀ v, Even (G.degree v))
    (hmod : (4 : ℤ) ∣ edgeVec p G.edgeFinset 0 0 + edgeVec p G.edgeFinset 0 2 -
      edgeVec p G.edgeFinset 0 3)
    (hsum : edgeVec p G.edgeFinset 0 0 + edgeVec p G.edgeFinset 1 1 +
      2 * edgeVec p G.edgeFinset 2 3 =
      edgeVec p G.edgeFinset 0 2 + edgeVec p G.edgeFinset 0 3 +
      edgeVec p G.edgeFinset 1 2 + edgeVec p G.edgeFinset 1 3) :
    IsIntDiv p F2 G.edgeFinset := by
  set E := G.edgeFinset with hE
  have hsym := PartitionedTriangleAbsorption.TypedLoadFamilies.edgeVec_symm p E
  have hz01 : edgeVec p E 0 1 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by decide)
  have hz22 : edgeVec p E 2 2 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by decide)
  have hz33 : edgeVec p E 3 3 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by decide)
  refine ⟨?_, fun v => ?_⟩
  · obtain ⟨y0, hy0⟩ := even_edgeVec_diag p E 0
    obtain ⟨y1, hy1⟩ := even_edgeVec_diag p E 1
    obtain ⟨m, hm⟩ := hmod
    have r2 := even_row_edgeVec p hev 2
    rw [Fin.sum_univ_four, ← hE] at r2
    obtain ⟨r, hr⟩ := r2
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := typeEdgeVec_F2_vals
    have s01 := hsym 0 1
    have s02 := hsym 0 2
    have s03 := hsym 0 3
    have s12 := hsym 1 2
    have s13 := hsym 1 3
    have s23 := hsym 2 3
    set e := edgeVec p E 0 2 - 2 * m
    set f := edgeVec p E 2 3 - e
    set c := r - edgeVec p E 2 3 - m
    refine ⟨fun τ => if τ = {0, 0, 2} then m else if τ = {0, 0, 3} then y0 - m else
      if τ = {1, 1, 2} then c else if τ = {1, 1, 3} then y1 - c else
      if τ = {0, 2, 3} then e else if τ = {1, 2, 3} then f else 0, ?_⟩
    rw [F2_sum]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w1, w2, w3, w4, w5, w6]
    fin_cases i <;> fin_cases j <;> simp +decide <;> omega
  · have hd : degVec p E v = fun j => (degT G p v j : ℤ) := by
      funext j; exact degVec_eq_degT p G v j
    rw [hd]
    refine vertex_lattice_F2 _ (p v) (fun j hj => ?_) ?_
    · rw [degT_eq_zero_of_not_allowed hbl hj]; simp
    · have h1 := sum_degT_eq_degree G p v
      rw [Fin.sum_univ_four] at h1
      have h2 := hev v
      rw [← h1] at h2
      exact_mod_cast h2

omit [DecidableEq V] in
/-- In an Eulerian `F₂`-blowup, `E₀₀ + E₀₂ − E₀₃` is even. -/
theorem even_parity_F2 {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4}
    (hbl : ∀ u v, G.Adj u v → AllowedT F2 (p u) (p v)) (hev : ∀ v, Even (G.degree v)) :
    Even (edgeVec p G.edgeFinset 0 0 + edgeVec p G.edgeFinset 0 2 -
      edgeVec p G.edgeFinset 0 3) := by
  classical
  set E := G.edgeFinset with hE
  have hz01 : edgeVec p E 0 1 = 0 :=
    edgeVec_eq_zero_of_not_allowed hbl (by decide)
  have r0 := even_row_edgeVec p hev 0
  rw [Fin.sum_univ_four, ← hE] at r0
  obtain ⟨a0, ha0⟩ := even_edgeVec_diag p E 0
  obtain ⟨k0, hk0⟩ := r0
  exact ⟨k0 - edgeVec p E 0 3, by omega⟩

end NashWilliams18
