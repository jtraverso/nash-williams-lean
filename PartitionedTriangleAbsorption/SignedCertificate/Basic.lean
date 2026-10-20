/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Signed physical F0 triangle certificates

A *signed physical certificate* for an edge set `P` is a finite family of actual F0
triangles `t j` of the host `G` (three distinct vertices, all three edges in `G`, type
`001` or `011`) and integer coefficients `c j`, such that for **every** `e : Sym2 V`

  `[e ∈ P] = ∑ j, c j * [e ∈ triEdges (t j)]`.

Negative coefficients are allowed. This module proves the prerequisites requested in
Stage 49 by exchanging finite sums:

* `sum_eq_of_cert`: `∑_{e ∈ P} f e = ∑ j, c j * ∑_{e ∈ t j} f e` for every `f`;
* `charge_zero_of_cert`: every triangle-annihilating integer charge vanishes on `P`;
* `card_eq_of_cert`: `|P| = 3 ∑ j c j`, so `3 ∣ |P|`;
* `pairCount00_of_cert`, `pairCount11_of_cert`, `pairCount01_of_cert`: the signed total of
  type-`001` triangles equals the (nonnegative, physical) number of `00` edges of `P`,
  similarly `011`/`11`, and the number of `01` edges is `2 ∑ j c j`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

variable {V : Type*} [Finite V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- Integer indicator of an edge set. -/
def ind (S : Finset (Sym2 V)) (e : Sym2 V) : ℤ := if e ∈ S then 1 else 0

/-- **Signed physical F0 certificate** for `P`: actual F0 triangles of `G` with integer
coefficients whose signed edge-indicator sum is the indicator of `P`, at every `e`. -/
def IsSignedCert (p : V → Fin 2) (G : SimpleGraph V) (P : Finset (Sym2 V))
    (t : ι → Finset V) (c : ι → ℤ) : Prop :=
  (∀ j, IsCopy p F0 G (t j)) ∧ ∀ e : Sym2 V, ind P e = ∑ j, c j * ind (triEdges (t j)) e

/-- The size `∑ j |c j|` of a certificate. -/
def certWeight (c : ι → ℤ) : ℤ := ∑ j, |c j|

/-- Number of edges of `E` whose endpoint parts are `{a, b}`. -/
def pairCount (p : V → Fin 2) (E : Finset (Sym2 V)) (a b : Fin 2) : ℕ :=
  (E.filter fun e => e.map p = s(a, b)).card

/-- Signed number of certificate triangles of part-type `τ`. -/
def signedType (p : V → Fin 2) (t : ι → Finset V) (c : ι → ℤ) (τ : Multiset (Fin 2)) : ℤ :=
  ∑ j, c j * (if (t j).val.map p = τ then 1 else 0)

omit [Finite V] in
theorem sum_eq_sum_ind (S : Finset (Sym2 V)) (f : Sym2 V → ℤ) [Fintype (Sym2 V)] :
    ∑ e ∈ S, f e = ∑ e, f e * ind S e := by
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Exchange of finite sums.** For every integer edge function `f`,
`∑_{e ∈ P} f e = ∑ j, c j * ∑_{e ∈ triEdges (t j)} f e`. -/
theorem sum_eq_of_cert {P : Finset (Sym2 V)} {t : ι → Finset V} {c : ι → ℤ}
    (hc : ∀ e : Sym2 V, ind P e = ∑ j, c j * ind (triEdges (t j)) e) (f : Sym2 V → ℤ) :
    ∑ e ∈ P, f e = ∑ j, c j * ∑ e ∈ triEdges (t j), f e := by
  classical
  let := Fintype.ofFinite V
  rw [sum_eq_sum_ind P f]
  calc ∑ e, f e * ind P e = ∑ e, ∑ j, c j * (f e * ind (triEdges (t j)) e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hc e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, ∑ e, c j * (f e * ind (triEdges (t j)) e) := Finset.sum_comm
    _ = ∑ j, c j * ∑ e ∈ triEdges (t j), f e := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_eq_sum_ind (triEdges (t j)) f, Finset.mul_sum]

/-- **Annihilating charges vanish.** If an integer charge `χ` sums to zero on every
certificate triangle, then it sums to zero on `P`. In particular this holds for every
charge annihilating all F0 triangles of `G`. -/
theorem charge_zero_of_cert {P : Finset (Sym2 V)} {t : ι → Finset V} {c : ι → ℤ}
    (hc : ∀ e : Sym2 V, ind P e = ∑ j, c j * ind (triEdges (t j)) e) (χ : Sym2 V → ℤ)
    (hχ : ∀ j, ∑ e ∈ triEdges (t j), χ e = 0) : ∑ e ∈ P, χ e = 0 := by
  rw [sum_eq_of_cert hc χ]
  simp [hχ]

/-- Version of `charge_zero_of_cert` for charges annihilating every F0 copy of `G`. -/
theorem charge_zero (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) (χ : Sym2 V → ℤ)
    (hχ : ∀ s, IsCopy p F0 G s → ∑ e ∈ triEdges s, χ e = 0) : ∑ e ∈ P, χ e = 0 :=
  charge_zero_of_cert h.2 χ fun j => hχ _ (h.1 j)

omit [Finite V] [DecidableEq V] in
theorem card_three_of_isCopy {p : V → Fin 2} {G : SimpleGraph V} {s : Finset V}
    (h : IsCopy p F0 G s) : s.card = 3 := h.1.card_eq

/-- The finite check behind `tri_counts`, over the part labels only. -/
theorem fin2_counts : ∀ x y z : Fin 2, ({x, y, z} : Multiset (Fin 2)) ∈ F0 →
    ((if s(x, y) = s(0, 0) then 1 else 0) + (if s(x, z) = s(0, 0) then 1 else 0) +
        (if s(y, z) = s(0, 0) then 1 else 0) : ℤ) =
        (if ({x, y, z} : Multiset (Fin 2)) = {0, 0, 1} then 1 else 0) ∧
    ((if s(x, y) = s(1, 1) then 1 else 0) + (if s(x, z) = s(1, 1) then 1 else 0) +
        (if s(y, z) = s(1, 1) then 1 else 0) : ℤ) =
        (if ({x, y, z} : Multiset (Fin 2)) = {0, 1, 1} then 1 else 0) ∧
    ((if s(x, y) = s(0, 1) then 1 else 0) + (if s(x, z) = s(0, 1) then 1 else 0) +
        (if s(y, z) = s(0, 1) then 1 else 0) : ℤ) = 2 := by
  decide

omit [Finite V] in
/-- Triangle-level edge-type counts for an F0 triangle. -/
theorem tri_counts (p : V → Fin 2) {s : Finset V} (hs : s.card = 3) (hF : s.val.map p ∈ F0) :
    ((pairCount p (triEdges s) 0 0 : ℤ) = if s.val.map p = {0, 0, 1} then 1 else 0) ∧
    ((pairCount p (triEdges s) 1 1 : ℤ) = if s.val.map p = {0, 1, 1} then 1 else 0) ∧
    ((pairCount p (triEdges s) 0 1 : ℤ) = 2) ∧ (triEdges s).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have key : ∀ x y : Fin 2, ∀ E : Finset (Sym2 V),
      ((pairCount p E x y : ℕ) : ℤ) = ∑ e ∈ E, (if e.map p = s(x, y) then 1 else 0) := by
    intro x y E
    rw [pairCount, Finset.card_filter]
    push_cast
    rfl
  rw [key, key, key, sum_triEdges_three _ hab hac hbc, sum_triEdges_three _ hab hac hbc,
    sum_triEdges_three _ hab hac hbc]
  rw [map_three p hab hac hbc] at hF ⊢
  have hcard : (triEdges ({a, b, c} : Finset V)).card = 3 := by
    have := sum_triEdges_three (M := ℕ) (fun _ => 1) hab hac hbc
    simpa using this
  have h := fin2_counts (p a) (p b) (p c) hF
  simp only [Sym2.map_mk]
  exact ⟨h.1, h.2.1, h.2.2, hcard⟩

/-- **`|P| = 3 ∑ j c j`.** Hence `|P|` is a multiple of three and `∑ j c j ≥ 0`. -/
theorem card_eq_of_cert (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) :
    (P.card : ℤ) = 3 * ∑ j, c j := by
  have := sum_eq_of_cert h.2 (fun _ => 1)
  simp only [sum_const, nsmul_eq_mul, mul_one] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 := (tri_counts p (card_three_of_isCopy (h.1 j)) (h.1 j).2).2.2.2
  rw [h3]; push_cast; ring

theorem three_dvd_card (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) : 3 ∣ P.card := by
  have := card_eq_of_cert p G h
  exact_mod_cast (show (3 : ℤ) ∣ P.card from ⟨_, this⟩)

theorem pairCount_of_cert (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) (a b : Fin 2) :
    (pairCount p P a b : ℤ) = ∑ j, c j * (pairCount p (triEdges (t j)) a b : ℤ) := by
  have key : ∀ E : Finset (Sym2 V),
      ((pairCount p E a b : ℕ) : ℤ) = ∑ e ∈ E, (if e.map p = s(a, b) then 1 else 0) := by
    intro E
    rw [pairCount, Finset.card_filter]
    push_cast
    rfl
  rw [key, sum_eq_of_cert h.2]
  simp_rw [key]

/-- **`00` edges.** The signed number of type-`001` certificate triangles equals the
physical number of `00` edges of `P` (a nonnegative count). -/
theorem pairCount00_of_cert (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) :
    (pairCount p P 0 0 : ℤ) = signedType p t c {0, 0, 1} := by
  rw [pairCount_of_cert p G h, signedType]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(tri_counts p (card_three_of_isCopy (h.1 j)) (h.1 j).2).1]

/-- **`11` edges.** The signed number of type-`011` certificate triangles equals the
physical number of `11` edges of `P`. -/
theorem pairCount11_of_cert (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) :
    (pairCount p P 1 1 : ℤ) = signedType p t c {0, 1, 1} := by
  rw [pairCount_of_cert p G h, signedType]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(tri_counts p (card_three_of_isCopy (h.1 j)) (h.1 j).2).2.1]

/-- **`01` edges.** The number of cross edges of `P` is `2 ∑ j c j`. -/
theorem pairCount01_of_cert (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) :
    (pairCount p P 0 1 : ℤ) = 2 * ∑ j, c j := by
  rw [pairCount_of_cert p G h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(tri_counts p (card_three_of_isCopy (h.1 j)) (h.1 j).2).2.2.1]; ring

/-- The coarse F0 charge `2(e₀₀ + e₁₁) - e₀₁` of a certified source is zero. -/
theorem coarse_charge_of_cert (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (h : IsSignedCert p G P t c) :
    2 * ((pairCount p P 0 0 : ℤ) + pairCount p P 1 1) - pairCount p P 0 1 = 0 := by
  rw [pairCount00_of_cert p G h, pairCount11_of_cert p G h, pairCount01_of_cert p G h,
    signedType, signedType, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hF := (h.1 j).2
  simp only [F0, Finset.mem_insert, Finset.mem_singleton] at hF
  rcases hF with hF | hF <;> rw [hF] <;> simp

end PartitionedTriangleAbsorption.SignedCertificate
