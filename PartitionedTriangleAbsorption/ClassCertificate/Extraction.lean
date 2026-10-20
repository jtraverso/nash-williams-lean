/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassLatticeStage65
public import PartitionedTriangleAbsorption.IntegerCertificate.Combination
public import PartitionedTriangleAbsorption.MultipartiteBoundaryStage64
public import Mathlib.Algebra.BigOperators.Fin

/-! # Extracting the structural lattice data from `IsIntDiv cls F3 P`

Let `cls : V → Fin 4` be a structural class map and `P` an edge set none of whose
edges lies inside one class. From the unchanged predicate `IsIntDiv cls F3 P` we extract:

* `degVec_swap`: the double-counting identity
  `∑ v, ∑ j, degVec cls P v j • g v j = ∑ e ∈ P, ∑ v, ∑ j, degContrib cls v e j • g v j`,
  where the edge term at `s(a, b)` is `g a (cls b) + g b (cls a)` (`sum_degContrib_mk`);
* `degVec_self_eq_zero`, `degVec_nonneg`: degree vectors vanish on the own class and are
  nonnegative;
* `sum_degVec_eq_two_mul`: every structural signed degree sum is even, from the `typeDegVec`
  equation (each F3 type has total root degree `2`);
* `edgeVec_F3_six`: all six unordered class-pair counts `m_ij = edgeVec cls P i j` (`i < j`)
  are given by four integer triangle coefficients, accounting for the ordered `pairVec`
  convention;
* `edgeVec_six_sum`: the six unordered class-pair counts add up to `|P|`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassCertificate

open Finset TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

/-! ### Double counting through `degContrib` -/

theorem degContrib_mk {t : ℕ} (cls : V → Fin t) (v a b : V) (j : Fin t) :
    degContrib cls v s(a, b) j =
      (if a = v ∧ cls b = j then 1 else 0) + (if b = v ∧ cls a = j then 1 else 0) := rfl

/-- Contribution of one edge `s(a, b)` to a degree-weighted sum. -/
theorem sum_degContrib_mk [Fintype V] {t : ℕ} {M : Type*} [AddCommGroup M] (cls : V → Fin t)
    (g : V → Fin t → M) (a b : V) :
    ∑ v, ∑ j, degContrib cls v s(a, b) j • g v j = g a (cls b) + g b (cls a) := by
  simp only [degContrib_mk, add_smul, sum_add_distrib, ite_smul, one_smul, zero_smul,
    ite_and]
  simp

/-- **Double counting.** A degree-weighted vertex sum is a sum over the edges of `P`. -/
theorem degVec_swap [Fintype V] {t : ℕ} {M : Type*} [AddCommGroup M] (cls : V → Fin t)
    (P : Finset (Sym2 V)) (g : V → Fin t → M) :
    ∑ v, ∑ j, degVec cls P v j • g v j =
      ∑ e ∈ P, ∑ v, ∑ j, degContrib cls v e j • g v j := by
  calc ∑ v, ∑ j, degVec cls P v j • g v j
        = ∑ v, ∑ j, ∑ e ∈ P, degContrib cls v e j • g v j := by
          refine sum_congr rfl fun v _ => sum_congr rfl fun j _ => ?_
          rw [degVec, Finset.sum_apply, Finset.sum_smul]
    _ = ∑ v, ∑ e ∈ P, ∑ j, degContrib cls v e j • g v j :=
          sum_congr rfl fun v _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem degContrib_nonneg {t : ℕ} (cls : V → Fin t) (v : V) (e : Sym2 V) (j : Fin t) :
    0 ≤ degContrib cls v e j := by
  induction e using Sym2.ind with
  | _ a b =>
  rw [degContrib_mk]
  split_ifs <;> norm_num

theorem degVec_nonneg {t : ℕ} (cls : V → Fin t) (P : Finset (Sym2 V)) (v : V) (j : Fin t) :
    0 ≤ degVec cls P v j := by
  simp only [degVec, Finset.sum_apply]
  exact Finset.sum_nonneg fun e _ => degContrib_nonneg cls v e j

/-- An edge between distinct classes contributes nothing to the own-class degree. -/
theorem degVec_self_eq_zero {t : ℕ} (cls : V → Fin t) (P : Finset (Sym2 V))
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (v : V) : degVec cls P v (cls v) = 0 := by
  simp only [degVec, Finset.sum_apply]
  refine Finset.sum_eq_zero fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
  have hab := hP a b he
  rw [degContrib_mk]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst ha; subst hb; exact absurd rfl hab
  · subst ha; simp [hb, Ne.symm hab]
  · subst hb; simp [ha, hab]
  · simp [ha, hb]

/-! ### Even structural degrees -/

theorem typeDegVec_sum_F3 : ∀ τ ∈ F3, ∀ a : Fin 4, ∑ i, typeDegVec τ a i = 2 := by
  intro τ hτ a
  simp only [F3, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;> fin_cases a <;>
    simp [typeDegVec, Fin.sum_univ_four]

/-- **Physical even-degree condition.** The structural signed degrees at every vertex add up
to an even number, read off from the `typeDegVec` lattice equation of `IsIntDiv cls F3 P`. -/
theorem sum_degVec_eq_two_mul {cls : V → Fin 4} {P : Finset (Sym2 V)}
    (h : IsIntDiv cls F3 P) (v : V) : ∃ s : ℤ, ∑ j, degVec cls P v j = 2 * s := by
  obtain ⟨c, hc⟩ := h.2 v
  refine ⟨∑ τ ∈ F3 with cls v ∈ τ, c τ, ?_⟩
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [← Finset.mul_sum, typeDegVec_sum_F3 τ (mem_filter.mp hτ).1, mul_comm]

/-! ### The six unordered class-pair equations -/

/-- Evaluation of the F3 edge lattice at the six unordered class pairs. -/
theorem F3_edge_lattice_eval (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ F3, c τ • typeEdgeVec τ) 0 1 = c {0, 1, 2} + c {0, 1, 3} ∧
    (∑ τ ∈ F3, c τ • typeEdgeVec τ) 0 2 = c {0, 1, 2} + c {0, 2, 3} ∧
    (∑ τ ∈ F3, c τ • typeEdgeVec τ) 0 3 = c {0, 1, 3} + c {0, 2, 3} ∧
    (∑ τ ∈ F3, c τ • typeEdgeVec τ) 1 2 = c {0, 1, 2} + c {1, 2, 3} ∧
    (∑ τ ∈ F3, c τ • typeEdgeVec τ) 1 3 = c {0, 1, 3} + c {1, 2, 3} ∧
    (∑ τ ∈ F3, c τ • typeEdgeVec τ) 2 3 = c {0, 2, 3} + c {1, 2, 3} := by
  have h1 : ({0, 1, 2} : Multiset (Fin 4)) ∉ ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} :
      Finset (Multiset (Fin 4))) := by decide
  have h2 : ({0, 1, 3} : Multiset (Fin 4)) ∉ ({{0, 2, 3}, {1, 2, 3}} :
      Finset (Multiset (Fin 4))) := by decide
  have h3 : ({0, 2, 3} : Multiset (Fin 4)) ∉ ({{1, 2, 3}} :
      Finset (Multiset (Fin 4))) := by decide
  simp only [F3, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton, Pi.add_apply, Pi.smul_apply, smul_eq_mul, typeEdgeVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- **All six unordered class-pair equations** extracted from `IsIntDiv cls F3 P`. -/
theorem edgeVec_F3_six {cls : V → Fin 4} {P : Finset (Sym2 V)} (h : IsIntDiv cls F3 P) :
    ∃ a b c d : ℤ,
      edgeVec cls P 0 1 = a + b ∧ edgeVec cls P 0 2 = a + c ∧ edgeVec cls P 0 3 = b + c ∧
      edgeVec cls P 1 2 = a + d ∧ edgeVec cls P 1 3 = b + d ∧ edgeVec cls P 2 3 = c + d := by
  obtain ⟨c, hc⟩ := h.1
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := F3_edge_lattice_eval c
  exact ⟨c {0, 1, 2}, c {0, 1, 3}, c {0, 2, 3}, c {1, 2, 3}, hc ▸ h01, hc ▸ h02, hc ▸ h03,
    hc ▸ h12, hc ▸ h13, hc ▸ h23⟩

/-! ### Distributing a cross-class edge over the six unordered pairs -/

/-- The six-term sum over unordered class pairs `i < j`. -/
def six {M : Type*} [AddCommMonoid M] (g : Fin 4 → Fin 4 → M) : M :=
  g 0 1 + g 0 2 + g 0 3 + g 1 2 + g 1 3 + g 2 3

/-- One ordered-pair contribution `pairVec` of a cross-class pair `(x, y)`, spread over the six
unordered pairs, picks out exactly `g x y`. -/
theorem six_pair {M : Type*} [AddCommGroup M] (g : Fin 4 → Fin 4 → M)
    (hg : ∀ i j, g i j = g j i) (x y : Fin 4) (hxy : x ≠ y) :
    six (fun i j => ((if x = i ∧ y = j then (1 : ℤ) else 0) +
      (if y = i ∧ x = j then 1 else 0)) • g i j) = g x y := by
  fin_cases x <;> fin_cases y <;> simp_all [six, hg 1 0, hg 2 0, hg 3 0, hg 2 1, hg 3 1, hg 3 2]

omit [DecidableEq V] in
/-- The ordered edge vector, read along the six unordered class pairs. -/
theorem six_edgeVec {M : Type*} [AddCommGroup M] (cls : V → Fin 4) (P : Finset (Sym2 V))
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) (g : Fin 4 → Fin 4 → M)
    (hg : ∀ i j, g i j = g j i) :
    six (fun i j => edgeVec cls P i j • g i j) =
      ∑ e ∈ P, Sym2.lift ⟨fun a b => g (cls a) (cls b), fun _ _ => hg _ _⟩ e := by
  have key : ∀ e ∈ P, six (fun i j => pairVec cls e i j • g i j) =
      Sym2.lift ⟨fun a b => g (cls a) (cls b), fun _ _ => hg _ _⟩ e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
    exact six_pair g hg (cls a) (cls b) (hP a b he)
  rw [← Finset.sum_congr rfl key]
  simp only [six, edgeVec, Finset.sum_apply, Finset.sum_smul, Finset.sum_add_distrib]

omit [DecidableEq V] in
/-- The six unordered class-pair counts add up to `|P|`. -/
theorem edgeVec_six_sum (cls : V → Fin 4) (P : Finset (Sym2 V))
    (hP : ∀ a b, s(a, b) ∈ P → cls a ≠ cls b) :
    six (edgeVec cls P) = P.card := by
  have h := six_edgeVec cls P hP (fun _ _ => (1 : ℤ)) (fun _ _ => rfl)
  have hone : ∀ e : Sym2 V, Sym2.lift ⟨fun (_ _ : V) => (1 : ℤ), fun _ _ => rfl⟩ e = 1 := by
    intro e; induction e using Sym2.ind with | _ a b => rfl
  simp only [smul_eq_mul, mul_one, hone, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

omit [DecidableEq V] in
theorem edgeVec_nonneg {t : ℕ} (cls : V → Fin t) (P : Finset (Sym2 V)) (i j : Fin t) :
    0 ≤ edgeVec cls P i j := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.sum_nonneg fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
  simp only [pairVec, Sym2.lift_mk]
  split_ifs <;> norm_num

end PartitionedTriangleAbsorption.ClassCertificate
