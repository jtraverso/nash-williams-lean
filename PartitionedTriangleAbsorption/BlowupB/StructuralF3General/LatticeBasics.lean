/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPieceConditions
public import PartitionedTriangleAbsorption.TypedRefinerCharge

/-! Elementary identities extracted from the supplied ClassCertificate and TypedLoad files; no near-consumer imports. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.LatticeBasics

open Finset TypedApplicationLinks

theorem edgeVec_symm {V : Type*} {t : ℕ} (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = edgeVec p E j i := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    rw [add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl

section Counting
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem pairVec_eq_sum_degContrib (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    pairVec p e i j = ∑ v ∈ univ.filter (fun v => p v = i), degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, degContrib, Sym2.lift_mk, Finset.sum_add_distrib]
    rw [Finset.sum_filter, Finset.sum_filter]
    simp only [← ite_and]
    congr 1
    · rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    · rw [Finset.sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp

/-- Ordered edge counts from degree vectors. -/
theorem edgeVec_eq_sum_degVec (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = ∑ v ∈ univ.filter (fun v => p v = i), degVec p E v j := by
  simp only [edgeVec, degVec, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => pairVec_eq_sum_degContrib p e i j

end Counting

variable {V : Type*} [DecidableEq V]

/-- A third class distinct from two given classes. -/
def third (i j : Fin 4) : Fin 4 :=
  if 0 ≠ i ∧ 0 ≠ j then 0 else if 1 ≠ i ∧ 1 ≠ j then 1 else 2

theorem third_ne : ∀ i j : Fin 4, i ≠ j → third i j ≠ i ∧ third i j ≠ j := by decide

theorem distinct_mem_F3 : ∀ x y z : Fin 4, x ≠ y → x ≠ z → y ≠ z →
    ({x, y, z} : Multiset (Fin 4)) ∈ F3 := by decide

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


#print axioms edgeVec_eq_sum_degVec
#print axioms edgeVec_six_sum

end PartitionedTriangleAbsorption.StructuralF3General.LatticeBasics
