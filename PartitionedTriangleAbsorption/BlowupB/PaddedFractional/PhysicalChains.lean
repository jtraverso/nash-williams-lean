/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveMean
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.BoundaryIdentities
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernaryCopies
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# Real chains on physical triangles

Chains are functions on the original finite vertex sets. Their boundary is
the usual unsigned triangle-edge incidence map, with no ordering or
multiplicity convention hidden in the definition. The finite boundary
commutes with the adaptive means used to place the local gadgets.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset PaddedNibble.TypedNibble

variable {V : Type*} [DecidableEq V]

abbrev TriangleChain (V : Type*) := Finset V → ℝ

def triangleBasis (T : Finset V) : TriangleChain V := fun Q => if Q = T then 1 else 0

def edgeBasis (d : Sym2 V) : Sym2 V → ℝ := fun e => if e = d then 1 else 0

@[simp] theorem triangleBasis_self (T : Finset V) : triangleBasis T T = 1 := by
  simp only [triangleBasis, ite_true]

theorem triangleBasis_nonneg (T Q : Finset V) : 0 ≤ triangleBasis T Q := by
  unfold triangleBasis
  split_ifs <;> norm_num

@[simp] theorem abs_triangleBasis (T Q : Finset V) : |triangleBasis T Q| = triangleBasis T Q :=
  abs_of_nonneg (triangleBasis_nonneg T Q)

theorem triangleBasis_eq_zero (T Q : Finset V) (h : Q ≠ T) : triangleBasis T Q = 0 := by
  simp only [triangleBasis, h, ite_false]

variable [Fintype V]

noncomputable def boundary (z : TriangleChain V) (e : Sym2 V) : ℝ :=
  ∑ T : Finset V, z T * (if e ∈ triEdges T then 1 else 0)

@[simp] theorem boundary_zero (e : Sym2 V) : boundary (fun _ : Finset V => 0) e = 0 := by
  simp only [boundary, zero_mul, sum_const_zero]

theorem boundary_add (z w : TriangleChain V) (e : Sym2 V) :
    boundary (fun T => z T + w T) e = boundary z e + boundary w e := by
  simp only [boundary, add_mul, sum_add_distrib]

theorem boundary_neg (z : TriangleChain V) (e : Sym2 V) :
    boundary (fun T => -z T) e = -boundary z e := by
  simp only [boundary, neg_mul, sum_neg_distrib]

theorem boundary_sub (z w : TriangleChain V) (e : Sym2 V) :
    boundary (fun T => z T - w T) e = boundary z e - boundary w e := by
  simp only [boundary, sub_mul, sum_sub_distrib]

theorem boundary_smul (c : ℝ) (z : TriangleChain V) (e : Sym2 V) :
    boundary (fun T => c * z T) e = c * boundary z e := by
  simp only [boundary, mul_assoc, mul_sum]

theorem boundary_sum {ι : Type*} (s : Finset ι) (z : ι → TriangleChain V) (e : Sym2 V) :
    boundary (fun T => ∑ i ∈ s, z i T) e = ∑ i ∈ s, boundary (z i) e := by
  simp only [boundary, sum_mul]
  exact sum_comm

theorem boundary_basis (T : Finset V) (e : Sym2 V) :
    boundary (triangleBasis T) e = if e ∈ triEdges T then 1 else 0 := by
  classical
  simp only [boundary, triangleBasis, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
    ite_true]

theorem boundary_triangle_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : Sym2 V) :
    boundary (triangleBasis {a, b, c}) e =
      edgeBasis s(a, b) e + edgeBasis s(b, c) e + edgeBasis s(c, a) e := by
  calc
    _ = ∑ d ∈ triEdges ({a, b, c} : Finset V), edgeBasis d e := by
      rw [boundary_basis]
      simp [edgeBasis]
    _ = edgeBasis s(a, b) e + edgeBasis s(a, c) e + edgeBasis s(b, c) e :=
      sum_triEdges_three (fun d => edgeBasis d e) hab hac hbc
    _ = _ := by
      have hca : s(c, a) = s(a, c) := Sym2.eq_swap
      rw [hca]
      ring

theorem boundary_face {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : Sym2 V) :
    boundary (triangleBasis {a, b, c}) e =
      faceBoundary (fun u v => edgeBasis s(u, v) e) a b c :=
  boundary_triangle_three hab hac hbc e

theorem face_three_adj (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) (e : Sym2 V) :
    boundary (triangleBasis {a, b, c}) e =
      faceBoundary (fun u v => edgeBasis s(u, v) e) a b c :=
  boundary_face hab.ne hac.ne hbc.ne e

/-- The physical boundary commutes with every finite adaptive placement mean. -/
theorem boundary_mean {W : Type*} {n : ℕ} (T : ChoiceTree W n)
    (z : (Fin n → W) → TriangleChain V) (e : Sym2 V) :
    boundary (fun Q => ChoiceTree.mean T (fun f => z f Q)) e =
      ChoiceTree.mean T (fun f => boundary (z f) e) := by
  classical
  simp only [boundary, ChoiceTree.mean_sum]
  apply sum_congr rfl
  intro Q _
  simpa only [mul_comm] using
    (ChoiceTree.mean_smul T (if e ∈ triEdges Q then 1 else 0) (fun f => z f Q)).symm

variable {t : ℕ}

def CopySupported (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (z : TriangleChain V) : Prop :=
  ∀ T, ¬ IsCopy p F G T → z T = 0

omit [Fintype V] in
theorem triangleBasis_supported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) {T : Finset V} (hT : IsCopy p F G T) :
    CopySupported p F G (triangleBasis T) := by
  intro Q hQ
  exact triangleBasis_eq_zero T Q (fun h => hQ (h ▸ hT))

omit [DecidableEq V] [Fintype V] in
theorem CopySupported.add {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {z w : TriangleChain V}
    (hz : CopySupported p F G z) (hw : CopySupported p F G w) :
    CopySupported p F G (fun T => z T + w T) := by
  intro T hT
  dsimp only
  rw [hz T hT, hw T hT, zero_add]

omit [DecidableEq V] [Fintype V] in
theorem CopySupported.sub {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {z w : TriangleChain V}
    (hz : CopySupported p F G z) (hw : CopySupported p F G w) :
    CopySupported p F G (fun T => z T - w T) := by
  intro T hT
  dsimp only
  rw [hz T hT, hw T hT, sub_self]

omit [DecidableEq V] [Fintype V] in
theorem CopySupported.smul {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {z : TriangleChain V} (hz : CopySupported p F G z) (c : ℝ) :
    CopySupported p F G (fun T => c * z T) := by
  intro T hT
  dsimp only
  rw [hz T hT, mul_zero]

omit [DecidableEq V] [Fintype V] in
theorem CopySupported.sum {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {ι : Type*} (s : Finset ι) (z : ι → TriangleChain V)
    (hz : ∀ i ∈ s, CopySupported p F G (z i)) :
    CopySupported p F G (fun T => ∑ i ∈ s, z i T) := by
  intro T hT
  exact sum_eq_zero fun i hi => hz i hi T hT

omit [DecidableEq V] [Fintype V] in
theorem CopySupported.mean {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {W : Type*} {n : ℕ} (T : ChoiceTree W n)
    (z : (Fin n → W) → TriangleChain V)
    (hz : ∀ f, ChoiceTree.Supports T f → CopySupported p F G (z f)) :
    CopySupported p F G (fun Q => ChoiceTree.mean T (fun f => z f Q)) := by
  intro Q hQ
  rw [← ChoiceTree.mean_zero T]
  exact ChoiceTree.mean_congr T _ _ fun f hf => hz f hf Q hQ

/-- For chains supported on host copies, the boundary is exactly the original
typed-copy edge-load sum. -/
theorem boundary_eq_copy_load (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (hz : CopySupported p F G z)
    (e : Sym2 V) :
    boundary z e = ∑ T ∈ copies p F G with e ∈ triEdges T, z T := by
  classical
  calc
    _ = ∑ T ∈ copies p F G, z T * (if e ∈ triEdges T then 1 else 0) := by
      symm
      apply sum_subset (subset_univ _)
      intro T _ hT
      rw [hz T (fun hcopy => hT (mem_copies_iff.mpr hcopy)), zero_mul]
    _ = _ := by simp only [sum_filter, mul_ite, mul_one, mul_zero]

omit [DecidableEq V] in
theorem copies_card_le_cube (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) : (copies p F G).card ≤ Fintype.card V ^ 3 := by
  classical
  have hc : (copies p F G).card ≤ ((univ : Finset V).powersetCard 3).card :=
    card_filter_le _ _
  rw [card_powersetCard, card_univ] at hc
  exact hc.trans (Nat.choose_le_pow _ _)

theorem copies_through_card_le_square (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (v : V) :
    ((copies p F G).filter fun T => v ∈ T).card ≤ Fintype.card V ^ 2 := by
  classical
  have hc : ((copies p F G).filter fun T => v ∈ T).card ≤
      ((univ : Finset V).powersetCard 2).card := by
    apply card_le_card_of_injOn (fun T : Finset V => T.erase v)
    · intro T hT
      obtain ⟨hcopy, hv⟩ := mem_filter.mp hT
      refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
      rw [card_erase_of_mem hv, (mem_copies_iff.mp hcopy).1.card_eq]
    · intro T hT U hU heq
      dsimp only at heq
      have hvT := (mem_filter.mp hT).2
      have hvU := (mem_filter.mp hU).2
      calc
        T = insert v (T.erase v) := (insert_erase hvT).symm
        _ = insert v (U.erase v) := by rw [heq]
        _ = U := insert_erase hvU
  rw [card_powersetCard, card_univ] at hc
  exact hc.trans (Nat.choose_le_pow _ _)

/-! ## Absolute masses and exact edge incidence budgets -/

omit [Fintype V] in
theorem physical_triEdges_card {T : Finset V} (hT : T.card = 3) :
    (triEdges T).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hT
  simpa using (sum_triEdges_three (M := ℕ) (fun _ => 1) hab hac hbc)

omit [Fintype V] in
theorem physical_triangle_star_card {T : Finset V} (hT : T.card = 3) (v : V) :
    ((triEdges T).filter fun e => v ∈ e).card = if v ∈ T then 2 else 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hT
  rw [card_filter, sum_triEdges_three _ hab hac hbc]
  simp only [Sym2.mem_iff, mem_insert, mem_singleton]
  by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvc : v = c <;>
    simp_all

noncomputable def edgeMass (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (e : Sym2 V) : ℝ :=
  ∑ T ∈ copies p F G with e ∈ triEdges T, |z T|

theorem edgeMass_nonneg (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (e : Sym2 V) :
    0 ≤ edgeMass p F G z e :=
  sum_nonneg fun T _ => abs_nonneg (z T)

/-- Arbitrary edge restrictions count each triangle according to its actual
number of edges in that restriction. -/
theorem sum_edgeMass_over (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (B : Finset (Sym2 V)) :
    (∑ e ∈ B, edgeMass p F G z e) =
      ∑ T ∈ copies p F G, ((B ∩ triEdges T).card : ℝ) * |z T| := by
  classical
  simp only [edgeMass, sum_filter]
  rw [sum_comm]
  simp only [sum_ite_mem, sum_const, nsmul_eq_mul]

/-- Every physical triangle has exactly three edges. -/
theorem sum_edgeMass (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) :
    (∑ e : Sym2 V, edgeMass p F G z e) = 3 * ∑ T ∈ copies p F G, |z T| := by
  rw [sum_edgeMass_over, mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [univ_inter, physical_triEdges_card (mem_copies_iff.mp hT).1.card_eq]
  norm_num

/-- Every triangle through a fixed vertex has exactly two incident edges. -/
theorem sum_incident_edgeMass (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (v : V) :
    (∑ e ∈ univ with v ∈ e, edgeMass p F G z e) =
      2 * ∑ T ∈ copies p F G with v ∈ T, |z T| := by
  classical
  rw [sum_edgeMass_over, sum_filter, mul_sum]
  apply sum_congr rfl
  intro T hT
  have hinter : ((univ : Finset (Sym2 V)).filter fun e => v ∈ e) ∩ triEdges T =
      (triEdges T).filter (fun e => v ∈ e) := by
    ext e
    simp only [mem_inter, mem_filter, mem_univ, true_and, and_comm]
  rw [hinter, physical_triangle_star_card (mem_copies_iff.mp hT).1.card_eq]
  by_cases hv : v ∈ T <;> simp only [hv, ite_true, ite_false, Nat.cast_ofNat,
    Nat.cast_zero, mul_zero, zero_mul]

theorem abs_boundary_le_edgeMass (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (hz : CopySupported p F G z)
    (e : Sym2 V) : |boundary z e| ≤ edgeMass p F G z e := by
  rw [boundary_eq_copy_load p F G z hz]
  exact abs_sum_le_sum_abs _ _

#print axioms boundary_basis
#print axioms boundary_triangle_three
#print axioms face_three_adj
#print axioms boundary_mean
#print axioms boundary_eq_copy_load
#print axioms copies_card_le_cube
#print axioms copies_through_card_le_square
#print axioms physical_triangle_star_card
#print axioms sum_edgeMass
#print axioms sum_incident_edgeMass
#print axioms abs_boundary_le_edgeMass

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
