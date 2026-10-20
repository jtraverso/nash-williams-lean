/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Families
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval

/-! # BlowupB.Cost — ℓ¹ norms, entry bounds, bounded lattice representations

* `l1 w = ∑ e, |w e|`, subadditive, homogeneous; `l1 (indZ E) = |E|`; a certificate of cost `K`
  has `l1 ≤ 3K` (`l1_le_of_physCostZ`);
* the entries of edge-count and degree vectors are bounded by `2 · l1`
  (`abs_edgeVecZ_le`, `sum_abs_degVecZ_le`);
* `exists_rep_bound`: on a finite set of lattice vectors (a box) representations of bounded
  cost can be chosen uniformly. With `boxVec`, `boxMat` this gives constants depending only on the
  family and on the size bound, never on the host.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### ℓ¹ norm -/

/-- The ℓ¹ norm of an integer edge function. -/
def l1 (w : Sym2 V → ℤ) : ℤ := ∑ e, |w e|

omit [DecidableEq V] in
theorem l1_nonneg (w : Sym2 V → ℤ) : 0 ≤ l1 w := sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq V] in
theorem l1_zero : l1 (0 : Sym2 V → ℤ) = 0 := by simp [l1]

omit [DecidableEq V] in
theorem l1_add_le (w₁ w₂ : Sym2 V → ℤ) : l1 (w₁ + w₂) ≤ l1 w₁ + l1 w₂ := by
  unfold l1
  rw [← sum_add_distrib]
  exact sum_le_sum fun e _ => abs_add_le _ _

omit [DecidableEq V] in
theorem l1_neg (w : Sym2 V → ℤ) : l1 (-w) = l1 w := by simp [l1]

theorem l1_sub_le (w₁ w₂ : Sym2 V → ℤ) : l1 (w₁ - w₂) ≤ l1 w₁ + l1 w₂ := by
  rw [sub_eq_add_neg, ← l1_neg w₂]; exact l1_add_le _ _

omit [DecidableEq V] in
theorem l1_smul (a : ℤ) (w : Sym2 V → ℤ) : l1 (a • w) = |a| * l1 w := by
  simp only [l1, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (l1_add_le _ _).trans (add_le_add le_rfl ih)

theorem l1_indZ (E : Finset (Sym2 V)) : l1 (indZ E) = E.card := by
  unfold l1 indZ
  have h : ∀ e, |(if e ∈ E then (1 : ℤ) else 0)| = if e ∈ E then 1 else 0 := fun e => by
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, univ_inter]

omit [Fintype V] in
theorem card_triEdges_le {s : Finset V} (hs : s.card = 3) : (triEdges s).card ≤ 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  rw [triEdges_three hab hac hbc]
  exact card_le_three

theorem l1_triEdges_le {s : Finset V} (hs : s.card = 3) : l1 (indZ (triEdges s)) ≤ 3 := by
  rw [l1_indZ]
  exact_mod_cast card_triEdges_le hs

/-- A certificate of cost `K` has ℓ¹ norm at most `3K`. -/
theorem l1_le_of_physCostZ {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) : l1 w ≤ 3 * K := by
  obtain ⟨ι, hι, T, c, ⟨hT, hw⟩, hK⟩ := h
  have hw' : w = ∑ j, c j • indZ (triEdges (T j)) := by
    funext e
    rw [hw e, Finset.sum_apply]
    exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]
  rw [hw']
  calc l1 (∑ j, c j • indZ (triEdges (T j))) ≤ ∑ j, l1 (c j • indZ (triEdges (T j))) :=
        l1_sum_le _ _
    _ = ∑ j, |c j| * l1 (indZ (triEdges (T j))) := sum_congr rfl fun j _ => l1_smul _ _
    _ ≤ ∑ j, |c j| * 3 := sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (l1_triEdges_le (hT j).1.card_eq) (abs_nonneg _)
    _ = 3 * ∑ j, |c j| := by rw [mul_sum]; exact sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ 3 * K := by linarith

/-! ### Entry bounds -/

omit [Fintype V] [DecidableEq V] in
theorem pairVec_nonneg (p : V → Fin t) (e : Sym2 V) (i j : Fin t) : 0 ≤ pairVec p e i j := by
  induction e using Sym2.ind with
  | _ a b => simp only [pairVec, Sym2.lift_mk]; split_ifs <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem pairVec_le_two (p : V → Fin t) (e : Sym2 V) (i j : Fin t) : pairVec p e i j ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b => simp only [pairVec, Sym2.lift_mk]; split_ifs <;> norm_num

omit [Fintype V] in
theorem degContrib_nonneg (p : V → Fin t) (v : V) (e : Sym2 V) (j : Fin t) :
    0 ≤ degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b => simp only [degContrib, Sym2.lift_mk]; split_ifs <;> norm_num

theorem sum_sum_ite_and_eq_one {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α]
    [DecidableEq γ] (a : α) (b : γ) :
    ∑ x, ∑ k, (if a = x ∧ b = k then (1 : ℤ) else 0) = 1 := by
  have := sum_sum_ite_pair' a b (fun (_ : α) (_ : γ) => (1 : ℤ))
  simpa using this

theorem sum_sum_degContrib (p : V → Fin t) (e : Sym2 V) :
    ∑ v, ∑ j, degContrib p v e j = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk, sum_add_distrib]
    rw [sum_sum_ite_and_eq_one, sum_sum_ite_and_eq_one]
    norm_num

omit [DecidableEq V] in
theorem abs_edgeVecZ_le (p : V → Fin t) (w : Sym2 V → ℤ) (i j : Fin t) :
    |edgeVecZ p w i j| ≤ 2 * l1 w := by
  rw [edgeVecZ_apply]
  calc |∑ e, w e * pairVec p e i j| ≤ ∑ e, |w e * pairVec p e i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |w e| * 2 := sum_le_sum fun e _ => by
        rw [abs_mul, abs_of_nonneg (pairVec_nonneg p e i j)]
        exact mul_le_mul_of_nonneg_left (pairVec_le_two p e i j) (abs_nonneg _)
    _ = 2 * l1 w := by rw [l1, mul_sum]; exact sum_congr rfl fun e _ => mul_comm _ _

theorem sum_abs_degVecZ_le (p : V → Fin t) (w : Sym2 V → ℤ) :
    ∑ v, ∑ j, |degVecZ p w v j| ≤ 2 * l1 w := by
  have hv : ∀ v, ∑ j, |degVecZ p w v j| ≤ ∑ e, |w e| * ∑ j, degContrib p v e j := by
    intro v
    calc ∑ j, |degVecZ p w v j| ≤ ∑ j, ∑ e, |w e| * degContrib p v e j := by
          refine sum_le_sum fun j _ => ?_
          rw [degVecZ_apply]
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun e _ => ?_))
          rw [abs_mul, abs_of_nonneg (degContrib_nonneg p v e j)]
      _ = ∑ e, |w e| * ∑ j, degContrib p v e j := by
          rw [sum_comm]; exact sum_congr rfl fun e _ => by rw [mul_sum]
  calc ∑ v, ∑ j, |degVecZ p w v j| ≤ ∑ v, ∑ e, |w e| * ∑ j, degContrib p v e j :=
        sum_le_sum fun v _ => hv v
    _ = ∑ e, |w e| * ∑ v, ∑ j, degContrib p v e j := by
        rw [sum_comm]; exact sum_congr rfl fun e _ => by rw [mul_sum]
    _ = 2 * l1 w := by
        simp_rw [sum_sum_degContrib]
        rw [l1, mul_sum]
        exact sum_congr rfl fun e _ => mul_comm _ _

theorem abs_degVecZ_le (p : V → Fin t) (w : Sym2 V → ℤ) (v : V) (j : Fin t) :
    |degVecZ p w v j| ≤ 2 * l1 w := by
  have h1 : |degVecZ p w v j| ≤ ∑ k, |degVecZ p w v k| :=
    single_le_sum (f := fun k => |degVecZ p w v k|) (fun _ _ => abs_nonneg _) (mem_univ j)
  have h2 : ∑ k, |degVecZ p w v k| ≤ ∑ x, ∑ k, |degVecZ p w x k| :=
    single_le_sum (f := fun x => ∑ k, |degVecZ p w x k|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ v)
  exact h1.trans (h2.trans (sum_abs_degVecZ_le p w))

omit [Fintype V] in
theorem degContrib_eq_zero_of_not_mem (p : V → Fin t) {v : V} {e : Sym2 V} (h : v ∉ e) :
    degContrib p v e = 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ v := fun hh => h (by rw [← hh]; exact Sym2.mem_mk_left a b)
    have hb : b ≠ v := fun hh => h (by rw [← hh]; exact Sym2.mem_mk_right a b)
    funext j
    simp [degContrib, ha, hb]

theorem exists_of_degVecZ_ne_zero {p : V → Fin t} {w : Sym2 V → ℤ} {v : V}
    (h : degVecZ p w v ≠ 0) : ∃ e, w e ≠ 0 ∧ v ∈ e := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  apply h
  unfold degVecZ
  refine sum_eq_zero fun e _ => ?_
  by_cases hwe : w e = 0
  · rw [hwe, zero_smul]
  · rw [degContrib_eq_zero_of_not_mem p (hc e hwe), smul_zero]

theorem one_le_sum_abs_of_ne_zero {x : Fin t → ℤ} (h : x ≠ 0) : 1 ≤ ∑ j, |x j| := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have h1 : 1 ≤ |x j| := Int.one_le_abs hj
  exact h1.trans (single_le_sum (f := fun k => |x k|) (fun _ _ => abs_nonneg _) (mem_univ j))

/-! ### Bounded representations on finite sets -/

open Classical in
/-- The cost of a chosen representation of `x` (or `0` if there is none). -/
noncomputable def repCost {M ι : Type*} [AddCommMonoid M] [SMul ℤ M] (s : Finset ι)
    (g : ι → M) (x : M) : ℤ :=
  if h : ∃ c : ι → ℤ, x = ∑ i ∈ s, c i • g i then ∑ i ∈ s, |h.choose i| else 0

theorem repCost_nonneg {M ι : Type*} [AddCommMonoid M] [SMul ℤ M] (s : Finset ι) (g : ι → M)
    (x : M) : 0 ≤ repCost s g x := by
  unfold repCost
  split_ifs
  · exact sum_nonneg fun _ _ => abs_nonneg _
  · exact le_refl 0

/-- **Uniform bounded representations.** For a finite set `X` of vectors, representations in the
lattice spanned by `g` can be chosen with cost bounded by a single constant. -/
theorem exists_rep_bound {M ι : Type*} [AddCommMonoid M] [SMul ℤ M] (s : Finset ι) (g : ι → M)
    (X : Finset M) : ∃ C : ℤ, 0 ≤ C ∧ ∀ x ∈ X, (∃ c : ι → ℤ, x = ∑ i ∈ s, c i • g i) →
      ∃ c : ι → ℤ, x = ∑ i ∈ s, c i • g i ∧ ∑ i ∈ s, |c i| ≤ C := by
  classical
  refine ⟨∑ x ∈ X, repCost s g x, sum_nonneg fun x _ => repCost_nonneg s g x,
    fun x hx h => ⟨h.choose, h.choose_spec, ?_⟩⟩
  have hx' : repCost s g x = ∑ i ∈ s, |h.choose i| := by
    unfold repCost; rw [dif_pos h]
  rw [← hx']
  exact single_le_sum (fun y _ => repCost_nonneg s g y) hx

/-- The box of integer vectors with entries in `[-B, B]`. -/
def boxVec {t : ℕ} (B : ℤ) : Finset (Fin t → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-B) B

theorem mem_boxVec {t : ℕ} {B : ℤ} {x : Fin t → ℤ} : x ∈ boxVec B ↔ ∀ j, |x j| ≤ B := by
  simp only [boxVec, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- The box of integer matrices with entries in `[-B, B]`. -/
def boxMat {t : ℕ} (B : ℤ) : Finset (Fin t → Fin t → ℤ) := Fintype.piFinset fun _ => boxVec B

theorem mem_boxMat {t : ℕ} {B : ℤ} {x : Fin t → Fin t → ℤ} :
    x ∈ boxMat B ↔ ∀ i j, |x i j| ≤ B := by
  simp only [boxMat, Fintype.mem_piFinset, mem_boxVec]

end PartitionedTriangleAbsorption.BlowupB
