/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBridge
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! # Count physical hinges with fixed roots

The count is over edge sets, not only their vertex supports. Diagonal edges
are allowed in the counting upper bound, so the bound is deliberately loose.
No absorption theorem or corrected abundance assumption is introduced.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalHinge

variable {V : Type*} [DecidableEq V]

theorem edges_subset_support_sym2 (H : Finset (Sym2 V)) : H ⊆ (support H).sym2 := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    apply Finset.mk_mem_sym2_iff.mpr
    constructor <;> apply Finset.mem_biUnion.mpr <;>
      exact ⟨s(u, v), he, by simp [Sym2.mem_toFinset, Sym2.mem_iff]⟩

/-- There are at most `2 ^ choose (|S| + 1) 2` edge sets with support `S`.
This includes loops in the upper bound; physical simple graphs only decrease it. -/
theorem support_fiber_card_le (K : Finset (Finset (Sym2 V))) (S : Finset V) :
    (K.filter (fun H => support H = S)).card ≤ 2 ^ Nat.choose (S.card + 1) 2 := by
  have hsub : K.filter (fun H => support H = S) ⊆ S.sym2.powerset := by
    intro H hH
    have he := edges_subset_support_sym2 H
    rw [(Finset.mem_filter.mp hH).2] at he
    exact Finset.mem_powerset.mpr he
  simpa only [Finset.card_powerset, Finset.card_sym2] using Finset.card_le_card hsub

/-- Universal edge-set count with prescribed roots and fixed support order. -/
theorem rooted_edge_sets_card_le [Fintype V] (K : Finset (Finset (Sym2 V)))
    (R : Finset V) (i : ℕ) (hi : R.card ≤ i)
    (hroot : ∀ H ∈ K, R ⊆ support H)
    (horder : ∀ H ∈ K, (support H).card = i) :
    K.card ≤ Nat.choose (Fintype.card V - R.card) (i - R.card) *
      2 ^ Nat.choose (i + 1) 2 := by
  let Q := ((Finset.univ : Finset V).powersetCard i).filter (R ⊆ ·)
  have hmaps : (K : Set (Finset (Sym2 V))).MapsTo support Q := by
    intro H hH
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, horder H hH⟩, hroot H hH⟩
  have hQ : Q.card = Nat.choose (Fintype.card V - R.card) (i - R.card) := by
    simpa only [Q, Finset.card_univ] using
      Finset.card_filter_powersetCard_subset R Finset.univ i (Finset.subset_univ _) hi
  calc
    K.card = ∑ S ∈ Q, (K.filter (fun H => support H = S)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _S ∈ Q, 2 ^ Nat.choose (i + 1) 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
      simpa only [hcard] using support_fiber_card_le K S
    _ = Q.card * 2 ^ Nat.choose (i + 1) 2 := by simp
    _ = _ := by rw [hQ]

end PartitionedTriangleAbsorption.PhysicalHinge

namespace PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem vertSet_eq_support (H : Finset (Sym2 V)) : vertSet H = PhysicalHinge.support H := by
  ext v
  simp [vertSet, PhysicalHinge.support, Sym2.mem_toFinset]

open Classical in
/-- Actual hinge edge-set count for the unchanged Aristotle/source predicate. -/
theorem hinge_count_le (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (E : Finset (Sym2 V)) (u v w z : V) (i : ℕ)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) (hi : 4 ≤ i) :
    ((E.powerset.filter (fun H => IsHinge p F {u, v, w} {u, v, z} H ∧
      (vertSet H).card = i)).card) ≤
      Nat.choose (Fintype.card V - 4) (i - 4) * 2 ^ Nat.choose (i + 1) 2 := by
  classical
  have hcard : ({u, v, w, z} : Finset V).card = 4 := by
    simp [huv, huw, huz, hvw, hvz, hwz]
  apply (show _ ≤ _ from PhysicalHinge.rooted_edge_sets_card_le
    (E.powerset.filter (fun H => IsHinge p F {u, v, w} {u, v, z} H ∧
      (vertSet H).card = i)) {u, v, w, z} i (by simpa only [hcard] using hi) ?_ ?_)
      |>.trans_eq (by rw [hcard])
  · intro H hH
    exact IsHinge.four_roots H u v w z huv huw huz hvw hvz hwz
      (Finset.mem_filter.mp hH).2.1
  · intro H hH
    rw [← vertSet_eq_support]
    exact (Finset.mem_filter.mp hH).2.2

open Classical in
/-- Polynomial upper bound: four roots, hence at most `i - 4` free choices. -/
theorem hinge_count_le_pow (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (E : Finset (Sym2 V)) (u v w z : V) (i : ℕ)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) (hi : 4 ≤ i) :
    ((E.powerset.filter (fun H => IsHinge p F {u, v, w} {u, v, z} H ∧
      (vertSet H).card = i)).card) ≤
      2 ^ Nat.choose (i + 1) 2 * Fintype.card V ^ (i - 4) := by
  have hc := hinge_count_le p F E u v w z i huv huw huz hvw hvz hwz hi
  have hp : Nat.choose (Fintype.card V - 4) (i - 4) ≤ Fintype.card V ^ (i - 4) :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  exact hc.trans (by simpa only [Nat.mul_comm] using
    (Nat.mul_le_mul_right (2 ^ Nat.choose (i + 1) 2) hp))

/-- The arithmetic contradiction caused by requiring two additional powers of `n`.
The combinatorial upper bound is proved above, rather than assumed by this lemma. -/
theorem scaling_gap (α n B : ℝ) (m : ℕ) (hn : 0 < n) (hB : B < α * n ^ 2) :
    B * n ^ m < α * n ^ (m + 2) := by
  calc
    B * n ^ m < (α * n ^ 2) * n ^ m :=
      mul_lt_mul_of_pos_right hB (pow_pos hn m)
    _ = α * n ^ (m + 2) := by rw [pow_add]; ring

open Classical in
/-- With overlapping physical copies, the literal `n^(i-2)` abundance condition
fails once `α n²` exceeds a constant depending only on `C`.
This is a diagnosis of the supplied definition, not an absorption proof. -/
theorem not_hingeful_above_threshold (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (C : ℕ)
    (u v w z : V) (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hW : IsCopy p F G {u, v, w}) (hZ : IsCopy p F G {u, v, z})
    (hα : 0 < α)
    (hlarge : (2 ^ Nat.choose (C + 1) 2 : ℕ) < α * (Fintype.card V : ℝ) ^ 2) :
    ¬ Hingeful p F G α C := by
  intro hhinge
  have hnNat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnNat
  have hinter : (triEdges ({u, v, w} : Finset V) ∩ triEdges {u, v, z}).card = 1 := by
    simp [triEdges_three huv huw hvw, triEdges_three huv huz hvz,
      huv, huw, huz, hvw, hvz, hwz]
  obtain ⟨i, hi, habundant⟩ := hhinge {u, v, w} {u, v, z} hW hZ hinter
  let K := G.edgeFinset.powerset.filter
    (fun H => IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = i)
  have hpositive : (0 : ℝ) < K.card :=
    lt_of_lt_of_le (mul_pos hα (zpow_pos hn _)) habundant
  have hnonempty : K.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpositive)
  obtain ⟨H, hH⟩ := hnonempty
  have hHinge := (Finset.mem_filter.mp hH).2.1
  have horder := (Finset.mem_filter.mp hH).2.2
  have hi4 : 4 ≤ i := by
    have hfour := PhysicalHinge.four_le_support_card H u v w z huv huw huz hvw hvz hwz
      (IsHinge.four_roots H u v w z huv huw huz hvw hvz hwz hHinge)
    simpa only [← vertSet_eq_support, horder] using hfour
  have hcount := hinge_count_le_pow p F G.edgeFinset u v w z i
    huv huw huz hvw hvz hwz hi4
  have hcountReal : (K.card : ℝ) ≤
      (2 ^ Nat.choose (i + 1) 2 : ℕ) * (Fintype.card V : ℝ) ^ (i - 4) := by
    exact_mod_cast hcount
  have hconst : (2 ^ Nat.choose (i + 1) 2 : ℕ) ≤ 2 ^ Nat.choose (C + 1) 2 := by
    exact Nat.pow_le_pow_right (by decide)
      (Nat.choose_le_choose 2 (Nat.add_le_add_right (Finset.mem_Icc.mp hi).2 1))
  have hconstReal : ((2 ^ Nat.choose (i + 1) 2 : ℕ) : ℝ) ≤
      (2 ^ Nat.choose (C + 1) 2 : ℕ) := by exact_mod_cast hconst
  have hupper : (K.card : ℝ) ≤
      (2 ^ Nat.choose (C + 1) 2 : ℕ) * (Fintype.card V : ℝ) ^ (i - 4) :=
    hcountReal.trans (mul_le_mul_of_nonneg_right hconstReal (by positivity))
  have hexponent : ((i : ℤ) - 2) = ((i - 4 + 2 : ℕ) : ℤ) := by omega
  rw [hexponent, zpow_natCast] at habundant
  have hstrict := scaling_gap α (Fintype.card V) (2 ^ Nat.choose (C + 1) 2 : ℕ)
    (i - 4) hn hlarge
  exact (not_lt_of_ge (habundant.trans hupper)) hstrict

end PartitionedTriangleAbsorption
