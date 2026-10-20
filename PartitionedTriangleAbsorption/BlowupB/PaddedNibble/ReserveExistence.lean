/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveWitness
public import PartitionedTriangleAbsorption.BlowupB.PaddedQuantitative.EffectiveTail

@[expose] public section

/-!
# Simultaneous decomposable reserve with a polynomial threshold

There are at most four common-neighbour queries for each ordered pair of
vertices and one degree query per vertex. Selecting entire blocks of a typed
triangle packing supplies a decomposable reserve. The estimates on the actual
edge sets are simultaneous, with all quantifiers over roots and classes.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking

open Finset Nibble ReserveTests TypedNibble BernoulliExposure BernoulliConcentration

theorem reserve_tail_lt_one (ρ ω n : ℝ) (hρ : 0 < ρ) (hω : 0 < ω) (hn : 0 < n)
    (hlarge : (2 : ℝ) ^ 27 * ρ⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ n) :
    5 * n ^ 2 * Real.exp (-(ρ ^ 3 * ω ^ 2 * n / 48)) < 1 := by
  let c : ℝ := ρ ^ 3 * ω ^ 2 / 48
  have hc : 0 < c := by dsimp [c]; positivity
  have hscaled := mul_le_mul_of_nonneg_left hlarge (pow_nonneg hc.le 3)
  have hcancel : c ^ 3 * ((2 : ℝ) ^ 27 * ρ⁻¹ ^ 9 * ω⁻¹ ^ 6) =
      (2 : ℝ) ^ 27 / 48 ^ 3 := by
    dsimp [c]
    field_simp
  rw [hcancel] at hscaled
  have hnum : 5 * ((2 + 1).factorial : ℝ) < c ^ (2 + 1) * n := by
    norm_num at hscaled ⊢
    linarith only [hscaled]
  have hh := KeevashQuantitative.polynomial_exp_tail_lt_one c 5 n 2 hc
    (by norm_num) hn hnum
  simpa only [c, div_mul_eq_mul_div] using hh

variable {V : Type*} [Fintype V] [DecidableEq V] {m t : ℕ}

def reserveQueries (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    Finset (V × V × Fin t) :=
  univ.filter fun q => q.1 ≠ q.2.1 ∧
    ({p q.1, p q.2.1, q.2.2} : Multiset (Fin t)) ∈ F

theorem reserveQueries_card (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (ht : t ≤ 4) :
    ((reserveQueries p F).card : ℝ) ≤ 4 * (Fintype.card V : ℝ) ^ 2 := by
  have hcard := card_le_univ (reserveQueries p F)
  have hcardR : ((reserveQueries p F).card : ℝ) ≤
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * t) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
      (show ((reserveQueries p F).card : ℝ) ≤ Fintype.card (V × V × Fin t) by
        exact_mod_cast hcard)
  have htR : (t : ℝ) ≤ 4 := by exact_mod_cast ht
  have hm := mul_le_mul_of_nonneg_left htR (sq_nonneg (Fintype.card V : ℝ))
  nlinarith only [hcardR, hm]

/-- Whole-block selection simultaneously supplies a typed decomposition,
small maximum degree, and common neighbours in every permitted class. -/
theorem exists_reserve_of_system (S : TriSystem V m) (hpack : IsPacking S univ)
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (ht : t ≤ 4)
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (htyped : ∀ i, IsTypedTri p F (S.tri i))
    (hhost : ∀ i, Nibble.triEdges (S.tri i) ⊆ J.edgeFinset)
    (ρ ω : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 0 < Fintype.card V)
    (hlarge : (2 : ℝ) ^ 27 * ρ⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ Fintype.card V)
    (hanti : AntiEdgeful p F J ω)
    (hleft : DegBounded (J.edgeFinset \ edgesOf S univ) (ω * Fintype.card V / 8)) :
    ∃ X : Finset (Sym2 V), X ⊆ J.edgeFinset ∧ HasDecomp p F X ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      AntiEdgeful p F (ReserveCoverDown.reserveGraph X) (ρ ^ 2 * ω / 12) := by
  classical
  let n : ℝ := Fintype.card V
  let e : ℝ := Real.exp (-(ρ ^ 3 * ω ^ 2 * n / 48))
  let badD (v : V) (x : Fin m → Bool) : Prop :=
    2 * ρ * n < ((star (S.touched x) v).card : ℝ)
  let badC (q : V × V × Fin t) (x : Fin m → Bool) : Prop :=
    ((reserveNeighbours S p x q.1 q.2.1 q.2.2).card : ℝ) < ρ ^ 2 * ω * n / 4
  let Q := reserveQueries p F
  have hnR : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast hn
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hq : ∀ _i : Fin m, 0 ≤ ρ ∧ ρ ≤ 1 := fun _ => ⟨hρ.le, hρ1⟩
  have hrate : ρ ^ 3 * ω ^ 2 * n / 48 ≤ ρ * n / 8 := by
    have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ.le hρ1
    have hω2 : ω ^ 2 ≤ 1 := pow_le_one₀ hω.le hω1
    have hρ3 : ρ ^ 3 ≤ ρ := by
      have hh := mul_le_mul_of_nonneg_left hρ2 hρ.le
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_left hω2 (pow_nonneg hρ.le 3)
    have hprod : ρ ^ 3 * ω ^ 2 ≤ ρ := by nlinarith only [hh, hρ3]
    have hm := mul_le_mul_of_nonneg_right hprod hnR.le
    have hpos : 0 ≤ ρ * n := mul_nonneg hρ.le hnR.le
    linarith only [hm, hpos]
  have hD (v : V) : cubeProb (fun _ : Fin m => ρ) (badD v) ≤ e := by
    exact (reserveDegree_upper_tail S hpack ρ hρ hρ1 hn v).trans
      (Real.exp_le_exp.mpr (neg_le_neg hrate))
  have hC (q : V × V × Fin t) (hqQ : q ∈ Q) :
      cubeProb (fun _ : Fin m => ρ) (badC q) ≤ e := by
    have hvalid := (mem_filter.mp hqQ).2
    exact reserveNeighbours_lower_tail S p F J ρ ω hρ hρ1 hω hω1 hn hanti hleft
      hvalid.1 hvalid.2
  have hDall : cubeProb (fun _ : Fin m => ρ) (fun x => ∃ v ∈ univ, badD v x) ≤
      n * e := by
    calc
      _ ≤ ∑ v : V, cubeProb (fun _ : Fin m => ρ) (badD v) :=
        cubeProb_exists_le _ hq univ badD
      _ ≤ ∑ _v : V, e := sum_le_sum fun v _ => hD v
      _ = n * e := by simp [n]
  have hCall : cubeProb (fun _ : Fin m => ρ) (fun x => ∃ q ∈ Q, badC q x) ≤
      4 * n ^ 2 * e := by
    calc
      _ ≤ ∑ q ∈ Q, cubeProb (fun _ : Fin m => ρ) (badC q) :=
        cubeProb_exists_le _ hq Q badC
      _ ≤ ∑ _q ∈ Q, e := sum_le_sum hC
      _ = (Q.card : ℝ) * e := by simp
      _ ≤ 4 * n ^ 2 * e := mul_le_mul_of_nonneg_right (reserveQueries_card p F ht) he
  have hfail : cubeProb (fun _ : Fin m => ρ)
      (fun x => (∃ v ∈ univ, badD v x) ∨ ∃ q ∈ Q, badC q x) < 1 := by
    calc
      _ ≤ cubeProb (fun _ : Fin m => ρ) (fun x => ∃ v ∈ univ, badD v x) +
          cubeProb (fun _ : Fin m => ρ) (fun x => ∃ q ∈ Q, badC q x) :=
        cubeProb_or_le _ hq _ _
      _ ≤ n * e + 4 * n ^ 2 * e := add_le_add hDall hCall
      _ ≤ 5 * n ^ 2 * e := by
        have hnsq : n ≤ n ^ 2 := by nlinarith only [hnR.le, hn1]
        have hh := mul_le_mul_of_nonneg_right hnsq he
        linarith only [hh]
      _ < 1 := reserve_tail_lt_one ρ ω n hρ hω hnR hlarge
  obtain ⟨x, hx⟩ := exists_not_of_cubeProb_lt_one _ _ hfail
  refine ⟨S.touched x, ?_, touched_hasDecomp S hpack p F htyped x, ?_, ?_⟩
  · intro edge hedge
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hedge
    exact hhost i hi
  · intro v
    exact le_of_not_gt (fun hv => hx (Or.inl ⟨v, mem_univ _, hv⟩))
  · intro τ hτ i j k hijk u v huv hui hvj
    have hquery : (u, v, k) ∈ Q := by
      refine mem_filter.mpr ⟨mem_univ _, huv, ?_⟩
      rw [hui, hvj, ← hijk]
      exact hτ
    have hcount : ρ ^ 2 * ω * n / 4 ≤
        ((reserveNeighbours S p x u v k).card : ℝ) :=
      le_of_not_gt (fun hh => hx (Or.inr ⟨(u, v, k), hquery, hh⟩))
    change (ρ ^ 2 * ω / 12) * n ≤ _
    have hnonneg : 0 ≤ ρ ^ 2 * ω * n := by positivity
    change (ρ ^ 2 * ω / 12) * n ≤ ((reserveNeighbours S p x u v k).card : ℝ)
    linarith only [hcount, hnonneg]

#print axioms reserve_tail_lt_one
#print axioms reserveQueries_card
#print axioms exists_reserve_of_system

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
