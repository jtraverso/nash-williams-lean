/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.BipCount
import RequestProject.FracStab.StabCut

/-!
# Lemma 9.5: the types of the four classes (Claims 9.5.4 and 9.5.5)

In the four part outcome of the stability lemma, one class consists almost entirely of
`u`-obtuse vertices, one of `v`-obtuse vertices and the remaining two of acute vertices.
-/

namespace NashWilliams.Frac

open Finset

/-- Pigeonhole for the three types over four classes. -/
lemma select4 (PU PW PA : Fin 4 → Prop) (hU : ∀ i j, PU i → PU j → i = j)
    (hW : ∀ i j, PW i → PW j → i = j)
    (hA : ∀ i j k, PA i → PA j → PA k → i = j ∨ i = k ∨ j = k)
    (hc : ∀ i, PU i ∨ PW i ∨ PA i) :
    ∃ p q s t : Fin 4, p ≠ q ∧ p ≠ s ∧ p ≠ t ∧ q ≠ s ∧ q ≠ t ∧ s ≠ t ∧
      (∀ i, PU i → i = p) ∧ (∀ i, PW i → i = q) ∧ (∀ i, PA i → i = s ∨ i = t) ∧
      PU p ∧ PW q ∧ PA s ∧ PA t := by
  classical
  set SU := univ.filter PU
  set SW := univ.filter PW
  set SA := univ.filter PA
  have cU : SU.card ≤ 1 := card_le_one.2 fun i hi j hj =>
    hU i j (mem_filter.1 hi).2 (mem_filter.1 hj).2
  have cW : SW.card ≤ 1 := card_le_one.2 fun i hi j hj =>
    hW i j (mem_filter.1 hi).2 (mem_filter.1 hj).2
  have cA : SA.card ≤ 2 := by
    by_contra h; push_neg at h
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := two_lt_card_iff.1 h
    rcases hA i j k (mem_filter.1 hi).2 (mem_filter.1 hj).2 (mem_filter.1 hk).2 with h | h | h
    · exact hij h
    · exact hik h
    · exact hjk h
  have hall : SU ∪ SW ∪ SA = univ := by
    ext i; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true, SU, SW, SA]
    rcases hc i with h | h | h <;> tauto
  have h4 : (SU ∪ SW ∪ SA).card = 4 := by rw [hall]; rfl
  have i1 := card_union_add_card_inter SU SW
  have i2 := card_union_add_card_inter (SU ∪ SW) SA
  have eU : SU.card = 1 := by omega
  have eW : SW.card = 1 := by omega
  have eA : SA.card = 2 := by omega
  have d1 : (SU ∩ SW).card = 0 := by omega
  have d2 : ((SU ∪ SW) ∩ SA).card = 0 := by omega
  rw [card_eq_zero] at d1 d2
  obtain ⟨p, hp⟩ := card_eq_one.1 eU
  obtain ⟨q, hq⟩ := card_eq_one.1 eW
  obtain ⟨s, t, hst, hA2⟩ := card_eq_two.1 eA
  have mp : p ∈ SU := by rw [hp]; exact mem_singleton_self _
  have mq : q ∈ SW := by rw [hq]; exact mem_singleton_self _
  have ms : s ∈ SA := by rw [hA2]; simp
  have mt : t ∈ SA := by rw [hA2]; simp
  have nd1 : ∀ i, i ∈ SU → i ∈ SW → False := fun i h1 h2 => by
    have : i ∈ SU ∩ SW := mem_inter.2 ⟨h1, h2⟩
    rw [d1] at this; exact absurd this (notMem_empty _)
  have nd2 : ∀ i, i ∈ SU ∪ SW → i ∈ SA → False := fun i h1 h2 => by
    have : i ∈ (SU ∪ SW) ∩ SA := mem_inter.2 ⟨h1, h2⟩
    rw [d2] at this; exact absurd this (notMem_empty _)
  refine ⟨p, q, s, t, ?_, ?_, ?_, ?_, ?_, hst, ?_, ?_, ?_, (mem_filter.1 mp).2,
    (mem_filter.1 mq).2, (mem_filter.1 ms).2, (mem_filter.1 mt).2⟩
  · rintro rfl; exact nd1 p mp mq
  · rintro rfl; exact nd2 p (mem_union_left _ mp) ms
  · rintro rfl; exact nd2 p (mem_union_left _ mp) mt
  · rintro rfl; exact nd2 q (mem_union_right _ mq) ms
  · rintro rfl; exact nd2 q (mem_union_right _ mq) mt
  · intro i hi
    have : i ∈ SU := mem_filter.2 ⟨mem_univ _, hi⟩
    rw [hp] at this; exact mem_singleton.1 this
  · intro i hi
    have : i ∈ SW := mem_filter.2 ⟨mem_univ _, hi⟩
    rw [hq] at this; exact mem_singleton.1 this
  · intro i hi
    have : i ∈ SA := mem_filter.2 ⟨mem_univ _, hi⟩
    rw [hA2] at this; simpa using this

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- If all pairs of `X × Y` are far, the far count is `|X| |Y|`. -/
lemma card_le_bsum_farI {a : V → V → ℝ} {μ θ : ℝ} {X Y : Finset V}
    (h : ∀ x ∈ X, ∀ y ∈ Y, θ < |a x y - μ|) :
    (X.card : ℝ) * Y.card ≤ bsum (farI a μ θ) X Y := by
  have : ∑ x ∈ X, ∑ y ∈ Y, (1:ℝ) ≤ bsum (farI a μ θ) X Y :=
    sum_le_sum fun x hx => sum_le_sum fun y hy => one_le_farI (h x hx y hy)
  simpa using this

/-- **Claims 9.5.4 and 9.5.5.** -/
theorem classify {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ}
    {Su Sv : Finset V} (L : LocFacts C a g U W A du dv Su Sv) [DecidablePred U]
    [DecidablePred W] [DecidablePred A] {Vc : Fin 4 → Finset V} (P : Part4 C Vc)
    {m : Fin 4 → Fin 4 → ℝ} {κ τ θ r : ℝ} (hsize : ∀ i, κ * C.card ≤ (Vc i).card)
    (hτ : ∀ i j, i ≠ j → τ ≤ m i j)
    (hfar : ∀ i j, i ≠ j → bsum (farI a (m i j) θ) (Vc i) (Vc j) ≤ θ * (C.card : ℝ) ^ 2)
    (hθ0 : 0 ≤ θ) (hθτ : θ < τ) (hr0 : 0 ≤ r) (hr : 3 * θ * (C.card : ℝ) ^ 2 ≤ r ^ 2)
    (h3r : 3 * r < κ * C.card) :
    ∃ p q s t : Fin 4, p ≠ q ∧ p ≠ s ∧ p ≠ t ∧ q ≠ s ∧ q ≠ t ∧ s ≠ t ∧
      ((Vc p).card : ℝ) ≤ ((Vc p).filter U).card + 2 * r ∧
      ((Vc q).card : ℝ) ≤ ((Vc q).filter W).card + 2 * r ∧
      ((Vc s).card : ℝ) ≤ ((Vc s).filter A).card + 2 * r ∧
      ((Vc t).card : ℝ) ≤ ((Vc t).filter A).card + 2 * r := by
  have hsplit : ∀ i, ((Vc i).card : ℝ) ≤
      ((Vc i).filter U).card + ((Vc i).filter W).card + ((Vc i).filter A).card := by
    intro i
    have hsub : Vc i ⊆ ((Vc i).filter U ∪ (Vc i).filter W) ∪ (Vc i).filter A := by
      intro x hx
      simp only [mem_union, mem_filter]
      rcases L.cov x (P.sub i hx) with h | h | h <;> tauto
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    exact_mod_cast this
  -- far pairs between two classes
  have far2 : ∀ i j, i ≠ j → ∀ X ⊆ Vc i, ∀ Y ⊆ Vc j, (∀ x ∈ X, ∀ y ∈ Y, a x y = 0) →
      (X.card : ℝ) * Y.card ≤ θ * (C.card : ℝ) ^ 2 := by
    intro i j hij X hX Y hY h0
    refine le_trans (card_le_bsum_farI fun x hx y hy => ?_) ((bsum_farI_mono _ _ _ hX hY).trans
      (hfar i j hij))
    rw [h0 x hx y hy, zero_sub, abs_neg, abs_of_nonneg (by linarith [hτ i j hij])]
    linarith [hτ i j hij]
  have hrsq : θ * (C.card : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (C.card : ℝ)]
  have prod_gt : ∀ x y : ℝ, r < x → r < y → r ^ 2 < x * y := fun x y hx hy => by nlinarith
  have hU' : ∀ i j, r < (((Vc i).filter U).card : ℝ) → r < (((Vc j).filter U).card : ℝ) → i = j := by
    intro i j hi hj
    by_contra hij
    have := far2 i j hij _ (filter_subset _ _) _ (filter_subset _ _) fun x hx y hy =>
      L.UU x (P.sub i (mem_filter.1 hx).1) y (P.sub j (mem_filter.1 hy).1) (mem_filter.1 hx).2
        (mem_filter.1 hy).2
    linarith [prod_gt _ _ hi hj]
  have hW' : ∀ i j, r < (((Vc i).filter W).card : ℝ) → r < (((Vc j).filter W).card : ℝ) → i = j := by
    intro i j hi hj
    by_contra hij
    have := far2 i j hij _ (filter_subset _ _) _ (filter_subset _ _) fun x hx y hy =>
      L.WW x (P.sub i (mem_filter.1 hx).1) y (P.sub j (mem_filter.1 hy).1) (mem_filter.1 hx).2
        (mem_filter.1 hy).2
    linarith [prod_gt _ _ hi hj]
  have hA' : ∀ i j k, r < (((Vc i).filter A).card : ℝ) → r < (((Vc j).filter A).card : ℝ) → r < (((Vc k).filter A).card : ℝ) → i = j ∨ i = k ∨ j = k := by
    intro i j k hi hj hk
    by_contra hne
    push_neg at hne
    obtain ⟨hij, hik, hjk⟩ := hne
    set A1 := (Vc i).filter A
    set A2 := (Vc j).filter A
    set A3 := (Vc k).filter A
    have hfarA : ∀ i' j', i' ≠ j' → ∀ x ∈ (Vc i').filter A, ∀ y ∈ (Vc j').filter A,
        1 ≤ farI a (m i' j') θ x y ∨ 0 < g x y := by
      intro i' j' hij' x hx y hy
      rcases (L.g0 x y).lt_or_eq with h | h
      · exact Or.inr h
      · left
        apply one_le_farI
        rw [L.AA x (P.sub i' (mem_filter.1 hx).1) y (P.sub j' (mem_filter.1 hy).1)
          (mem_filter.1 hx).2 (mem_filter.1 hy).2 h.symm, zero_sub, abs_neg,
          abs_of_nonneg (by linarith [hτ i' j' hij'])]
        linarith [hτ i' j' hij']
    have ht := triple_count A1 A2 A3 (farI a (m i j) θ) (farI a (m i k) θ) (farI a (m j k) θ)
      (by
        intro x hx y hy z hz
        have n1 := farI_nonneg a (m i j) θ x y
        have n2 := farI_nonneg a (m i k) θ x z
        have n3 := farI_nonneg a (m j k) θ y z
        rcases hfarA i j hij x hx y hy with h1 | h1
        · linarith
        rcases hfarA i k hik x hx z hz with h2 | h2
        · linarith
        rcases hfarA j k hjk y hy z hz with h3 | h3
        · linarith
        exact (L.tri x y z h1 h2 h3).elim)
    have b12 := (bsum_farI_mono a (m i j) θ (filter_subset A (Vc i)) (filter_subset A (Vc j))).trans
      (hfar i j hij)
    have b13 := (bsum_farI_mono a (m i k) θ (filter_subset A (Vc i)) (filter_subset A (Vc k))).trans
      (hfar i k hik)
    have b23 := (bsum_farI_mono a (m j k) θ (filter_subset A (Vc j)) (filter_subset A (Vc k))).trans
      (hfar j k hjk)
    have p12 := prod_gt _ _ hi hj
    have p13 := prod_gt _ _ hi hk
    have p23 := prod_gt _ _ hj hk
    have n1 : (0:ℝ) < A1.card := by linarith
    have n2 : (0:ℝ) < A2.card := by linarith
    have n3 : (0:ℝ) < A3.card := by linarith
    have e1 : (A3.card : ℝ) * bsum (farI a (m i j) θ) A1 A2 ≤ A3.card * (θ * (C.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left b12 n3.le
    have e2 : (A2.card : ℝ) * bsum (farI a (m i k) θ) A1 A3 ≤ A2.card * (θ * (C.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left b13 n2.le
    have e3 : (A1.card : ℝ) * bsum (farI a (m j k) θ) A2 A3 ≤ A1.card * (θ * (C.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left b23 n1.le
    have f1 : (A3.card : ℝ) * (3 * (θ * (C.card : ℝ) ^ 2)) < A3.card * (A1.card * A2.card) :=
      mul_lt_mul_of_pos_left (by linarith) n3
    have f2 : (A2.card : ℝ) * (3 * (θ * (C.card : ℝ) ^ 2)) < A2.card * (A1.card * A3.card) :=
      mul_lt_mul_of_pos_left (by linarith) n2
    have f3 : (A1.card : ℝ) * (3 * (θ * (C.card : ℝ) ^ 2)) < A1.card * (A2.card * A3.card) :=
      mul_lt_mul_of_pos_left (by linarith) n1
    nlinarith
  have hc' : ∀ i, r < (((Vc i).filter U).card : ℝ) ∨ r < (((Vc i).filter W).card : ℝ) ∨ r < (((Vc i).filter A).card : ℝ) := by
    intro i
    by_contra h
    push_neg at h
    have := hsplit i
    have := hsize i
    linarith [h.1, h.2.1, h.2.2]
  obtain ⟨p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, hUp, hWq, hAst, -, -, -, -⟩ := select4
    (fun i => r < ((Vc i).filter U).card) (fun i => r < ((Vc i).filter W).card)
    (fun i => r < ((Vc i).filter A).card) hU' hW' hA' hc'
  refine ⟨p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, ?_, ?_, ?_, ?_⟩
  · have h1 : (((Vc p).filter W).card : ℝ) ≤ r := not_lt.1 fun h => hpq (hWq p h)
    have h2 : (((Vc p).filter A).card : ℝ) ≤ r := not_lt.1 fun h => (hAst p h).elim hps hpt
    linarith [hsplit p]
  · have h1 : (((Vc q).filter U).card : ℝ) ≤ r := not_lt.1 fun h => hpq (hUp q h).symm
    have h2 : (((Vc q).filter A).card : ℝ) ≤ r := not_lt.1 fun h => (hAst q h).elim hqs hqt
    linarith [hsplit q]
  · have h1 : (((Vc s).filter U).card : ℝ) ≤ r := not_lt.1 fun h => hps (hUp s h).symm
    have h2 : (((Vc s).filter W).card : ℝ) ≤ r := not_lt.1 fun h => hqs (hWq s h).symm
    linarith [hsplit s]
  · have h1 : (((Vc t).filter U).card : ℝ) ≤ r := not_lt.1 fun h => hpt (hUp t h).symm
    have h2 : (((Vc t).filter W).card : ℝ) ≤ r := not_lt.1 fun h => hqt (hWq t h).symm
    linarith [hsplit t]

end NashWilliams.Frac
