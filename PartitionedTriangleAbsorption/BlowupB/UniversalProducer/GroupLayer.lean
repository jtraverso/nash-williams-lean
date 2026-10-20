/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.GroupLedger

@[expose] public section

/-!
# One cyclic charge layer, including torsion

Let `Hn` be a subgroup of an abelian group `A`, let `g ∈ A`, and let `d` be the order of
`g` modulo `Hn` (`d = 0` when that order is infinite), i.e. `k • g ∈ Hn ↔ d ∣ k`.
Suppose every library piece `P i` of a predicate refiner `E` has a coefficient `c i` with
`val(P i) - c i • g ∈ Hn`, nonnegative when `d > 0`.

For a leftover `L` with `val L = 0` the selected pieces satisfy
`∑ i ∈ T, val(P i) = val R0`, hence `(∑ T c - ∑ T₀ c) • g ∈ Hn` and `d ∣ ∑ T c - ∑ T₀ c`.
When `d = 0` the total demand is exactly conserved.  When `d > 0` it is conserved only
modulo `d`; the discrepancy is absorbed by *wrap pieces*: empty library pieces of demand
`-d`, of which exactly `s_T = (∑ T c - K₀)/d` are selected.  A wrap piece receives `d` plus
tokens, of value `d • g ∈ Hn`.  The wrap pieces are part of the FIXED library (their number
`Ab · |lib|` is fixed before the leftover), so the quantifier order of the shared refiner
is preserved.

`group_layer` then applies the group-valued ledger layer `ledger_layer`: all new pieces
have value in `Hn`.  The fixed remainder `R0` needs no separate charge assumption: its
conserved demand is read off from the leftover `L = ∅`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0

variable {W : Type*} [DecidableEq W] {κ : Type*}

/-- The order of `g` modulo `Hn` and normalized coefficients (in `[0, d)` when `d > 0`). -/
theorem exists_cyclic_coef {A : Type*} [AddCommGroup A] (Hp Hn : AddSubgroup A) (g : A)
    (hgen : ∀ x ∈ Hp, ∃ a : ℤ, x - a • g ∈ Hn) :
    ∃ d : ℕ, (∀ k : ℤ, k • g ∈ Hn ↔ (d : ℤ) ∣ k) ∧ ∃ coef : A → ℤ,
      (∀ x ∈ Hp, x - coef x • g ∈ Hn) ∧ (0 < d → ∀ x, 0 ≤ coef x ∧ coef x < d) := by
  classical
  set q := QuotientAddGroup.mk' Hn with hq
  have hd : ∀ k : ℤ, k • g ∈ Hn ↔ (addOrderOf (q g) : ℤ) ∣ k := by
    intro k
    rw [addOrderOf_dvd_iff_zsmul_eq_zero, ← map_zsmul, hq, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
  refine ⟨addOrderOf (q g), hd, ?_⟩
  set d := addOrderOf (q g)
  let coef : A → ℤ := fun x => if h : x ∈ Hp then (Classical.choose (hgen x h)) % d else 0
  refine ⟨coef, ?_, ?_⟩
  · intro x hx
    have h0 := Classical.choose_spec (hgen x hx)
    set a := Classical.choose (hgen x hx)
    have : coef x = a % d := by simp [coef, hx, a]
    rw [this]
    have hmul : ((d : ℤ) * (a / d)) • g ∈ Hn := by
      rw [mul_comm, mul_zsmul]
      exact Hn.zsmul_mem ((hd d).mpr dvd_rfl) _
    have heq : x - (a % (d:ℤ)) • g = (x - a • g) + ((d:ℤ) * (a / d)) • g := by
      rw [Int.emod_def, sub_zsmul]; abel
    rw [heq]
    exact Hn.add_mem h0 hmul
  · intro hd0 x
    have hd0' : (0 : ℤ) < d := by exact_mod_cast hd0
    by_cases hx : x ∈ Hp
    · simp only [coef, dif_pos hx]
      exact ⟨Int.emod_nonneg _ hd0'.ne', Int.emod_lt_of_pos _ hd0'⟩
    · simp only [coef, dif_neg hx]
      exact ⟨le_rfl, hd0'⟩

/-- The refiner extended by `M` empty wrap pieces (never selected by this refiner itself). -/
def wrapRefiner [DecidableEq κ] {X0 : Finset (Sym2 W)} {Q : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q) (M : ℕ) : PredRefiner (κ ⊕ ℕ) X0 Q where
  lib := E.lib.image Sum.inl ∪ (range M).image Sum.inr
  P := Sum.elim E.P (fun _ => ∅)
  R0 := E.R0
  loopP := by
    intro j hj e he
    rcases j with i | k
    · exact E.loopP i (by simpa using hj) e he
    · simp at he
  evenP := by
    intro j hj w
    rcases j with i | k
    · exact E.evenP i (by simpa using hj) w
    · simp [incidentLoad]
  subP := by
    intro j hj
    rcases j with i | k
    · exact E.subP i (by simpa using hj)
    · simp
  disjRX := E.disjRX
  refines := by
    classical
    intro L hL hQ
    obtain ⟨T, hT, hdis, hU⟩ := E.refines L hL hQ
    refine ⟨T.image Sum.inl, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      exact mem_union_left _ (mem_image_of_mem _ (hT hi))
    · intro j hj j' hj' hne
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      obtain ⟨i', hi', rfl⟩ := mem_image.mp hj'
      exact hdis hi hi' (fun h => hne (by rw [h]))
    · rw [← hU, image_biUnion]
      rfl

/-- **One cyclic layer** (free or torsion), with wrap pieces and the ledger layer. -/
theorem group_layer [DecidableEq κ] {X0 : Finset (Sym2 W)} {Q Q' : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q) (hQ' : ∀ L, Q' L → Q L) (hQ0 : Q' ∅)
    {A : Type*} [AddCommGroup A] (val : Sym2 W → A)
    (hval : ∀ L ⊆ X0, Q' L → edgeVal val L = 0)
    (Hn : AddSubgroup A) (g : A) (d : ℕ) (hd : ∀ k : ℤ, k • g ∈ Hn ↔ (d : ℤ) ∣ k)
    (c : κ → ℤ) (hc : ∀ i ∈ E.lib, edgeVal val (E.P i) - c i • g ∈ Hn)
    (hnn : 0 < d → ∀ i ∈ E.lib, 0 ≤ c i)
    (Ab : ℕ) (hAb : ∀ i ∈ E.lib, (c i).natAbs ≤ Ab) (hdAb : d ≤ Ab)
    (sz : ℕ) (Extra : Finset (Tok (κ ⊕ ℕ)) → (Tok (κ ⊕ ℕ) → Finset (Sym2 W)) → Prop)
    (hsupply : ∀ S : Finset (Tok (κ ⊕ ℕ)), S.card ≤ 9 * (Ab * (Ab + 1) * E.lib.card) →
      ∃ tokE, TokRealV val g sz (E.R0 ∪ X0) S tokE ∧ Extra S tokE) :
    ∃ (S : Finset (Tok (κ ⊕ ℕ))) (tokE : Tok (κ ⊕ ℕ) → Finset (Sym2 W))
      (E' : PredRefiner (JIdx (κ ⊕ ℕ)) X0 Q'),
      TokRealV val g sz (E.R0 ∪ X0) S tokE ∧ Extra S tokE ∧
      S.card ≤ 9 * (Ab * (Ab + 1) * E.lib.card) ∧
      E'.R0 = E.R0 ∪ S.biUnion tokE ∧
      (∀ j ∈ E'.lib, edgeVal val (E'.P j) ∈ Hn) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ 2 * sz ∨ (E'.P j).card ≤ sz * Ab ∨
        ∃ i ∈ E.lib, (E'.P j).card ≤ (E.P i).card + sz * Ab) ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w + 44 * ∑ τ ∈ S, incidentLoad (tokE τ) w) ∧
      E'.lib.card ≤ E.lib.card * (1 + 98 * (Ab * (Ab + 1))) := by
  classical
  set M := Ab * E.lib.card with hM
  set Ew := wrapRefiner E M with hEw
  let c' : κ ⊕ ℕ → ℤ := Sum.elim c (fun _ => -(d : ℤ))
  -- conservation modulo `Hn`
  have hcons : ∀ T ⊆ E.lib, (T : Set κ).PairwiseDisjoint E.P → ∀ L ⊆ X0, Q' L →
      T.biUnion E.P = E.R0 ∪ L → edgeVal val E.R0 - (∑ i ∈ T, c i) • g ∈ Hn := by
    intro T hT hdisT L hL hQL hU
    have h1 : edgeVal val (T.biUnion E.P) = ∑ i ∈ T, edgeVal val (E.P i) :=
      edgeVal_biUnion val T E.P hdisT
    have hdis : Disjoint E.R0 L := disjoint_of_subset_right hL E.disjRX
    rw [hU, edgeVal_union val hdis, hval L hL hQL, add_zero] at h1
    have h2 : edgeVal val E.R0 - (∑ i ∈ T, c i) • g = ∑ i ∈ T, (edgeVal val (E.P i) - c i • g) := by
      rw [h1, sum_sub_distrib, Finset.sum_smul]
    rw [h2]
    exact Hn.sum_mem fun i hi => hc i (hT hi)
  obtain ⟨T0, hT0, hdis0, hU0⟩ := E.refines ∅ (empty_subset _) (hQ' ∅ hQ0)
  set K0 : ℤ := (∑ i ∈ T0, c i) % (d : ℤ) with hK0
  have hcons0 := hcons T0 hT0 hdis0 ∅ (empty_subset _) hQ0 (by rw [hU0, union_empty])
  have hdvd : ∀ T ⊆ E.lib, (T : Set κ).PairwiseDisjoint E.P → ∀ L ⊆ X0, Q' L →
      T.biUnion E.P = E.R0 ∪ L → (d : ℤ) ∣ (∑ i ∈ T, c i) - K0 := by
    intro T hT hdisT L hL hQL hU
    have h1 := hcons T hT hdisT L hL hQL hU
    have h2 : ((∑ i ∈ T, c i) - ∑ i ∈ T0, c i) • g ∈ Hn := by
      have := Hn.sub_mem hcons0 h1
      have heq : edgeVal val E.R0 - (∑ i ∈ T0, c i) • g -
          (edgeVal val E.R0 - (∑ i ∈ T, c i) • g) = ((∑ i ∈ T, c i) - ∑ i ∈ T0, c i) • g := by
        rw [sub_zsmul]; abel
      rwa [heq] at this
    have h3 := (hd _).mp h2
    have h4 : (d : ℤ) ∣ (∑ i ∈ T0, c i) - K0 := by
      rw [hK0, Int.emod_def]; simp
    have := dvd_add h3 h4
    rwa [show (∑ i ∈ T, c i) - ∑ i ∈ T0, c i + ((∑ i ∈ T0, c i) - K0) =
      (∑ i ∈ T, c i) - K0 by ring] at this
  -- the selection with wraps
  have hsel : ∀ L ⊆ X0, Q' L → ∃ T ⊆ Ew.lib, (T : Set (κ ⊕ ℕ)).PairwiseDisjoint Ew.P ∧
      T.biUnion Ew.P = Ew.R0 ∪ L ∧ ∑ i ∈ T, c' i = K0 := by
    intro L hL hQL
    obtain ⟨T, hT, hdisT, hU⟩ := E.refines L hL (hQ' L hQL)
    have hdT := hdvd T hT hdisT L hL hQL hU
    obtain ⟨q, hq⟩ := hdT
    -- the number of selected wraps
    have hqnn : d = 0 ∨ (0 ≤ q ∧ q ≤ M) := by
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · left; exact h0
      · right
        have hdpos : (0 : ℤ) < d := by exact_mod_cast hpos
        have hST : 0 ≤ ∑ i ∈ T, c i := sum_nonneg fun i hi => hnn hpos i (hT hi)
        have hK0lt : K0 < d := Int.emod_lt_of_pos _ hdpos
        have hK0nn : 0 ≤ K0 := Int.emod_nonneg _ hdpos.ne'
        have hle : ∑ i ∈ T, c i ≤ Ab * E.lib.card := by
          calc ∑ i ∈ T, c i ≤ ∑ i ∈ E.lib, c i :=
                sum_le_sum_of_subset_of_nonneg hT fun i hi _ => hnn hpos i hi
            _ ≤ ∑ i ∈ E.lib, (Ab : ℤ) := sum_le_sum fun i hi => by
                have := hAb i hi
                have h2 : |c i| ≤ (Ab : ℤ) := by
                  rw [Int.abs_eq_natAbs]; exact_mod_cast this
                exact (le_abs_self _).trans h2
            _ = Ab * E.lib.card := by rw [sum_const, nsmul_eq_mul]; ring
        constructor
        · by_contra hneg
          push_neg at hneg
          have : (d : ℤ) * q ≤ -(d : ℤ) := by nlinarith
          linarith
        · have h1 : (d : ℤ) * q ≤ Ab * E.lib.card := by linarith
          have h2 : q ≤ (d : ℤ) * q := by
            rcases le_or_gt 0 q with hq0 | hq0
            · nlinarith
            · nlinarith
          have : q ≤ (Ab : ℤ) * E.lib.card := by linarith
          rw [hM]; push_cast; exact this
    set s : ℕ := q.toNat with hs
    have hsq : d = 0 ∨ ((s : ℤ) = q ∧ s ≤ M) := by
      rcases hqnn with h | ⟨h1, h2⟩
      · left; exact h
      · right
        refine ⟨Int.toNat_of_nonneg h1, ?_⟩
        have : (s : ℤ) ≤ M := by rw [hs, Int.toNat_of_nonneg h1]; exact h2
        exact_mod_cast this
    have hsM : s ≤ M ∨ d = 0 := by
      rcases hsq with h | ⟨_, h⟩
      · right; exact h
      · left; exact h
    let s' : ℕ := if d = 0 then 0 else s
    have hs'M : s' ≤ M := by
      by_cases h : d = 0
      · simp [s', h]
      · simp only [s', if_neg h]
        rcases hsM with h' | h'
        · exact h'
        · exact absurd h' h
    refine ⟨T.image Sum.inl ∪ (range s').image Sum.inr, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases mem_union.mp hj with hj | hj
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        exact mem_union_left _ (mem_image_of_mem _ (hT hi))
      · obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
        exact mem_union_right _ (mem_image_of_mem _ (mem_range.mpr
          ((mem_range.mp hk).trans_le hs'M)))
    · intro j hj j' hj' hne
      rcases j with i | k
      · rcases j' with i' | k'
        · have hi : i ∈ T := by simpa using hj
          have hi' : i' ∈ T := by simpa using hj'
          exact hdisT hi hi' (fun h => hne (by rw [h]))
        · exact disjoint_empty_right _
      · exact disjoint_empty_left _
    · rw [union_biUnion, image_biUnion, image_biUnion]
      have h2 : (range s').biUnion (fun k => Ew.P (Sum.inr k)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨k, -, hk⟩ := mem_biUnion.mp he
        exact (Finset.notMem_empty e) hk
      rw [h2, union_empty]
      exact hU
    · rw [sum_union]
      · rw [sum_image (fun a _ b _ h => Sum.inl_injective h),
          sum_image (fun a _ b _ h => Sum.inr_injective h)]
        simp only [c', Sum.elim_inl, Sum.elim_inr, sum_const, card_range, smul_neg,
          nsmul_eq_mul]
        by_cases h : d = 0
        · simp only [s', h, if_true, Nat.cast_zero, mul_zero, neg_zero, add_zero]
          rw [h] at hq; simp at hq; linarith
        · simp only [s', if_neg h]
          rcases hsq with h' | ⟨h1, -⟩
          · exact absurd h' h
          · rw [h1]; linarith
      · rw [disjoint_left]
        intro x hx hx'
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        obtain ⟨k, -, hk⟩ := mem_image.mp hx'
        exact Sum.inr_ne_inl hk
  -- demand bounds
  have hlibw : Ew.lib.card ≤ E.lib.card + M := by
    refine (card_union_le _ _).trans ?_
    exact Nat.add_le_add card_image_le (card_image_le.trans (by simp))
  have hsumw : ∑ i ∈ Ew.lib, (c' i).natAbs ≤ Ab * (Ab + 1) * E.lib.card := by
    have hdisj : Disjoint (E.lib.image Sum.inl) ((range M).image (Sum.inr : ℕ → κ ⊕ ℕ)) := by
      rw [disjoint_left]
      intro x hx hx'
      obtain ⟨i, -, rfl⟩ := mem_image.mp hx
      obtain ⟨k, -, hk⟩ := mem_image.mp hx'
      exact Sum.inr_ne_inl hk
    have h1 : ∑ i ∈ Ew.lib, (c' i).natAbs = ∑ i ∈ E.lib, (c i).natAbs + M * d := by
      change ∑ i ∈ E.lib.image Sum.inl ∪ (range M).image Sum.inr, (c' i).natAbs = _
      rw [sum_union hdisj, sum_image (fun a _ b _ h => Sum.inl_injective h),
        sum_image (fun a _ b _ h => Sum.inr_injective h)]
      simp [c']
    have h2 : ∑ i ∈ E.lib, (c i).natAbs ≤ Ab * E.lib.card := by
      calc ∑ i ∈ E.lib, (c i).natAbs ≤ ∑ _i ∈ E.lib, Ab := sum_le_sum hAb
        _ = Ab * E.lib.card := by rw [sum_const, smul_eq_mul, mul_comm]
    have h3 : M * d ≤ M * Ab := Nat.mul_le_mul_left _ hdAb
    have h4 : Ab * (Ab + 1) * E.lib.card = Ab * E.lib.card + M * Ab := by
      rw [hM]; ring
    omega
  obtain ⟨S, tokE, E', hreal, hextra, hScard, hR', hval', hcard, hload, hlib⟩ :=
    ledger_layer Ew c' K0 hsel hQ0 val g sz Extra
      (fun S hS => hsupply S (hS.trans (Nat.mul_le_mul_left 9 hsumw)))
  refine ⟨S, tokE, E', hreal, hextra, hScard.trans (Nat.mul_le_mul_left 9 hsumw), hR', ?_,
    ?_, ?_, ?_⟩
  · refine hval' Hn ?_
    intro j hj
    rcases j with i | k
    · exact hc i (by simpa [hEw, wrapRefiner] using hj)
    · change edgeVal val ∅ - (-(d : ℤ)) • g ∈ Hn
      rw [edgeVal_empty, neg_zsmul, sub_neg_eq_add, zero_add]
      exact (hd d).mpr dvd_rfl
  · intro j hj
    rcases hcard j hj with h | ⟨i, hi, h⟩
    · left; exact h
    · rcases i with i | k
      · right; right
        have hiE : i ∈ E.lib := by simpa [hEw, wrapRefiner] using hi
        refine ⟨i, hiE, h.trans ?_⟩
        exact Nat.add_le_add_left (Nat.mul_le_mul_left sz (hAb i hiE)) _
      · right; left
        refine h.trans ?_
        change (∅ : Finset (Sym2 W)).card + sz * (-(d : ℤ)).natAbs ≤ sz * Ab
        simp only [card_empty, zero_add, Int.natAbs_neg, Int.natAbs_natCast]
        exact Nat.mul_le_mul_left sz hdAb
  · intro w
    refine (hload w).trans (le_of_eq ?_)
    congr 1
    change ∑ i ∈ E.lib.image Sum.inl ∪ (range M).image Sum.inr,
      incidentLoad (Sum.elim E.P (fun _ => ∅) i) w = _
    rw [sum_union]
    · rw [sum_image (fun a _ b _ h => Sum.inl_injective h),
        sum_image (fun a _ b _ h => Sum.inr_injective h)]
      simp [incidentLoad]
    · rw [disjoint_left]
      intro x hx hx'
      obtain ⟨i, -, rfl⟩ := mem_image.mp hx
      obtain ⟨k, -, hk⟩ := mem_image.mp hx'
      exact Sum.inr_ne_inl hk
  · have h1 := hlib
    have h2 : E.lib.card * (1 + 98 * (Ab * (Ab + 1))) =
        E.lib.card + Ab * E.lib.card + 97 * (Ab * (Ab + 1) * E.lib.card) +
          (Ab * Ab) * E.lib.card := by ring
    have h3 := Nat.mul_le_mul_left 97 hsumw
    rw [h2]
    omega

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
