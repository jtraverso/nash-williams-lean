/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.Prob

@[expose] public section

/-!
# From random sequences to random sets

If a property of the set `{u, v} ∪ {ω 1, …, ω m}` holds for every injective sequence `ω` of
vertices different from `u, v` outside an event of probability at most `p`, then (when `m` is
small compared to `N = n - 2`) at least a `(1 - 2p)`-fraction of the `(m+2)`-sets containing
`u, v` have the property.
-/

namespace NashWilliams18.Sampling

open Finset Pseudorandom

/-- `N^m ≤ 2 · N(N-1)⋯(N-m+1)` when `2m² ≤ N`. -/
lemma pow_le_two_descFactorial {N m : ℕ} (hN : 2 * m ^ 2 ≤ N) :
    ((N : ℝ) ^ m) ≤ 2 * (N.descFactorial m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hN
    exact_mod_cast this
  have hmN : m ≤ N := by nlinarith
  have h1 : ((N + 1 - m : ℕ) : ℝ) ^ m ≤ (N.descFactorial m : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N m
  have h2 : ((N : ℝ) - m) ≤ ((N + 1 - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have hNm : (0 : ℝ) ≤ (N : ℝ) - m := by
    have : (m : ℝ) ≤ N := by exact_mod_cast hmN
    linarith
  have h3 : ((N : ℝ) - m) ^ m ≤ (N.descFactorial m : ℝ) :=
    le_trans (pow_le_pow_left₀ hNm h2 m) h1
  have hB := one_add_mul_le_pow (a := -(m : ℝ) / N) (by
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hNpos]
    have : (m : ℝ) ≤ N := by exact_mod_cast hmN
    linarith) m
  have hsq : (2 * (m : ℝ) ^ 2) ≤ N := by exact_mod_cast hN
  have h4 : (1 : ℝ) / 2 ≤ 1 + (m : ℝ) * (-(m : ℝ) / N) := by
    rw [mul_div_assoc', mul_neg, neg_div, ← sub_eq_add_neg, le_sub_iff_add_le,
      ← le_sub_iff_add_le', div_le_iff₀ hNpos]
    nlinarith
  have h5 : (1 + -(m : ℝ) / N) * N = N - m := by field_simp; ring
  have h6 : ((N : ℝ) - m) ^ m = (1 + -(m : ℝ) / N) ^ m * N ^ m := by
    rw [← h5, mul_pow]
  have : (N : ℝ) ^ m / 2 ≤ ((N : ℝ) - m) ^ m := by
    rw [h6]
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ m := by positivity
    nlinarith
  linarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertices other than `u, v`. -/
abbrev Rest (u v : V) := {w : V // w ≠ u ∧ w ≠ v}

/-- The set `{u, v} ∪ {ω j}`. -/
def setOf (u v : V) {m : ℕ} (ω : Fin m → Rest u v) : Finset V :=
  insert u (insert v (univ.image fun j => (ω j).val))

lemma card_rest {u v : V} (huv : u ≠ v) : Fintype.card (Rest u v) = Fintype.card V - 2 := by
  rw [Fintype.card_subtype]
  have : (univ.filter fun w : V => w ≠ u ∧ w ≠ v) = (univ.erase u).erase v := by
    ext w; simp [and_comm]
  rw [this, card_erase_of_mem (by simp [Ne.symm huv]), card_erase_of_mem (mem_univ _),
    card_univ]
  omega

omit [Fintype V] in
lemma card_setOf {u v : V} (huv : u ≠ v) {m : ℕ} (ω : Fin m → Rest u v)
    (hω : Function.Injective ω) : (setOf u v ω).card = m + 2 := by
  unfold setOf
  have hinj : Function.Injective fun j => (ω j).val :=
    fun a b h => hω (Subtype.ext h)
  have hv : v ∉ univ.image fun j => (ω j).val := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j h => (ω j).2.2 h
  have hu : u ∉ insert v (univ.image fun j => (ω j).val) := by
    simp only [mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
    exact ⟨huv, fun j h => (ω j).2.1 h⟩
  rw [card_insert_of_notMem hu, card_insert_of_notMem hv, card_image_of_injective _ hinj]
  simp

/-- The counting conversion. -/
theorem card_sets_ge {u v : V} (huv : u ≠ v) (m : ℕ)
    (hN : 2 * m ^ 2 ≤ Fintype.card V - 2)
    (Pr : Finset V → Prop) [DecidablePred Pr] (Bad : (Fin m → Rest u v) → Prop)
    [DecidablePred Bad] (p : ℝ)
    (hBad : pProb (unif (Fin m) (Rest u v)) Bad ≤ p)
    (hgood : ∀ ω : Fin m → Rest u v, Function.Injective ω → ¬ Bad ω → Pr (setOf u v ω)) :
    (1 - 2 * p) * ((Fintype.card V - 2).choose m : ℝ) ≤
      ((((univ : Finset V).powersetCard (m + 2)).filter
        (fun S => u ∈ S ∧ v ∈ S ∧ Pr S)).card : ℝ) := by
  set N := Fintype.card V - 2 with hNdef
  have hcardR : Fintype.card (Rest u v) = N := card_rest huv
  set Inj := (univ : Finset (Fin m → Rest u v)).filter Function.Injective
  set Good := Inj.filter fun ω => ¬ Bad ω
  set Tgt := ((univ : Finset V).powersetCard (m + 2)).filter (fun S => u ∈ S ∧ v ∈ S ∧ Pr S)
  -- number of injective sequences
  have hInj : Inj.card = N.descFactorial m := by
    have h1 : Inj.card = Fintype.card {ω : Fin m → Rest u v // Function.Injective ω} :=
      (Fintype.card_subtype _).symm
    rw [h1, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
      Fintype.card_embedding_eq, hcardR, Fintype.card_fin]
  -- number of bad sequences
  have hpos : (0 : ℝ) < (N : ℝ) ^ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : 0 < N := by nlinarith
      positivity
  rw [pProb_unif, hcardR, Fintype.card_fin] at hBad
  have hp : 0 ≤ p := le_trans (by positivity) hBad
  have hBadc : (((univ : Finset (Fin m → Rest u v)).filter Bad).card : ℝ) ≤ p * (N : ℝ) ^ m := by
    have hpos : (0 : ℝ) < (N : ℝ) ^ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · have : 0 < N := by nlinarith
        positivity
    rwa [div_le_iff₀ hpos] at hBad
  -- good sequences
  have hGood : (N.descFactorial m : ℝ) - p * (N : ℝ) ^ m ≤ (Good.card : ℝ) := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Inj) (fun ω => ¬ Bad ω)
    have h2 : (Inj.filter fun ω => ¬ ¬ Bad ω).card ≤ ((univ : Finset _).filter Bad).card :=
      card_le_card fun ω hω => by simp_all
    have h3 : (N.descFactorial m : ℝ) ≤ Good.card + ((univ : Finset _).filter Bad).card := by
      rw [← hInj]; exact_mod_cast (h1.symm.le.trans (Nat.add_le_add_left h2 _))
    linarith
  -- the image lies in the target
  have hsub : Good.image (setOf u v) ⊆ Tgt := by
    intro S hS
    obtain ⟨ω, hω, rfl⟩ := mem_image.mp hS
    simp only [Good, Inj, mem_filter, mem_univ, true_and] at hω
    simp only [Tgt, mem_filter, mem_powersetCard, subset_univ, true_and]
    refine ⟨card_setOf huv ω hω.1, by simp [setOf], by simp [setOf], hgood ω hω.1 hω.2⟩
  -- fibers
  have hfib : ∀ S ∈ Good.image (setOf u v),
      (Good.filter fun ω => setOf u v ω = S).card ≤ m.factorial := by
    intro S hS
    obtain ⟨ω₀, hω₀, rfl⟩ := mem_image.mp hS
    simp only [Good, Inj, mem_filter, mem_univ, true_and] at hω₀
    set S := setOf u v ω₀
    have hS2 : S.card = m + 2 := card_setOf huv ω₀ hω₀.1
    have hT : Fintype.card {w : Rest u v // w.val ∈ S} ≤ m := by
      have : Fintype.card {w : Rest u v // w.val ∈ S} ≤ ((S.erase u).erase v).card := by
        rw [← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun w => ⟨w.1.1, ?_⟩) ?_
        · simp only [mem_erase]; exact ⟨w.1.2.2, w.1.2.1, w.2⟩
        · intro a b h
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext (Subtype.ext h)
      rw [card_erase_of_mem (by simp [S, setOf, Ne.symm huv]),
        card_erase_of_mem (by simp [S, setOf]), hS2] at this
      omega
    have hcard : (Good.filter fun ω => setOf u v ω = S).card ≤
        Fintype.card (Fin m ↪ {w : Rest u v // w.val ∈ S}) := by
      rw [← Fintype.card_coe]
      refine Fintype.card_le_of_injective (fun x => ⟨fun j => ⟨x.1 j, ?_⟩, ?_⟩) ?_
      · have hx := x.2
        simp only [Good, Inj, mem_filter, mem_univ, true_and] at hx
        have h0 : (x.1 j).val ∈ setOf u v x.1 := by simp [setOf]
        exact Eq.mp (congrArg (fun T => (x.1 j).val ∈ T) hx.2) h0
      · intro a b h
        have hx := x.2
        simp only [Good, Inj, mem_filter, mem_univ, true_and] at hx
        exact hx.1.1 (congrArg Subtype.val h)
      · intro a b h
        apply Subtype.ext
        funext j
        have hh := congrArg (fun e : Fin m ↪ {w : Rest u v // w.val ∈ S} => (e j).val) h
        change a.val j = b.val j at hh
        exact hh
    rw [Fintype.card_embedding_eq, Fintype.card_fin] at hcard
    refine hcard.trans ?_
    rcases lt_or_eq_of_le hT with h | h
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]; exact Nat.zero_le _
    · rw [h, Nat.descFactorial_self]
  have hmain := card_le_mul_card_image Good m.factorial hfib
  have hTg : (Good.card : ℝ) ≤ m.factorial * (Tgt.card : ℝ) := by
    have := hmain.trans (Nat.mul_le_mul_left _ (card_le_card hsub))
    exact_mod_cast this
  have hpow := pow_le_two_descFactorial hN
  have hdesc : (N.descFactorial m : ℝ) = m.factorial * (N.choose m : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have : (m.factorial : ℝ) * ((1 - 2 * p) * (N.choose m : ℝ)) ≤ m.factorial * (Tgt.card : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_left this hfac

end NashWilliams18.Sampling
