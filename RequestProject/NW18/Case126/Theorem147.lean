/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.Hinge
public import RequestProject.NW18.Theorem124

@[expose] public section

/-!
# Theorem 14.7 (idealized `F_i`-decomposition theorem), generic part

For a family `F` of `4`-partitioned triangles in which every allowed pair of parts has exactly
two third parts (`TwoThirds F`; true for `F₁` and `F₂`), an `ε`-balanced `ε`-nearly-complete
`F`-blowup (`IsIdealizedT F ε G p`)

* carries the constant `8`-regular almost fractional packing (Claim 14.7.1,
  `isRegularAlmostPacking_ideal`),
* is `1/5`-anti-edgeful (Claim 14.7.3, `antiEdgeful_ideal`),
* is `(1/25, 6)`-hingeful (Claim 14.7.4, `hingeful_ideal`).

`theorem_14_7_of_fracDiv` then applies Theorem 13.16 (hypothesis `h1316`); fractional
divisibility (Claim 14.7.2) is a hypothesis here and is proved separately for each family.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma triple_perm1 {t : ℕ} (a b c : Fin t) : ({a, b, c} : Multiset (Fin t)) = {c, a, b} := by
  rw [triple_swap23, triple_swap12]

lemma triple_perm2 {t : ℕ} (a b c : Fin t) : ({a, b, c} : Multiset (Fin t)) = {c, b, a} := by
  rw [triple_swap12, triple_swap23, triple_swap12]

omit [DecidableEq V] in
lemma IsIdealizedT.miss {F : Finset (Multiset (Fin 4))} {ε : ℝ} {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (h : IsIdealizedT F ε G p) {v : V} {j : Fin 4}
    (hj : AllowedT F (p v) j) : ((clsT p j).card : ℝ) - degT G p v j ≤ ε * Fintype.card V := by
  have := h.2.2 v j hj; linarith

omit [DecidableEq V] in
lemma IsIdealizedT.lo {F : Finset (Multiset (Fin 4))} {ε : ℝ} {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (h : IsIdealizedT F ε G p) (i : Fin 4) :
    (1 - ε) * Fintype.card V / 4 ≤ ((clsT p i).card : ℝ) := by
  have := h.1 i; simpa using this

/-- **Claim 14.7.1.** The constant weighting `2 / ((1 + 3ε) n)` is an `8`-regular
`ε'`-almost fractional `F`-packing for every `ε' ≥ 12 ε`. -/
lemma isRegularAlmostPacking_ideal {F : Finset (Multiset (Fin 4))} (hF : TwoThirds F)
    {ε ε' : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) (hεε : 12 * ε ≤ ε') {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 4} (hn : 0 < Fintype.card V)
    (h : IsIdealizedT F ε G p) :
    IsRegularAlmostPacking p F G 8 ε' (fun _ => 2 / ((1 + 3 * ε) * Fintype.card V)) := by
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : 0 < (1 + 3 * ε) * (Fintype.card V : ℝ) := by positivity
  refine ⟨fun s _ => ⟨?_, ?_⟩, fun e he => ?_⟩
  · rw [div_le_div_iff₀ (by positivity) hd]; nlinarith
  · rw [div_le_div_iff₀ hd hn']; nlinarith
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := by simpa using he
  rw [sum_const, card_copies_through_eq_sum p F G huv, nsmul_eq_mul]
  set T := thirdsT F (p u) (p v) with hT
  have hT2 : T.card = 2 := hF _ _ (h.2.1 u v huv)
  set c : ℝ := ((∑ l ∈ T, (comNbT G p u v l).card : ℕ) : ℝ) with hc
  have hlow : ∀ l ∈ T, (1 - ε) * Fintype.card V / 4 - 2 * ε * Fintype.card V ≤
      ((comNbT G p u v l).card : ℝ) := by
    intro l hl
    have hl' : ({p u, p v, l} : Multiset (Fin 4)) ∈ F := (mem_filter.mp hl).2
    have h1 := h.miss (allowedT_of_mem hl')
    have h2 := h.miss (allowedT_of_mem' hl')
    have h3 := card_comNbT_ge G p u v l
    have h4 := h.lo l
    linarith
  have hup : ∀ l ∈ T, ((comNbT G p u v l).card : ℝ) ≤ (1 + 3 * ε) * Fintype.card V / 4 := by
    intro l _
    have h1 : ((comNbT G p u v l).card : ℝ) ≤ (clsT p l).card := by
      exact_mod_cast card_comNbT_le_class G p u v l
    exact h1.trans (card_clsT_le_four p h.lo l)
  have hcl : 2 * ((1 - ε) * Fintype.card V / 4 - 2 * ε * Fintype.card V) ≤ c := by
    rw [hc]; push_cast
    have := card_nsmul_le_sum T (fun l => ((comNbT G p u v l).card : ℝ)) _ hlow
    rw [hT2, nsmul_eq_mul] at this; push_cast at this; linarith
  have hcu : c ≤ 2 * ((1 + 3 * ε) * Fintype.card V / 4) := by
    rw [hc]; push_cast
    have := sum_le_card_nsmul T (fun l => ((comNbT G p u v l).card : ℝ)) _ hup
    rw [hT2, nsmul_eq_mul] at this; push_cast at this; linarith
  constructor
  · rw [mul_div_assoc', le_div_iff₀ hd]; nlinarith
  · rw [mul_div_assoc', div_le_one hd]; linarith

/-- **Claim 14.7.3.** An idealized blowup (`ε ≤ 1/100`) is `1/5`-`F`-anti-edgeful. -/
lemma antiEdgeful_ideal {F : Finset (Multiset (Fin 4))} {ε : ℝ} (hε : ε ≤ 1 / 100)
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} (h : IsIdealizedT F ε G p) :
    AntiEdgeful p F G (1 / 5) := by
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  intro τ hτ i j k hτeq u v _ hu hv
  subst hτeq
  have h1 := h.miss (v := u) (j := k) (by rw [hu]; exact allowedT_of_mem hτ)
  have h2 := h.miss (v := v) (j := k) (by rw [hv]; exact allowedT_of_mem' hτ)
  have h3 := card_comNbT_ge G p u v k
  have h4 := h.lo k
  have e : ((comNbT G p u v k).card : ℝ) =
      ((univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)).card : ℝ) := rfl
  rw [← e]
  nlinarith

/-- **Claim 14.7.4.** An idealized blowup (`ε ≤ 1/100`, `n ≥ 1000`) is `(1/25, 6)`-`F`-hingeful
(with the normalisation `n^{i-4}`): six-vertex hinges. -/
lemma hingeful_ideal {F : Finset (Multiset (Fin 4))} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4}
    (hn : 1000 ≤ (Fintype.card V : ℝ)) (h : IsIdealizedT F ε G p) :
    HingefulN p F G (1 / 25) 6 := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  intro S S' hS hS' h1
  obtain ⟨u₁, u₂, v₁, v₂, h12, h13, h14, h23, h24, h34, rfl, rfl⟩ :=
    two_triangles_sharing_edge hS.1.2 hS'.1.2 h1
  have adj : ∀ {T : Finset V} {x y : V}, IsCopy p F G T → x ∈ T → y ∈ T → x ≠ y →
      G.Adj x y := fun hT hx hy hxy => hT.1.1 (mem_coe.mpr hx) (mem_coe.mpr hy) hxy
  have a12 : G.Adj u₁ u₂ := adj hS (by simp) (by simp) h12
  have a11 : G.Adj u₁ v₁ := adj hS (by simp) (by simp) h13
  have a21 : G.Adj u₂ v₁ := adj hS (by simp) (by simp) h23
  have a1' : G.Adj u₁ v₂ := adj hS' (by simp) (by simp) h14
  have a2' : G.Adj u₂ v₂ := adj hS' (by simp) (by simp) h24
  have hT1 := hS.2
  rw [triple_val_map p h12 h13 h23] at hT1
  have hT2 := hS'.2
  rw [triple_val_map p h12 h14 h24] at hT2
  have hpow : n ^ (((6 : ℕ) : ℤ) - 4) = n ^ 2 := by
    rw [show ((6 : ℕ) : ℤ) - 4 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  refine ⟨6, by simp, ?_⟩
  rw [hpow]
  set Bd : Finset V := {u₁, u₂, v₁, v₂} with hBddef
  have hBd : (Bd.card : ℝ) ≤ 4 := by exact_mod_cast card_le_four
  have hr : (0 : ℝ) ≤ n / 5 := by positivity
  -- allowed pairs
  have al12 : AllowedT F (p u₁) (p u₂) := ⟨_, hT1⟩
  have al21 := allowedT_symm al12
  have alv1u2 : AllowedT F (p v₁) (p u₂) := allowedT_symm (allowedT_of_mem' hT1)
  have alv2u2 : AllowedT F (p v₂) (p u₂) := allowedT_symm (allowedT_of_mem' hT2)
  have alv1u1 : AllowedT F (p v₁) (p u₁) := allowedT_symm (allowedT_of_mem hT1)
  have alv2u1 : AllowedT F (p v₂) (p u₁) := allowedT_symm (allowedT_of_mem hT2)
  have hlo1 := h.lo (p u₁)
  have hlo2 := h.lo (p u₂)
  have hsq : 1 / 25 * n ^ 2 = n / 5 * (n / 5) := by ring
  have hεn : ε * n ≤ n / 100 := by nlinarith
  rw [hsq]
  refine hinge6_count_gen G p F u₁ u₂ v₁ v₂ (candT G p (p u₂) {u₁, v₁, v₂} Bd)
    (fun x => candT G p (p u₁) {u₂, v₁, v₂, x} Bd) hr ?_ ?_ ?_
  · have := card_candT_ge G p (p u₂) {u₁, v₁, v₂} Bd (m := ε * n) (by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact h.miss al12
      · exact h.miss alv1u2
      · exact h.miss alv2u2)
    have hc : (({u₁, v₁, v₂} : Finset V).card : ℝ) ≤ 3 := by exact_mod_cast card_le_three
    have hm : (({u₁, v₁, v₂} : Finset V).card : ℝ) * (ε * n) ≤ 3 * (ε * n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  · intro x hx
    have px := (mem_candT.mp hx).1.1
    have := card_candT_ge G p (p u₁) {u₂, v₁, v₂, x} Bd (m := ε * n) (by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact h.miss al21
      · exact h.miss alv1u1
      · exact h.miss alv2u1
      · exact h.miss (by rw [px]; exact al21))
    have hc : (({u₂, v₁, v₂, x} : Finset V).card : ℝ) ≤ 4 := by exact_mod_cast card_le_four
    have hm : (({u₂, v₁, v₂, x} : Finset V).card : ℝ) * (ε * n) ≤ 4 * (ε * n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  · intro x hx y hy
    obtain ⟨⟨px, hxZ⟩, hxB⟩ := mem_candT.mp hx
    obtain ⟨⟨py, hyZ⟩, hyB⟩ := mem_candT.mp hy
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hxZ hyZ
    refine ⟨vec6_injective_of h12 h13 h14 h23 h24 h34 hxB hyB (G.ne_of_adj hyZ.2.2.2),
      hxZ.1, hyZ.1, hxZ.2.1, hyZ.2.1, hxZ.2.2, hyZ.2.2.1, hyZ.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [px, ← triple_perm1]; exact hT1
    · rw [py, triple_swap23, ← triple_perm1]; exact hT1
    · rw [px, py, ← triple_perm2]; exact hT2
    · rw [px, ← triple_perm1]; exact hT2
    · rw [py, triple_swap23, ← triple_perm1]; exact hT2
    · rw [px, py, ← triple_perm2]; exact hT1

/-- **Theorem 14.7 from Theorem 13.16, given fractional divisibility.** For a family `F`
of `4`-partitioned triangles with `TwoThirds F` there are `ε > 0` and `n₀` such that every
fractionally and integrally `F`-divisible `ε`-balanced `ε`-nearly-complete `F`-blowup on
`n ≥ n₀` vertices has an `F`-decomposition. -/
theorem theorem_14_7_of_fracDiv (h1316 : Theorem1316Statement)
    (F : Finset (Multiset (Fin 4))) (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hF : TwoThirds F) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      IsFracDiv p F G.edgeFinset → IsIntDiv p F G.edgeFinset → IsIdealizedT F ε G p →
      HasDecomp p F G.edgeFinset := by
  obtain ⟨ε', hε', n₁, h⟩ := h1316 4 F hF3 (1 / 25) (by norm_num) 8 (by norm_num)
  refine ⟨min (ε' / 12) (1 / 100), lt_min (by positivity) (by norm_num), max n₁ 1000,
    fun V _ _ p G _ hn hfrac hint hid => ?_⟩
  set ε := min (ε' / 12) (1 / 100)
  have hε0 : 0 ≤ ε := le_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 / 100 := min_le_right _ _
  have hε2 : 12 * ε ≤ ε' := by have := min_le_left (ε' / 12) (1 / 100); linarith
  have hnpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) hn
  have hn1000 : (1000 : ℝ) ≤ Fintype.card V := by
    have : 1000 ≤ Fintype.card V := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  refine h V p G (le_trans (le_max_left _ _) hn) hfrac
    ⟨fun _ => 2 / ((1 + 3 * ε) * Fintype.card V), ?_⟩ hint ?_ ?_
  · have := isRegularAlmostPacking_ideal hF hε0 hε1 hε2 hnpos hid
    simpa using this
  · exact AntiEdgeful.mono (by norm_num) (antiEdgeful_ideal hε1 hid)
  · exact (hingeful_ideal hε0 hε1 hn1000 hid).mono le_rfl (by norm_num)

end NashWilliams18
