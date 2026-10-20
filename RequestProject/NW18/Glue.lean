/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.CloseCert

@[expose] public section

/-!
# Gluing two structured halves

`V` is split into `N` and its complement; `N` carries a structure `(N₁, b₁)` (complete
bipartite if `b₁`, two cliques otherwise) and a subset `D` of the complement carries a structure
`(B₁, b₂)`.  The four classes `N₁, N ∖ N₁, B₁, rest` together with the pattern `Pat b₁ b₂`
(the two halves completely joined) give a certificate whose cost is controlled by the local
deviations.
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pattern: classes `0, 1` carry the structure `b₁`, classes `2, 3` the structure `b₂`,
and the two halves are completely joined. -/
def Pat (b₁ b₂ : Bool) (i j : Fin 4) : Bool :=
  if (i.val < 2) ≠ (j.val < 2) then true
  else if i.val < 2 then (if i = j then !b₁ else b₁) else (if i = j then !b₂ else b₂)

lemma Pat_symm (b₁ b₂ : Bool) (i j : Fin 4) : Pat b₁ b₂ i j = Pat b₁ b₂ j i := by
  revert i j; cases b₁ <;> cases b₂ <;> decide

lemma Pat_tt : Pat true true = patT2T2 := by funext i j; revert i j; decide
lemma Pat_ft : Pat false true = patT2bT2 := by funext i j; revert i j; decide
lemma Pat_ff : Pat false false = patT2bT2b := by funext i j; revert i j; decide

/-- Exchange of the two halves. -/
def swapHalves (i : Fin 4) : Fin 4 := ⟨(i.val + 2) % 4, Nat.mod_lt _ (by norm_num)⟩

lemma Pat_tf (i j : Fin 4) : Pat true false i j = patT2bT2 (swapHalves i) (swapHalves j) := by
  revert i j; decide

/-- The class map. -/
def glueMap (N N₁ B₁ : Finset V) (x : V) : Fin 4 :=
  if x ∈ N then (if x ∈ N₁ then 0 else 1) else (if x ∈ B₁ then 2 else 3)

section
variable (N N₁ D B₁ : Finset V) (b₁ b₂ : Bool)
omit [Fintype V]

lemma pat_NN {x z : V} (hx : x ∈ N) (hz : z ∈ N) :
    Pat b₁ b₂ (glueMap N N₁ B₁ x) (glueMap N N₁ B₁ z) = true ↔ z ∈ tgt N N₁ b₁ x := by
  simp only [glueMap, hx, hz, if_true, tgt]
  by_cases h1 : x ∈ N₁ <;> by_cases h2 : z ∈ N₁ <;> cases b₁ <;>
    simp [h1, h2, hz, Pat]

lemma pat_NB {x z : V} (hx : x ∈ N) (hz : z ∉ N) :
    Pat b₁ b₂ (glueMap N N₁ B₁ x) (glueMap N N₁ B₁ z) = true := by
  simp only [glueMap, hx, hz, if_true, if_false]
  by_cases h1 : x ∈ N₁ <;> by_cases h2 : z ∈ B₁ <;> simp [h1, h2, Pat]

lemma pat_BN {x z : V} (hx : x ∉ N) (hz : z ∈ N) :
    Pat b₁ b₂ (glueMap N N₁ B₁ x) (glueMap N N₁ B₁ z) = true := by
  rw [Pat_symm]; exact pat_NB N N₁ B₁ b₁ b₂ hz hx

lemma pat_DD {x z : V} (hx : x ∉ N) (hz : z ∉ N) (hzD : z ∈ D) :
    Pat b₁ b₂ (glueMap N N₁ B₁ x) (glueMap N N₁ B₁ z) = true ↔ z ∈ tgt D B₁ b₂ x := by
  simp only [glueMap, hx, hz, if_false, tgt]
  by_cases h1 : x ∈ B₁ <;> by_cases h2 : z ∈ B₁ <;> cases b₂ <;>
    simp [h1, h2, hzD, Pat]

end

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local cost at a vertex of `N`. -/
lemma cost_N (N N₁ B₁ : Finset V) (b₁ b₂ : Bool) {x : V} (hx : x ∈ N) :
    (symmDiff (univ.filter (G.Adj x)) (patNb (Pat b₁ b₂) (glueMap N N₁ B₁) x)).card ≤
      (symmDiff (nbIn G N x) (tgt N N₁ b₁ x)).card + 1 +
        ((univ \ N) \ univ.filter (G.Adj x)).card := by
  have hsub : symmDiff (univ.filter (G.Adj x)) (patNb (Pat b₁ b₂) (glueMap N N₁ B₁) x) ⊆
      (symmDiff (nbIn G N x) (tgt N N₁ b₁ x) ∪ {x}) ∪ ((univ \ N) \ univ.filter (G.Adj x)) := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp
    by_cases hzN : z ∈ N
    · refine mem_union_left _ (mem_union_left _ ?_)
      have hp := pat_NN N N₁ B₁ b₁ b₂ hx hzN
      simp only [mem_symmDiff, mem_filter, mem_univ, true_and, patNb, ne_eq, hzx,
        not_false_eq_true, hp, nbIn, hzN] at hz ⊢
      exact hz
    · refine mem_union_right _ ?_
      have hp := pat_NB N N₁ B₁ b₁ b₂ hx hzN
      simp only [mem_symmDiff, mem_filter, mem_univ, true_and, patNb, ne_eq, hzx,
        not_false_eq_true, hp, mem_sdiff, hzN] at hz ⊢
      tauto
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have := card_union_le (symmDiff (nbIn G N x) (tgt N N₁ b₁ x)) {x}
  rw [card_singleton] at this
  omega

/-- Local cost at a vertex of `D`. -/
lemma cost_D (N N₁ D B₁ : Finset V) (b₁ b₂ : Bool) (hD : Disjoint D N)
    {x : V} (hx : x ∈ D) :
    (symmDiff (univ.filter (G.Adj x)) (patNb (Pat b₁ b₂) (glueMap N N₁ B₁) x)).card ≤
      (N \ univ.filter (G.Adj x)).card + (symmDiff (nbIn G D x) (tgt D B₁ b₂ x)).card + 1 +
        ((univ \ N) \ D).card := by
  have hxN : x ∉ N := disjoint_left.mp hD hx
  have hsub : symmDiff (univ.filter (G.Adj x)) (patNb (Pat b₁ b₂) (glueMap N N₁ B₁) x) ⊆
      ((N \ univ.filter (G.Adj x) ∪ symmDiff (nbIn G D x) (tgt D B₁ b₂ x)) ∪ {x}) ∪
        ((univ \ N) \ D) := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp
    by_cases hzN : z ∈ N
    · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
      have hp := pat_BN N N₁ B₁ b₁ b₂ hxN hzN
      simp only [mem_symmDiff, mem_filter, mem_univ, true_and, patNb, ne_eq, hzx,
        not_false_eq_true, hp, mem_sdiff, hzN] at hz ⊢
      tauto
    by_cases hzD : z ∈ D
    · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
      have hp := pat_DD N N₁ D B₁ b₁ b₂ hxN hzN hzD
      simp only [mem_symmDiff, mem_filter, mem_univ, true_and, patNb, ne_eq, hzx,
        not_false_eq_true, hp, nbIn, hzD] at hz ⊢
      exact hz
    · exact mem_union_right _ (by simp [hzN, hzD])
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have h1 := card_union_le (N \ univ.filter (G.Adj x) ∪ symmDiff (nbIn G D x) (tgt D B₁ b₂ x)) {x}
  have h2 := card_union_le (N \ univ.filter (G.Adj x)) (symmDiff (nbIn G D x) (tgt D B₁ b₂ x))
  rw [card_singleton] at h1
  omega

/-- **Gluing.** -/
theorem glue_cost (N N₁ D B₁ E₁ E₂ : Finset V) (b₁ b₂ : Bool)
    (hD : Disjoint D N) {e e' k : ℝ} (he : 0 ≤ e) (he' : 0 ≤ e') (hk : 0 ≤ k)
    (hdev₁ : ∀ x ∈ N, x ∉ E₁ → ((symmDiff (nbIn G N x) (tgt N N₁ b₁ x)).card : ℝ) ≤ e)
    (hdev₂ : ∀ x ∈ D, x ∉ E₂ → ((symmDiff (nbIn G D x) (tgt D B₁ b₂ x)).card : ℝ) ≤ e')
    (hcr₁ : ∀ x ∈ N, x ∉ E₁ → (((univ \ N) \ univ.filter (G.Adj x)).card : ℝ) ≤ k)
    (hcr₂ : ∀ x ∈ D, x ∉ E₂ → ((N \ univ.filter (G.Adj x)).card : ℝ) ≤ k) :
    (patCost G (Pat b₁ b₂) (glueMap N N₁ B₁) : ℝ) ≤
      N.card * (e + 1 + k) + E₁.card * Fintype.card V +
        D.card * (k + e' + 1 + ((univ \ N) \ D).card) +
        (E₂.card + ((univ \ N) \ D).card) * Fintype.card V := by
  set c : V → ℝ := fun x =>
    ((symmDiff (univ.filter (G.Adj x)) (patNb (Pat b₁ b₂) (glueMap N N₁ B₁) x)).card : ℝ)
  have hc_le : ∀ x, c x ≤ Fintype.card V := fun x => by
    simp only [c]; exact_mod_cast card_le_univ _
  have hc0 : ∀ x, 0 ≤ c x := fun x => by positivity
  have hcost : (patCost G (Pat b₁ b₂) (glueMap N N₁ B₁) : ℝ) = ∑ x, c x := by
    simp [patCost, c]
  rw [hcost]
  set R := (univ \ N) \ D
  have hpart : (univ : Finset V) = N ∪ D ∪ R := by
    ext x; simp only [mem_univ, mem_union, true_iff, R, mem_sdiff]; tauto
  have hdisj1 : Disjoint (N ∪ D) R := by
    rw [disjoint_left]; intro x hx hR
    simp only [R, mem_sdiff, mem_union] at hx hR; tauto
  rw [hpart, sum_union hdisj1, sum_union (disjoint_comm.mp hD)]
  -- the part `N`
  have hN : ∑ x ∈ N, c x ≤ N.card * (e + 1 + k) + E₁.card * Fintype.card V := by
    rw [← sum_filter_add_sum_filter_not N (fun x => x ∈ E₁)]
    have h1 : ∑ x ∈ N.filter (fun x => x ∈ E₁), c x ≤ E₁.card * Fintype.card V := by
      calc _ ≤ ∑ x ∈ N.filter (fun x => x ∈ E₁), (Fintype.card V : ℝ) :=
            sum_le_sum fun x _ => hc_le x
        _ = (N.filter (fun x => x ∈ E₁)).card * (Fintype.card V : ℝ) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            gcongr
            intro x hx; exact (mem_filter.mp hx).2
    have h2 : ∑ x ∈ N.filter (fun x => x ∉ E₁), c x ≤ N.card * (e + 1 + k) := by
      calc _ ≤ ∑ x ∈ N.filter (fun x => x ∉ E₁), (e + 1 + k) := by
            refine sum_le_sum fun x hx => ?_
            obtain ⟨hxN, hxE⟩ := mem_filter.mp hx
            have := cost_N G N N₁ B₁ b₁ b₂ hxN
            have h' : c x ≤ ((symmDiff (nbIn G N x) (tgt N N₁ b₁ x)).card : ℝ) + 1 +
                (((univ \ N) \ univ.filter (G.Adj x)).card : ℝ) := by
              simp only [c]; exact_mod_cast this
            linarith [hdev₁ x hxN hxE, hcr₁ x hxN hxE]
        _ = (N.filter (fun x => x ∉ E₁)).card * (e + 1 + k) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ N.card * (e + 1 + k) := by
            have hek : 0 ≤ e + 1 + k := by linarith
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) hek
    linarith
  -- the part `D`
  have hDp : ∑ x ∈ D, c x ≤ D.card * (k + e' + 1 + R.card) + E₂.card * Fintype.card V := by
    rw [← sum_filter_add_sum_filter_not D (fun x => x ∈ E₂)]
    have h1 : ∑ x ∈ D.filter (fun x => x ∈ E₂), c x ≤ E₂.card * Fintype.card V := by
      calc _ ≤ ∑ x ∈ D.filter (fun x => x ∈ E₂), (Fintype.card V : ℝ) :=
            sum_le_sum fun x _ => hc_le x
        _ = (D.filter (fun x => x ∈ E₂)).card * (Fintype.card V : ℝ) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            gcongr
            intro x hx; exact (mem_filter.mp hx).2
    have h2 : ∑ x ∈ D.filter (fun x => x ∉ E₂), c x ≤ D.card * (k + e' + 1 + R.card) := by
      calc _ ≤ ∑ x ∈ D.filter (fun x => x ∉ E₂), (k + e' + 1 + (R.card : ℝ)) := by
            refine sum_le_sum fun x hx => ?_
            obtain ⟨hxD, hxE⟩ := mem_filter.mp hx
            have := cost_D G N N₁ D B₁ b₁ b₂ hD hxD
            have h' : c x ≤ ((N \ univ.filter (G.Adj x)).card : ℝ) +
                ((symmDiff (nbIn G D x) (tgt D B₁ b₂ x)).card : ℝ) + 1 + (R.card : ℝ) := by
              simp only [c]; exact_mod_cast this
            linarith [hdev₂ x hxD hxE, hcr₂ x hxD hxE]
        _ = (D.filter (fun x => x ∉ E₂)).card * (k + e' + 1 + (R.card : ℝ)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ D.card * (k + e' + 1 + R.card) := by
            have hek : 0 ≤ k + e' + 1 + (R.card : ℝ) := by
              have : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
              linarith
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) hek
    linarith
  -- the rest
  have hR : ∑ x ∈ R, c x ≤ R.card * Fintype.card V := by
    calc _ ≤ ∑ x ∈ R, (Fintype.card V : ℝ) := sum_le_sum fun x _ => hc_le x
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  linarith

lemma fib_glueMap (N N₁ B₁ : Finset V) (hN₁ : N₁ ⊆ N) (hB₁ : Disjoint B₁ N) :
    fib (glueMap N N₁ B₁) 0 = N₁.card ∧ fib (glueMap N N₁ B₁) 1 = (N \ N₁).card ∧
      fib (glueMap N N₁ B₁) 2 = B₁.card ∧ fib (glueMap N N₁ B₁) 3 = ((univ \ N) \ B₁).card := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold fib <;> apply congrArg Finset.card
  all_goals
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    by_cases hx : x ∈ N <;> by_cases h1 : x ∈ N₁ <;> by_cases h2 : x ∈ B₁ <;>
    simp [glueMap, hx, h1, h2] <;>
    first | exact False.elim (hx (hN₁ h1)) | exact False.elim (disjoint_left.mp hB₁ h2 hx)

end NashWilliams18
