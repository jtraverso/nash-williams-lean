/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Phases

/-!
# From two structured halves to closeness to an extremal graph
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex misses few vertices of `S` if it has few neighbours outside `S`. -/
lemma cross_bound (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (S : Finset V) (x : V) :
    ((S \ univ.filter (G.Adj x)).card : ℝ) ≤
      Fintype.card V / 4 - (univ \ S).card + (nbIn G (univ \ S) x).card := by
  have h1 : (nbIn G S x).card + (nbIn G (univ \ S) x).card = G.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← nbIn_univ]
    have : nbIn G univ x = nbIn G S x ∪ nbIn G (univ \ S) x := by
      ext y; simp [nbIn]; tauto
    rw [this, card_union_of_disjoint]
    rw [disjoint_left]; intro y h1 h2
    simp [nbIn] at h1 h2; exact h2.1 h1.1
  have h2 : (S \ univ.filter (G.Adj x)).card + (nbIn G S x).card = S.card := by
    have : S \ univ.filter (G.Adj x) = S.filter (fun y => ¬ G.Adj x y) := by
      ext y; simp
    rw [this, nbIn, add_comm]
    exact card_filter_add_card_filter_not _
  have h3 : (univ \ S).card + S.card = Fintype.card V := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_univ S
    omega
  have h4 : G.minDegree ≤ G.degree x := G.minDegree_le_degree x
  have h5 : (3 : ℝ) * Fintype.card V ≤ 4 * G.minDegree := by exact_mod_cast hδ
  have h6 : (G.minDegree : ℝ) ≤ G.degree x := by exact_mod_cast h4
  have h1' : ((nbIn G S x).card : ℝ) + (nbIn G (univ \ S) x).card = G.degree x := by
    exact_mod_cast h1
  have h2' : ((S \ univ.filter (G.Adj x)).card : ℝ) + (nbIn G S x).card = S.card := by
    exact_mod_cast h2
  have h3' : ((univ \ S).card : ℝ) + S.card = Fintype.card V := by exact_mod_cast h3
  linarith

omit [Fintype V] in
lemma card_nbIn_le_tgt (D D₁ : Finset V) (b : Bool) (x : V) {e : ℝ}
    (h : ((symmDiff (nbIn G D x) (tgt D D₁ b x)).card : ℝ) ≤ e) :
    ((nbIn G D x).card : ℝ) ≤ (tgt D D₁ b x).card + e := by
  have := card_ge_of_symmDiff (nbIn G D x) (tgt D D₁ b x)
  linarith

omit [Fintype V] [DecidableEq V] in
lemma card_tgt_le (D D₁ : Finset V) (b : Bool) (x : V) [DecidableEq V] {t : ℝ}
    (h1 : (D₁.card : ℝ) ≤ t) (h2 : ((D \ D₁).card : ℝ) ≤ t) :
    ((tgt D D₁ b x).card : ℝ) ≤ t := by
  unfold tgt; split_ifs <;> assumption

omit [DecidableEq V] in
lemma fib_swap (f : V → Fin 4) (i : Fin 4) :
    fib (fun x => swapHalves (f x)) i = fib f (swapHalves i) := by
  unfold fib; congr 1; ext x
  simp only [mem_filter, mem_univ, true_and]
  have hss : ∀ j : Fin 4, swapHalves (swapHalves j) = j := by decide
  constructor
  · intro h; rw [← h, hss]
  · intro h; rw [h, hss]

lemma patCost_swap (f : V → Fin 4) :
    patCost G patT2bT2 (fun x => swapHalves (f x)) = patCost G (Pat true false) f := by
  unfold patCost patNb
  congr 1; ext x; congr 2; ext y
  simp only [mem_filter, mem_univ, true_and, Pat_tf]

/-- The certificate gives closeness to one of the three extremal graphs. -/
lemma isCloseToExtremal_of_glue (N N₁ B₁ : Finset V) (b₁ b₂ : Bool) {θ : ℝ}
    (hcost : (patCost G (Pat b₁ b₂) (glueMap N N₁ B₁) : ℝ) ≤ θ * (Fintype.card V : ℝ) ^ 2)
    (hfib : ∀ i, |(fib (glueMap N N₁ B₁) i : ℝ) - Fintype.card V / 4| ≤ θ * Fintype.card V)
    (hn : 9 ≤ θ * Fintype.card V) :
    IsCloseToExtremal (6 * θ) G := by
  cases b₁ <;> cases b₂
  · right; right
    rw [Pat_ff] at hcost
    exact isClose_of_cert G patT2bT2b (by decide) _ hcost hfib hn
  · right; left
    rw [Pat_ft] at hcost
    exact isClose_of_cert G patT2bT2 (by decide) _ hcost hfib hn
  · right; left
    rw [← patCost_swap] at hcost
    refine isClose_of_cert G patT2bT2 (by decide) _ hcost (fun i => ?_) hn
    rw [fib_swap]; exact hfib _
  · left
    rw [Pat_tt] at hcost
    exact isClose_of_cert G patT2T2 (by decide) _ hcost hfib hn

lemma cost_arith {cost m n e₁ E₁c d r E₂c s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100)
    (hsn : 2 ≤ s * n) (hmn : m ≤ n) (he0 : 0 ≤ e₁)
    (he1 : e₁ ≤ s ^ 2 * n / 500) (hE₁ : E₁c ≤ e₁) (hd0 : 0 ≤ d) (hdn : d ≤ n / 2)
    (hr0 : 0 ≤ r) (hr : r ≤ s ^ 2 * n / 100) (hE₂ : E₂c ≤ 20 * s * d)
    (hcost : cost ≤ m * (e₁ + 1 + 21 * s * n) + E₁c * n +
      d * (21 * s * n + 20 * s * d + 1 + r) + (E₂c + r) * n) :
    cost ≤ (50 * s) * n ^ 2 := by
  have hn0 : 0 < n := by nlinarith
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have hsn2 : n ≤ s * n ^ 2 / 2 := by nlinarith
  have hS0 : 0 ≤ s * n ^ 2 := by positivity
  have he : e₁ ≤ s * n / 50000 := by
    have : s ^ 2 * n ≤ s / 100 * n := mul_le_mul_of_nonneg_right hs2 hn0.le
    linarith
  have hr' : r ≤ s * n / 10000 := by
    have : s ^ 2 * n ≤ s / 100 * n := mul_le_mul_of_nonneg_right hs2 hn0.le
    linarith
  have hsd : 20 * s * d ≤ 10 * s * n := by nlinarith
  have t1 : m * (e₁ + 1 + 21 * s * n) ≤ n * (s * n / 50000 + 1 + 21 * s * n) := by
    have h0 : 0 ≤ e₁ + 1 + 21 * s * n := by positivity
    calc m * (e₁ + 1 + 21 * s * n) ≤ n * (e₁ + 1 + 21 * s * n) :=
          mul_le_mul_of_nonneg_right hmn h0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hn0.le
  have t2 : E₁c * n ≤ s * n / 50000 * n := mul_le_mul_of_nonneg_right (by linarith) hn0.le
  have t3 : d * (21 * s * n + 20 * s * d + 1 + r) ≤
      n / 2 * (21 * s * n + 10 * s * n + 1 + s * n / 10000) := by
    have h0 : 0 ≤ 21 * s * n + 20 * s * d + 1 + r := by positivity
    calc d * (21 * s * n + 20 * s * d + 1 + r) ≤ n / 2 * (21 * s * n + 20 * s * d + 1 + r) :=
          mul_le_mul_of_nonneg_right hdn h0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t4 : (E₂c + r) * n ≤ (10 * s * n + s * n / 10000) * n :=
    mul_le_mul_of_nonneg_right (by linarith) hn0.le
  have e1 : n * (s * n / 50000 + 1 + 21 * s * n) = (21 + 1 / 50000) * (s * n ^ 2) + n := by
    ring
  have e2 : s * n / 50000 * n = (1 / 50000) * (s * n ^ 2) := by ring
  have e3 : n / 2 * (21 * s * n + 10 * s * n + 1 + s * n / 10000) =
      (31 / 2 + 1 / 20000) * (s * n ^ 2) + n / 2 := by ring
  have e4 : (10 * s * n + s * n / 10000) * n = (10 + 1 / 10000) * (s * n ^ 2) := by ring
  have e5 : (50 * s) * n ^ 2 = 50 * (s * n ^ 2) := by ring
  linarith

lemma cross2_arith {k n b nbB nbD tg d r m s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100)
    (hn0 : 0 < n) (h1 : k ≤ n / 4 - b + nbB) (h2 : nbB ≤ nbD + r) (h3 : nbD ≤ tg + 20 * s * d)
    (h4 : tg ≤ (1 / 2 + s ^ 2) * d + 20 * s * d) (hdr : r + d = b) (hbm : b + m = n)
    (hm : m ≤ (1 / 2 + s ^ 2 / 100) * n) (hdn : d ≤ n / 2)
    (hr : r ≤ s ^ 2 * n / 100) : k ≤ 21 * s * n := by
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have h5 : s ^ 2 * d ≤ s ^ 2 * (n / 2) := mul_le_mul_of_nonneg_left hdn (by positivity)
  have h6 : s * d ≤ s * (n / 2) := mul_le_mul_of_nonneg_left hdn hs0.le
  have h7 : s ^ 2 * n ≤ s / 100 * n := mul_le_mul_of_nonneg_right hs2 hn0.le
  nlinarith

lemma fib_arith_3 {x y b n s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100) (hn0 : 0 < n)
    (hx : |x - n / 4| ≤ (12 * s) * n) (hb1 : (1 / 2 - s ^ 2 / 100) * n ≤ b) (hb2 : b ≤ n / 2)
    (h : y + x = b) : |y - n / 4| ≤ (50 * s) * n := by
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have h7 : s ^ 2 * n ≤ s / 100 * n := mul_le_mul_of_nonneg_right hs2 hn0.le
  rw [abs_le] at hx ⊢
  obtain ⟨hx1, hx2⟩ := hx
  have e1 : (1 / 2 - s ^ 2 / 100) * n = n / 2 - s ^ 2 * n / 100 := by ring
  have e2 : 12 * s * n = 12 * (s * n) := by ring
  have e3 : 50 * s * n = 50 * (s * n) := by ring
  have e4 : s / 100 * n = (s * n) / 100 := by ring
  constructor <;> linarith

lemma fib_arith_N {x m n e₁ s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100) (hn0 : 0 < n)
    (hm1 : n / 2 ≤ m) (hm2 : m ≤ (1 / 2 + s ^ 2 / 100) * n) (he1 : e₁ ≤ s ^ 2 * n / 500)
    (hx1 : m / 2 - e₁ ≤ x) (hx2 : x ≤ m / 2 + e₁) : |x - n / 4| ≤ (50 * s) * n := by
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have h7 : s ^ 2 * n ≤ s / 100 * n := mul_le_mul_of_nonneg_right hs2 hn0.le
  rw [abs_le]; constructor <;> nlinarith

lemma fib_arith_B {x d b n s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100) (hn0 : 0 < n)
    (hdb : d ≤ b) (hb1 : (1 / 2 - s ^ 2 / 100) * n - s ^ 2 * n / 100 ≤ d)
    (hb2 : b ≤ n / 2)
    (hx1 : (1 / 2 - s ^ 2 - 20 * s) * d ≤ x) (hx2 : x ≤ (1 / 2 + s ^ 2 + 20 * s) * d) :
    |x - n / 4| ≤ (12 * s) * n := by
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have h7 : s ^ 2 * n ≤ s / 100 * n := mul_le_mul_of_nonneg_right hs2 hn0.le
  have h5 : s ^ 2 * d ≤ s ^ 2 * (n / 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h6 : s * d ≤ s * (n / 2) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
  rw [abs_le]; constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- **Final gluing.** -/
theorem final_glue (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (N N₁ D B₁ E₁ E₂ : Finset V)
    (b₁ b₂ : Bool) {s e₁ : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100)
    (hsn : 2 ≤ s * Fintype.card V)
    (hN₁ : N₁ ⊆ N) (hD : D ⊆ univ \ N) (hB₁ : B₁ ⊆ D)
    (hm1 : (Fintype.card V : ℝ) / 2 ≤ N.card)
    (hm2 : (N.card : ℝ) ≤ (1 / 2 + s ^ 2 / 100) * Fintype.card V)
    (he1 : 0 ≤ e₁) (he1' : e₁ ≤ s ^ 2 * Fintype.card V / 500)
    (hE₁ : (E₁.card : ℝ) ≤ e₁)
    (hdev₁ : ∀ x ∈ N, x ∉ E₁ → ((symmDiff (nbIn G N x) (tgt N N₁ b₁ x)).card : ℝ) ≤ e₁)
    (hN₁c : (N₁.card : ℝ) ≤ N.card / 2 + e₁) (hN₂c : ((N \ N₁).card : ℝ) ≤ N.card / 2 + e₁)
    (hr : (((univ \ N) \ D).card : ℝ) ≤ s ^ 2 * Fintype.card V / 100)
    (hE₂ : (E₂.card : ℝ) ≤ 20 * s * D.card)
    (hdev₂ : ∀ x ∈ D, x ∉ E₂ →
      ((symmDiff (nbIn G D x) (tgt D B₁ b₂ x)).card : ℝ) ≤ 20 * s * D.card)
    (hB₁c : (B₁.card : ℝ) ≤ (1 / 2 + s ^ 2) * D.card + 20 * s * D.card)
    (hB₂c : ((D \ B₁).card : ℝ) ≤ (1 / 2 + s ^ 2) * D.card + 20 * s * D.card) :
    IsCloseToExtremal (6 * (50 * s)) G := by
  have hn0 : (0 : ℝ) < Fintype.card V := by nlinarith
  have hDN : Disjoint D N := by
    rw [disjoint_left]; intro x hx hxN; exact (mem_sdiff.mp (hD hx)).2 hxN
  have hbm : ((univ \ N).card : ℝ) + N.card = Fintype.card V := by
    have := card_sdiff_of_subset' (subset_univ N)
    rw [card_univ] at this; exact_mod_cast this
  have hdr : (((univ \ N) \ D).card : ℝ) + D.card = (univ \ N).card := by
    exact_mod_cast card_sdiff_of_subset' hD
  have hN12 : (N₁.card : ℝ) + (N \ N₁).card = N.card := by
    have := card_sdiff_of_subset' hN₁
    exact_mod_cast (by omega : N₁.card + (N \ N₁).card = N.card)
  have hB12 : (B₁.card : ℝ) + (D \ B₁).card = D.card := by
    have := card_sdiff_of_subset' hB₁
    exact_mod_cast (by omega : B₁.card + (D \ B₁).card = D.card)
  have hd0 : (0 : ℝ) ≤ D.card := by positivity
  have hr0 : (0 : ℝ) ≤ (((univ \ N) \ D).card : ℝ) := by positivity
  have hdn : (D.card : ℝ) ≤ Fintype.card V / 2 := by linarith
  -- cross bounds
  have hcr₁ : ∀ x ∈ N, x ∉ E₁ →
      (((univ \ N) \ univ.filter (G.Adj x)).card : ℝ) ≤ 21 * s * Fintype.card V := by
    intro x hxN hxE
    have h1 := cross_bound G hδ (univ \ N) x
    rw [Finset.sdiff_sdiff_eq_self (subset_univ N)] at h1
    have h2 := card_nbIn_le_tgt G N N₁ b₁ x (hdev₁ x hxN hxE)
    have h3 := card_tgt_le N N₁ b₁ x hN₁c hN₂c
    have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
    have : s ^ 2 * Fintype.card V ≤ s / 100 * Fintype.card V :=
      mul_le_mul_of_nonneg_right hs2 hn0.le
    linarith
  have hcr₂ : ∀ x ∈ D, x ∉ E₂ →
      ((N \ univ.filter (G.Adj x)).card : ℝ) ≤ 21 * s * Fintype.card V := by
    intro x hxD hxE
    have h1 := cross_bound G hδ N x
    have h2 := card_nbIn_le_tgt G D B₁ b₂ x (hdev₂ x hxD hxE)
    have h3 := card_tgt_le D B₁ b₂ x hB₁c hB₂c
    have h4 : ((nbIn G (univ \ N) x).card : ℝ) ≤ (nbIn G D x).card +
        (((univ \ N) \ D).card : ℝ) := by
      have hsub : nbIn G (univ \ N) x ⊆ nbIn G D x ∪ ((univ \ N) \ D) := by
        intro y hy
        rw [mem_nbIn] at hy
        by_cases hyD : y ∈ D
        · exact mem_union_left _ ((mem_nbIn G).mpr ⟨hyD, hy.2⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨hy.1, hyD⟩)
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    exact cross2_arith hs0 hs hn0 h1 h4 h2 h3 hdr hbm hm2 hdn hr
  -- the cost
  have hcost := glue_cost G N N₁ D B₁ E₁ E₂ b₁ b₂ hDN he1 (by positivity) (by positivity)
    hdev₁ hdev₂ hcr₁ hcr₂
  have hcost' := cost_arith hs0 hs hsn (by linarith) he1 he1' hE₁ hd0 hdn hr0 hr
    hE₂ hcost
  -- the classes
  have hB₁N : Disjoint B₁ N := disjoint_left.mpr fun x hx hxN =>
    (mem_sdiff.mp (hD (hB₁ hx))).2 hxN
  obtain ⟨f0, f1, f2, f3⟩ := fib_glueMap N N₁ B₁ hN₁ hB₁N
  have hB3 : (((univ \ N) \ B₁).card : ℝ) + B₁.card = (univ \ N).card := by
    exact_mod_cast card_sdiff_of_subset' (hB₁.trans hD)
  have hfib : ∀ i, |(fib (glueMap N N₁ B₁) i : ℝ) - Fintype.card V / 4| ≤
      (50 * s) * Fintype.card V := by
    have hb2 : ((univ \ N).card : ℝ) ≤ Fintype.card V / 2 := by linarith
    have hb1 : (1 / 2 - s ^ 2 / 100) * Fintype.card V ≤ ((univ \ N).card : ℝ) := by
      have : (1 / 2 - s ^ 2 / 100) * (Fintype.card V : ℝ) =
          Fintype.card V - (1 / 2 + s ^ 2 / 100) * Fintype.card V := by ring
      linarith
    have hdl : (1 / 2 - s ^ 2 / 100) * Fintype.card V - s ^ 2 * Fintype.card V / 100 ≤
        (D.card : ℝ) := by linarith
    have hx1 : (1 / 2 - s ^ 2 - 20 * s) * (D.card : ℝ) ≤ B₁.card := by
      have : (1 / 2 - s ^ 2 - 20 * s) * (D.card : ℝ) =
          D.card - ((1 / 2 + s ^ 2) * D.card + 20 * s * D.card) := by ring
      linarith
    have hx2 : (B₁.card : ℝ) ≤ (1 / 2 + s ^ 2 + 20 * s) * (D.card : ℝ) := by
      have : (1 / 2 + s ^ 2 + 20 * s) * (D.card : ℝ) =
          (1 / 2 + s ^ 2) * D.card + 20 * s * D.card := by ring
      linarith
    have hB := fib_arith_B hs0 hs hn0 (by linarith) hdl hb2 hx1 hx2
    intro i
    fin_cases i
    · show |(fib (glueMap N N₁ B₁) 0 : ℝ) - _| ≤ _
      rw [f0]; exact fib_arith_N hs0 hs hn0 hm1 hm2 he1' (by linarith) hN₁c
    · show |(fib (glueMap N N₁ B₁) 1 : ℝ) - _| ≤ _
      rw [f1]; exact fib_arith_N hs0 hs hn0 hm1 hm2 he1' (by linarith) hN₂c
    · show |(fib (glueMap N N₁ B₁) 2 : ℝ) - _| ≤ _
      rw [f2]
      exact hB.trans (mul_le_mul_of_nonneg_right (by linarith) hn0.le)
    · show |(fib (glueMap N N₁ B₁) 3 : ℝ) - _| ≤ _
      rw [f3]
      exact fib_arith_3 (x := (B₁.card : ℝ)) (y := (((univ \ N) \ B₁).card : ℝ))
        (b := ((univ \ N).card : ℝ)) (n := (Fintype.card V : ℝ)) hs0 hs hn0 hB hb1 hb2 hB3
  exact isCloseToExtremal_of_glue G N N₁ B₁ b₁ b₂ hcost' hfib (by nlinarith)

end NashWilliams18
