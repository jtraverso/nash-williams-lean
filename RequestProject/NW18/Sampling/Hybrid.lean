/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.Counts

@[expose] public section

/-!
# The hybrid argument for max-cut sampling (deterministic part)

For a sequence `y : Fin m → α` of vertices of a graph `H` (the "sample"), the doubled cut value
of a labelling `a : Fin m → Bool` is `cutQ H y a = #{(i, j) : H.Adj (y i) (y j), a i ≠ a j}`.

We show (`hybrid`), following Goldreich–Goldwasser–Ron, that every labelling is almost beaten
by a labelling of the form `i ↦ X (y i)`, where `X : α → Bool` is a *rule* determined by a
bounded amount of data: a partition `blk : α → Fin ℓ` of the vertices into blocks, and for each
block `t` anchor positions with Boolean labels.  The rule puts a vertex `w` of block `b` on the
side `true` iff it has at most as many neighbours among the `true`-labelled anchors of block `b`
as among the `false`-labelled ones (greedy local improvement with estimated degrees).
-/

namespace NashWilliams18.Sampling

open Finset Pseudorandom

variable {α : Type*} (H : SimpleGraph α) [DecidableRel H.Adj]

/-- Doubled cut value of the labelling `a` of the sample `y`. -/
def cutQ {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) : ℝ :=
  ∑ i, ∑ j, if H.Adj (y i) (y j) ∧ a i ≠ a j then 1 else 0

/-- Number of sample positions with label `c` adjacent to `y i`. -/
def nbrD {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool) : ℝ :=
  ∑ j, if H.Adj (y i) (y j) ∧ a j = c then 1 else 0

/-- The greedy rule with anchor vertices `z` and anchor labels `lam`. -/
def greedy {t : ℕ} (z : Fin t → α) (lam : Fin t → Bool) (w : α) : Bool :=
  decide ((univ.filter fun r => lam r = true ∧ H.Adj w (z r)).card ≤
    (univ.filter fun r => lam r = false ∧ H.Adj w (z r)).card)

/-- The block rule: block `b` uses anchors `z b` with labels `lam b`. -/
def ruleZ {ℓ t : ℕ} (blk : α → Fin ℓ) (z : Fin ℓ → Fin t → α) (lam : Fin ℓ → Fin t → Bool)
    (w : α) : Bool :=
  greedy H (z (blk w)) (lam (blk w)) w

variable {H}

lemma nbrD_nonneg {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool) :
    0 ≤ nbrD H y a i c :=
  sum_nonneg fun j _ => by split_ifs <;> norm_num

lemma nbrD_le {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool) :
    nbrD H y a i c ≤ m := by
  calc nbrD H y a i c ≤ ∑ _j : Fin m, (1 : ℝ) :=
        sum_le_sum fun j _ => by split_ifs <;> norm_num
    _ = m := by simp

/-- The loss of position `i` when its label becomes `b`: how much worse than the best side. -/
def lossAt {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (b : Bool) : ℝ :=
  max (nbrD H y a i true) (nbrD H y a i false) - nbrD H y a i (!b)

lemma lossAt_le {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (b : Bool) :
    lossAt (H := H) y a i b ≤ m := by
  unfold lossAt
  have h1 := nbrD_le (H := H) y a i true
  have h2 := nbrD_le (H := H) y a i false
  have h3 := nbrD_nonneg (H := H) y a i (!b)
  have : max (nbrD H y a i true) (nbrD H y a i false) ≤ m := max_le h1 h2
  linarith

/-- Change of the pair `(i, j)` (with `i ∈ M`, `j ∉ M`) when the labels on `M` change. -/
def pairChange {m : ℕ} (y : Fin m → α) (a a' : Fin m → Bool) (M : Finset (Fin m))
    (i j : Fin m) : ℝ :=
  if i ∈ M ∧ j ∉ M then
    ((if H.Adj (y i) (y j) ∧ a' i ≠ a j then 1 else 0) -
      (if H.Adj (y i) (y j) ∧ a i ≠ a j then 1 else 0))
  else 0

/-- **Switching the labels of a set `M` of positions.** -/
lemma cutQ_switch {m : ℕ} (y : Fin m → α) (a a' : Fin m → Bool) (M : Finset (Fin m))
    (hM : ∀ i, i ∉ M → a' i = a i) :
    cutQ H y a - 2 * ∑ i ∈ M, lossAt (H := H) y a i (a' i) - 3 * (M.card : ℝ) ^ 2 ≤
      cutQ H y a' := by
  classical
  set g := pairChange (H := H) y a a' M with hg
  have hpair : ∀ i j,
      (if H.Adj (y i) (y j) ∧ a i ≠ a j then (1 : ℝ) else 0) + g i j + g j i -
        (if i ∈ M ∧ j ∈ M then 1 else 0) ≤
      (if H.Adj (y i) (y j) ∧ a' i ≠ a' j then 1 else 0) := by
    intro i j
    by_cases hi : i ∈ M <;> by_cases hj : j ∈ M
    · simp only [hg, pairChange, hi, hj, not_true_eq_false, and_false, if_false, and_self, if_true]
      split_ifs <;> norm_num
    · simp only [hg, pairChange, hi, hj, not_false_eq_true, and_self, if_true, not_true_eq_false,
        and_false, if_false, add_zero, sub_zero, hM j hj]
      split_ifs <;> norm_num
    · have hji : H.Adj (y j) (y i) ↔ H.Adj (y i) (y j) := H.adj_comm _ _
      simp only [hg, pairChange, hi, hj, not_false_eq_true, and_self, if_true, not_true_eq_false,
        if_false, add_zero, sub_zero, false_and, hM i hi, hji, ne_comm (a := a i)]
      split_ifs <;> norm_num
    · simp only [hg, pairChange, hi, hj, false_and, if_false, add_zero, sub_zero, hM i hi, hM j hj,
        and_self]
      exact le_rfl
  have hsum : cutQ H y a + 2 * ∑ i, ∑ j, g i j - (M.card : ℝ) ^ 2 ≤ cutQ H y a' := by
    have h := sum_le_sum fun i (_ : i ∈ univ) => sum_le_sum fun j (_ : j ∈ univ) => hpair i j
    simp only [sum_sub_distrib, sum_add_distrib] at h
    have hswap : ∑ i, ∑ j, g j i = ∑ i, ∑ j, g i j := sum_comm
    have hMM : ∑ i : Fin m, ∑ j : Fin m, (if i ∈ M ∧ j ∈ M then (1 : ℝ) else 0) =
        (M.card : ℝ) ^ 2 := by
      simp_rw [ite_and]
      simp [sum_ite_mem, sq]
    rw [hswap, hMM] at h
    unfold cutQ
    linarith
  -- bound each row of `g`
  have hrow : ∀ i ∈ M, -(lossAt (H := H) y a i (a' i)) - M.card ≤ ∑ j, g i j := by
    intro i hi
    have e : ∑ j, g i j = ∑ j, ((if j ∉ M ∧ H.Adj (y i) (y j) ∧ a' i ≠ a j then (1 : ℝ) else 0) -
        (if j ∉ M ∧ H.Adj (y i) (y j) ∧ a i ≠ a j then 1 else 0)) := by
      refine sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ M
      · simp only [hg, pairChange, hj, not_true_eq_false, and_false, false_and, if_false,
          sub_self]
      · simp only [hg, pairChange, hi, hj, not_false_eq_true, and_self, if_true, true_and]
    rw [e, sum_sub_distrib]
    have h1 : nbrD H y a i (!a' i) - M.card ≤
        ∑ j, (if j ∉ M ∧ H.Adj (y i) (y j) ∧ a' i ≠ a j then (1 : ℝ) else 0) := by
      have hM' : (M.card : ℝ) = ∑ j, (if j ∈ M then (1 : ℝ) else 0) := by simp
      rw [hM', nbrD, ← sum_sub_distrib]
      refine sum_le_sum fun j _ => ?_
      have : (a j = !a' i) ↔ (a' i ≠ a j) := by
        cases a j <;> cases a' i <;> simp
      by_cases hj : j ∈ M <;> by_cases hA : H.Adj (y i) (y j) <;> by_cases hb : a' i ≠ a j <;>
        simp only [hj, hA, hb, this, if_true, if_false, and_false, true_and, false_and,
          not_true_eq_false, not_false_eq_true] <;> (try split_ifs) <;> norm_num
    have h2 : ∑ j, (if j ∉ M ∧ H.Adj (y i) (y j) ∧ a i ≠ a j then (1 : ℝ) else 0) ≤
        max (nbrD H y a i true) (nbrD H y a i false) := by
      refine le_trans ?_ (show nbrD H y a i (!a i) ≤ _ by
        cases a i
        · exact le_max_left _ _
        · exact le_max_right _ _)
      refine sum_le_sum fun j _ => ?_
      have : (a j = !a i) ↔ (a i ≠ a j) := by
        cases a j <;> cases a i <;> simp
      by_cases hj : j ∈ M <;> by_cases hA : H.Adj (y i) (y j) <;> by_cases hb : a i ≠ a j <;>
        simp only [hj, hA, hb, this, if_false, and_false, true_and, false_and,
          not_true_eq_false, not_false_eq_true] <;> (try split_ifs) <;> norm_num
    unfold lossAt
    linarith
  have hrows : -(∑ i ∈ M, lossAt (H := H) y a i (a' i)) - (M.card : ℝ) ^ 2 ≤
      ∑ i, ∑ j, g i j := by
    have e : ∑ i, ∑ j, g i j = ∑ i ∈ M, ∑ j, g i j := by
      rw [← sum_subset (subset_univ M)]
      intro i _ hi
      exact sum_eq_zero fun j _ => by simp only [hg, pairChange, hi, false_and, if_false]
    rw [e]
    calc -(∑ i ∈ M, lossAt (H := H) y a i (a' i)) - (M.card : ℝ) ^ 2
        = ∑ i ∈ M, (-(lossAt (H := H) y a i (a' i)) - M.card) := by
          rw [sum_sub_distrib, sum_neg_distrib, sum_const, nsmul_eq_mul, sq]
      _ ≤ _ := sum_le_sum hrow
  linarith

/-! ### Estimating degrees from anchors -/

/-- Number of anchors with label `c` adjacent to `y i` (anchors at positions `s`). -/
def estC {m t : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool)
    (s : Fin t → Fin m) : ℝ :=
  ((univ.filter fun r => H.Adj (y i) (y (s r)) ∧ a (s r) = c).card : ℝ)

lemma greedy_eq {m t : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (s : Fin t → Fin m) :
    greedy H (fun r => y (s r)) (fun r => a (s r)) (y i) =
      decide (estC (H := H) y a i true s ≤ estC (H := H) y a i false s) := by
  unfold greedy estC
  have e1 : (univ.filter fun r => a (s r) = true ∧ H.Adj (y i) (y (s r))) =
      univ.filter fun r => H.Adj (y i) (y (s r)) ∧ a (s r) = true := by
    ext r; simp [and_comm]
  have e2 : (univ.filter fun r => a (s r) = false ∧ H.Adj (y i) (y (s r))) =
      univ.filter fun r => H.Adj (y i) (y (s r)) ∧ a (s r) = false := by
    ext r; simp [and_comm]
  rw [e1, e2]
  simp only [Nat.cast_le]

/-- With accurate estimates, the greedy choice loses at most `2 θ m`. -/
lemma lossAt_greedy_le {m t : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m)
    (s : Fin t → Fin m) {θ : ℝ} (ht : 0 < t)
    (hT : |(m / t : ℝ) * estC (H := H) y a i true s - nbrD H y a i true| ≤ θ * m)
    (hF : |(m / t : ℝ) * estC (H := H) y a i false s - nbrD H y a i false| ≤ θ * m) :
    lossAt (H := H) y a i (greedy H (fun r => y (s r)) (fun r => a (s r)) (y i)) ≤
      2 * θ * m := by
  rw [greedy_eq]
  have hmt : (0 : ℝ) ≤ m / t := by positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_le] at hT hF
  unfold lossAt
  by_cases h : estC (H := H) y a i true s ≤ estC (H := H) y a i false s
  · simp only [h, decide_true, Bool.not_true]
    have := mul_le_mul_of_nonneg_left h hmt
    have : max (nbrD H y a i true) (nbrD H y a i false) ≤ nbrD H y a i false + 2 * θ * m :=
      max_le (by linarith) (by nlinarith)
    linarith
  · simp only [h, decide_false, Bool.not_false]
    push_neg at h
    have := mul_le_mul_of_nonneg_left h.le hmt
    have : max (nbrD H y a i true) (nbrD H y a i false) ≤ nbrD H y a i true + 2 * θ * m :=
      max_le (by nlinarith) (by linarith)
    linarith

/-- Failure probability of the anchor estimates for one position. -/
noncomputable def pbad (θ : ℝ) (t : ℕ) : ℝ :=
  4 * Real.exp (-((θ * t) ^ 2 / (2 * (t + θ * t))))

lemma pbad_nonneg (θ : ℝ) (t : ℕ) : 0 ≤ pbad θ t := by unfold pbad; positivity

/-- The anchor estimates for position `i` are accurate. -/
def AnchorGood {m t : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (θ : ℝ)
    (s : Fin t → Fin m) : Prop :=
  ∀ c, |(m / t : ℝ) * estC (H := H) y a i c s - nbrD H y a i c| ≤ θ * m

noncomputable instance {m t : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (θ : ℝ) (s : Fin t → Fin m) :
    Decidable (AnchorGood (H := H) y a i θ s) := by
  unfold AnchorGood; infer_instance

/-- Indicator of "position `j` has label `c` and is adjacent to `y i`". -/
def anchorPhi {m : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool) (j : Fin m) : ℝ :=
  if H.Adj (y i) (y j) ∧ a j = c then 1 else 0

lemma estC_eq_sum {m t : ℕ} (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool)
    (s : Fin t → Fin m) :
    estC (H := H) y a i c s = ∑ r, (fun (_ : Fin t) j => anchorPhi (H := H) y a i c j) r (s r) := by
  simp [estC, anchorPhi, Finset.sum_boole]

lemma pE_estC {m t : ℕ} [NeZero m] (y : Fin m → α) (a : Fin m → Bool) (i : Fin m) (c : Bool) :
    pE (unif (Fin t) (Fin m))
        (fun s => ∑ r, (fun (_ : Fin t) j => anchorPhi (H := H) y a i c j) r (s r)) =
      t * nbrD H y a i c / m := by
  rw [pE_sum_coord (α := Fin m) (fun (_ : Fin t) j => anchorPhi (H := H) y a i c j)]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nbrD, anchorPhi]
  ring

lemma abs_scale_aux {m t E D θ : ℝ} (hm : 0 < m) (ht : 0 < t)
    (hs : θ * m < |(m / t) * E - D|) : θ * t < |E - t * D / m| := by
  have e : (m / t) * E - D = (m / t) * (E - t * D / m) := by field_simp
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < m / t)] at hs
  by_contra hcon
  push_neg at hcon
  have h1 := mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ m / t)
  have h2 : m / t * (θ * t) = θ * m := by field_simp
  linarith

/-- For uniformly random anchors, the estimates for position `i` fail with probability at most
`pbad θ t`. -/
lemma pProb_not_anchorGood {m t : ℕ} [NeZero m] (y : Fin m → α) (a : Fin m → Bool) (i : Fin m)
    {θ : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    pProb (unif (Fin t) (Fin m)) (fun s => ¬ AnchorGood (H := H) y a i θ s) ≤ pbad θ t := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hθt : 0 < θ * t := by positivity
  have hc : ∀ _r : Fin t, (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 := fun _ => ⟨zero_le_one, le_rfl⟩
  have hexp : ∀ c,
      pProb (unif (Fin t) (Fin m)) (fun s =>
        θ * m < |(m / t : ℝ) * estC (H := H) y a i c s - nbrD H y a i c|) ≤
      2 * Real.exp (-((θ * t) ^ 2 / (2 * (t + θ * t)))) := by
    intro c
    have hgap : CoordGap (fun s : Fin t → Fin m =>
        ∑ r, (fun (_ : Fin t) j => anchorPhi (H := H) y a i c j) r (s r)) (fun _ => 1) :=
      coordGap_sum _ _ fun r j j' => by
        simp only [anchorPhi]; split_ifs <;> norm_num
    have hu := upper_tail unif_isPMF _ _ 1 one_pos hc hgap (θ * t) hθt
    have hl := lower_tail unif_isPMF _ _ 1 one_pos hc hgap (θ * t) hθt
    simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      one_mul] at hu hl
    rw [pE_estC] at hu hl
    refine le_trans (pProb_mono unif_isPMF fun s hs => ?_) ((pProb_or_le unif_isPMF _ _).trans
      (by rw [two_mul]; exact add_le_add hu hl))
    have key := abs_scale_aux hm htr hs
    rw [estC_eq_sum] at key
    rcases le_or_gt 0 (∑ r, (fun (_ : Fin t) j => anchorPhi (H := H) y a i c j) r (s r) -
        t * nbrD H y a i c / m) with h0 | h0
    · left; rw [abs_of_nonneg h0] at key; linarith
    · right; rw [abs_of_neg h0] at key; linarith
  have hall := pProb_exists_le (unif_isPMF (ι := Fin t) (α := Fin m)) (univ : Finset Bool)
    (fun c s =>
      θ * m < |(m / t : ℝ) * estC (H := H) y a i c s - nbrD H y a i c|)
  refine le_trans (pProb_mono unif_isPMF fun s hs => ?_) (hall.trans ?_)
  · unfold AnchorGood at hs
    push_neg at hs
    obtain ⟨c, hc⟩ := hs
    exact ⟨c, mem_univ _, hc⟩
  · calc ∑ c ∈ (univ : Finset Bool), pProb (unif (Fin t) (Fin m)) _
        ≤ ∑ _c ∈ (univ : Finset Bool), 2 * Real.exp (-((θ * t) ^ 2 / (2 * (t + θ * t)))) :=
          sum_le_sum fun c _ => hexp c
      _ = pbad θ t := by simp [pbad]; ring

/-- Good anchors exist: at most a `pbad θ t` fraction of the positions of `M` have inaccurate
estimates. -/
lemma exists_good_anchors {m t : ℕ} [NeZero m] (y : Fin m → α) (a : Fin m → Bool)
    (M : Finset (Fin m)) {θ : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∃ s : Fin t → Fin m,
      (((M.filter fun i => ¬ AnchorGood (H := H) y a i θ s).card : ℕ) : ℝ) ≤
        pbad θ t * M.card := by
  obtain ⟨s, hs⟩ := exists_le_pE (unif_isPMF (ι := Fin t) (α := Fin m))
    (fun s => ∑ i ∈ M, if ¬ AnchorGood (H := H) y a i θ s then (1 : ℝ) else 0)
  refine ⟨s, ?_⟩
  have e : (((M.filter fun i => ¬ AnchorGood (H := H) y a i θ s).card : ℕ) : ℝ) =
      ∑ i ∈ M, if ¬ AnchorGood (H := H) y a i θ s then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  rw [e]
  refine hs.trans ?_
  rw [pE_sum]
  calc ∑ i ∈ M, pE (unif (Fin t) (Fin m))
        (fun s => if ¬ AnchorGood (H := H) y a i θ s then (1 : ℝ) else 0)
      ≤ ∑ _i ∈ M, pbad θ t := sum_le_sum fun i _ => by
          exact (pProb_eq_pE _ (fun s => if ¬ AnchorGood (H := H) y a i θ s then (1 : ℝ) else 0)
            (fun s h => if_pos h) (fun s h => if_neg h)).symm.trans_le
            (pProb_not_anchorGood (H := H) y a i hθ ht)
      _ = pbad θ t * M.card := by rw [sum_const, nsmul_eq_mul, mul_comm]

/-- **One hybrid step**: relabel the positions of `M` greedily, using good anchors. -/
lemma hybrid_step {m t : ℕ} [NeZero m] (y : Fin m → α) (a : Fin m → Bool)
    (M : Finset (Fin m)) {θ : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∃ s : Fin t → Fin m,
      cutQ H y a - (4 * θ * m + 2 * m * pbad θ t) * M.card - 3 * (M.card : ℝ) ^ 2 ≤
        cutQ H y (fun i => if i ∈ M then greedy H (fun r => y (s r)) (fun r => a (s r)) (y i)
          else a i) := by
  obtain ⟨s, hs⟩ := exists_good_anchors (H := H) y a M hθ ht
  refine ⟨s, ?_⟩
  set a' : Fin m → Bool := fun i => if i ∈ M then greedy H (fun r => y (s r))
    (fun r => a (s r)) (y i) else a i
  have hsw := cutQ_switch (H := H) y a a' M (fun i hi => by simp [a', hi])
  have hloss : ∑ i ∈ M, lossAt (H := H) y a i (a' i) ≤
      ∑ i ∈ M, (2 * θ * m + m * (if ¬ AnchorGood (H := H) y a i θ s then (1 : ℝ) else 0)) := by
    refine sum_le_sum fun i hi => ?_
    have ha' : a' i = greedy H (fun r => y (s r)) (fun r => a (s r)) (y i) := by simp [a', hi]
    rw [ha']
    by_cases hg : AnchorGood (H := H) y a i θ s
    · simp only [hg, not_true_eq_false, if_false, mul_zero, add_zero]
      exact lossAt_greedy_le (H := H) y a i s ht (hg true) (hg false)
    · simp only [hg, not_false_eq_true, if_true, mul_one]
      have := lossAt_le (H := H) y a i (greedy H (fun r => y (s r)) (fun r => a (s r)) (y i))
      have : 0 ≤ 2 * θ * m := by positivity
      linarith
  have hcnt : ∑ i ∈ M, (if ¬ AnchorGood (H := H) y a i θ s then (1 : ℝ) else 0) =
      (((M.filter fun i => ¬ AnchorGood (H := H) y a i θ s).card : ℕ) : ℝ) := by
    rw [Finset.sum_boole]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, hcnt] at hloss
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have := mul_le_mul_of_nonneg_left hs hm
  nlinarith

/-! ### The full hybrid argument -/

/-- Number of sample positions whose vertex lies in block `b`. -/
def blockCnt {m ℓ : ℕ} (blk : α → Fin ℓ) (y : Fin m → α) (b : Fin ℓ) : ℕ :=
  (univ.filter fun i => blk (y i) = b).card

lemma sum_blockCnt {m ℓ : ℕ} (blk : α → Fin ℓ) (y : Fin m → α) :
    ∑ b, blockCnt blk y b = m := by
  unfold blockCnt
  rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (blk (y i)))]
  simp

/-- **The hybrid argument.**  Every labelling of the sample is beaten, up to an error
`(4 θ + 2 pbad θ t) m² + 3 Σ_b |M_b|²`, by a labelling given by a block rule whose anchors are
sample positions. -/
theorem hybrid {m ℓ t : ℕ} [NeZero m] (blk : α → Fin ℓ) (y : Fin m → α) (a0 : Fin m → Bool)
    {θ : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∃ (s : Fin ℓ → Fin t → Fin m) (lam : Fin ℓ → Fin t → Bool),
      cutQ H y a0 - (4 * θ + 2 * pbad θ t) * (m : ℝ) ^ 2 -
          3 * ∑ b, ((blockCnt blk y b : ℕ) : ℝ) ^ 2 ≤
        cutQ H y (fun i => ruleZ H blk (fun b r => y (s b r)) lam (y i)) := by
  set C : ℝ := 4 * θ * m + 2 * m * pbad θ t
  set lossB : Fin ℓ → ℝ := fun b => C * blockCnt blk y b + 3 * ((blockCnt blk y b : ℕ) : ℝ) ^ 2
  have key : ∀ k, k ≤ ℓ → ∃ (s : Fin ℓ → Fin t → Fin m) (lam : Fin ℓ → Fin t → Bool),
      cutQ H y a0 - ∑ b ∈ univ.filter (fun b : Fin ℓ => b.val < k), lossB b ≤
        cutQ H y (fun i => if (blk (y i)).val < k then
          ruleZ H blk (fun b r => y (s b r)) lam (y i) else a0 i) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ _ => 0, fun _ _ => true, ?_⟩
      simp
    | succ k ih =>
      intro hk
      obtain ⟨s, lam, hsl⟩ := ih (Nat.le_of_succ_le hk)
      set b0 : Fin ℓ := ⟨k, hk⟩
      set a : Fin m → Bool := fun i => if (blk (y i)).val < k then
          ruleZ H blk (fun b r => y (s b r)) lam (y i) else a0 i
      set M : Finset (Fin m) := univ.filter fun i => blk (y i) = b0
      obtain ⟨s0, hs0⟩ := hybrid_step (H := H) y a M hθ ht
      refine ⟨Function.update s b0 s0, Function.update lam b0 (fun r => a (s0 r)), ?_⟩
      have hlab : (fun i => if (blk (y i)).val < k + 1 then
            ruleZ H blk (fun b r => y (Function.update s b0 s0 b r))
              (Function.update lam b0 (fun r => a (s0 r))) (y i) else a0 i) =
          (fun i => if i ∈ M then greedy H (fun r => y (s0 r)) (fun r => a (s0 r)) (y i)
            else a i) := by
        funext i
        by_cases hi : blk (y i) = b0
        · have hiM : i ∈ M := by simp [M, hi]
          have hlt : (blk (y i)).val < k + 1 := by rw [hi]; simp [b0]
          rw [if_pos hlt, if_pos hiM]
          simp only [ruleZ]
          rw [hi, Function.update_self, Function.update_self]
        · have hiM : i ∉ M := by simp [M, hi]
          simp only [hiM, if_false, a]
          have hne : (blk (y i)).val ≠ k := fun h => hi (Fin.ext h)
          by_cases hlt : (blk (y i)).val < k
          · have hlt' : (blk (y i)).val < k + 1 := by omega
            simp only [hlt, hlt', if_true, ruleZ, Function.update_of_ne hi]
          · have hlt' : ¬ (blk (y i)).val < k + 1 := by omega
            simp only [hlt, hlt', if_false]
      rw [hlab]
      have hsplit : ∑ b ∈ univ.filter (fun b : Fin ℓ => b.val < k + 1), lossB b =
          ∑ b ∈ univ.filter (fun b : Fin ℓ => b.val < k), lossB b + lossB b0 := by
        have : univ.filter (fun b : Fin ℓ => b.val < k + 1) =
            insert b0 (univ.filter (fun b : Fin ℓ => b.val < k)) := by
          ext b
          simp only [mem_filter, mem_univ, true_and, mem_insert]
          constructor
          · intro h
            by_cases hb : b.val = k
            · left; exact Fin.ext hb
            · right; omega
          · rintro (h | h)
            · rw [h]; simp [b0]
            · omega
        rw [this, sum_insert (by simp [b0]), add_comm]
      have hMc : M.card = blockCnt blk y b0 := rfl
      rw [hsplit]
      have : lossB b0 = C * M.card + 3 * (M.card : ℝ) ^ 2 := by simp [lossB, hMc]
      rw [this]
      have e : cutQ H y a = cutQ H y (fun i => if (blk (y i)).val < k then
          ruleZ H blk (fun b r => y (s b r)) lam (y i) else a0 i) := rfl
      linarith
  obtain ⟨s, lam, h⟩ := key ℓ le_rfl
  refine ⟨s, lam, ?_⟩
  have hall : univ.filter (fun b : Fin ℓ => b.val < ℓ) = univ := by
    ext b; simp
  have hlab : (fun i => if (blk (y i)).val < ℓ then
      ruleZ H blk (fun b r => y (s b r)) lam (y i) else a0 i) =
      (fun i => ruleZ H blk (fun b r => y (s b r)) lam (y i)) := by
    funext i; simp [(blk (y i)).isLt]
  rw [hall, hlab] at h
  have hsum : ∑ b, lossB b = C * m + 3 * ∑ b, ((blockCnt blk y b : ℕ) : ℝ) ^ 2 := by
    simp only [lossB, sum_add_distrib, ← mul_sum]
    congr 2
    exact_mod_cast sum_blockCnt blk y
  rw [hsum] at h
  have : C * m = (4 * θ + 2 * pbad θ t) * (m : ℝ) ^ 2 := by simp only [C]; ring
  linarith

end NashWilliams18.Sampling
