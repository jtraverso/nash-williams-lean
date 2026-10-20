/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.Hybrid

@[expose] public section

/-!
# Max-cut of a random sample is not much larger than expected

`maxcut_sample`: for every `η > 0` and all large `m` (and all large `N`), if every labelling
`X : α → Bool` of a graph `H` on `N` vertices has doubled cut value at most `K`, then for a
uniformly random sequence `ω : Fin m → α` of vertices, with probability at least `1 - η` every
labelling of the sample has doubled cut value less than `K m² / N² + η m²`.

This is the direction of the estimability of max-cut (Theorem 11.4 of the paper) used in
Lemma 11.6.  The proof combines the deterministic hybrid argument (`hybrid`) with a union bound,
over the boundedly many block rules, of a bounded-differences inequality.
-/

namespace NashWilliams18.Sampling

open Finset Pseudorandom Filter Topology

/-! ### Asymptotics -/

lemma eventually_pow_mul_exp_le (T : ℕ) {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (2 * (m : ℝ)) ^ T * Real.exp (-(c * m)) ≤ ε := by
  have h1 : Tendsto (fun x : ℝ => x ^ T * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero T
  have h2 : Tendsto (fun m : ℕ => c * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h3 := (h1.comp h2).const_mul ((2 / c) ^ T)
  rw [mul_zero] at h3
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (h3.eventually (eventually_le_nhds hε))
  refine ⟨m₀, fun m hm => ?_⟩
  have := hm₀ m hm
  simp only [Function.comp] at this
  convert this using 1
  rw [← mul_assoc, ← mul_pow]
  congr 2
  field_simp

/-! ### A balanced block partition -/

lemma exists_blk (α : Type*) [Fintype α] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ blk : α → Fin ℓ, ∀ b,
      (((univ.filter fun w => blk w = b).card : ℕ) : ℝ) ≤ Fintype.card α / ℓ + 1 := by
  classical
  set e := Fintype.equivFin α
  refine ⟨fun w => ⟨(e w).val % ℓ, Nat.mod_lt _ hℓ⟩, fun b => ?_⟩
  have hcard : (univ.filter fun w => (⟨(e w).val % ℓ, Nat.mod_lt _ hℓ⟩ : Fin ℓ) = b).card ≤
      Fintype.card α / ℓ + 1 := by
    have := card_le_card_of_injOn (fun w => (e w).val / ℓ)
      (s := univ.filter fun w => (⟨(e w).val % ℓ, Nat.mod_lt _ hℓ⟩ : Fin ℓ) = b) (t := range (Fintype.card α / ℓ + 1)) (fun w _ => by
        simp only [coe_range, Set.mem_Iio]
        have : (e w).val < Fintype.card α := (e w).isLt
        exact Nat.lt_succ_of_le (Nat.div_le_div_right this.le)) (fun w hw w' hw' h => by
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hw hw'
        have hmod : (e w).val % ℓ = (e w').val % ℓ := by
          have := congrArg Fin.val (hw.trans hw'.symm); simpa using this
        have hdiv : (e w).val / ℓ = (e w').val / ℓ := h
        have : (e w).val = (e w').val := by
          rw [← Nat.div_add_mod (e w).val ℓ, ← Nat.div_add_mod (e w').val ℓ, hmod, hdiv]
        exact e.injective (Fin.ext this))
    simpa using this
  calc (((univ.filter fun w => (⟨(e w).val % ℓ, Nat.mod_lt _ hℓ⟩ : Fin ℓ) = b).card : ℕ) : ℝ)
      ≤ ((Fintype.card α / ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Fintype.card α / ℓ + 1 := by
      push_cast
      have := Nat.cast_div_le (α := ℝ) (m := Fintype.card α) (n := ℓ)
      linarith

/-! ### Pair sums -/

/-- A double sum of `[0,1]`-valued functions of pairs of coordinates has bounded differences
`2 m`. -/
lemma coordGap_pairs {α : Type*} {m : ℕ} (G : Fin m → Fin m → α → α → ℝ)
    (hG : ∀ i j a b, 0 ≤ G i j a b ∧ G i j a b ≤ 1) :
    CoordGap (fun ω : Fin m → α => ∑ i, ∑ j, G i j (ω i) (ω j)) (fun _ => 2 * m) := by
  intro k ω a b
  simp only
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hrow : ∀ i, |∑ j, G i j (Function.update ω k a i) (Function.update ω k a j) -
      ∑ j, G i j (Function.update ω k b i) (Function.update ω k b j)| ≤
      (if i = k then (m : ℝ) else 0) + 1 := by
    intro i
    rw [← sum_sub_distrib]
    by_cases hik : i = k
    · rw [if_pos hik]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |G i j (Function.update ω k a i) (Function.update ω k a j) -
            G i j (Function.update ω k b i) (Function.update ω k b j)|
          ≤ ∑ _j : Fin m, (1 : ℝ) := sum_le_sum fun j _ => by
              have h1 := hG i j (Function.update ω k a i) (Function.update ω k a j)
              have h2 := hG i j (Function.update ω k b i) (Function.update ω k b j)
              rw [abs_le]; constructor <;> linarith
        _ ≤ m + 1 := by simp
    · rw [if_neg hik, zero_add]
      rw [sum_eq_single k]
      · have h1 := hG i k (Function.update ω k a i) (Function.update ω k a k)
        have h2 := hG i k (Function.update ω k b i) (Function.update ω k b k)
        rw [abs_le]; constructor <;> linarith
      · intro j _ hjk
        simp [Function.update_of_ne hik, Function.update_of_ne hjk]
      · simp
  calc ∑ i, |∑ j, G i j (Function.update ω k a i) (Function.update ω k a j) -
        ∑ j, G i j (Function.update ω k b i) (Function.update ω k b j)|
      ≤ ∑ i, ((if i = k then (m : ℝ) else 0) + 1) := sum_le_sum fun i _ => hrow i
    _ = 2 * m := by
      rw [sum_add_distrib, sum_ite_eq']; simp; ring

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Expectation of a double sum of functions of pairs of coordinates, bounded termwise. -/
lemma pE_pairs_le {m : ℕ} (G : Fin m → Fin m → α → α → ℝ) (B : ℝ)
    (hdiag : ∀ i a, G i i a a ≤ B)
    (hoff : ∀ i j, i ≠ j → (∑ a, ∑ b, G i j a b) / (Fintype.card α : ℝ) ^ 2 ≤ B) :
    pE (unif (Fin m) α) (fun ω => ∑ i, ∑ j, G i j (ω i) (ω j)) ≤ m ^ 2 * B := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pE_sum]
  have hterm : ∀ i j, pE (unif (Fin m) α) (fun ω => G i j (ω i) (ω j)) ≤ B := by
    intro i j
    by_cases hij : i = j
    · subst hij
      calc pE (unif (Fin m) α) (fun ω => G i i (ω i) (ω i))
          ≤ pE (unif (Fin m) α) (fun _ => B) := pE_mono unif_isPMF fun ω => hdiag i (ω i)
        _ = B := pE_const unif_isPMF B
    · rw [pE_pair unif_isPMF hij]
      refine le_trans (le_of_eq ?_) (hoff i j hij)
      simp only [unif]
      rw [eq_div_iff (by positivity), sum_mul]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun b _ => ?_
      field_simp
  calc ∑ i, pE (unif (Fin m) α) (fun ω => ∑ j, G i j (ω i) (ω j))
      = ∑ i, ∑ j, pE (unif (Fin m) α) (fun ω => G i j (ω i) (ω j)) :=
        sum_congr rfl fun i _ => pE_sum _ _
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, B := sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
    _ = m ^ 2 * B := by simp; ring

/-! ### Second moment of the block counts -/

omit [Fintype α] [Nonempty α] in
lemma sum_blockCnt_sq {m ℓ : ℕ} (blk : α → Fin ℓ) (ω : Fin m → α) :
    ∑ b, ((blockCnt blk ω b : ℕ) : ℝ) ^ 2 =
      ∑ i, ∑ j, if blk (ω i) = blk (ω j) then (1 : ℝ) else 0 := by
  have e : ∀ b, ((blockCnt blk ω b : ℕ) : ℝ) = ∑ i, if blk (ω i) = b then (1 : ℝ) else 0 := by
    intro b; simp [blockCnt, Finset.sum_boole]
  simp_rw [e, sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_eq_single (blk (ω i))]
  · by_cases h : blk (ω i) = blk (ω j)
    · simp [h]
    · simp [h, Ne.symm h]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma pE_sum_blockCnt_sq {m ℓ : ℕ} (hℓ : 0 < ℓ) (blk : α → Fin ℓ)
    (hblk : ∀ b, (((univ.filter fun w => blk w = b).card : ℕ) : ℝ) ≤
      Fintype.card α / ℓ + 1) :
    pE (unif (Fin m) α) (fun ω => ∑ b, ((blockCnt blk ω b : ℕ) : ℝ) ^ 2) ≤
      m + m ^ 2 * (1 / ℓ + 1 / Fintype.card α) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  simp_rw [sum_blockCnt_sq]
  -- the number of pairs in a common block
  have hpairs : (∑ a : α, ∑ b : α, if blk a = blk b then (1 : ℝ) else 0) ≤
      Fintype.card α * (Fintype.card α / ℓ + 1) := by
    calc (∑ a : α, ∑ b : α, if blk a = blk b then (1 : ℝ) else 0)
        = ∑ a : α, (((univ.filter fun w => blk w = blk a).card : ℕ) : ℝ) := by
          refine sum_congr rfl fun a _ => ?_
          rw [Finset.sum_boole]
          congr 2; ext b; simp [eq_comm]
      _ ≤ ∑ _a : α, ((Fintype.card α : ℝ) / ℓ + 1) := sum_le_sum fun a _ => hblk _
      _ = _ := by simp; ring
  -- termwise comparison
  have hle : pE (unif (Fin m) α) (fun ω => ∑ i, ∑ j,
      if blk (ω i) = blk (ω j) then (1 : ℝ) else 0) ≤
      pE (unif (Fin m) α) (fun _ => ∑ i : Fin m, ∑ j : Fin m,
        ((if i = j then (1 : ℝ) else 0) + (1 / ℓ + 1 / Fintype.card α))) := by
    rw [pE_sum, pE_sum]
    refine sum_le_sum fun i _ => ?_
    rw [pE_sum, pE_sum]
    refine sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      refine pE_mono unif_isPMF fun ω => ?_
      simp only [if_true]
      have : (0 : ℝ) ≤ 1 / ℓ + 1 / Fintype.card α := by positivity
      linarith
    · rw [pE_pair unif_isPMF hij (fun a b => if blk a = blk b then (1 : ℝ) else 0)]
      rw [pE_const unif_isPMF]
      simp only [if_neg hij, zero_add, unif]
      calc ∑ a : α, ∑ b : α, 1 / (Fintype.card α : ℝ) * (1 / Fintype.card α) *
            (if blk a = blk b then (1 : ℝ) else 0)
          = (∑ a : α, ∑ b : α, if blk a = blk b then (1 : ℝ) else 0) /
              (Fintype.card α : ℝ) ^ 2 := by
            rw [eq_div_iff (by positivity), sum_mul]
            refine sum_congr rfl fun a _ => ?_
            rw [sum_mul]
            refine sum_congr rfl fun b _ => ?_
            field_simp
        _ ≤ Fintype.card α * (Fintype.card α / ℓ + 1) / (Fintype.card α : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hpairs (by positivity)
        _ = 1 / ℓ + 1 / Fintype.card α := by field_simp
  refine hle.trans (le_of_eq ?_)
  rw [pE_const unif_isPMF]
  simp [sum_add_distrib]
  ring

/-! ### Concentration of the cut value of a fixed block rule -/

variable (H : SimpleGraph α) [DecidableRel H.Adj]

/-- Doubled cut value of the block rule `ruleZ H blk Z lam`, counting only pairs of positions
outside `π`. -/
def Fcut {m ℓ t : ℕ} (blk : α → Fin ℓ) (lam : Fin ℓ → Fin t → Bool) (π : Finset (Fin m))
    (Z : Fin ℓ → Fin t → α) (ω : Fin m → α) : ℝ :=
  ∑ i, ∑ j, if i ∉ π ∧ j ∉ π ∧ H.Adj (ω i) (ω j) ∧
    ruleZ H blk Z lam (ω i) ≠ ruleZ H blk Z lam (ω j) then 1 else 0

variable {H}

lemma pE_Fcut_le {m ℓ t : ℕ} (blk : α → Fin ℓ) (lam : Fin ℓ → Fin t → Bool)
    (π : Finset (Fin m)) (Z : Fin ℓ → Fin t → α) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X : α → Bool, (∑ a, ∑ b, if H.Adj a b ∧ X a ≠ X b then (1 : ℝ) else 0) ≤ K) :
    pE (unif (Fin m) α) (Fcut H blk lam π Z) ≤ m ^ 2 * (K / (Fintype.card α : ℝ) ^ 2) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine pE_pairs_le (fun i j a b => if i ∉ π ∧ j ∉ π ∧ H.Adj a b ∧
    ruleZ H blk Z lam a ≠ ruleZ H blk Z lam b then (1 : ℝ) else 0) _ (fun i a => ?_)
    (fun i j _ => ?_)
  · simp only [SimpleGraph.irrefl, false_and, and_false, if_false]
    positivity
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine le_trans (sum_le_sum fun a _ => sum_le_sum fun b _ => ?_) (hK (ruleZ H blk Z lam))
    by_cases h1 : H.Adj a b ∧ ruleZ H blk Z lam a ≠ ruleZ H blk Z lam b
    · rw [if_pos h1]; split_ifs <;> norm_num
    · rw [if_neg h1, if_neg]
      exact fun h => h1 ⟨h.2.2.1, h.2.2.2⟩

lemma prob_Fcut {m ℓ t : ℕ} (hm : 0 < m) (blk : α → Fin ℓ) (lam : Fin ℓ → Fin t → Bool)
    (π : Finset (Fin m)) (Z : Fin ℓ → Fin t → α) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X : α → Bool, (∑ a, ∑ b, if H.Adj a b ∧ X a ≠ X b then (1 : ℝ) else 0) ≤ K)
    {η : ℝ} (hη : 0 < η) :
    pProb (unif (Fin m) α) (fun ω =>
      m ^ 2 * (K / (Fintype.card α : ℝ) ^ 2) + η * m ^ 2 ≤ Fcut H blk lam π Z ω) ≤
      Real.exp (-((η ^ 2 / (8 + 4 * η)) * m)) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hgap := coordGap_pairs (α := α) (m := m) (fun i j a b => if i ∉ π ∧ j ∉ π ∧ H.Adj a b ∧
    ruleZ H blk Z lam a ≠ ruleZ H blk Z lam b then (1 : ℝ) else 0)
    (fun i j a b => by split_ifs <;> norm_num)
  have h := upper_tail unif_isPMF (Fcut H blk lam π Z) (fun _ => 2 * m) (2 * m) (by positivity)
    (fun _ => ⟨by positivity, le_rfl⟩) hgap (η * m ^ 2) (by positivity)
  have hmean := pE_Fcut_le (H := H) (m := m) blk lam π Z hK0 hK
  refine le_trans (pProb_mono unif_isPMF fun ω hω => ?_) (h.trans (le_of_eq ?_))
  · linarith
  · congr 1
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

omit [Fintype α] [Nonempty α] in
/-- Overwriting the positions in `π` does not change `Fcut`. -/
lemma Fcut_updOn {m ℓ t : ℕ} (blk : α → Fin ℓ) (lam : Fin ℓ → Fin t → Bool)
    (π : Finset (Fin m)) (Z : Fin ℓ → Fin t → α) (z ω : Fin m → α) :
    Fcut H blk lam π Z (updOn π z ω) = Fcut H blk lam π Z ω := by
  unfold Fcut
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hi : i ∈ π
  · simp [hi]
  · by_cases hj : j ∈ π
    · simp [hj]
    · simp [updOn, hi, hj]

/-- The anchors of a rule are sample positions: concentration for the rule read off the
sample. -/
lemma prob_Fcut_anchor {m ℓ t : ℕ} (hm : 0 < m) (blk : α → Fin ℓ)
    (s : Fin ℓ → Fin t → Fin m) (lam : Fin ℓ → Fin t → Bool) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X : α → Bool, (∑ a, ∑ b, if H.Adj a b ∧ X a ≠ X b then (1 : ℝ) else 0) ≤ K)
    {η : ℝ} (hη : 0 < η) :
    pProb (unif (Fin m) α) (fun ω =>
      m ^ 2 * (K / (Fintype.card α : ℝ) ^ 2) + η * m ^ 2 ≤
        Fcut H blk lam (univ.image fun p : Fin ℓ × Fin t => s p.1 p.2)
          (fun b r => ω (s b r)) ω) ≤
      Real.exp (-((η ^ 2 / (8 + 4 * η)) * m)) := by
  set π := univ.image fun p : Fin ℓ × Fin t => s p.1 p.2
  refine pProb_le_of_updOn unif_isPMF π _ _ fun z => ?_
  have hz : ∀ ω, (fun b r => updOn π z ω (s b r)) = fun b r => z (s b r) := by
    intro ω; funext b r
    have : s b r ∈ π := mem_image.mpr ⟨(b, r), mem_univ _, rfl⟩
    simp [updOn, this]
  simp_rw [hz, Fcut_updOn]
  exact prob_Fcut hm blk lam π _ hK0 hK hη

omit [Fintype α] [Nonempty α] in
lemma ite_le_aux (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    (if P then (1 : ℝ) else 0) ≤
      (if ¬ Q ∧ ¬ R ∧ P then 1 else 0) + ((if Q then 1 else 0) + (if R then 1 else 0)) := by
  by_cases hQ : Q <;> by_cases hR : R <;> by_cases hP : P <;> simp [hQ, hR, hP]

omit [Fintype α] [Nonempty α] in
/-- The cut value of a rule read off the sample is at most `Fcut` plus the pairs meeting the
anchor positions. -/
lemma cutQ_rule_le {m ℓ t : ℕ} (blk : α → Fin ℓ) (lam : Fin ℓ → Fin t → Bool)
    (π : Finset (Fin m)) (Z : Fin ℓ → Fin t → α) (ω : Fin m → α) :
    cutQ H ω (fun i => ruleZ H blk Z lam (ω i)) ≤
      Fcut H blk lam π Z ω + 2 * π.card * m := by
  unfold cutQ Fcut
  have hterm : ∀ i j, (if H.Adj (ω i) (ω j) ∧ ruleZ H blk Z lam (ω i) ≠ ruleZ H blk Z lam (ω j)
      then (1 : ℝ) else 0) ≤
      (if i ∉ π ∧ j ∉ π ∧ H.Adj (ω i) (ω j) ∧
        ruleZ H blk Z lam (ω i) ≠ ruleZ H blk Z lam (ω j) then 1 else 0) +
      ((if i ∈ π then 1 else 0) + (if j ∈ π then 1 else 0)) := by
    intro i j
    exact ite_le_aux _ _ _
  refine le_trans (sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j) (le_of_eq ?_)
  simp only [sum_add_distrib]
  congr 1
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_ite_mem, univ_inter,
    mul_one]
  simp [Finset.sum_ite_mem]
  ring

/-! ### The main sampling theorem -/

lemma exists_t_pbad_le {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ t : ℕ, 0 < t ∧ pbad θ t ≤ ε := by
  set c := θ ^ 2 / (2 * (1 + θ))
  have hc : 0 < c := by positivity
  obtain ⟨t₀, ht₀⟩ := eventually_pow_mul_exp_le 0 hc (ε := ε / 4) (by positivity)
  refine ⟨max t₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  have h := ht₀ (max t₀ 1) (le_max_left _ _)
  simp only [pow_zero, one_mul] at h
  have ht : (0 : ℝ) < ((max t₀ 1 : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_pos (le_max_right t₀ 1)
  unfold pbad
  have e : (θ * ((max t₀ 1 : ℕ) : ℝ)) ^ 2 / (2 * (((max t₀ 1 : ℕ) : ℝ) +
      θ * ((max t₀ 1 : ℕ) : ℝ))) = c * ((max t₀ 1 : ℕ) : ℝ) := by
    simp only [c]; field_simp
  rw [e]; linarith

lemma chain_aux {X Y F S A P Q M2 η θ η₁ c : ℝ}
    (hhyb : X - (4 * θ + 2 * P) * M2 - 3 * S ≤ Y) (hrule : Y ≤ F + Q) (hQ : Q ≤ η / 5 * M2)
    (hθm : (4 * θ + 2 * P) * M2 ≤ 2 * η / 5 * M2) (hη₁m : η₁ * M2 = η / 5 * M2)
    (hcm : 3 * (c * M2) = η / 5 * M2) (hn2 : S < c * M2) (ha : A + η * M2 ≤ X)
    (hF : F < A + η₁ * M2) : False := by
  linarith

set_option maxHeartbeats 1000000 in
/-- **Max-cut sampling.**  For every `η > 0` there are `m₀, N₀` such that for `m ≥ m₀` and every
graph `H` on `N ≥ N₀` vertices all of whose labellings have doubled cut value at most `K`, a
uniformly random sequence of `m` vertices has, with probability at least `1 - η`, no labelling
of doubled cut value at least `m² K / N² + η m²`. -/
theorem maxcut_sample {η : ℝ} (hη : 0 < η) :
    ∃ m₀ N₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (β : Type) [Fintype β] [Nonempty β]
      (H : SimpleGraph β) [DecidableRel H.Adj] (K : ℝ), N₀ ≤ Fintype.card β → 0 ≤ K →
      (∀ X : β → Bool, (∑ a, ∑ b, if H.Adj a b ∧ X a ≠ X b then (1 : ℝ) else 0) ≤ K) →
      pProb (unif (Fin m) β) (fun ω => ∃ a : Fin m → Bool,
        m ^ 2 * (K / (Fintype.card β : ℝ) ^ 2) + η * m ^ 2 ≤ cutQ H ω a) ≤ η := by
  set η₁ := η / 5 with hη₁
  set θ := η / 20 with hθ
  set c := η / 15 with hc
  have hη₁p : 0 < η₁ := by positivity
  have hθp : 0 < θ := by positivity
  have hcp : 0 < c := by positivity
  obtain ⟨t, ht, hpbad⟩ := exists_t_pbad_le (θ := θ) (ε := η / 10) hθp (by positivity)
  obtain ⟨ℓ, hℓ, hℓbig⟩ : ∃ ℓ : ℕ, 0 < ℓ ∧ 6 / (c * η) ≤ ℓ :=
    ⟨⌈6 / (c * η)⌉₊ + 1, Nat.succ_pos _, by
      have := Nat.le_ceil (6 / (c * η)); push_cast; linarith⟩
  set T := ℓ * t with hT
  set c' := η₁ ^ 2 / (8 + 4 * η₁) with hc'
  obtain ⟨m₁, hm₁⟩ := eventually_pow_mul_exp_le T (c := c') (by positivity) (ε := η / 2)
    (by positivity)
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℕ, 6 / (c * η) + 10 * T / η + 1 ≤ m₂ :=
    ⟨⌈6 / (c * η) + 10 * T / η + 1⌉₊, Nat.le_ceil _⟩
  refine ⟨max m₁ m₂, ℓ, fun m hm β _ _ H _ K hN hK0 hK => ?_⟩
  have hmm₂ : (m₂ : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ 6 / (c * η) + 10 * T / η := by positivity
    linarith
  have hmpos : 0 < m := by exact_mod_cast (lt_of_lt_of_le one_pos hm1)
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hmpos⟩
  have hmr : (0 : ℝ) < m := by linarith
  have hNr : (ℓ : ℝ) ≤ Fintype.card β := by exact_mod_cast hN
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  obtain ⟨blk, hblk⟩ := exists_blk β ℓ hℓ
  -- the two bad events
  set Bad1 : (Fin m → β) → Prop := fun ω =>
    ∃ p ∈ (univ : Finset ((Fin ℓ → Fin t → Fin m) × (Fin ℓ → Fin t → Bool))),
      m ^ 2 * (K / (Fintype.card β : ℝ) ^ 2) + η₁ * m ^ 2 ≤
        Fcut H blk p.2 (univ.image fun q : Fin ℓ × Fin t => p.1 q.1 q.2)
          (fun b r => ω (p.1 b r)) ω
  set Bad2 : (Fin m → β) → Prop := fun ω =>
    c * m ^ 2 ≤ ∑ b, ((blockCnt blk ω b : ℕ) : ℝ) ^ 2
  have hB1 : pProb (unif (Fin m) β) Bad1 ≤ η / 2 := by
    refine (pProb_exists_le unif_isPMF _ _).trans ?_
    calc ∑ p ∈ (univ : Finset ((Fin ℓ → Fin t → Fin m) × (Fin ℓ → Fin t → Bool))),
          pProb (unif (Fin m) β) (fun ω => m ^ 2 * (K / (Fintype.card β : ℝ) ^ 2) +
            η₁ * m ^ 2 ≤ Fcut H blk p.2 (univ.image fun q : Fin ℓ × Fin t => p.1 q.1 q.2)
              (fun b r => ω (p.1 b r)) ω)
        ≤ ∑ _p ∈ (univ : Finset ((Fin ℓ → Fin t → Fin m) × (Fin ℓ → Fin t → Bool))),
            Real.exp (-(c' * m)) :=
          sum_le_sum fun p _ => prob_Fcut_anchor hmpos blk p.1 p.2 hK0 hK hη₁p
      _ = (2 * (m : ℝ)) ^ T * Real.exp (-(c' * m)) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          congr 1
          simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
          push_cast
          rw [← pow_mul, ← pow_mul, ← mul_pow, hT, mul_comm t ℓ, mul_comm (m : ℝ) 2]
      _ ≤ η / 2 := hm₁ m (le_trans (le_max_left _ _) hm)
  have hB2 : pProb (unif (Fin m) β) Bad2 ≤ η / 2 := by
    refine (pProb_ge_le_markov unif_isPMF (fun ω => sum_nonneg fun b _ => sq_nonneg _)
      (by positivity)).trans ?_
    rw [div_le_iff₀ (by positivity)]
    refine (pE_sum_blockCnt_sq hℓ blk hblk).trans ?_
    have h1 : 1 / (m : ℝ) ≤ c * η / 6 := by
      rw [div_le_iff₀ hmr]
      have : 6 / (c * η) ≤ m := by
        have : (0 : ℝ) ≤ 10 * T / η := by positivity
        linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    have h2 : 1 / (ℓ : ℝ) ≤ c * η / 6 := by
      rw [div_le_iff₀ hℓr]
      rw [div_le_iff₀ (by positivity)] at hℓbig
      nlinarith
    have h3 : 1 / (Fintype.card β : ℝ) ≤ c * η / 6 :=
      le_trans (one_div_le_one_div_of_le hℓr hNr) h2
    have hmm : (m : ℝ) ≤ c * η / 6 * m ^ 2 := by
      have h1' := h1
      rw [div_le_iff₀ hmr] at h1'
      nlinarith
    have hsq : (m : ℝ) ^ 2 * (1 / ℓ + 1 / Fintype.card β) ≤ (m : ℝ) ^ 2 * (c * η / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    nlinarith
  -- the event is contained in `Bad1 ∨ Bad2`
  have hincl : ∀ ω, (∃ a : Fin m → Bool,
      m ^ 2 * (K / (Fintype.card β : ℝ) ^ 2) + η * m ^ 2 ≤ cutQ H ω a) → Bad1 ω ∨ Bad2 ω := by
    rintro ω ⟨a, ha⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    obtain ⟨s, lam, hhyb⟩ := hybrid (H := H) blk ω a hθp ht
    set π := univ.image fun q : Fin ℓ × Fin t => s q.1 q.2
    have hrule := cutQ_rule_le (H := H) blk lam π (fun b r => ω (s b r)) ω
    have hF : Fcut H blk lam π (fun b r => ω (s b r)) ω <
        m ^ 2 * (K / (Fintype.card β : ℝ) ^ 2) + η₁ * m ^ 2 := by
      by_contra h
      push_neg at h
      exact hn1 ⟨(s, lam), mem_univ _, h⟩
    have hπ : (π.card : ℝ) ≤ T := by
      have := card_image_le (s := (univ : Finset (Fin ℓ × Fin t)))
        (f := fun q : Fin ℓ × Fin t => s q.1 q.2)
      have : π.card ≤ ℓ * t := by simpa using this
      exact_mod_cast this
    have hn2' : ∑ b, ((blockCnt blk ω b : ℕ) : ℝ) ^ 2 < c * m ^ 2 := lt_of_not_ge hn2
    have hTm : 2 * (T : ℝ) * m ≤ η / 5 * m ^ 2 := by
      have : 10 * (T : ℝ) / η ≤ m := by
        have : (0 : ℝ) ≤ 6 / (c * η) := by positivity
        linarith
      rw [div_le_iff₀ hη] at this
      nlinarith
    have hpb : 2 * pbad θ t ≤ η / 5 := by linarith only [hpbad]
    have h2πm : 2 * (π.card : ℝ) * m ≤ 2 * T * m := by
      have := mul_le_mul_of_nonneg_right hπ hmr.le
      linarith
    have h4θ : 4 * θ = η / 5 := by rw [hθ]; ring
    have hθm : (4 * θ + 2 * pbad θ t) * (m : ℝ) ^ 2 ≤ (2 * η / 5) * m ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [h4θ, hpb]) (sq_nonneg _)
    have hη₁m : η₁ * (m : ℝ) ^ 2 = η / 5 * m ^ 2 := by rw [hη₁]
    have hcm : 3 * (c * (m : ℝ) ^ 2) = η / 5 * m ^ 2 := by rw [hc]; ring
    exact chain_aux hhyb hrule (h2πm.trans hTm) hθm hη₁m hcm hn2' ha hF
  calc pProb (unif (Fin m) β) (fun ω => ∃ a : Fin m → Bool,
        m ^ 2 * (K / (Fintype.card β : ℝ) ^ 2) + η * m ^ 2 ≤ cutQ H ω a)
      ≤ pProb (unif (Fin m) β) (fun ω => Bad1 ω ∨ Bad2 ω) := pProb_mono unif_isPMF hincl
    _ ≤ pProb (unif (Fin m) β) Bad1 + pProb (unif (Fin m) β) Bad2 := pProb_or_le unif_isPMF _ _
    _ ≤ η := by linarith

end NashWilliams18.Sampling
