/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BernoulliConcentration
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Finite product-measure tools on the Bernoulli cube

All statements are about the accepted product expectation `cubeMean`.

* linearity, union bound, existence of a good outcome;
* integrating out one coordinate (`cubeMean_integrate`);
* the conditional exponential product bound for coins whose weights depend
  only on other coordinates (`cond_mgf_le`): this is the precise form of
  "conditional on the outside coins, the inside coins keep their law";
* conditioning on a specified set of coins being zero (`cubeMean_zeroing`):
  the conditioned expectation is again a product expectation, with those
  probabilities set to zero. No global good event is conditioned on.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {n : ℕ}

/-! ## Linearity and basic facts -/

theorem cubeMean_add (q : Fin n → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => f ω + g ω) = cubeMean q f + cubeMean q g := by
  simp only [cubeMean_eq_sum_prod, mul_add, sum_add_distrib]

theorem cubeMean_sum {ι : Type*} (q : Fin n → ℝ) (s : Finset ι)
    (f : ι → (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, cubeMean q (f k) := by
  simp only [cubeMean_eq_sum_prod, mul_sum]
  exact sum_comm

theorem cubeMean_congr (q : Fin n → ℝ) {f g : (Fin n → Bool) → ℝ} (h : ∀ ω, f ω = g ω) :
    cubeMean q f = cubeMean q g := by
  rw [show f = g from funext h]

theorem cubeProb_def (q : Fin n → ℝ) (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    cubeProb q P = cubeMean q (fun ω => if P ω then 1 else 0) := by
  unfold cubeProb
  congr 1
  funext ω
  congr

theorem cubeProb_nonneg (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (P : (Fin n → Bool) → Prop) : 0 ≤ cubeProb q P := by
  classical
  unfold cubeProb
  have := cubeMean_mono q hq (fun _ => (0 : ℝ)) (fun ω => if P ω then 1 else 0)
    (fun ω => by split_ifs <;> norm_num)
  rwa [cubeMean_const] at this

theorem cubeProb_mono (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    {P Q : (Fin n → Bool) → Prop} (h : ∀ ω, P ω → Q ω) : cubeProb q P ≤ cubeProb q Q := by
  classical
  unfold cubeProb
  apply cubeMean_mono q hq
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, ite_false]; split_ifs <;> norm_num

/-- Union bound. -/
theorem cubeProb_exists_le {ι : Type*} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (s : Finset ι) (P : ι → (Fin n → Bool) → Prop) :
    cubeProb q (fun ω => ∃ k ∈ s, P k ω) ≤ ∑ k ∈ s, cubeProb q (P k) := by
  classical
  unfold cubeProb
  rw [← cubeMean_sum]
  apply cubeMean_mono q hq
  intro ω
  split_ifs with h
  · obtain ⟨k, hk, hP⟩ := h
    calc (1 : ℝ) = (fun k => if P k ω then (1 : ℝ) else 0) k := by simp [hP]
      _ ≤ ∑ k ∈ s, (if P k ω then (1 : ℝ) else 0) :=
          single_le_sum (f := fun k => if P k ω then (1 : ℝ) else 0)
            (fun k _ => by split_ifs <;> norm_num) hk
  · exact sum_nonneg fun k _ => by split_ifs <;> norm_num

theorem cubeProb_or_le (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (P Q : (Fin n → Bool) → Prop) :
    cubeProb q (fun ω => P ω ∨ Q ω) ≤ cubeProb q P + cubeProb q Q := by
  classical
  unfold cubeProb
  rw [← cubeMean_add]
  apply cubeMean_mono q hq
  intro ω
  by_cases hp : P ω <;> by_cases hq' : Q ω <;> simp [hp, hq']

/-- A good outcome exists when the failure probability is below one. -/
theorem exists_not_of_cubeProb_lt_one (q : Fin n → ℝ) (P : (Fin n → Bool) → Prop)
    (h : cubeProb q P < 1) : ∃ ω, ¬ P ω := by
  classical
  by_contra hne
  push Not at hne
  unfold cubeProb at h
  rw [cubeMean_congr q (g := fun _ => (1 : ℝ)) (fun ω => by simp [hne ω]),
    cubeMean_const] at h
  exact lt_irrefl _ h

/-! ## Integrating out one coordinate -/

theorem coinMean_const (q a : ℝ) : coinMean q (fun _ => a) = a := by
  unfold coinMean; ring

theorem cubeMean_coinMean (q : Fin n → ℝ) (p : ℝ) (g : Bool → (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => coinMean p (fun b => g b ω)) =
      coinMean p (fun b => cubeMean q (g b)) := by
  unfold coinMean
  rw [cubeMean_add, cubeMean_const_mul, cubeMean_const_mul]

/-- Integrating out coordinate `j`. -/
theorem cubeMean_integrate (q : Fin n → ℝ) (j : Fin n) (f : (Fin n → Bool) → ℝ) :
    cubeMean q f = cubeMean q (fun ω => coinMean (q j) (fun b => f (Function.update ω j b))) := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero =>
      simp only [cubeMean]
      simp only [Fin.update_cons_zero]
      rw [cubeMean_coinMean, coinMean_const]
    | succ j =>
      simp only [cubeMean]
      congr 1
      funext b
      simp only [← Fin.cons_update]
      exact ih (fun i => q i.succ) j (fun ω => f (Fin.cons b ω))

/-- `φ` does not depend on the coordinates in `J`. -/
def IndepOf (J : Finset (Fin n)) (φ : (Fin n → Bool) → ℝ) : Prop :=
  ∀ ω j b, j ∈ J → φ (Function.update ω j b) = φ ω

theorem IndepOf.mono {J J' : Finset (Fin n)} {φ : (Fin n → Bool) → ℝ} (h : IndepOf J φ)
    (hJ : J' ⊆ J) : IndepOf J' φ := fun ω j b hj => h ω j b (hJ hj)

/-- The mean of one coin. -/
theorem cubeMean_coord (q : Fin n → ℝ) (i : Fin n) :
    cubeMean q (fun ω => if ω i then (1 : ℝ) else 0) = q i := by
  rw [cubeMean_integrate q i]
  simp only [Function.update_self]
  rw [cubeMean_congr q (g := fun _ => q i) (fun ω => by simp [coinMean]), cubeMean_const]

/-- A coin times a function not depending on it. -/
theorem cubeMean_coord_mul (q : Fin n → ℝ) (i : Fin n) (g : (Fin n → Bool) → ℝ)
    (hg : IndepOf {i} g) :
    cubeMean q (fun ω => (if ω i then (1 : ℝ) else 0) * g ω) = q i * cubeMean q g := by
  rw [cubeMean_integrate q i, ← cubeMean_const_mul]
  apply cubeMean_congr
  intro ω
  simp only [Function.update_self, hg _ i _ (mem_singleton_self i), coinMean]
  simp

/-! ## Conditional exponential product bound -/

theorem exp_mul_le_convex (lam a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (lam * a) ≤ 1 + a * (Real.exp lam - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ lam) (Set.mem_univ 0) ha0 (by linarith : 0 ≤ 1 - a)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero] at h
  rw [mul_comm]
  linarith

/-- Inside coins `J`, whose weights `a i ∈ [0,1]` and prefactor `φ ≥ 0` do not depend on
the inside coins: the exponential moment is bounded by the product law. -/
theorem cond_mgf_le (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (lam : ℝ)
    (J : Finset (Fin n)) (a : Fin n → (Fin n → Bool) → ℝ)
    (ha : ∀ i ∈ J, IndepOf J (a i)) (ha01 : ∀ i ∈ J, ∀ ω, 0 ≤ a i ω ∧ a i ω ≤ 1) :
    ∀ φ : (Fin n → Bool) → ℝ, (∀ ω, 0 ≤ φ ω) → IndepOf J φ →
      cubeMean q (fun ω => φ ω * Real.exp (lam * ∑ i ∈ J, (if ω i then a i ω else 0))) ≤
        cubeMean q (fun ω => φ ω * Real.exp ((Real.exp lam - 1) * ∑ i ∈ J, q i * a i ω)) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro φ _ _
    simp
  | insert j J hj ih =>
    intro φ hφ0 hφ
    have haJ : ∀ i ∈ J, IndepOf J (a i) := fun i hi =>
      (ha i (mem_insert_of_mem hi)).mono (subset_insert _ _)
    have ha01J : ∀ i ∈ J, ∀ ω, 0 ≤ a i ω ∧ a i ω ≤ 1 := fun i hi => ha01 i (mem_insert_of_mem hi)
    set φ' : (Fin n → Bool) → ℝ :=
      fun ω => φ ω * Real.exp ((Real.exp lam - 1) * (q j * a j ω)) with hφ'
    have hφ'0 : ∀ ω, 0 ≤ φ' ω := fun ω => mul_nonneg (hφ0 ω) (Real.exp_pos _).le
    have hφ'J : IndepOf J φ' := by
      intro ω k b hk
      simp only [hφ', hφ ω k b (mem_insert_of_mem hk),
        ha j (mem_insert_self _ _) ω k b (mem_insert_of_mem hk)]
    have hstep : ∀ ω, coinMean (q j) (fun b =>
        φ (Function.update ω j b) * Real.exp (lam * ∑ i ∈ insert j J,
          (if Function.update ω j b i then a i (Function.update ω j b) else 0))) ≤
        φ' ω * Real.exp (lam * ∑ i ∈ J, (if ω i then a i ω else 0)) := by
      intro ω
      have hsum : ∀ b, ∑ i ∈ insert j J,
          (if Function.update ω j b i then a i (Function.update ω j b) else 0) =
          (if b then a j ω else 0) + ∑ i ∈ J, (if ω i then a i ω else 0) := by
        intro b
        rw [sum_insert hj, Function.update_self,
          ha j (mem_insert_self _ _) ω j b (mem_insert_self _ _)]
        congr 1
        apply sum_congr rfl
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij, ha i (mem_insert_of_mem hi) ω j b (mem_insert_self _ _)]
      simp only [hsum, hφ ω j _ (mem_insert_self _ _), coinMean, hφ']
      obtain ⟨h0, h1⟩ := ha01 j (mem_insert_self _ _) ω
      have hconv := exp_mul_le_convex lam (a j ω) h0 h1
      have hexp := Real.add_one_le_exp ((Real.exp lam - 1) * (q j * a j ω))
      have e0 : (if false = true then a j ω else 0) = 0 := by simp
      have e1 : (if True then a j ω else 0) = a j ω := by simp
      rw [e0, e1, zero_add, mul_add lam (a j ω), Real.exp_add]
      generalize hEdef : Real.exp (lam * ∑ i ∈ J, (if ω i then a i ω else 0)) = E
      have hE : 0 ≤ E := by rw [← hEdef]; positivity
      have hqc := mul_le_mul_of_nonneg_left hconv (hq j).1
      have hmain : (1 - q j) + q j * Real.exp (lam * a j ω) ≤
          Real.exp ((Real.exp lam - 1) * (q j * a j ω)) := by nlinarith
      have hφE : 0 ≤ φ ω * E := mul_nonneg (hφ0 ω) hE
      calc _ = φ ω * E * ((1 - q j) + q j * Real.exp (lam * a j ω)) := by ring
        _ ≤ φ ω * E * Real.exp ((Real.exp lam - 1) * (q j * a j ω)) :=
            mul_le_mul_of_nonneg_left hmain hφE
        _ = _ := by ring
    calc _ = cubeMean q (fun ω => coinMean (q j) (fun b =>
          φ (Function.update ω j b) * Real.exp (lam * ∑ i ∈ insert j J,
            (if Function.update ω j b i then a i (Function.update ω j b) else 0)))) :=
          cubeMean_integrate q j _
      _ ≤ cubeMean q (fun ω => φ' ω * Real.exp (lam * ∑ i ∈ J, (if ω i then a i ω else 0))) :=
          cubeMean_mono q hq _ _ hstep
      _ ≤ cubeMean q (fun ω => φ' ω * Real.exp ((Real.exp lam - 1) * ∑ i ∈ J, q i * a i ω)) :=
          ih haJ ha01J φ' hφ'0 hφ'J
      _ = _ := by
          apply cubeMean_congr
          intro ω
          simp only [hφ', sum_insert hj, mul_add, Real.exp_add]
          ring

/-! ## Conditioning on a specified set of coins being zero -/

/-- Probabilities with the coins of `I` forced to zero. -/
def zeroOn (q : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ I then 0 else q i

theorem zeroOn_prob (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (I : Finset (Fin n)) :
    ∀ i, 0 ≤ zeroOn q I i ∧ zeroOn q I i ≤ 1 := by
  intro i
  unfold zeroOn
  split_ifs
  · norm_num
  · exact hq i

theorem prod_ite_split (I : Finset (Fin n)) (A B : Fin n → ℝ) :
    ∏ i, (if i ∈ I then A i else B i) = (∏ i ∈ I, A i) * ∏ i ∈ Iᶜ, B i := by
  rw [← prod_mul_prod_compl I]
  congr 1 <;> apply prod_congr rfl <;> intro i hi <;> simp_all [mem_compl]

/-- The event "all coins of `I` are zero" times `f`: its expectation is the
product of the zero probabilities times the product expectation with those coins
forced to zero. -/
theorem cubeMean_zeroing (q : Fin n → ℝ) (I : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => (if ∀ i ∈ I, ω i = false then (1 : ℝ) else 0) * f ω) =
      (∏ i ∈ I, (1 - q i)) * cubeMean (zeroOn q I) f := by
  classical
  rw [cubeMean_eq_sum_prod, cubeMean_eq_sum_prod, mul_sum]
  apply sum_congr rfl
  intro ω _
  by_cases hω : ∀ i ∈ I, ω i = false
  · simp only [cubeWeight]
    have h1 : ∏ i, (if ω i = true then q i else 1 - q i) =
        ∏ i, (if i ∈ I then (1 - q i) else (if ω i = true then q i else 1 - q i)) := by
      apply prod_congr rfl
      intro i _
      split_ifs with h2 h3 <;> simp_all
    have h2 : ∏ i, (if ω i = true then zeroOn q I i else 1 - zeroOn q I i) =
        ∏ i, (if i ∈ I then 1 else (if ω i = true then q i else 1 - q i)) := by
      apply prod_congr rfl
      intro i _
      unfold zeroOn
      split_ifs with h2 h3 <;> simp_all
    rw [h1, h2, prod_ite_split, prod_ite_split, prod_const_one, one_mul, ite_eq_left hω]
    ring
  · simp only [hω, ite_false, zero_mul]
    push Not at hω
    obtain ⟨i, hi, hωi⟩ := hω
    have : cubeWeight (zeroOn q I) ω = 0 := by
      unfold cubeWeight
      apply prod_eq_zero (mem_univ i)
      simp [zeroOn, hi, hωi]
    rw [this]; ring

/-- Probability that all coins of `I` are zero. -/
theorem cubeProb_allZero (q : Fin n → ℝ) (I : Finset (Fin n)) :
    cubeProb q (fun ω => ∀ i ∈ I, ω i = false) = ∏ i ∈ I, (1 - q i) := by
  classical
  unfold cubeProb
  have := cubeMean_zeroing q I (fun _ => 1)
  simp only [mul_one, cubeMean_const] at this
  convert this

/-- Conditioning on the coins of `I` being zero, as a bound on a joint probability. -/
theorem cubeProb_allZero_and_le (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (I : Finset (Fin n)) (P : (Fin n → Bool) → Prop) :
    cubeProb q (fun ω => (∀ i ∈ I, ω i = false) ∧ P ω) ≤ cubeProb (zeroOn q I) P := by
  classical
  have h := cubeMean_zeroing q I (fun ω => if P ω then 1 else 0)
  have hpt : ∀ ω, (if (∀ i ∈ I, ω i = false) ∧ P ω then (1 : ℝ) else 0) =
      (if ∀ i ∈ I, ω i = false then (1 : ℝ) else 0) * (if P ω then 1 else 0) := by
    intro ω
    by_cases h1 : ∀ i ∈ I, ω i = false <;> by_cases h2 : P ω <;> simp [h1, h2]
  rw [cubeProb_def, cubeProb_def, cubeMean_congr q hpt, h]
  have hp0 : 0 ≤ ∏ i ∈ I, (1 - q i) := prod_nonneg fun i _ => by linarith [(hq i).2]
  have hp1 : ∏ i ∈ I, (1 - q i) ≤ 1 :=
    prod_le_one₀ (fun i _ => by linarith [(hq i).2]) (fun i _ => by linarith [(hq i).1])
  have hm := cubeProb_nonneg _ (zeroOn_prob q hq I) P
  rw [cubeProb_def] at hm
  nlinarith

end PartitionedTriangleAbsorption.Nibble
