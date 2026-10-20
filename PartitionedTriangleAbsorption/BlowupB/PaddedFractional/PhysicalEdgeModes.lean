/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompletePhysical

@[expose] public section

/-!
# Physical lifts of the zero-row edge modes

All weights here are functions on actual vertices.  An oriented repeated-class
block is symmetrized in the three possible positions of its singleton class.
-/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer

variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

def classVertices (p : V → Fin t) (i : Fin t) : Finset V := univ.filter (p · = i)

@[simp] theorem mem_classVertices (p : V → Fin t) (i : Fin t) (a : V) :
    a ∈ classVertices p i ↔ p a = i := by simp [classVertices]

def classSize (p : V → Fin t) (i : Fin t) : ℝ := (classVertices p i).card

def ClassRowsZero (p : V → Fin t) (g : V → V → ℝ) : Prop :=
  ∀ a i, ∑ b ∈ classVertices p i, g a b = 0

def pairSymmetrize (f : V → V → V → ℝ) (a b c : V) : ℝ :=
  f a b c + f a c b + f b c a

theorem pairSymmetrize_symmetric (f : V → V → V → ℝ)
    (hf : ∀ a b c, f a b c = f b a c) : TernarySymmetric (pairSymmetrize f) := by
  constructor
  · intro a b c
    simp only [pairSymmetrize]
    rw [hf b a c]
    ring
  · intro a b c
    simp only [pairSymmetrize]
    rw [hf c b a]
    ring

theorem pairSymmetrize_bound (f : V → V → V → ℝ) (M : ℝ)
    (hf : ∀ a b c, |f a b c| ≤ M) (a b c : V) :
    |pairSymmetrize f a b c| ≤ 3 * M := by
  calc
    |pairSymmetrize f a b c| ≤ |f a b c| + |f a c b| + |f b c a| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M + M + M := add_le_add (add_le_add (hf _ _ _) (hf _ _ _)) (hf _ _ _)
    _ = 3 * M := by ring

def aabBase (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ)
    (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = j ∧ a ≠ b then h a b c else 0

def aabLift (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ) :
    V → V → V → ℝ := pairSymmetrize (aabBase p i j h)

theorem aabLift_symmetric (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ)
    (hs : ∀ a b c, h a b c = h b a c) : TernarySymmetric (aabLift p i j h) := by
  apply pairSymmetrize_symmetric
  intro a b c
  unfold aabBase
  rw [hs a b c]
  congr 1
  apply propext
  tauto

theorem aabLift_load (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ) (a b : V) :
    ternaryLoad (aabLift p i j h) a b =
      (if p a = i ∧ p b = i ∧ a ≠ b then ∑ c ∈ classVertices p j, h a b c else 0) +
      (if p a = i ∧ p b = j then
        ∑ c ∈ classVertices p i, if a ≠ c then h a c b else 0 else 0) +
      (if p b = i ∧ p a = j then
        ∑ c ∈ classVertices p i, if b ≠ c then h b c a else 0 else 0) := by
  simp only [ternaryLoad, aabLift, pairSymmetrize, sum_add_distrib]
  congr 2
  · by_cases ha : p a = i <;> by_cases hb : p b = i <;> by_cases hab : a = b <;>
      simp [aabBase, classVertices, ha, hb, hab, sum_filter]
  · by_cases ha : p a = i <;> by_cases hb : p b = j <;>
      simp [aabBase, classVertices, ha, hb, sum_filter]
    apply sum_congr rfl
    intro c hc
    by_cases hi : p c = i <;> by_cases he : a = c <;> simp [hi, he]
  · by_cases ha : p a = j <;> by_cases hb : p b = i <;>
      simp [aabBase, classVertices, ha, hb, sum_filter]
    apply sum_congr rfl
    intro c hc
    by_cases hi : p c = i <;> by_cases he : b = c <;> simp [hi, he]

theorem sum_ne_eq_erase (S : Finset V) (f : V → ℝ) (a : V) :
    (∑ c ∈ S, if a ≠ c then f c else 0) = ∑ c ∈ S.erase a, f c := by
  rw [← sum_filter]
  congr 1
  ext c
  simp [ne_comm, and_comm]

theorem class_repeated_numerator (p : V → Fin t) (i : Fin t) (f : V → ℝ)
    (hf : ∑ c ∈ classVertices p i, f c = 0) (a : V) (ha : p a = i) :
    (∑ c ∈ classVertices p i, if a ≠ c then f a + f c else 0) =
      (classSize p i - 2) * f a := by
  rw [sum_ne_eq_erase]
  have he := sum_erase_add (classVertices p i) (fun c => f a + f c)
    ((mem_classVertices p i a).mpr ha)
  have ht : (∑ c ∈ classVertices p i, (f a + f c)) = classSize p i * f a := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, hf, add_zero]
    rfl
  rw [ht] at he
  linarith

theorem class_erase_sum_zero (p : V → Fin t) (i : Fin t) (f : V → ℝ)
    (hf : ∑ c ∈ classVertices p i, f c = 0) (a : V) (hfa : f a = 0) :
    (∑ c ∈ classVertices p i, if a ≠ c then f c else 0) = 0 := by
  rw [sum_ne_eq_erase, sum_erase _ hfa, hf]

def repeatedPairWeight (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ) :
    V → V → V → ℝ :=
  aabLift p i j (fun a b c => (g a c + g b c) / (classSize p i - 2))

def internalPairWeight (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ) :
    V → V → V → ℝ :=
  aabLift p i j (fun a b _c => g a b / classSize p j)

theorem repeatedPairWeight_symmetric (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ) :
    TernarySymmetric (repeatedPairWeight p i j g) := by
  apply aabLift_symmetric
  intro a b c
  rw [add_comm]

theorem internalPairWeight_symmetric (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (internalPairWeight p i j g) := by
  apply aabLift_symmetric
  intro a b c
  rw [hs a b]

theorem repeatedPairWeight_load (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g)
    (hi : classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (repeatedPairWeight p i j g) a b =
      (if p a = i ∧ p b = j then g a b else 0) +
      (if p b = i ∧ p a = j then g a b else 0) := by
  have hzero (a b : V) :
      (∑ c ∈ classVertices p j, (g a c + g b c) / (classSize p i - 2)) = 0 := by
    rw [← sum_div, sum_add_distrib, hr a j, hr b j, add_zero, zero_div]
  have hcross (a b : V) (ha : p a = i) :
      (∑ c ∈ classVertices p i, if a ≠ c then
        (g a b + g c b) / (classSize p i - 2) else 0) = g a b := by
    have hc : ∑ c ∈ classVertices p i, g c b = 0 := by
      simp_rw [hs _ b]
      exact hr b i
    have he : (∑ c ∈ classVertices p i, if a ≠ c then
        (g a b + g c b) / (classSize p i - 2) else 0) =
        (∑ c ∈ classVertices p i, if a ≠ c then (g a b + g c b) else 0) /
          (classSize p i - 2) := by
      rw [sum_div]
      apply sum_congr rfl
      intro c hc
      by_cases hac : a = c <;> simp [hac]
    rw [he, class_repeated_numerator p i (fun c => g c b) hc a ha]
    exact mul_div_cancel_left₀ _ hi
  rw [repeatedPairWeight, aabLift_load]
  simp only [hzero, ite_self, zero_add]
  congr 1
  · split_ifs with h
    · exact hcross a b h.1
    · rfl
  · split_ifs with h
    · rw [hcross b a h.1, hs b a]
    · rfl

theorem internalPairWeight_load (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ)
    (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hj : classSize p j ≠ 0) (a b : V) :
    ternaryLoad (internalPairWeight p i j g) a b =
      if p a = i ∧ p b = i then g a b else 0 := by
  have ht (a b : V) : (∑ c ∈ classVertices p j, g a b / classSize p j) = g a b := by
    rw [sum_const, nsmul_eq_mul]
    change classSize p j * (g a b / classSize p j) = g a b
    field_simp
  have hc (a : V) :
      (∑ c ∈ classVertices p i, if a ≠ c then g a c / classSize p j else 0) = 0 := by
    have he : (∑ c ∈ classVertices p i, if a ≠ c then g a c / classSize p j else 0) =
        (∑ c ∈ classVertices p i, if a ≠ c then g a c else 0) / classSize p j := by
      rw [sum_div]
      apply sum_congr rfl
      intro c hc
      by_cases hac : a = c <;> simp [hac]
    rw [he, class_erase_sum_zero p i (g a) (hr a i) a (hd a), zero_div]
  rw [internalPairWeight, aabLift_load]
  simp only [ht, hc, ite_self, add_zero]
  by_cases ha : p a = i <;> by_cases hb : p b = i <;> by_cases hab : a = b <;>
    simp [ha, hb, hab, hd]

theorem admissible_swap12 {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {a b c : V} (h : AdmissibleTriple p F a b c) : AdmissibleTriple p F b a c := by
  exact ⟨h.1.symm, h.2.2.1, h.2.1, (link_root_swap F _ _ _).mp h.2.2.2⟩

theorem admissible_swap23 {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {a b c : V} (h : AdmissibleTriple p F a b c) : AdmissibleTriple p F a c b := by
  exact ⟨h.2.1, h.1, h.2.2.1.symm, (link_swap F _ _ _).mp h.2.2.2⟩

theorem pairSymmetrize_supported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (f : V → V → V → ℝ) (hf : TernarySupported p F f) :
    TernarySupported p F (pairSymmetrize f) := by
  intro a b c h
  have h23 : ¬ AdmissibleTriple p F a c b := fun h' => h (admissible_swap23 h')
  have hr : ¬ AdmissibleTriple p F b c a :=
    fun h' => h (admissible_swap12 (admissible_swap23 h'))
  simp only [pairSymmetrize, hf a b c h, hf a c b h23, hf b c a hr, add_zero]

theorem aabLift_supported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (i j : Fin t) (hij : i ≠ j) (hF : Link F i i j) (h : V → V → V → ℝ) :
    TernarySupported p F (aabLift p i j h) := by
  apply pairSymmetrize_supported
  intro a b c hbad
  unfold aabBase
  split_ifs with hc
  · exfalso
    apply hbad
    refine ⟨hc.2.2.2, ?_, ?_, ?_⟩
    · intro he
      apply hij
      calc i = p a := hc.1.symm
           _ = p c := congrArg p he
           _ = j := hc.2.2.1
    · intro he
      apply hij
      calc i = p b := hc.2.1.symm
           _ = p c := congrArg p he
           _ = j := hc.2.2.1
    · simpa only [hc.1, hc.2.1, hc.2.2.1] using hF
  · rfl

theorem aabLift_bound (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hh : ∀ a b c, |h a b c| ≤ M) (a b c : V) :
    |aabLift p i j h a b c| ≤ 3 * M := by
  apply pairSymmetrize_bound
  intro a b c
  unfold aabBase
  split_ifs
  · exact hh a b c
  · simpa only [abs_zero] using hM

theorem repeatedPairWeight_bound (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hg : ∀ a b, |g a b| ≤ ε) (hi : 0 < classSize p i - 2)
    (a b c : V) : |repeatedPairWeight p i j g a b c| ≤ 6 * ε / (classSize p i - 2) := by
  have hM : 0 ≤ 2 * ε / (classSize p i - 2) := div_nonneg (by positivity) hi.le
  have h := aabLift_bound p i j
    (fun a b c => (g a c + g b c) / (classSize p i - 2))
    (2 * ε / (classSize p i - 2)) hM
    (fun a b c => repeated_bound _ _ ε _ (hg a c) (hg b c) hi) a b c
  calc
    _ ≤ 3 * (2 * ε / (classSize p i - 2)) := h
    _ = 6 * ε / (classSize p i - 2) := by ring

theorem internalPairWeight_bound (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hg : ∀ a b, |g a b| ≤ ε) (hj : 0 < classSize p j)
    (a b c : V) : |internalPairWeight p i j g a b c| ≤ 3 * ε / classSize p j := by
  have hM : 0 ≤ ε / classSize p j := div_nonneg hε hj.le
  have h := aabLift_bound p i j (fun a b _c => g a b / classSize p j)
    (ε / classSize p j) hM (fun a b _c => uniform_bound _ ε _ (hg a b) hj) a b c
  calc
    _ ≤ 3 * (ε / classSize p j) := h
    _ = 3 * ε / classSize p j := by ring

def abcBase (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ)
    (a b c : V) : ℝ :=
  if p a = i ∧ p b = j ∧ p c = k then h a b c else 0

def abcLift (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ) :
    V → V → V → ℝ :=
  pairSymmetrize (fun a b c => abcBase p i j k h a b c + abcBase p i j k h b a c)

theorem abcLift_symmetric (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ) :
    TernarySymmetric (abcLift p i j k h) := by
  apply pairSymmetrize_symmetric
  intro a b c
  rw [add_comm]

theorem abcLift_load (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ) (a b : V) :
    ternaryLoad (abcLift p i j k h) a b =
      ((if p a = i ∧ p b = j then ∑ c ∈ classVertices p k, h a b c else 0) +
       (if p b = i ∧ p a = j then ∑ c ∈ classVertices p k, h b a c else 0)) +
      ((if p a = i ∧ p b = k then ∑ c ∈ classVertices p j, h a c b else 0) +
       (if p a = j ∧ p b = k then ∑ c ∈ classVertices p i, h c a b else 0)) +
      ((if p b = i ∧ p a = k then ∑ c ∈ classVertices p j, h b c a else 0) +
       (if p b = j ∧ p a = k then ∑ c ∈ classVertices p i, h c b a else 0)) := by
  have h3 (a b : V) : (∑ c, abcBase p i j k h a b c) =
      if p a = i ∧ p b = j then ∑ c ∈ classVertices p k, h a b c else 0 := by
    by_cases ha : p a = i <;> by_cases hb : p b = j <;>
      simp [abcBase, classVertices, ha, hb, sum_filter]
  have h2 (a b : V) : (∑ c, abcBase p i j k h a c b) =
      if p a = i ∧ p b = k then ∑ c ∈ classVertices p j, h a c b else 0 := by
    by_cases ha : p a = i <;> by_cases hb : p b = k <;>
      simp [abcBase, classVertices, ha, hb, sum_filter]
  have h1 (a b : V) : (∑ c, abcBase p i j k h c a b) =
      if p a = j ∧ p b = k then ∑ c ∈ classVertices p i, h c a b else 0 := by
    by_cases ha : p a = j <;> by_cases hb : p b = k <;>
      simp [abcBase, classVertices, ha, hb, sum_filter]
  simp only [ternaryLoad, abcLift, pairSymmetrize, sum_add_distrib, h1, h2, h3]

def tripartitePairWeight (p : V → Fin t) (i j k : Fin t) (g : V → V → ℝ) :
    V → V → V → ℝ := abcLift p i j k (fun a b _c => g a b / classSize p k)

theorem tripartitePairWeight_load (p : V → Fin t) (i j k : Fin t) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g)
    (hk : classSize p k ≠ 0) (a b : V) :
    ternaryLoad (tripartitePairWeight p i j k g) a b =
      (if p a = i ∧ p b = j then g a b else 0) +
      (if p b = i ∧ p a = j then g a b else 0) := by
  have ht (a b : V) : (∑ c ∈ classVertices p k, g a b / classSize p k) = g a b := by
    rw [sum_const, nsmul_eq_mul]
    change classSize p k * (g a b / classSize p k) = g a b
    field_simp
  have hrow (a : V) (i : Fin t) : (∑ c ∈ classVertices p i, g a c / classSize p k) = 0 := by
    rw [← sum_div, hr, zero_div]
  have hcol (a : V) (i : Fin t) : (∑ c ∈ classVertices p i, g c a / classSize p k) = 0 := by
    simp_rw [hs _ a]
    exact hrow a i
  rw [tripartitePairWeight, abcLift_load]
  simp only [ht, hrow, hcol, hs b a, ite_self, add_zero]

theorem abcLift_supported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (i j k : Fin t) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hF : Link F i j k) (h : V → V → V → ℝ) :
    TernarySupported p F (abcLift p i j k h) := by
  have hbase : TernarySupported p F (abcBase p i j k h) := by
    intro a b c hbad
    unfold abcBase
    split_ifs with hc
    · exfalso
      apply hbad
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro he
        exact hij (hc.1.symm.trans ((congrArg p he).trans hc.2.1))
      · intro he
        exact hik (hc.1.symm.trans ((congrArg p he).trans hc.2.2))
      · intro he
        exact hjk (hc.2.1.symm.trans ((congrArg p he).trans hc.2.2))
      · simpa only [hc.1, hc.2.1, hc.2.2] using hF
    · rfl
  apply pairSymmetrize_supported
  intro a b c hbad
  dsimp only
  rw [hbase a b c hbad, hbase b a c (fun h' => hbad (admissible_swap12 h')), add_zero]

theorem abcLift_bound (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hh : ∀ a b c, |h a b c| ≤ M) (a b c : V) :
    |abcLift p i j k h a b c| ≤ 6 * M := by
  have hbase (a b c : V) : |abcBase p i j k h a b c| ≤ M := by
    unfold abcBase
    split_ifs
    · exact hh a b c
    · simpa only [abs_zero] using hM
  have hb (a b c : V) : |abcBase p i j k h a b c + abcBase p i j k h b a c| ≤ 2 * M := by
    calc
      _ ≤ |abcBase p i j k h a b c| + |abcBase p i j k h b a c| := abs_add_le _ _
      _ ≤ M + M := add_le_add (hbase _ _ _) (hbase _ _ _)
      _ = 2 * M := by ring
  have hbound := pairSymmetrize_bound _ (2 * M) hb a b c
  calc
    _ ≤ 3 * (2 * M) := hbound
    _ = 6 * M := by ring

theorem tripartitePairWeight_bound (p : V → Fin t) (i j k : Fin t) (g : V → V → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hg : ∀ a b, |g a b| ≤ ε) (hk : 0 < classSize p k)
    (a b c : V) : |tripartitePairWeight p i j k g a b c| ≤ 6 * ε / classSize p k := by
  have hM : 0 ≤ ε / classSize p k := div_nonneg hε hk.le
  have h := abcLift_bound p i j k (fun a b _c => g a b / classSize p k)
    (ε / classSize p k) hM (fun a b _c => uniform_bound _ ε _ (hg a b) hk) a b c
  calc
    _ ≤ 6 * (ε / classSize p k) := h
    _ = 6 * ε / classSize p k := by ring

theorem TernarySymmetric.add {w w' : V → V → V → ℝ}
    (h : TernarySymmetric w) (h' : TernarySymmetric w') :
    TernarySymmetric (fun a b c => w a b c + w' a b c) := by
  constructor
  · intro a b c
    dsimp only
    rw [h.1 a b c, h'.1 a b c]
  · intro a b c
    dsimp only
    rw [h.2 a b c, h'.2 a b c]

theorem TernarySupported.add {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {w w' : V → V → V → ℝ} (h : TernarySupported p F w) (h' : TernarySupported p F w') :
    TernarySupported p F (fun a b c => w a b c + w' a b c) := by
  intro a b c hbad
  dsimp only
  rw [h a b c hbad, h' a b c hbad, add_zero]

#print axioms repeatedPairWeight_load
#print axioms internalPairWeight_load
#print axioms tripartitePairWeight_load
#print axioms aabLift_supported
#print axioms abcLift_supported
#print axioms repeatedPairWeight_bound
#print axioms internalPairWeight_bound
#print axioms tripartitePairWeight_bound

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
