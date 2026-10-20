/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Global

@[expose] public section

/-! # The vertex-profile stage and the zero-profile edge stage

* `vertex_stage`: vertex functions `φ τ` with zero sum on every class give a
  bounded symmetric supported ternary weight whose local profiles are
  `∑ τ ∈ F, φ τ u * vertexFactor τ (p u) l`.
* `edge_stage`: a symmetric, diagonal-zero, allowed-pair-supported edge function
  with zero rows into every class is exactly the load of a symmetric supported
  ternary weight bounded by `6 B / m`. Each allowed pair of classes is spread
  evenly over all permitted types containing it. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem classRow_sum {ι : Type*} (s : Finset ι) (p : V → Fin 4) (g : ι → V → V → ℝ)
    (u : V) (l : Fin 4) :
    classRow p (fun a b => ∑ k ∈ s, g k a b) u l = ∑ k ∈ s, classRow p (g k) u l := by
  unfold classRow
  exact sum_comm

theorem vertex_stage (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (φ : Multiset (Fin 4) → V → ℝ) (hφ : ∀ τ l, ∑ c ∈ classVertices p l, φ τ c = 0)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ τ v, |φ τ v| ≤ B) :
    TernarySymmetric (typedWeight p F (fun τ a b c => φ τ a + φ τ b + φ τ c)) ∧
    TernarySupported p F (typedWeight p F (fun τ a b c => φ τ a + φ τ b + φ τ c)) ∧
    (∀ a b c, |typedWeight p F (fun τ a b c => φ τ a + φ τ b + φ τ c) a b c| ≤ 3 * B) ∧
    ∀ u l, classRow p (fun a b =>
        ternaryLoad (typedWeight p F (fun τ a b c => φ τ a + φ τ b + φ τ c)) a b) u l =
      ∑ τ ∈ F, φ τ u * vertexFactor (classSize p) τ (p u) l := by
  refine ⟨typedWeight_symmetric p F _ (fun τ => ⟨fun a b c => by ring, fun a b c => by ring⟩),
    typedWeight_supported p F _, ?_, ?_⟩
  · intro a b c
    apply typedWeight_bound p F _ (3 * B) (by linarith)
    intro a b c _ _ _ _
    calc
      _ ≤ |φ {p a, p b, p c} a| + |φ {p a, p b, p c} b| + |φ {p a, p b, p c} c| :=
        abs_add_three _ _ _
      _ ≤ B + B + B := add_le_add_three (hB _ _) (hB _ _) (hB _ _)
      _ = 3 * B := by ring
  · intro u l
    have hload : (fun a b => ternaryLoad
        (typedWeight p F (fun τ a b c => φ τ a + φ τ b + φ τ c)) a b) =
        fun a b => ∑ τ ∈ F,
          ternaryLoad (fun a b c => chi p τ a b c * (φ τ a + φ τ b + φ τ c)) a b := by
      funext a b
      exact load_typedWeight p F _ a b
    rw [hload, classRow_sum]
    exact sum_congr rfl fun τ _ => classRow_vertexMode p τ (φ τ) (hφ τ) u l

/-- Number of permitted types containing the label pair `(i, j)`. -/
def pairMult (F : Finset (Multiset (Fin 4))) (i j : Fin 4) : ℝ := by
  classical
  exact ((F.filter fun τ => ∃ z, ({i, j, z} : Multiset (Fin 4)) = τ).card : ℝ)

/-- The edge-mode normalisation of type `τ` for the label pair `(i, j)`. -/
def edgeScale (n : Fin 4 → ℝ) (F : Finset (Multiset (Fin 4))) (τ : Multiset (Fin 4))
    (i j : Fin 4) : ℝ := by
  classical
  exact if ∃ z, ({i, j, z} : Multiset (Fin 4)) = τ then
    1 / (pairMult F i j * edgeFactor n τ i j) else 0

theorem pair_cond_comm (τ : Multiset (Fin 4)) (i j : Fin 4) :
    (∃ z, ({i, j, z} : Multiset (Fin 4)) = τ) ↔ ∃ z, ({j, i, z} : Multiset (Fin 4)) = τ := by
  constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨z, by rw [← hz]; exact Multiset.cons_swap _ _ _⟩

theorem pairMult_comm (F : Finset (Multiset (Fin 4))) (i j : Fin 4) :
    pairMult F i j = pairMult F j i := by
  unfold pairMult
  congr 2
  exact filter_congr fun τ _ => pair_cond_comm τ i j

theorem edgeFactor_comm (n : Fin 4 → ℝ) (τ : Multiset (Fin 4)) (i j : Fin 4) :
    edgeFactor n τ i j = edgeFactor n τ j i := by
  unfold edgeFactor
  apply sum_congr rfl
  intro z _
  have h : ({i, j, z} : Multiset (Fin 4)) = {j, i, z} := Multiset.cons_swap _ _ _
  rw [h]
  split_ifs <;> ring

theorem edgeScale_comm (n : Fin 4 → ℝ) (F : Finset (Multiset (Fin 4)))
    (τ : Multiset (Fin 4)) (i j : Fin 4) :
    edgeScale n F τ i j = edgeScale n F τ j i := by
  unfold edgeScale
  simp only [pair_cond_comm τ i j, pairMult_comm F i j, edgeFactor_comm n τ i j]

theorem edgeScale_bound {n : Fin 4 → ℝ} {m : ℝ} (hm : 8 ≤ m) (hn : ∀ k, m ≤ n k)
    (F : Finset (Multiset (Fin 4))) (τ : Multiset (Fin 4)) (hτ : τ ∈ F) (i j : Fin 4) :
    |edgeScale n F τ i j| ≤ 2 / m := by
  unfold edgeScale
  split_ifs with h
  · obtain ⟨z, hz⟩ := h
    have hE := edgeFactor_lower hn hz
    have hK : 1 ≤ pairMult F i j := by
      unfold pairMult
      have : 0 < (F.filter fun τ => ∃ z, ({i, j, z} : Multiset (Fin 4)) = τ).card :=
        card_pos.mpr ⟨τ, mem_filter.mpr ⟨hτ, z, hz⟩⟩
      exact_mod_cast this
    have hE0 : 0 < edgeFactor n τ i j := by linarith
    have hprod : m / 2 ≤ pairMult F i j * edgeFactor n τ i j := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
    nlinarith
  · simp only [abs_zero]
    positivity

theorem sum_edgeScale_mul_edgeFactor (n : Fin 4 → ℝ) {m : ℝ} (hm : 8 ≤ m)
    (hn : ∀ k, m ≤ n k) (F : Finset (Multiset (Fin 4))) (i j : Fin 4)
    (hij : ∃ k, Link F i j k) :
    ∑ τ ∈ F, edgeScale n F τ i j * edgeFactor n τ i j = 1 := by
  classical
  obtain ⟨k, hk⟩ := hij
  have hK0 : (F.filter fun τ => ∃ z, ({i, j, z} : Multiset (Fin 4)) = τ).card ≠ 0 :=
    (card_pos.mpr ⟨_, mem_filter.mpr ⟨hk, k, rfl⟩⟩).ne'
  have hK : pairMult F i j ≠ 0 := by
    unfold pairMult
    exact_mod_cast hK0
  have hterm : ∀ τ ∈ F, edgeScale n F τ i j * edgeFactor n τ i j =
      if ∃ z, ({i, j, z} : Multiset (Fin 4)) = τ then 1 / pairMult F i j else 0 := by
    intro τ _
    unfold edgeScale
    split_ifs with h
    · obtain ⟨z, hz⟩ := h
      have hE : edgeFactor n τ i j ≠ 0 := by
        have := edgeFactor_lower hn hz
        intro h0
        linarith
      field_simp
    · simp
  rw [sum_congr rfl hterm, ← sum_filter, sum_const, nsmul_eq_mul]
  unfold pairMult at hK ⊢
  field_simp

theorem edge_stage (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hr : ∀ a l, ∑ c ∈ classVertices p l, g a c = 0)
    (hact : ∀ x y, x ≠ y → (¬ ∃ k, Link F (p x) (p y) k) → g x y = 0)
    {m B : ℝ} (hm : 8 ≤ m) (hmin : ∀ k, m ≤ classSize p k) (hB0 : 0 ≤ B)
    (hB : ∀ a b, |g a b| ≤ B) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
      (∀ a b c, |w a b c| ≤ 6 * B / m) ∧ ∀ x y, ternaryLoad w x y = g x y := by
  classical
  set h : Multiset (Fin 4) → V → V → ℝ :=
    fun τ x y => g x y * edgeScale (classSize p) F τ (p x) (p y) with hh
  have hhs : ∀ τ a b, h τ a b = h τ b a := by
    intro τ a b
    simp only [hh, hs a b, edgeScale_comm (classSize p) F τ (p a) (p b)]
  have hhd : ∀ τ a, h τ a a = 0 := by intro τ a; simp [hh, hd a]
  have hhr : ∀ τ a l, ∑ c ∈ classVertices p l, h τ a c = 0 := by
    intro τ a l
    have : ∀ c ∈ classVertices p l,
        h τ a c = edgeScale (classSize p) F τ (p a) l * g a c := by
      intro c hc
      show g a c * edgeScale (classSize p) F τ (p a) (p c) = _
      rw [(mem_classVertices p l c).mp hc]
      ring
    rw [sum_congr rfl this, ← mul_sum, hr a l, mul_zero]
  set X : Multiset (Fin 4) → V → V → V → ℝ :=
    fun τ a b c => h τ a b + h τ a c + h τ b c with hX
  have hXs : ∀ τ, TernarySymmetric (X τ) := by
    intro τ
    constructor
    · intro a b c; simp only [hX, hhs τ a b]; ring
    · intro a b c; simp only [hX, hhs τ b c]; ring
  have hm0 : 0 < m := by linarith
  refine ⟨typedWeight p F X, typedWeight_symmetric p F X hXs, typedWeight_supported p F X,
    ?_, ?_⟩
  · intro a b c
    apply typedWeight_bound p F X _ (by positivity)
    intro a b c _ _ _ hτ
    have hb : ∀ x y, |h {p a, p b, p c} x y| ≤ B * (2 / m) := by
      intro x y
      rw [hh, abs_mul]
      exact mul_le_mul (hB x y) (edgeScale_bound hm hmin F _ hτ _ _) (abs_nonneg _) hB0
    calc
      _ ≤ |h {p a, p b, p c} a b| + |h {p a, p b, p c} a c| + |h {p a, p b, p c} b c| :=
        abs_add_three _ _ _
      _ ≤ B * (2 / m) + B * (2 / m) + B * (2 / m) :=
        add_le_add_three (hb _ _) (hb _ _) (hb _ _)
      _ = 6 * B / m := by ring
  · intro x y
    by_cases hxy : x = y
    · subst y
      rw [(typedWeight_supported p F X).load_diag, hd]
    · rw [load_typedWeight]
      have hmode : ∀ τ ∈ F,
          ternaryLoad (fun a b c => chi p τ a b c * X τ a b c) x y =
            g x y * (edgeScale (classSize p) F τ (p x) (p y) *
              edgeFactor (classSize p) τ (p x) (p y)) := by
        intro τ _
        have := load_edgeMode p τ (h τ) (hhs τ) (hhd τ) (hhr τ) hxy
        rw [hh] at this
        simp only [hX]
        rw [this]
        ring
      rw [sum_congr rfl hmode, ← mul_sum]
      by_cases hij : ∃ k, Link F (p x) (p y) k
      · rw [sum_edgeScale_mul_edgeFactor (classSize p) hm hmin F _ _ hij, mul_one]
      · rw [hact x y hxy hij, zero_mul]

end PaddedGeneral.RealInverse
