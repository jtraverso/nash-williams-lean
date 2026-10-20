/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Factors

@[expose] public section

/-! # Global type columns

`typeCount p F τ` is the number of actual permitted copies of type `τ`. It is at
least `m³ / 64` when every class has at least `m ≥ 8` vertices. The uniform
chain `c τ / typeCount τ` on the copies of type `τ` has class totals exactly
`c τ • typeEdgeVec τ` (ordered convention: for `τ = iii` the diagonal total is
`6 c τ`), for every type simultaneously. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of actual permitted copies of type `τ`. -/
def typeCount (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (τ : Multiset (Fin 4)) : ℕ :=
  ((copies p F (activeCompleteGraph p F)).filter (fun T => triType p T = τ)).card

theorem sum_classVertices_avoid_two_ge (p : V → Fin 4) (z : Fin 4) {a b : V} (hab : a ≠ b) :
    classSize p z - 2 ≤
      ∑ c ∈ classVertices p z, (if a ≠ c ∧ b ≠ c then (1 : ℝ) else 0) := by
  rw [sum_avoid_two _ hab, sum_classVertices_one]
  have h1 : (if a ∈ classVertices p z then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h2 : (if b ∈ classVertices p z then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  linarith

theorem typeCount_lower (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    {τ : Multiset (Fin 4)} (hτF : τ ∈ F) (hτ : Multiset.card τ = 3)
    {m : ℝ} (hm : 8 ≤ m) (hmin : ∀ k, m ≤ classSize p k) :
    m ^ 3 / 64 ≤ (typeCount p F τ : ℝ) := by
  obtain ⟨x, y, u, rfl⟩ := Multiset.card_eq_three.mp hτ
  let P : Finset (V × V × V) :=
    classVertices p x ×ˢ (classVertices p y ×ˢ classVertices p u)
  let S : Finset (V × V × V) :=
    P.filter (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
  -- lower bound for the ordered triples
  have hS : classSize p x * (classSize p y - 1) * (classSize p u - 2) ≤ (S.card : ℝ) := by
    have hcard : (S.card : ℝ) = ∑ a ∈ classVertices p x, ∑ b ∈ classVertices p y,
        ∑ c ∈ classVertices p u,
          (if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℝ) else 0) := by
      rw [show (S.card : ℝ) = ∑ t ∈ S, (1 : ℝ) by simp, sum_filter, sum_product]
      apply sum_congr rfl
      intro a _
      rw [sum_product]
    rw [hcard]
    have hinner : ∀ a ∈ classVertices p x,
        (classSize p y - 1) * (classSize p u - 2) ≤ ∑ b ∈ classVertices p y,
          ∑ c ∈ classVertices p u, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℝ) else 0) := by
      intro a _
      have hb : ∀ b ∈ classVertices p y,
          (if b ≠ a then classSize p u - 2 else 0) ≤
            ∑ c ∈ classVertices p u, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℝ) else 0) := by
        intro b _
        by_cases hba : b ≠ a
        · rw [if_pos hba]
          have := sum_classVertices_avoid_two_ge p u (Ne.symm hba)
          refine this.trans (le_of_eq (sum_congr rfl fun c _ => ?_))
          by_cases hc : a ≠ c ∧ b ≠ c
          · rw [if_pos hc, if_pos ⟨Ne.symm hba, hc.1, hc.2⟩]
          · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.1, h.2.2⟩)]
        · rw [if_neg hba]
          exact sum_nonneg fun c _ => by split_ifs <;> norm_num
      refine le_trans ?_ (sum_le_sum hb)
      rw [sum_avoid_one, sum_const]
      simp only [nsmul_eq_mul]
      rw [show ((classVertices p y).card : ℝ) = classSize p y from rfl]
      have hu2 : 0 ≤ classSize p u - 2 := by linarith [hmin u]
      split_ifs
      · nlinarith
      · nlinarith
    calc
      classSize p x * (classSize p y - 1) * (classSize p u - 2) =
          ∑ _a ∈ classVertices p x, (classSize p y - 1) * (classSize p u - 2) := by
        rw [sum_const, nsmul_eq_mul]
        rw [show ((classVertices p x).card : ℝ) = classSize p x from rfl]
        ring
      _ ≤ _ := sum_le_sum hinner
  -- the image of ordered triples lies among the copies of type τ
  let f : V × V × V → Finset V := fun t => {t.1, t.2.1, t.2.2}
  have himg : S.image f ⊆
      (copies p F (activeCompleteGraph p F)).filter (fun T => triType p T = {x, y, u}) := by
    intro T hT
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
    obtain ⟨htP, h12, h13, h23⟩ := mem_filter.mp ht
    obtain ⟨hx, hy, hu⟩ : t.1 ∈ classVertices p x ∧ t.2.1 ∈ classVertices p y ∧
        t.2.2 ∈ classVertices p u := by
      simpa [P, mem_product] using htP
    have hpx := (mem_classVertices p x _).mp hx
    have hpy := (mem_classVertices p y _).mp hy
    have hpu := (mem_classVertices p u _).mp hu
    have hadm : AdmissibleTriple p F t.1 t.2.1 t.2.2 := by
      refine ⟨h12, h13, h23, ?_⟩
      show ({p t.1, p t.2.1, p t.2.2} : Multiset (Fin 4)) ∈ F
      rw [hpx, hpy, hpu]
      exact hτF
    refine mem_filter.mpr ⟨mem_copies_iff.mpr (isCopy_activeComplete_of_admissible p F hadm), ?_⟩
    show ({t.1, t.2.1, t.2.2} : Finset V).val.map p = _
    rw [map_three p h12 h13 h23, hpx, hpy, hpu]
  have hfib : ∀ T ∈ S.image f, (S.filter fun t => f t = T).card ≤ 27 := by
    intro T hT
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
    obtain ⟨_, h12, h13, h23⟩ := mem_filter.mp ht
    have hc : (f t).card = 3 := card_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩
    have hsub : (S.filter fun s => f s = f t) ⊆ f t ×ˢ (f t ×ˢ f t) := by
      intro s hs
      obtain ⟨_, hst⟩ := mem_filter.mp hs
      rw [← hst]
      simp [f, mem_product]
    calc
      _ ≤ (f t ×ˢ (f t ×ˢ f t)).card := card_le_card hsub
      _ = 27 := by rw [card_product, card_product, hc]
  have h27 := card_le_mul_card_image S 27 hfib
  have hle : (S.image f).card ≤ typeCount p F {x, y, u} := card_le_card himg
  have hx := hmin x
  have hy := hmin y
  have hu := hmin u
  have h27R : (S.card : ℝ) ≤ 27 * (typeCount p F {x, y, u} : ℝ) := by
    have := h27.trans (Nat.mul_le_mul_left 27 hle)
    exact_mod_cast this
  have hprod : m * (m - 1) * (m - 2) ≤
      classSize p x * (classSize p y - 1) * (classSize p u - 2) := by
    have h1 : m * (m - 1) ≤ classSize p x * (classSize p y - 1) :=
      mul_le_mul hx (by linarith) (by linarith) (by linarith)
    exact mul_le_mul h1 (by linarith) (by linarith) (by nlinarith)
  nlinarith

theorem classTotal_globalMode (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (c : Multiset (Fin 4) → ℝ) (hN : ∀ τ ∈ F, typeCount p F τ ≠ 0) :
    classTotal p (fun a b => boundary
        (chainOf p F (typedWeight p F (fun τ _ _ _ => c τ / typeCount p F τ))) s(a, b)) =
      ∑ τ ∈ F, c τ • (fun i j => (typeEdgeVec τ i j : ℝ)) := by
  set X : Multiset (Fin 4) → V → V → V → ℝ := fun τ _ _ _ => c τ / typeCount p F τ
  have hsym : TernarySymmetric (typedWeight p F X) :=
    typedWeight_symmetric p F X (fun τ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩)
  have hsup := typedWeight_supported p F X
  funext i j
  rw [classTotal_boundary]
  have hcopy : ∀ T ∈ copies p F (activeCompleteGraph p F),
      chainOf p F (typedWeight p F X) T * (edgeVec p (triEdges T) i j : ℝ) =
        c (triType p T) / typeCount p F (triType p T) *
          (typeEdgeVec (triType p T) i j : ℝ) := by
    intro T hT
    have hT' := mem_copies_iff.mp hT
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := card_eq_three.mp hT'.1.card_eq
    have htype : triType p {a, b, d} = {p a, p b, p d} := map_three p hab had hbd
    rw [chainOf_three p F hsym hsup hab had hbd hT', edgeVec_triEdges p hT'.1.card_eq,
      typedWeight_eq, if_pos ⟨hab, had, hbd, htype ▸ hT'.2⟩, htype]
  calc
    _ = ∑ T ∈ copies p F (activeCompleteGraph p F),
        chainOf p F (typedWeight p F X) T * (edgeVec p (triEdges T) i j : ℝ) := by
      symm
      apply sum_subset (subset_univ _)
      intro T _ hT
      rw [chainOf_supported p F _ T (fun h => hT (mem_copies_iff.mpr h)), zero_mul]
    _ = ∑ T ∈ copies p F (activeCompleteGraph p F),
        c (triType p T) / typeCount p F (triType p T) *
          (typeEdgeVec (triType p T) i j : ℝ) := sum_congr rfl hcopy
    _ = ∑ τ ∈ F, ∑ T ∈ copies p F (activeCompleteGraph p F) with triType p T = τ,
        c (triType p T) / typeCount p F (triType p T) *
          (typeEdgeVec (triType p T) i j : ℝ) := by
      symm
      apply sum_fiberwise_of_maps_to
      intro T hT
      exact (mem_copies_iff.mp hT).2
    _ = ∑ τ ∈ F, c τ * (typeEdgeVec τ i j : ℝ) := by
      apply sum_congr rfl
      intro τ hτ
      rw [sum_congr rfl (fun T hT => by rw [(mem_filter.mp hT).2]), sum_const]
      rw [nsmul_eq_mul]
      change (typeCount p F τ : ℝ) * _ = _
      have hne : (typeCount p F τ : ℝ) ≠ 0 := by exact_mod_cast hN τ hτ
      field_simp
    _ = _ := by simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end PaddedGeneral.RealInverse
