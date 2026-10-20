/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedFiber

/-! # Pushing padded regularity to weights on the original physical copies -/

namespace PaddedInputs

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t K : ℕ}

noncomputable def physicalWeight (m : ℕ) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V))
    (y : Multiset (Fin t) → (PosT t m → V) → ℝ) (s : Finset V) : ℝ :=
  ∑ τ ∈ F, ∑ φ ∈ paddedFiber m p J τ s, y τ φ

theorem physicalWeight_eq_type (m : ℕ) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (J : Finset (Sym2 V)) (y : Multiset (Fin t) → (PosT t m → V) → ℝ)
    (s : Finset V) (hs : s.val.map p ∈ F) :
    physicalWeight m p F J y s =
      ∑ φ ∈ paddedFiber m p J (s.val.map p) s, y (s.val.map p) φ := by
  classical
  unfold physicalWeight
  apply sum_eq_single (s.val.map p)
  · intro τ hτ hne
    have hempty : paddedFiber m p J τ s = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro φ hφ
      obtain ⟨hvalid, heq⟩ := (mem_paddedFiber _ _ _ _ _ _).mp hφ
      have htype := copyTriT_type m p τ (hF τ hτ) φ hvalid.1
      rw [heq] at htype
      exact hne htype.symm
    rw [hempty, sum_empty]
  · exact fun h => (h hs).elim

open Classical in
/-- The sum over all padded embeddings is exactly the load of their physical images. -/
theorem physicalWeight_load (m : ℕ) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : Multiset (Fin t) → (PosT t m → V) → ℝ) (e : Sym2 V) :
    (∑ s ∈ copies p F G with e ∈ triEdges s, physicalWeight m p F G.edgeFinset y s) =
      ∑ τ ∈ F, ∑ φ ∈ univ.filter (fun φ => ValidCopyT m p G.edgeFinset τ φ ∧
        e ∈ triEdges (copyTriT m τ φ)), y τ φ := by
  classical
  unfold physicalWeight
  rw [sum_comm]
  apply sum_congr rfl
  intro τ hτ
  let C := univ.filter (fun φ => ValidCopyT m p G.edgeFinset τ φ ∧
    e ∈ triEdges (copyTriT m τ φ))
  let S := (copies p F G).filter (fun s => e ∈ triEdges s)
  have hmap : ∀ φ ∈ C, copyTriT m τ φ ∈ S := by
    intro φ hφ
    obtain ⟨hvalid, hedge⟩ := (mem_filter.mp hφ).2
    exact mem_filter.mpr ⟨mem_copies_iff.mpr
      (isCopy_of_validCopyT m p F G τ hτ (hF τ hτ) φ hvalid), hedge⟩
  have hfiber (s : Finset V) (hs : s ∈ S) :
      C.filter (fun φ => copyTriT m τ φ = s) = paddedFiber m p G.edgeFinset τ s := by
    ext φ
    simp only [C, mem_filter, mem_univ, true_and, mem_paddedFiber]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hvalid, heq⟩
      exact ⟨⟨hvalid, by simpa only [heq] using (mem_filter.mp hs).2⟩, heq⟩
  calc
    _ = ∑ s ∈ S, ∑ φ ∈ C with copyTriT m τ φ = s, y τ φ := by
      apply sum_congr rfl
      intro s hs
      rw [hfiber s hs]
    _ = _ := sum_fiberwise_of_maps_to hmap (y τ)

theorem padded_lower_normalization (ω n : ℝ) (q : ℕ) (hn : 0 < n) (hq : 3 ≤ q) :
    (ω * n ^ (q - 3)) * (ω / n ^ (q - 2)) = ω ^ 2 / n := by
  have he : q - 2 = (q - 3) + 1 := by omega
  rw [he, pow_succ]
  field_simp

theorem padded_upper_normalization (ω n : ℝ) (q : ℕ) (hω : 0 < ω)
    (hn : 0 < n) (hq : 3 ≤ q) :
    (27 * n ^ (q - 3)) * (1 / (ω * n ^ (q - 2))) = 27 / (ω * n) := by
  have he : q - 2 = (q - 3) + 1 := by omega
  rw [he, pow_succ]
  field_simp

/-- Every physical copy has weight at least ω²/n and at most 27/(ω n).
Its edge loads are exactly those in the supplied padded regularity hypothesis. -/
theorem physical_weights_of_regular_extendable (m : ℕ) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω c : ℝ)
    (hω : 0 < ω) (hn : 0 < Fintype.card V) (hq : 3 ≤ qT t m) (hK : qT t m ≤ K)
    (hreg : PaddedRegularT m p F G.edgeFinset ω c)
    (hext : ExtendableT K p F G.edgeFinset ω) :
    ∃ φ : Finset V → ℝ,
      (∀ s, IsCopy p F G s → ω ^ 2 / Fintype.card V ≤ φ s ∧
        φ s ≤ 27 / (ω * Fintype.card V)) ∧
      ∀ e ∈ G.edgeFinset,
        |(∑ s ∈ copies p F G with e ∈ triEdges s, φ s) - 1| ≤ c := by
  classical
  obtain ⟨y, hy, hload⟩ := hreg
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  refine ⟨physicalWeight m p F G.edgeFinset y, ?_, ?_⟩
  · intro s hs
    rw [physicalWeight_eq_type m p F hF G.edgeFinset y s hs.2]
    let τ := s.val.map p
    let C := paddedFiber m p G.edgeFinset τ s
    have hτ : τ.card = 3 := by simpa [τ] using hs.1.card_eq
    have hylo : (C.card : ℝ) * (ω / (Fintype.card V : ℝ) ^ (qT t m - 2)) ≤
        ∑ ψ ∈ C, y τ ψ := by
      simpa only [sum_const, nsmul_eq_mul] using
        (sum_le_sum fun ψ hψ => (hy τ hs.2 ψ ((mem_paddedFiber _ _ _ _ _ _).mp hψ).1).1)
    have hyhi : (∑ ψ ∈ C, y τ ψ) ≤
        (C.card : ℝ) * (1 / (ω * (Fintype.card V : ℝ) ^ (qT t m - 2))) := by
      simpa only [sum_const, nsmul_eq_mul] using
        (sum_le_sum fun ψ hψ => (hy τ hs.2 ψ ((mem_paddedFiber _ _ _ _ _ _).mp hψ).1).2)
    constructor
    · calc
        _ = (ω * (Fintype.card V : ℝ) ^ (qT t m - 3)) *
            (ω / (Fintype.card V : ℝ) ^ (qT t m - 2)) :=
          (padded_lower_normalization ω _ _ hnR hq).symm
        _ ≤ (C.card : ℝ) * (ω / (Fintype.card V : ℝ) ^ (qT t m - 2)) :=
          mul_le_mul_of_nonneg_right
            (paddedFiber_lower m p F G.edgeFinset ω hK hext s hs.1.card_eq
              (triEdges_subset_of_isCopy hs)) (div_nonneg hω.le (pow_nonneg hnR.le _))
        _ ≤ _ := hylo
    · have hc : (C.card : ℝ) ≤ 27 * (Fintype.card V : ℝ) ^ (qT t m - 3) := by
        exact_mod_cast paddedFiber_upper m p G.edgeFinset τ hτ s hs.1.card_eq
      calc
        _ ≤ (C.card : ℝ) * (1 / (ω * (Fintype.card V : ℝ) ^ (qT t m - 2))) := hyhi
        _ ≤ (27 * (Fintype.card V : ℝ) ^ (qT t m - 3)) *
            (1 / (ω * (Fintype.card V : ℝ) ^ (qT t m - 2))) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := padded_upper_normalization ω _ _ hω hnR hq
  · intro e he
    rw [physicalWeight_load m p F hF G y e]
    exact hload e he

#print axioms physicalWeight_load
#print axioms physical_weights_of_regular_extendable

end PaddedInputs
