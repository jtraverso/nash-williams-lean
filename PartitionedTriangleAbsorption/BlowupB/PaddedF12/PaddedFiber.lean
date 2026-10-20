/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedPattern

/-! # Counting the padded embeddings over one physical triangle -/

namespace PaddedInputs

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t K : ℕ}

/-- Restriction to a root set and its complement determines the entire function. -/
theorem card_restricted_functions_le {D : Type*} [Fintype D] [DecidableEq D]
    (S : Finset D) (A : Finset V) (C : Finset (D → V))
    (hC : ∀ f ∈ C, ∀ x ∈ S, f x ∈ A) :
    C.card ≤ A.card ^ S.card * Fintype.card V ^ (Fintype.card D - S.card) := by
  classical
  let enc : C → ((x : S) → A) × ({x : D // x ∉ S} → V) := fun f =>
    ⟨(fun x => ⟨f.val x.val, hC f.val f.property x.val x.property⟩),
      (fun x => f.val x.val)⟩
  have hinj : Function.Injective enc := by
    intro f g hfg
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · exact congrArg Subtype.val (congrFun (congrArg Prod.fst hfg) ⟨x, hx⟩)
    · exact congrFun (congrArg Prod.snd hfg) ⟨x, hx⟩
  have hc := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl] using hc

noncomputable def paddedFiber (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V))
    (τ : Multiset (Fin t)) (s : Finset V) : Finset (PosT t m → V) := by
  classical
  exact univ.filter fun φ => ValidCopyT m p J τ φ ∧ copyTriT m τ φ = s

theorem mem_paddedFiber (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V))
    (τ : Multiset (Fin t)) (s : Finset V) (φ : PosT t m → V) :
    φ ∈ paddedFiber m p J τ s ↔ ValidCopyT m p J τ φ ∧ copyTriT m τ φ = s := by
  classical
  simp only [paddedFiber, mem_filter, mem_univ, true_and]

theorem paddedFiber_upper (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V))
    (τ : Multiset (Fin t)) (hτ : τ.card = 3) (s : Finset V) (hs : s.card = 3) :
    (paddedFiber m p J τ s).card ≤ 27 * Fintype.card V ^ (qT t m - 3) := by
  classical
  have hc := card_restricted_functions_le (patPosT m τ) s (paddedFiber m p J τ s) (by
    intro φ hφ x hx
    rw [← ((mem_paddedFiber _ _ _ _ _ _).mp hφ).2]
    exact mem_image.mpr ⟨x, hx, rfl⟩)
  simpa only [patPosT_card m τ hτ, hs, Fintype.card_prod, Fintype.card_fin,
    show (3 : ℕ) ^ 3 = 27 by decide] using hc

theorem paddedFiber_lower (m : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V)) (ω : ℝ) (hK : qT t m ≤ K)
    (hext : ExtendableT K p F J ω) (s : Finset V) (hs : s.card = 3)
    (hsub : triEdges s ⊆ J) :
    ω * (Fintype.card V : ℝ) ^ (qT t m - 3) ≤
      ((paddedFiber m p J (s.val.map p) s).card : ℝ) := by
  classical
  let τ := s.val.map p
  have hτ : τ.card = 3 := by simpa [τ] using hs
  obtain ⟨φ, hinj, hlabel, hcopy⟩ := exists_pattern_roots m p s hs
  have hc := hext.domain (D := PosT t m) (by simpa only [Fintype.card_prod,
    Fintype.card_fin] using hK) Prod.fst (patPosT m τ) ∅ φ hinj hlabel
  have hcount : (goodExt p F J Prod.fst ∅ (patPosT m τ) φ).card ≤
      (paddedFiber m p J τ s).card := by
    apply card_le_card
    intro ψ hψ
    obtain ⟨hfix, hψinj, hψlabel, _⟩ := (mem_goodExt _ _ _ _ _ _ _ _).mp hψ
    have heq : copyTriT m τ ψ = s := by
      calc
        _ = copyTriT m τ φ := by
          apply image_congr
          exact hfix
        _ = s := hcopy
    apply (mem_paddedFiber _ _ _ _ _ _).mpr
    exact ⟨⟨⟨hψinj, hψlabel⟩, by simpa only [heq] using hsub⟩, heq⟩
  calc
    _ ≤ ((goodExt p F J Prod.fst ∅ (patPosT m τ) φ).card : ℝ) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, patPosT_card m τ hτ] using hc
    _ ≤ _ := by exact_mod_cast hcount

#print axioms card_restricted_functions_le
#print axioms paddedFiber_upper
#print axioms paddedFiber_lower

end PaddedInputs
