/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedExtension
import Mathlib.Data.Fintype.Fin

/-! # The three distinguished positions of a padded triangle -/

namespace PaddedInputs

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem mem_triEdges_iff {s : Finset V} {x y : V} :
    s(x, y) ∈ triEdges s ↔ x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff, and_assoc]

theorem mem_copies_iff {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {s : Finset V} : s ∈ copies p F G ↔ IsCopy p F G s := by
  simp only [copies, mem_filter, mem_powersetCard, subset_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h.1.card_eq, h⟩⟩

theorem triEdges_subset_of_isCopy {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V} (h : IsCopy p F G s) :
    triEdges s ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := mem_triEdges_iff.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (h.1.isClique hx hy hxy)

theorem patPosT_fiber_card (m : ℕ) (τ : Multiset (Fin t)) (hτ : τ.card = 3)
    (i : Fin t) : ((patPosT m τ).filter (fun x => x.1 = i)).card = τ.count i := by
  have hbound : τ.count i ≤ m + 3 := (Multiset.count_le_card i τ).trans (by omega)
  have hset : (patPosT m τ).filter (fun x => x.1 = i) =
      ({i} : Finset (Fin t)) ×ˢ (univ.filter fun j : Fin (m + 3) => j.val < τ.count i) := by
    ext x
    simp only [mem_filter, patPosT, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hx, rfl⟩
      exact ⟨rfl, hx⟩
    · rintro ⟨rfl, hx⟩
      exact ⟨hx, rfl⟩
  rw [hset, card_product, card_singleton, one_mul, Fin.card_filter_val_lt,
    Nat.min_eq_right hbound]

theorem patPosT_type (m : ℕ) (τ : Multiset (Fin t)) (hτ : τ.card = 3) :
    (patPosT m τ).val.map Prod.fst = τ := by
  apply Multiset.ext.mpr
  intro i
  rw [Multiset.count_map]
  simpa only [eq_comm, ← Finset.filter_val, Finset.card] using patPosT_fiber_card m τ hτ i

theorem patPosT_card (m : ℕ) (τ : Multiset (Fin t)) (hτ : τ.card = 3) :
    (patPosT m τ).card = 3 := by
  have h := congrArg Multiset.card (patPosT_type m τ hτ)
  simpa only [Multiset.card_map, hτ, Finset.card] using h

theorem copyTriT_card (m : ℕ) (τ : Multiset (Fin t)) (hτ : τ.card = 3)
    (φ : PosT t m → V) (hinj : Function.Injective φ) : (copyTriT m τ φ).card = 3 := by
  rw [copyTriT, card_image_of_injective _ hinj, patPosT_card m τ hτ]

theorem copyTriT_type (m : ℕ) (p : V → Fin t) (τ : Multiset (Fin t))
    (hτ : τ.card = 3) (φ : PosT t m → V) (hφ : IsEmbT m p φ) :
    (copyTriT m τ φ).val.map p = τ := by
  rw [copyTriT, image_val_of_injOn hφ.1.injOn, Multiset.map_map]
  have heq : p ∘ φ = Prod.fst := funext hφ.2
  rw [heq, patPosT_type m τ hτ]

theorem isCopy_of_validCopyT (m : ℕ) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : Multiset (Fin t)) (hτ : τ ∈ F) (hτ3 : τ.card = 3)
    (φ : PosT t m → V) (hφ : ValidCopyT m p G.edgeFinset τ φ) :
    IsCopy p F G (copyTriT m τ φ) := by
  refine ⟨⟨?_, copyTriT_card m τ hτ3 φ hφ.1.1⟩, ?_⟩
  · intro a ha b hb hab
    exact SimpleGraph.mem_edgeFinset.mp (hφ.2 (mem_triEdges_iff.mpr ⟨ha, hb, hab⟩))
  · rw [copyTriT_type m p τ hτ3 φ hφ.1]
    exact hτ

theorem count_type_eq_card_filter (p : V → Fin t) (s : Finset V) (i : Fin t) :
    (s.val.map p).count i = (s.filter fun v => p v = i).card := by
  rw [Multiset.count_map]
  simp only [eq_comm, filter_val, Finset.card]

/-- Label-preserving roots for any physical triangle, without selecting its isolated positions. -/
theorem exists_pattern_roots (m : ℕ) (p : V → Fin t) (s : Finset V)
    (hs : s.card = 3) :
    ∃ φ : PosT t m → V,
      Set.InjOn φ (patPosT m (s.val.map p)) ∧
      (∀ x ∈ patPosT m (s.val.map p), p (φ x) = x.1) ∧
      copyTriT m (s.val.map p) φ = s := by
  classical
  let τ := s.val.map p
  have hτ : τ.card = 3 := by simpa [τ] using hs
  obtain ⟨fallback, hfallback⟩ := card_pos.mp (show 0 < s.card by omega)
  let A : Fin t → Finset V := fun i => s.filter (fun v => p v = i)
  have hA (i : Fin t) : (A i).card = τ.count i := (count_type_eq_card_filter p s i).symm
  let φ : PosT t m → V := fun x =>
    if hx : x.2.val < (A x.1).card then ((A x.1).equivFin.symm ⟨x.2.val, hx⟩).val
    else fallback
  have hlt (x : PosT t m) (hx : x ∈ patPosT m τ) : x.2.val < (A x.1).card := by
    rw [hA]
    exact (mem_filter.mp hx).2
  have hmem (x : PosT t m) (hx : x ∈ patPosT m τ) : φ x ∈ A x.1 := by
    simpa only [φ, dite_eq_left (hlt x hx)] using
      ((A x.1).equivFin.symm ⟨x.2.val, hlt x hx⟩).property
  have hlabel (x : PosT t m) (hx : x ∈ patPosT m τ) : p (φ x) = x.1 :=
    (mem_filter.mp (hmem x hx)).2
  have hinj : Set.InjOn φ (patPosT m τ) := by
    intro x hx y hy hxy
    have hfirst : x.1 = y.1 := (hlabel x hx).symm.trans ((congrArg p hxy).trans (hlabel y hy))
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    dsimp only at hfirst
    subst j
    apply congrArg (fun j : Fin (m + 3) => (i, j))
    apply Fin.ext
    dsimp only [φ] at hxy
    rw [dite_eq_left (hlt _ hx), dite_eq_left (hlt _ hy)] at hxy
    have heq := (A i).equivFin.symm.injective (Subtype.ext hxy)
    exact congrArg (fun z : Fin (A i).card => z.val) heq
  refine ⟨φ, hinj, hlabel, ?_⟩
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp (hmem x hx)).1
  · rw [copyTriT, card_image_of_injOn hinj, patPosT_card m τ hτ, hs]

#print axioms patPosT_type
#print axioms isCopy_of_validCopyT
#print axioms exists_pattern_roots

end PaddedInputs
