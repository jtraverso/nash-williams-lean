/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCounts
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedTemplates

@[expose] public section

/-! # Exact physical invariants under an injective template embedding -/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

theorem unorderedCount_image (f : W → V) (hf : Function.Injective f)
    (p : V → Fin 4) (label : W → Fin 4) (hlabel : ∀ w, p (f w) = label w)
    (E : Finset (Sym2 W)) (i j : Fin 4) :
    unorderedCount p (E.image (Sym2.map f)) i j = unorderedCount label E i j := by
  rw [unorderedCount_sum, unorderedCount_sum,
    sum_image fun a _ b _ h => Sym2.map.injective hf h]
  apply sum_congr rfl
  intro e _
  have hmap : Sym2.map p (Sym2.map f e) = Sym2.map label e := by
    induction e using Sym2.ind with
    | _ a b => simp only [Sym2.map_mk, hlabel]
  rw [hmap]

omit [DecidableEq W] in
theorem charge_image {t : ℕ} (f : W → V) (hf : Function.Injective f)
    (p : V → Fin t) (label : W → Fin t) (hlabel : ∀ w, p (f w) = label w)
    (E : Finset (Sym2 W)) (χ : Fin t → Fin t → ℤ) :
    charge χ p (E.image (Sym2.map f)) = charge χ label E := by
  have hp : p ∘ f = label := funext hlabel
  have hv := edgeVec_image_embedding ⟨f, hf⟩ p E
  change edgeVec p (E.image (Sym2.map f)) = edgeVec (p ∘ f) E at hv
  unfold charge
  rw [hv, hp]

omit [DecidableEq W] in
theorem loopless_image (f : W → V) (hf : Function.Injective f)
    (E : Finset (Sym2 W)) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    ∀ e ∈ E.image (Sym2.map f), ¬ e.IsDiag := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_image.mp he
  simpa only [Sym2.isDiag_map hf] using hE e' he'

theorem even_image (f : W → V) (hf : Function.Injective f)
    (E : Finset (Sym2 W)) (hE : ∀ w, Even (incidentLoad E w)) :
    ∀ v, Even (incidentLoad (E.image (Sym2.map f)) v) := by
  intro v
  by_cases hv : ∃ w, f w = v
  · obtain ⟨w, rfl⟩ := hv
    rw [ColouredHub.incidentLoad_image_apply f hf]
    exact hE w
  · rw [ColouredHub.incidentLoad_image_of_notMem f E v (by simpa using hv)]
    exact ⟨0, rfl⟩

omit [DecidableEq W] in
theorem active_image {t : ℕ} (F : Finset (Multiset (Fin t)))
    (f : W → V) (p : V → Fin t) (label : W → Fin t)
    (hlabel : ∀ w, p (f w) = label w) (E : Finset (Sym2 W))
    (hE : ActiveEdges F label E) : ActiveEdges F p (E.image (Sym2.map f)) := by
  intro x y hxy
  obtain ⟨e, he, hmap⟩ := mem_image.mp hxy
  induction e using Sym2.ind with
  | _ a b =>
    change s(f a, f b) = s(x, y) at hmap
    rcases Sym2.eq_iff.mp hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa only [hlabel] using hE a b he
    · have hba : s(b, a) ∈ E := by simpa only [Sym2.eq_swap] using he
      simpa only [hlabel] using hE b a hba

theorem f1FreeCharge_image (f : W → V) (hf : Function.Injective f)
    (p : V → Fin 4) (label : W → Fin 4) (hlabel : ∀ w, p (f w) = label w)
    (E : Finset (Sym2 W)) :
    f1FreeCharge p (E.image (Sym2.map f)) = f1FreeCharge label E := by
  simp only [f1FreeCharge, f1Base, crossCount, unorderedCount_image f hf p label hlabel]

theorem f2FreeCharge_image (f : W → V) (hf : Function.Injective f)
    (p : V → Fin 4) (label : W → Fin 4) (hlabel : ∀ w, p (f w) = label w)
    (E : Finset (Sym2 W)) :
    f2FreeCharge p (E.image (Sym2.map f)) = f2FreeCharge label E := by
  simp only [f2FreeCharge, f2Base, crossCount, unorderedCount_image f hf p label hlabel]

theorem f2Numerator_image (f : W → V) (hf : Function.Injective f)
    (p : V → Fin 4) (label : W → Fin 4) (hlabel : ∀ w, p (f w) = label w)
    (E : Finset (Sym2 W)) :
    f2Numerator p (E.image (Sym2.map f)) = f2Numerator label E := by
  simp only [f2Numerator, unorderedCount_image f hf p label hlabel]

#print axioms unorderedCount_image
#print axioms charge_image
#print axioms even_image
#print axioms active_image

end PaddedF12
