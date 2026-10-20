/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.TemplateFamily
public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.TypedChargeCatalog
public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.GroupLedger

@[expose] public section

/-!
# Transporting edge sets along vertex maps that are injective on their vertices

Edge-count vectors, vertex incidences, evenness and looplessness are invariant under a vertex
map that is injective on the vertices of the edge set and preserves the parts.  These facts
transport template copies and library pieces between a host and abstract patterns.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection

section Mapping

variable {V V' : Type*} [DecidableEq V] [DecidableEq V'] {t : ℕ}

/-- `f` is injective on the vertices of `E`. -/
def VInjOn (f : V → V') (E : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ E, ∀ e' ∈ E, ∀ u ∈ e, ∀ u' ∈ e', f u = f u' → u = u'

theorem VInjOn.of_injective {f : V → V'} (hf : Function.Injective f) (E : Finset (Sym2 V)) :
    VInjOn f E :=
  fun _ _ _ _ _ _ _ _ h => hf h

theorem sym2_map_injOn {f : V → V'} {E : Finset (Sym2 V)} (hf : VInjOn f E) :
    Set.InjOn (Sym2.map f) (E : Set (Sym2 V)) := by
  intro e he e' he' h
  induction e using Sym2.ind with
  | _ a b =>
  induction e' using Sym2.ind with
  | _ c d =>
  simp only [Sym2.map_mk] at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := hf _ he _ he' a (Sym2.mem_mk_left a b) c (Sym2.mem_mk_left c d) h1
    have e2 := hf _ he _ he' b (Sym2.mem_mk_right a b) d (Sym2.mem_mk_right c d) h2
    rw [e1, e2]
  · have e1 := hf _ he _ he' a (Sym2.mem_mk_left a b) d (Sym2.mem_mk_right c d) h1
    have e2 := hf _ he _ he' b (Sym2.mem_mk_right a b) c (Sym2.mem_mk_left c d) h2
    rw [e1, e2]; exact Sym2.eq_swap

theorem pairVec_map (p' : V' → Fin t) (f : V → V') (e : Sym2 V) :
    pairVec p' (Sym2.map f e) = pairVec (p' ∘ f) e := by
  induction e using Sym2.ind with
  | _ a b => rfl

theorem pairVec_congr {p q : V → Fin t} {e : Sym2 V} (h : ∀ u ∈ e, p u = q u) :
    pairVec p e = pairVec q e := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    rw [h a (Sym2.mem_mk_left a b), h b (Sym2.mem_mk_right a b)]

theorem edgeVec_image {p : V → Fin t} {p' : V' → Fin t} {f : V → V'} {E : Finset (Sym2 V)}
    (hf : VInjOn f E) (hp : ∀ e ∈ E, ∀ u ∈ e, p' (f u) = p u) :
    edgeVec p' (E.image (Sym2.map f)) = edgeVec p E := by
  unfold edgeVec
  rw [sum_image (sym2_map_injOn hf)]
  refine sum_congr rfl fun e he => ?_
  rw [pairVec_map]
  exact pairVec_congr fun u hu => hp e he u hu

theorem loopless_image {f : V → V'} {E : Finset (Sym2 V)} (hf : VInjOn f E)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) : ∀ e ∈ E.image (Sym2.map f), ¬ e.IsDiag := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := mem_image.mp he'
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    intro hab
    exact hloop _ he (Sym2.mk_isDiag_iff.mpr
      (hf _ he _ he a (Sym2.mem_mk_left a b) b (Sym2.mem_mk_right a b) hab))

theorem incidentLoad_image_of_mem {f : V → V'} {E : Finset (Sym2 V)} (hf : VInjOn f E)
    {u : V} {e0 : Sym2 V} (he0 : e0 ∈ E) (hu : u ∈ e0) :
    incidentLoad (E.image (Sym2.map f)) (f u) = incidentLoad E u := by
  unfold incidentLoad
  have hfilt : (E.image (Sym2.map f)).filter (fun e => f u ∈ e) =
      (E.filter (fun e => u ∈ e)).image (Sym2.map f) := by
    ext e'
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hmem⟩
      obtain ⟨w, hw, hwu⟩ := Sym2.mem_map.mp hmem
      have := hf _ he _ he0 w hw u hu hwu
      exact ⟨e, ⟨he, this ▸ hw⟩, rfl⟩
    · rintro ⟨e, ⟨he, hue⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, Sym2.mem_map.mpr ⟨u, hue, rfl⟩⟩
  rw [hfilt, card_image_of_injOn ((sym2_map_injOn hf).mono (by
    intro e he; exact (mem_filter.mp he).1))]

theorem incidentLoad_image_of_not {f : V → V'} {E : Finset (Sym2 V)} {w : V'}
    (hw : ∀ e ∈ E, ∀ u ∈ e, f u ≠ w) : incidentLoad (E.image (Sym2.map f)) w = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e' he' hmem
  obtain ⟨e, he, rfl⟩ := mem_image.mp he'
  obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hmem
  exact hw e he u hu rfl

theorem even_image {f : V → V'} {E : Finset (Sym2 V)} (hf : VInjOn f E)
    (heven : ∀ u, Even (incidentLoad E u)) : ∀ w, Even (incidentLoad (E.image (Sym2.map f)) w) := by
  intro w
  by_cases h : ∃ e ∈ E, ∃ u ∈ e, f u = w
  · obtain ⟨e, he, u, hu, rfl⟩ := h
    rw [incidentLoad_image_of_mem hf he hu]
    exact heven u
  · push_neg at h
    rw [incidentLoad_image_of_not h]
    exact ⟨0, rfl⟩

end Mapping

section Charge

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The charge valuation of single edges. -/
noncomputable def chargeVal (F : Finset (Multiset (Fin t))) (p : V → Fin t) :
    Sym2 V → TypeChargeGroup F :=
  fun e => globalCharge F (pairVec p e)

omit [DecidableEq V] in
theorem edgeVal_chargeVal (F : Finset (Multiset (Fin t))) (p : V → Fin t) (E : Finset (Sym2 V)) :
    edgeVal (chargeVal F p) E = globalCharge F (edgeVec p E) := by
  simp only [edgeVal, chargeVal, edgeVec, map_sum]

theorem globalCharge_typeEdgeVec {F : Finset (Multiset (Fin t))} {τ : Multiset (Fin t)}
    (hτ : τ ∈ F) : globalCharge F (typeEdgeVec τ) = 0 := by
  classical
  rw [globalCharge_eq_zero_iff]
  refine ⟨fun σ => if σ = τ then 1 else 0, ?_⟩
  simp only [ite_smul, one_smul, zero_smul]
  rw [sum_ite_eq' F τ, if_pos hτ]

theorem charge_zero_of_isIntDiv {F : Finset (Multiset (Fin t))} {p : V → Fin t}
    {L : Finset (Sym2 V)} (h : IsIntDiv p F L) : edgeVal (chargeVal F p) L = 0 := by
  rw [edgeVal_chargeVal, globalCharge_eq_zero_iff]
  exact h.1

end Charge

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
