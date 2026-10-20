/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.GreedyMain
public import PartitionedTriangleAbsorption.SharedLibraryTransport
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # Promoting a shared map to physical F0 pieces and a physical refiner

For a map `f` that is injective on the vertex support of every piece, part-preserving there,
and edge-injective on the library union:

* `even_map_on_support`: transported pieces keep even degrees (summing over fibres);
* `isIntDiv_map_on_support`: transported loopless F0-divisible pieces stay F0-divisible;
* `refinesReserve_host`: an abstract refiner of the lifted reserve `mapE emb X`, where
  `f ∘ emb = id`, becomes a physical refiner of `X` with pieces `mapE f (B j)` and remainder
  `mapE f R`. Every physical leftover `L ⊆ X` is first pulled back along `emb`.

Edge injectivity alone does not give looplessness; that is a separate hypothesis here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SharedGreedyPort

open Finset AntiEdgeSelection TypedRefinerF0 TypedRefinerCharge TypedApplicationLinks

variable {A V I : Type*} [DecidableEq A] [DecidableEq V]

/-- Degrees of a transported piece are degrees of the unique preimage in its support. -/
theorem incidentLoad_map_on_support (f : A → V) (E : Finset (Sym2 A))
    (hinj : Set.InjOn f ↑(vsupp E)) (y : V) :
    (∃ u ∈ vsupp E, f u = y ∧ incidentLoad (mapE f E) y = incidentLoad E u) ∨
      incidentLoad (mapE f E) y = 0 := by
  have hEinj : Set.InjOn (Sym2.map f) ↑E := by
    intro e₁ he₁ e₂ he₂ h
    exact map_injOn_of_injOn hinj (fun x hx => mem_coe.mpr (mem_vsupp.mpr ⟨e₁, he₁, hx⟩))
      (fun x hx => mem_coe.mpr (mem_vsupp.mpr ⟨e₂, he₂, hx⟩)) h
  by_cases hy : ∃ u ∈ vsupp E, f u = y
  · obtain ⟨u, hu, rfl⟩ := hy
    left
    refine ⟨u, hu, rfl, ?_⟩
    unfold incidentLoad mapE
    rw [filter_image]
    have hf : (E.filter fun e => f u ∈ Sym2.map f e) = E.filter fun e => u ∈ e := by
      refine filter_congr fun e he => ?_
      rw [Sym2.mem_map]
      constructor
      · rintro ⟨b, hb, hfb⟩
        have hb' : b ∈ vsupp E := mem_vsupp.mpr ⟨e, he, hb⟩
        rwa [← hinj (mem_coe.mpr hb') (mem_coe.mpr hu) hfb]
      · intro h; exact ⟨u, h, rfl⟩
    rw [hf]
    exact card_image_of_injOn fun e₁ he₁ e₂ he₂ h =>
      hEinj (mem_coe.mpr (mem_filter.mp he₁).1) (mem_coe.mpr (mem_filter.mp he₂).1) h
  · right
    unfold incidentLoad
    rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hye
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hye
    exact hy ⟨x, mem_vsupp.mpr ⟨e', he', hx⟩, rfl⟩

theorem even_map_on_support (f : A → V) (E : Finset (Sym2 A))
    (hinj : Set.InjOn f ↑(vsupp E)) (heven : ∀ w, Even (incidentLoad E w)) (y : V) :
    Even (incidentLoad (mapE f E) y) := by
  rcases incidentLoad_map_on_support f E hinj y with ⟨u, -, -, h⟩ | h
  · rw [h]; exact heven u
  · rw [h]; exact ⟨0, rfl⟩

theorem loopless_map_on_support (f : A → V) (E : Finset (Sym2 A))
    (hinj : Set.InjOn f ↑(vsupp E)) (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    ∀ e ∈ mapE f E, ¬ e.IsDiag := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
  induction e' using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := fun h => hloop _ he' (Sym2.mk_isDiag_iff.mpr h)
    have hx : x ∈ vsupp E := mem_vsupp.mpr ⟨_, he', Sym2.mem_mk_left x y⟩
    have hy : y ∈ vsupp E := mem_vsupp.mpr ⟨_, he', Sym2.mem_mk_right x y⟩
    rw [map_pair, Sym2.mk_isDiag_iff]
    exact fun h => hxy (hinj (mem_coe.mpr hx) (mem_coe.mpr hy) h)

omit [DecidableEq A] in
theorem charge_congr_on (pw pw' : A → Fin 2) (E : Finset (Sym2 A))
    (h : ∀ e ∈ E, ∀ x ∈ e, pw x = pw' x) : charge chi0 pw E = charge chi0 pw' E := by
  rw [charge_eq_sum, charge_eq_sum]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    rw [h _ he a (Sym2.mem_mk_left a b), h _ he b (Sym2.mem_mk_right a b)]

/-- **Transported F0 pieces stay F0-divisible**, with only piecewise vertex injectivity. -/
theorem isIntDiv_map_on_support (pA : A → Fin 2) (pV : V → Fin 2) (f : A → V)
    (E : Finset (Sym2 A)) (hinj : Set.InjOn f ↑(vsupp E))
    (hpart : ∀ x ∈ vsupp E, pV (f x) = pA x) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hdiv : IsIntDiv pA F0 E) : IsIntDiv pV F0 (mapE f E) := by
  have hEinj : Set.InjOn (Sym2.map f) ↑E := by
    intro e₁ he₁ e₂ he₂ h
    exact map_injOn_of_injOn hinj (fun x hx => mem_coe.mpr (mem_vsupp.mpr ⟨e₁, he₁, hx⟩))
      (fun x hx => mem_coe.mpr (mem_vsupp.mpr ⟨e₂, he₂, hx⟩)) h
  refine isIntDiv_of_charge pV (loopless_map_on_support f E hinj hloop)
    (even_map_on_support f E hinj (TypedDivisibilityCollapse.even_of_isIntDiv
      TypedTransportExamples.F0_card hloop hdiv)) ?_
  rw [SharedLibraryTransport.charge_map_on_support pV f E E hEinj (subset_refl _),
    charge_congr_on (pV ∘ f) pA E fun e he x hx =>
      hpart x (mem_vsupp.mpr ⟨e, he, hx⟩)]
  exact charge_eq_zero_of_isIntDiv kills_chi0 hdiv

theorem mapE_id_of_leftInverse {f : A → V} {emb : V → A} (h : ∀ v, f (emb v) = v)
    (L : Finset (Sym2 V)) : mapE f (mapE emb L) = L := by
  have hc : Sym2.map f ∘ Sym2.map emb = id := by
    funext e
    induction e using Sym2.ind with
    | _ a b => simp only [Function.comp_apply, map_pair, h, id]
  unfold mapE
  rw [image_image, hc, image_id]

/-- **Physical refiner from a shared map.** The leftover is pulled back along `emb`
(root-map injectivity), selected abstractly, and pushed forward along the one fixed map `f`. -/
theorem refinesReserve_host (pA : A → Fin 2) (pV : V → Fin 2) (f : A → V) (emb : V → A)
    (hfemb : ∀ v, f (emb v) = v) (hpemb : ∀ v, pA (emb v) = pV v)
    (indices : Finset I) (B : I → Finset (Sym2 A)) (X : Finset (Sym2 V))
    (R : Finset (Sym2 A)) (hX : ∀ e ∈ X, ¬ e.IsDiag)
    (hinj : Set.InjOn (Sym2.map f) ↑(indices.biUnion B))
    (href : RefinerAssembly.RefinesReserve (p := pA) (F := F0) indices B (mapE emb X) R) :
    RefinerAssembly.RefinesReserve (p := pV) (F := F0) indices (fun j => mapE f (B j)) X
      (mapE f R) := by
  intro L hL hdiv
  have hembinj : Function.Injective emb := fun a b h => by
    rw [← hfemb a, ← hfemb b, h]
  have hloopL : ∀ e ∈ L, ¬ e.IsDiag := fun e he => hX e (hL he)
  have hevenL := TypedDivisibilityCollapse.even_of_isIntDiv TypedTransportExamples.F0_card
    hloopL hdiv
  have hdiv' : IsIntDiv pA F0 (mapE emb L) := by
    refine isIntDiv_of_charge pA (loopless_mapE hembinj hloopL) ?_ ?_
    · intro w
      by_cases hw : ∃ v, emb v = w
      · obtain ⟨v, rfl⟩ := hw
        rw [incidentLoad_mapE_apply hembinj]
        exact hevenL v
      · simp only [not_exists] at hw
        rw [incidentLoad_mapE_of_not_mem L hw]
        exact ⟨0, rfl⟩
    · rw [charge_mapE pA hembinj, show pA ∘ emb = pV from funext hpemb]
      exact charge_eq_zero_of_isIntDiv kills_chi0 hdiv
  obtain ⟨s, hs, hd, heq⟩ := href (mapE emb L) (fun e he => by
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
    exact mem_mapE.mpr ⟨e', hL he', rfl⟩) hdiv'
  obtain ⟨hd', heq'⟩ := SharedLibraryTransport.selection_transport f indices s B R
    (mapE emb L) hinj hs hd heq
  refine ⟨s, hs, hd', ?_⟩
  rw [heq', mapE_id_of_leftInverse hfemb]

end PartitionedTriangleAbsorption.SharedGreedyPort
