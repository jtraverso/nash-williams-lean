/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.OnePartDivisibility

/-! # Exact physical transport of ordinary triangle decompositions

An injective vertex map preserves each triangle, edge disjointness and exact
coverage. No template or decomposition of its physical image is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.OrdinaryDecompositionTransport

open Finset OnePart

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

theorem triEdges_image (f : W → V) (hf : Function.Injective f) (s : Finset W) :
    triEdges (s.image f) = (triEdges s).image (Sym2.map f) := by
  simp only [triEdges, sym2_image, filter_image, Sym2.isDiag_map hf]

omit [DecidableEq W] in
theorem typedTri_image (f : W → V) (hf : Function.Injective f)
    (s : Finset W) (hs : IsTypedTri part1 triFam s) :
    IsTypedTri part1 triFam (s.image f) := by
  have hc : (s.image f).card = 3 := (card_image_of_injective s hf).trans hs.1
  refine ⟨hc, ?_⟩
  change (s.image f).val.map (fun _ : V => (0 : Fin 1)) ∈ {{0, 0, 0}}
  rw [Multiset.map_const']
  change Multiset.replicate (s.image f).card (0 : Fin 1) ∈ {{0, 0, 0}}
  rw [hc]
  decide

theorem hasDecomp_image (f : W → V) (hf : Function.Injective f)
    (E : Finset (Sym2 W)) (hE : HasDecomp part1 triFam E) :
    HasDecomp part1 triFam (E.image (Sym2.map f)) := by
  obtain ⟨D, htri, hdis, hcover⟩ := hE
  refine ⟨D.image (fun s => s.image f), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s, hpre, rfl⟩ := mem_image.mp hs
    exact typedTri_image f hf s (htri s hpre)
  · intro s hs t ht hne
    obtain ⟨s, hpre, rfl⟩ := mem_image.mp hs
    obtain ⟨t, hpre', rfl⟩ := mem_image.mp ht
    change Disjoint (triEdges (s.image f)) (triEdges (t.image f))
    rw [triEdges_image f hf, triEdges_image f hf, disjoint_left]
    intro e he he'
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨b, hb, hab⟩ := mem_image.mp he'
    have hab' : b = a := Sym2.map.injective hf hab
    subst b
    exact disjoint_left.mp (hdis hpre hpre' (fun h => hne (h ▸ rfl))) ha hb
  · rw [image_biUnion]
    simp_rw [triEdges_image f hf]
    rw [← biUnion_image, hcover]

theorem hasDecomp_loopless (E : Finset (Sym2 W))
    (hE : HasDecomp part1 triFam E) : ∀ e ∈ E, ¬ e.IsDiag := by
  obtain ⟨D, _, _, hcover⟩ := hE
  intro e he
  rw [← hcover] at he
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp he
  exact (mem_filter.mp hs).2

end PartitionedTriangleAbsorption.OrdinaryDecompositionTransport
