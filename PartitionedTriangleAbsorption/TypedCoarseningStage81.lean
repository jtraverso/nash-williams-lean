/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Relabelling preserves the same physical decomposition

Only the allowed triangle types change. The vertices, triangle edge sets,
packing and covered edge set are not replaced. No converse divisibility
implication is asserted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedCoarseningStage81

open Finset TypedApplicationLinks

variable {V : Type*} [DecidableEq V] {t u : ℕ}

omit [DecidableEq V] in
theorem typedTri_map (p : V → Fin t) (g : Fin t → Fin u)
    (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, τ.map g ∈ F') {s : Finset V}
    (hs : IsTypedTri p F s) : IsTypedTri (g ∘ p) F' s := by
  refine ⟨hs.1, ?_⟩
  simpa only [Multiset.map_map] using hmap (s.val.map p) hs.2

theorem decomp_map (p : V → Fin t) (g : Fin t → Fin u)
    (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, τ.map g ∈ F') {E : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomp p F E D) :
    IsDecomp (g ∘ p) F' E D := by
  exact ⟨fun s hs => typedTri_map p g F F' hmap (hD.1 s hs), hD.2⟩

theorem hasDecomp_map (p : V → Fin t) (g : Fin t → Fin u)
    (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, τ.map g ∈ F') {E : Finset (Sym2 V)}
    (hE : HasDecomp p F E) : HasDecomp (g ∘ p) F' E := by
  obtain ⟨D, hD⟩ := hE
  exact ⟨D, decomp_map p g F F' hmap hD⟩

/-- Merge the first two and the last two fine classes. -/
def merge : Fin 4 → Fin 2 := ![0, 0, 1, 1]

theorem F3_map_F0 (τ : Multiset (Fin 4)) (hτ : τ ∈ F3) :
    τ.map merge ∈ F0 := by
  simp only [F3, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

theorem F3_decomp_as_F0 (p : V → Fin 4) {E : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomp p F3 E D) :
    IsDecomp (merge ∘ p) F0 E D :=
  decomp_map p merge F3 F0 F3_map_F0 hD

end PartitionedTriangleAbsorption.TypedCoarseningStage81
