/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedTransformerLabels

/-! # A constructed abstract typed transformer

The auxiliary vertices are fresh by construction. No existence of a typed
labelling is assumed. Embedding the resulting object into a prescribed host
and producing compatible trail data remain separate obligations.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedTransformer

open Finset PrivateTemplate AntiEdgeSelection

variable {W : Type*} [DecidableEq W] {I : Type*} [Fintype I] [DecidableEq I]
variable {t : ℕ}

abbrev Extended (W I : Type*) := W ⊕ (I × Fin 3)

def liftRoot (x : I → W) : I → Extended W I := fun i => Sum.inl (x i)

omit [DecidableEq W] [Fintype I] [DecidableEq I] in
/-- The original eleven-edge geometry is preserved on the extended type. -/
theorem fresh_data (σ : Equiv.Perm I) (x y : I → W)
    (hx : ∀ i, x i ≠ x (σ i)) (hy : ∀ i, y i ≠ y (σ i))
    (hxi : Function.Injective fun i => s(x i, x (σ i)))
    (hyi : Function.Injective fun i => s(y i, y (σ i)))
    (hxy : ∀ i j, x i ≠ y j) :
    TransformerData σ (liftRoot x) (liftRoot y) Sum.inr := by
  refine ⟨?_, ?_, ?_, ?_, Sum.inr_injective, ?_, ?_, ?_⟩
  · intro i h
    exact hx i (Sum.inl.inj h)
  · intro i h
    exact hy i (Sum.inl.inj h)
  · intro i j h
    apply hxi
    exact Sym2.map.injective (f := Sum.inl (α := W) (β := I × Fin 3))
      Sum.inl_injective h
  · intro i j h
    apply hyi
    exact Sym2.map.injective (f := Sum.inl (α := W) (β := I × Fin 3))
      Sum.inl_injective h
  · intros; exact Sum.inr_ne_inl
  · intros; exact Sum.inr_ne_inl
  · intro i j h
    exact hxy i j (Sum.inl.inj h)

/-- Produce a partition extending all root parts and both exact typed
decompositions. The template has exactly eleven edges per trail position.
The last identity counts incidences, even when a source vertex is repeated. -/
theorem exists_typed_transformer (F : Finset (Multiset (Fin t)))
    (hF : ThreeStepLinks F) (p : W → Fin t) (σ : Equiv.Perm I) (x y : I → W)
    (hx : ∀ i, x i ≠ x (σ i)) (hy : ∀ i, y i ≠ y (σ i))
    (hxi : Function.Injective fun i => s(x i, x (σ i)))
    (hyi : Function.Injective fun i => s(y i, y (σ i)))
    (hxy : ∀ i j, x i ≠ y j) (hp : ∀ i, p (x i) = p (y i))
    (he : ∀ i, ∃ c, Link F (p (x i)) (p (x (σ i))) c) :
    ∃ p' : Extended W I → Fin t,
      (∀ w, p' (Sum.inl w) = p w) ∧
      IsTransformer (p := p') (F := F)
        (transEdges σ (liftRoot x) (liftRoot y) Sum.inr)
        (srcEdges σ (liftRoot x)) (srcEdges σ (liftRoot y)) ∧
      (transEdges σ (liftRoot x) (liftRoot y) Sum.inr).card = 11 * Fintype.card I ∧
      ∀ z : W, (∀ i, y i ≠ z) →
        incidentLoad (transEdges σ (liftRoot x) (liftRoot y) Sum.inr) (Sum.inl z) =
          4 * (univ.filter fun i => x i = z).card := by
  obtain ⟨a, ha⟩ := exists_auxiliary_types F hF σ (fun i => p (x i)) he
  let p' : Extended W I → Fin t := Sum.elim p a
  have h := fresh_data σ x y hx hy hxi hyi hxy
  refine ⟨p', fun _ => rfl, ?_, h.card_transEdges, ?_⟩
  · exact transformer_typed h p' F hp ha
  · intro z hz
    have hload := h.incidentLoad_eq (Sum.inl z)
      (fun _ => Sum.inr_ne_inl) (fun i hi => hz i (Sum.inl.inj hi))
    simpa only [liftRoot, Sum.inl.injEq] using hload

end PartitionedTriangleAbsorption.TypedTransformer
