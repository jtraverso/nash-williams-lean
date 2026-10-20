/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.Transformer
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Auxiliary types for the eleven-edge transformer

The finite link tests below produce auxiliary parts for F0--F3. They do not
construct a universal refiner or an embedding in a prescribed host graph.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedTransformer

open Finset PrivateTemplate TypedApplicationLinks

variable {t : ℕ}

/-- A link edge records an allowed triangle, retaining repeated parts. -/
def Link (F : Finset (Multiset (Fin t))) (r a b : Fin t) : Prop :=
  ({r, a, b} : Multiset (Fin t)) ∈ F

/-- The length-three walks required by the eleven-edge transformer. -/
def ThreeStepLinks (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ r a b, (∃ c, Link F r a c) → (∃ c, Link F r b c) →
    ∃ v w, Link F r a v ∧ Link F r v w ∧ Link F r w b

theorem link_swap (F : Finset (Multiset (Fin t))) (r a b : Fin t) :
    Link F r a b ↔ Link F r b a := by
  change (r ::ₘ a ::ₘ b ::ₘ 0) ∈ F ↔ (r ::ₘ b ::ₘ a ::ₘ 0) ∈ F
  rw [Multiset.cons_swap a b]

theorem link_root_swap (F : Finset (Multiset (Fin t))) (r a b : Fin t) :
    Link F r a b ↔ Link F a r b := by
  simp only [Link, Multiset.insert_eq_cons, Multiset.cons_swap r a]

theorem F0_three_step : ThreeStepLinks F0 := by
  unfold ThreeStepLinks Link
  decide

theorem F1_three_step : ThreeStepLinks F1 := by
  unfold ThreeStepLinks Link
  decide

theorem F2_three_step : ThreeStepLinks F2 := by
  unfold ThreeStepLinks Link
  decide

theorem F3_three_step : ThreeStepLinks F3 := by
  unfold ThreeStepLinks Link
  decide

/-- All four source-mode triangles have allowed parts. Target mode uses the
same predicate when the corresponding source and target parts agree. -/
def AuxiliaryTypes {I : Type*} (F : Finset (Multiset (Fin t)))
    (σ : Equiv.Perm I) (r : I → Fin t) (a : I × Fin 3 → Fin t) : Prop :=
  ∀ i, Link F (r i) (r (σ i)) (a (σ i, 0)) ∧
    Link F (r i) (a (i, 1)) (a (i, 2)) ∧
    Link F (r i) (a (i, 0)) (a (i, 1)) ∧
    Link F (r i) (a (i, 2)) (a (σ i, 0))

/-- Construct auxiliary parts for arbitrary trail data, not only finite test
instances. Each consecutive pair must occur in an allowed triangle type. -/
theorem exists_auxiliary_types {I : Type*} (F : Finset (Multiset (Fin t)))
    (hF : ThreeStepLinks F) (σ : Equiv.Perm I) (r : I → Fin t)
    (he : ∀ i, ∃ c, Link F (r i) (r (σ i)) c) :
    ∃ a : I × Fin 3 → Fin t, AuxiliaryTypes F σ r a := by
  classical
  choose c hc using he
  let u : I → Fin t := fun i => c (σ.symm i)
  have hu : ∀ i, Link F (r i) (r (σ i)) (u (σ i)) := by
    intro i
    simpa [u] using hc i
  have hleft : ∀ i, ∃ k, Link F (r i) (u i) k := by
    intro i
    refine ⟨r (σ.symm i), ?_⟩
    apply (link_swap F _ _ _).mp
    apply (link_root_swap F _ _ _).mp
    simpa [u] using hc (σ.symm i)
  have hright : ∀ i, ∃ k, Link F (r i) (u (σ i)) k := by
    intro i
    exact ⟨r (σ i), (link_swap F _ _ _).mp (hu i)⟩
  have hb := fun i => hF (r i) (u i) (u (σ i)) (hleft i) (hright i)
  choose v w hw using hb
  refine ⟨fun z => ![u z.1, v z.1, w z.1] z.2, ?_⟩
  intro i
  exact ⟨hu i, (hw i).2.1, (hw i).1, (hw i).2.2⟩

variable {W : Type*} [DecidableEq W] {I : Type*} [Fintype I]

/-- Reuse the geometry of `GoodLabels`, adding only its typed condition. -/
theorem goodLabels_typed {ta tb tc : I → W} (h : GoodLabels ta tb tc)
    (p : W → Fin t) (F : Finset (Multiset (Fin t)))
    (ht : ∀ i, Link F (p (ta i)) (p (tb i)) (p (tc i))) :
    IsDecomp p F (labelEdges ta tb tc) (labelTris ta tb tc) := by
  refine ⟨?_, h.isDecomp.2⟩
  intro s hs
  obtain ⟨i, -, rfl⟩ := mem_image.mp hs
  refine ⟨card_three (h.hab i) (h.hac i) (h.hbc i), ?_⟩
  rw [map_three p (h.hab i) (h.hac i) (h.hbc i)]
  exact ht i

/-- Both exact typed decompositions on the same eleven-edge template. -/
theorem transformer_typed {σ : Equiv.Perm I} {x y : I → W} {a : I × Fin 3 → W}
    (h : TransformerData σ x y a) (p : W → Fin t)
    (F : Finset (Multiset (Fin t))) (hxy : ∀ i, p (x i) = p (y i))
    (ht : AuxiliaryTypes F σ (fun i => p (x i)) (fun z => p (a z))) :
    IsTransformer (p := p) (F := F)
      (transEdges σ x y a) (srcEdges σ x) (srcEdges σ y) := by
  have hs : HasDecomp p F (transEdges σ x y a ∪ srcEdges σ x) := by
    rw [← labelEdges_transformer]
    refine ⟨_, goodLabels_typed h.goodLabels p F ?_⟩
    rintro ⟨k, i⟩
    cases k
    · exact (ht i).1
    · exact (ht i).2.1
    · simpa only [triA, triB, triC, ← hxy i] using (ht i).2.2.1
    · simpa only [triA, triB, triC, ← hxy i] using (ht i).2.2.2
  have htgt : HasDecomp p F (transEdges σ x y a ∪ srcEdges σ y) := by
    rw [transEdges_comm, ← labelEdges_transformer]
    refine ⟨_, goodLabels_typed h.swap.goodLabels p F ?_⟩
    rintro ⟨k, i⟩
    cases k
    · simpa only [triA, triB, triC, ← hxy i, ← hxy (σ i)] using (ht i).1
    · simpa only [triA, triB, triC, ← hxy i] using (ht i).2.1
    · exact (ht i).2.2.1
    · exact (ht i).2.2.2
  exact ⟨disjoint_union_right.mpr ⟨h.disjoint_source, h.disjoint_target⟩, hs, htgt⟩

end PartitionedTriangleAbsorption.TypedTransformer
