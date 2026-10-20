/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveExistence
public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer

@[expose] public section

/-!
# A physical decomposable reserve from the effective typed nibble

This adapter enumerates an existing decomposition as a triangle system. It
then selects whole blocks using the simultaneous reserve theorem. In
particular, the original and selected decompositions are physical families
of three-element vertex sets, and their edge sets are actual subsets of
the input host.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking

open Finset Nibble TypedNibble TypedEffectiveConsumer KeevashQuantitative

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The finite blocks of a supplied decomposition, enumerated bijectively. -/
noncomputable def decompositionSystem (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D) :
    TriSystem V D.card where
  tri i := (D.equivFin.symm i).val
  card_tri i := (hD.1 _ (D.equivFin.symm i).property).1
  tri_inj := Subtype.val_injective.comp D.equivFin.symm.injective

theorem decompositionSystem_typed (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (i : Fin D.card) : IsTypedTri p F ((decompositionSystem p F Q D hD).tri i) :=
  hD.1 _ (D.equivFin.symm i).property

theorem decompositionSystem_packing (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D) :
    IsPacking (decompositionSystem p F Q D hD) univ := by
  intro i _ j _ hij
  exact hD.2.1 (D.equivFin.symm i).property (D.equivFin.symm j).property
    (fun h => hij ((decompositionSystem p F Q D hD).tri_inj h))

theorem decompositionSystem_edges (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D) :
    edgesOf (decompositionSystem p F Q D hD) univ = Q := by
  conv_rhs => rw [← hD.2.2]
  ext edge
  constructor
  · intro he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨_, (D.equivFin.symm i).property, hi⟩
  · intro he
    obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
    refine mem_biUnion.mpr ⟨D.equivFin ⟨T, hT⟩, mem_univ _, ?_⟩
    simpa only [decompositionSystem, Equiv.symm_apply_apply, nibble_triEdges_eq] using heT

variable [Fintype V]

/-- Extract a decomposable reserve from a decomposable subgraph with small
uncovered degree. No indexing or probabilistic hypotheses remain. -/
theorem exists_reserve_of_decomposition (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (ht : t ≤ 4)
    (J : SimpleGraph V) [DecidableRel J.Adj] (Q : Finset (Sym2 V))
    (hQ : Q ⊆ J.edgeFinset) (hdec : HasDecomp p F Q)
    (ρ ω : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : (2 : ℝ) ^ 27 * ρ⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ Fintype.card V)
    (hanti : AntiEdgeful p F J ω)
    (hleft : DegBounded (J.edgeFinset \ Q) (ω * Fintype.card V / 8)) :
    ∃ X : Finset (Sym2 V), X ⊆ J.edgeFinset ∧ HasDecomp p F X ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      AntiEdgeful p F (ReserveCoverDown.reserveGraph X) (ρ ^ 2 * ω / 12) := by
  classical
  obtain ⟨D, hD⟩ := hdec
  let S := decompositionSystem p F Q D hD
  have hSQ : edgesOf S univ = Q := decompositionSystem_edges p F Q D hD
  have hnR : (0 : ℝ) < Fintype.card V := lt_of_lt_of_le (by positivity) hlarge
  have hn : 0 < Fintype.card V := by exact_mod_cast hnR
  have hhost : ∀ i, Nibble.triEdges (S.tri i) ⊆ J.edgeFinset := by
    intro i edge he
    apply hQ
    rw [← hSQ]
    exact mem_biUnion.mpr ⟨i, mem_univ _, he⟩
  exact exists_reserve_of_system S (decompositionSystem_packing p F Q D hD) p F ht J
    (decompositionSystem_typed p F Q D hD) hhost ρ ω hρ hρ1 hω hω1 hn hlarge hanti
    (by simpa only [hSQ] using hleft)

/-- The effective near-load nibble followed by whole-block reserve selection.
All numerical thresholds are explicit and chosen before the vertex type. -/
theorem exists_decomposable_reserve_effective (b ρ ω : ℝ)
    (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (V : Type) [Fintype V] [DecidableEq V]
    (hlarge : (2 : ℝ) ^ 27 * ρ⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ Fintype.card V)
    (hnibble : packingThreshold b (min (ω / 8) (min 1 (ω ^ 2))) ≤ Fintype.card V)
    (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t))) (ht : t ≤ 4)
    (J : SimpleGraph V) [DecidableRel J.Adj] (φ : Finset V → ℝ)
    (hanti : AntiEdgeful p F J ω)
    (hw : ∀ T, IsCopy p F J T → 0 ≤ φ T ∧ φ T ≤ b / Fintype.card V)
    (hcap : DegBounded J.edgeFinset ((1 - ω) * Fintype.card V))
    (hload : ∀ e ∈ J.edgeFinset,
      |(∑ T ∈ copies p F J with e ∈ PartitionedTriangleAbsorption.triEdges T, φ T) - 1| ≤
        loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))) :
    ∃ X : Finset (Sym2 V), X ⊆ J.edgeFinset ∧ HasDecomp p F X ∧
      DegBounded X (2 * ρ * Fintype.card V) ∧
      AntiEdgeful p F (ReserveCoverDown.reserveGraph X) (ρ ^ 2 * ω / 12) := by
  obtain ⟨D, Q, _, _, hQ, _, hdec, hleft⟩ :=
    typed_nibble_packing_near_effective b (ω / 8) ω hb (by positivity) hω
      V hnibble t p F J φ hw hcap hload
  exact exists_reserve_of_decomposition p F ht J Q hQ hdec ρ ω hρ hρ1 hω hω1
    hlarge hanti (by simpa only [div_mul_eq_mul_div] using hleft)

#print axioms decompositionSystem_packing
#print axioms decompositionSystem_edges
#print axioms exists_reserve_of_decomposition
#print axioms exists_decomposable_reserve_effective

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
