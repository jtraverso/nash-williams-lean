/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalBounds

/-!
# Coloured-hub absorbers with a supplied, explicit coefficient budget

This is the existing coloured-hub construction applied to a proved negative
mass bound. The bound is an input, independent of the host and the piece.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.PrivateTemplate
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.OnePart
open PartitionedTriangleAbsorption.TypedLatticePadding
open PartitionedTriangleAbsorption.TypedPaddingProducer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.ColouredHub

variable {t : ℕ}

theorem bounded_lattice_absorber_of_mass (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hF : ThreeStepLinks F) (K B : ℕ) :
    ∀ {W : Type} [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
      P.card ≤ K → (∀ e ∈ P, ¬ e.IsDiag) → (∀ v, Even (incidentLoad P v)) →
      (∃ c : Multiset (Fin t) → ℤ, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧
        negativeMass F c ≤ B) →
      ∃ (c : Multiset (Fin t) → ℤ) (m' : ℕ) (p' : HV (Ext W (Index F c)) m' t → Fin t)
        (A : Finset (Sym2 (HV (Ext W (Index F c)) m' t))),
        (∀ v, p' (Sum.inl (Sum.inl v)) = p v) ∧
        (∀ u v : W, s(Sum.inl (Sum.inl u), Sum.inl (Sum.inl v)) ∉ A) ∧
        Disjoint A (liftOld m' (liftE (T := Index F c) P)) ∧
        HasDecomp p' F A ∧
        HasDecomp p' F (A ∪ liftOld m' (liftE (T := Index F c) P)) ∧
        A.card ≤ 105 * K + 318 * B ∧
        Fintype.card (Index F c × Fin 3) + Fintype.card (HAux m' t) ≤ 34 * K + 105 * B + t ∧
        (∀ v, incidentLoad A (Sum.inl (Sum.inl v)) = 4 * incidentLoad P v) := by
  intro W inst p P hK hloop heven hcoeff
  obtain ⟨c, hc, hmass⟩ := hcoeff
  have hdisj := padding_disjoint_lift (T := Index F c) P
  have hQdec := padding_hasDecomp p (labels F hF3 c) (labels_allowed F hF3 c)
  have hQcard : (padding (W := W) (T := Index F c)).card ≤ 3 * B := by
    rw [padding_size]
    exact Nat.mul_le_mul_left 3 hmass
  have hQold : ∀ w : W, incidentLoad (padding (W := W) (T := Index F c)) (Sum.inl w) = 0 :=
    fun w => padding_avoids_original w
  have hvec := positive_padded_vector F hF3 c p P hc
  set σ := labels F hF3 c
  set Q := padding (W := W) (T := Index F c) with hQdef
  set P' := liftE (T := Index F c) P ∪ Q with hP'def
  have hvec' : edgeVec (extPart p σ) P' =
      ∑ τ ∈ F, (((c τ).toNat : ℕ) : ℤ) • typeEdgeVec τ := by
    rw [hvec]
    refine sum_congr rfl fun τ _ => ?_
    rw [Int.toNat_eq_max]
  obtain ⟨p', A', hp', -, hnoold, hdis', hA', hA'P, hcardA', hcardAux, hdeg', -⟩ :=
    exists_colouredHubAbsorber (extPart p σ) F hF3 hF P' (padded_loopless P hloop hQdec)
      (padded_even P heven hQdec) (fun τ => (c τ).toNat) hvec'
  have hliftU : liftOld (t := t) P'.card P' =
      liftOld P'.card (liftE (T := Index F c) P) ∪ liftOld P'.card Q := by
    simp only [liftOld, hP'def, image_union]
  have hQlift : HasDecomp p' F (liftOld (t := t) P'.card Q) :=
    hasDecomp_image_typed Sum.inl Sum.inl_injective hp' Q hQdec
  have hPQ : Disjoint (liftOld (t := t) P'.card (liftE (T := Index F c) P)) (liftOld P'.card Q) :=
    (disjoint_image (Sym2.map.injective Sum.inl_injective)).mpr hdisj
  have hdisU : Disjoint A' (liftOld P'.card (liftE (T := Index F c) P) ∪ liftOld P'.card Q) :=
    hliftU ▸ hdis'
  have hA'PU : HasDecomp p' F
      (A' ∪ (liftOld P'.card (liftE (T := Index F c) P) ∪ liftOld P'.card Q)) :=
    hliftU ▸ hA'P
  obtain ⟨hfin1, hfin2, hfin3⟩ := absorber_of_padding hPQ hQlift hdisU hA' hA'PU
  have hQeq : Q.card = 3 * Fintype.card (Index F c) := padding_card
  have hm' : P'.card = P.card + Q.card := by
    rw [hP'def, card_union_of_disjoint (padding_disjoint_lift P), liftE,
      card_image_of_injective _ (Sym2.map.injective Sum.inl_injective)]
  have hQold' : ∀ u : W, ∀ e ∈ Q, (Sum.inl u : Ext W (Index F c)) ∉ e := by
    intro u e he hu
    have h0 := hQold u
    unfold incidentLoad at h0
    rw [card_eq_zero, filter_eq_empty_iff] at h0
    exact h0 he hu
  refine ⟨c, P'.card, p', A' ∪ liftOld P'.card Q, fun v => hp' (Sum.inl v), ?_, hfin1, hfin2, hfin3,
    ?_, ?_, fun v => ?_⟩
  · intro u v h
    rcases mem_union.mp h with h | h
    · exact hnoold _ _ h
    · obtain ⟨e, he, hee⟩ := mem_image.mp h
      have : e = s(Sum.inl u, Sum.inl v) :=
        Sym2.map.injective Sum.inl_injective (by simpa using hee)
      subst this
      exact hQold' u _ he (Sym2.mem_mk_left _ _)
  · have hQc : Q.card ≤ 3 * B := hQcard
    have h1 := card_union_le A' (liftOld (t := t) P'.card Q)
    have h2 : (liftOld (t := t) P'.card Q).card ≤ Q.card := card_image_le
    omega
  · have hQc : Q.card ≤ 3 * B := hQcard
    rw [Fintype.card_prod, Fintype.card_fin, card_hAux]
    omega
  · have hd : Disjoint A' (liftOld (t := t) P'.card Q) := hdisU.mono_right subset_union_right
    rw [incidentLoad_union hd, hdeg', liftOld,
      incidentLoad_image_apply Sum.inl Sum.inl_injective, hP'def,
      incidentLoad_union (padding_disjoint_lift P), liftE,
      incidentLoad_image_apply Sum.inl Sum.inl_injective, hQold v]
    ring


#print axioms bounded_lattice_absorber_of_mass

end PaddedF12
