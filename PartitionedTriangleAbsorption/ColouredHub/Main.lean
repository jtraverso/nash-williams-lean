/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Counts

/-! # The coloured-hub private absorber

**Producer.** For a family `F` of size-three multisets with `ThreeStepLinks F`, and a finite
loopless piece `P` with even degrees whose ordered edge vector is a **nonnegative integer**
combination `∑ τ ∈ F, c τ • typeEdgeVec τ`, there is an edge set `A` on the explicit vertex
type `V ⊕ ((Fin |P| × Tag) ⊕ Fin t)` and an extension `p'` of the partition such that:

1. no edge of `A` joins two original vertices (so `A` is disjoint from the copy of `P`);
2. `A` and `A ∪ P` have exact `F`-decompositions;
3. `|A| = 105 |P|`;
4. there are exactly `34 |P| + t` new vertices (`34` tagged per edge of `P`, one hub per part);
5. every original vertex has `d_A(v) = 4 d_P(v)`;

and `A = ∅` when `P = ∅`. Every hub `r` lies in part `r`.

This is an abstract private absorber: nothing is asserted about embedding it into a host graph.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer AntiEdgeSelection

variable {t : ℕ}

/-- The copy of a piece on the original vertices of the template. -/
def liftOld {V : Type*} [DecidableEq V] (m : ℕ) (P : Finset (Sym2 V)) :
    Finset (Sym2 (HV V m t)) :=
  P.image (Sym2.map Sum.inl)

theorem liftOld_eq_blkP {V : Type*} [DecidableEq V] {P : Finset (Sym2 V)} {m : ℕ}
    {σ : Equiv.Perm (Fin m)} {X : Fin m → V} (hX : IsTrailSystem P σ X) :
    liftOld (t := t) m P = blkP σ X := by
  ext e
  simp only [liftOld, mem_image, blkP, mem_posEdges]
  constructor
  · rintro ⟨e', he', rfl⟩
    obtain ⟨i, rfl⟩ := (hX.mem e').mp he'
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨s(X i, X (σ i)), (hX.mem _).mpr ⟨i, rfl⟩, rfl⟩

/-- **The coloured-hub private absorber exists** for every even loopless piece with
nonnegative integer global type coefficients. -/
theorem exists_colouredHubAbsorber {V : Type*} [DecidableEq V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hF3 : ∀ τ ∈ F, Multiset.card τ = 3)
    (hF : ThreeStepLinks F) (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad P v)) (c : Multiset (Fin t) → ℕ)
    (hc : edgeVec p P = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ) :
    ∃ (p' : HV V P.card t → Fin t) (A : Finset (Sym2 (HV V P.card t))),
      (∀ v, p' (Sum.inl v) = p v) ∧
      (∀ r, p' (Sum.inr (Sum.inr r)) = r) ∧
      (∀ u v : V, s(Sum.inl u, Sum.inl v) ∉ A) ∧
      Disjoint A (liftOld P.card P) ∧
      HasDecomp p' F A ∧
      HasDecomp p' F (A ∪ liftOld P.card P) ∧
      A.card = 105 * P.card ∧
      Fintype.card (HAux P.card t) = 34 * P.card + t ∧
      (∀ v, incidentLoad A (Sum.inl v) = 4 * incidentLoad P v) ∧
      (P = ∅ → A = ∅) := by
  classical
  obtain ⟨σ, X, hX⟩ := exists_trailSystem P hloop heven
  set w := triWord F hF3 c with hw_def
  have hvec : vecOf (fun i => s(p (X i), p (X (σ i)))) = vecOf (slotPair w) := by
    rw [← edgeVec_eq_vecOf hX, hc, hw_def, vecOf_slotPair]
  obtain ⟨π, hπ⟩ := exists_fibre_equiv hvec
  have hM : Matched p σ X w π := by
    intro i
    rw [pq_qPerm]
    exact hπ i
  have hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F := triWord_mem F hF3 c
  -- auxiliary types for `T_P`
  obtain ⟨aP, haP⟩ := exists_auxiliary_types F hF (blowPerm σ)
    (fourPath (rP p X) (sP p σ X) (cP w π) (rP p X)) (by
      rintro ⟨i, k⟩
      have L := link_of_mem (matched_mem hw hM i)
      fin_cases k
      · exact ⟨_, L.1⟩
      · exact ⟨_, L.2.1⟩
      · exact ⟨_, L.2.2.1⟩
      · exact ⟨_, L.1⟩)
  -- auxiliary types for `T_Q`
  obtain ⟨aQ, haQ⟩ := exists_auxiliary_types F hF (blowPerm (qPerm π))
    (fourPath (pq w π) (fun i => pq w π (qPerm π i)) (cP w π) (pq w π)) (by
      rintro ⟨i, k⟩
      have L := link_of_mem (pq_mem hw π i)
      fin_cases k
      · exact ⟨_, L.1⟩
      · exact ⟨_, L.2.1⟩
      · exact ⟨_, L.2.2.1⟩
      · exact ⟨_, L.1⟩)
  set p' := hpart p σ X w π aP aQ with hp'
  have eP : (fun z => p' (pathP X z)) = fourPath (rP p X) (sP p σ X) (cP w π) (rP p X) := by
    funext z
    obtain ⟨i, k⟩ := z
    fin_cases k <;> rfl
  have eQ : (fun z => p' (pathQ z)) =
      fourPath (pq w π) (fun i => pq w π (qPerm π i)) (cP w π) (pq w π) := by
    funext z
    obtain ⟨i, k⟩ := z
    fin_cases k <;> rfl
  have haP' : AuxiliaryTypes F (blowPerm σ) (fun z => p' (pathP X z))
      (fun z => p' (auxTP z)) := by
    rw [eP]; exact haP
  have haQ' : AuxiliaryTypes F (blowPerm (qPerm π)) (fun z => p' (pathQ z))
      (fun z => p' (auxTQ z)) := by
    rw [eQ]; exact haQ
  have hlift := liftOld_eq_blkP (t := t) hX
  have hcard := card_hubTemplate hX.ne hM
  refine ⟨p', hubTemplate p σ X w π, fun _ => rfl, fun _ => rfl,
    hubTemplate_no_old_edge p σ X w π, ?_, hasDecomp_hubTemplate hX.ne hw hM haP' haQ',
    ?_, hcard, card_hAux _ _, fun v => ?_, fun h0 => ?_⟩
  · rw [hlift]; exact disjoint_hubTemplate_P p σ X w π
  · rw [hlift]; exact hasDecomp_hubTemplate_union hX.ne hX.inj hw hM haP' haQ'
  · rw [incidentLoad_hubTemplate_old hX.ne v, ← hX.two_mul_card_tail v]
    ring
  · rw [← Finset.card_eq_zero, hcard, h0, card_empty]

end PartitionedTriangleAbsorption.ColouredHub
