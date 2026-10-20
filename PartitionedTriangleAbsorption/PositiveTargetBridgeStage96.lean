/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TargetTripleSelectionStage95

/-! # Bridging the padded integer coefficients to target token slots

Stage90 retains integer coefficients max(c,0). Stage95 indexes slots by
natural multiplicities. This bridge discharges that conversion rather than
requiring a second representation as a new hypothesis.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PositiveTargetBridgeStage96

open Finset ColouredHub TargetTripleSelectionStage95 CatalystInsertionStage89

variable {t : ℕ} {V : Type*}

theorem natural_positive_vector (p : V → Fin t) (Y : Finset (Sym2 V))
    (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ)
    (hvec : edgeVec p Y = ∑ τ ∈ F, max (c τ) 0 • typeEdgeVec τ) :
    edgeVec p Y = ∑ τ ∈ F, ((c τ).toNat : ℤ) • typeEdgeVec τ := by
  have hcast (τ : Multiset (Fin t)) : ((c τ).toNat : ℤ) = max (c τ) 0 := by omega
  simp_rw [hcast]
  exact hvec

theorem exists_padded_assignment (p : V → Fin t) (Y : Finset (Sym2 V))
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (c : Multiset (Fin t) → ℤ)
    (hvec : edgeVec p Y = ∑ τ ∈ F, max (c τ) 0 • typeEdgeVec τ) :
    ∃ f : Slots F (fun τ => (c τ).toNat) ≃ Y, ∀ x a,
      Sym2.map p (f (x,a)).val = slotPair (triWord F hF (fun τ => (c τ).toNat)) (x,a) :=
  exists_assignment p Y F hF _ (natural_positive_vector p Y F c hvec)

variable [Fintype V] [DecidableEq V]

/-- The exact max(c,0) representation produced by padding supplies the
current physical token assignment; no separate natural coefficient witness. -/
theorem exists_inserted_padded_assignment
    {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)}
    {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}
    {U : Finset (Sym2 V)} {Z : Finset V}
    (fr : Frame p F G B S Z₀) (inv : Inv p F G B S Z₀ cz cz' S.A U Z)
    (hF : ∀ τ ∈ F, τ.card = 3) (c : Multiset (Fin t) → ℤ)
    (hvec : edgeVec p S.Y = ∑ τ ∈ F, max (c τ) 0 • typeEdgeVec τ) :
    ∃ f : Slots F (fun τ => (c τ).toNat) ≃ S.Y,
      (∀ x a, Sym2.map p (S.curY cz cz' S.A (f (x,a)).val) =
        slotPair (triWord F hF (fun τ => (c τ).toNat)) (x,a)) ∧
      Function.Injective (fun z => S.curY cz cz' S.A (f z).val) ∧
      univ.image (fun z => S.curY cz cz' S.A (f z).val) =
        S.Y.image (S.curY cz cz' S.A) :=
  exists_inserted_assignment fr inv hF _ (natural_positive_vector p S.Y F c hvec)

end PartitionedTriangleAbsorption.PositiveTargetBridgeStage96
