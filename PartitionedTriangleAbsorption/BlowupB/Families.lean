/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Uniform
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # BlowupB.Families — the Nash–Williams families F₀–F₃

Instances of `isIntDiv_iff_physDiv_uniform` for the four families of the paper
(`TypedApplicationLinks.F0 … F3`), and the `F₃` instance in the language of the four-class host
of `ClassCertificate` (`G.Adj a b ↔ cls a ≠ cls b`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0 F1 F2 F3)

theorem card_F0 : ∀ τ ∈ F0, Multiset.card τ = 3 := by decide
theorem card_F1 : ∀ τ ∈ F1, Multiset.card τ = 3 := by decide
theorem card_F2 : ∀ τ ∈ F2, Multiset.card τ = 3 := by decide
theorem card_F3 : ∀ τ ∈ F3, Multiset.card τ = 3 := by decide

theorem allowedPair_F3_iff : ∀ i j : Fin 4, AllowedPair F3 i j ↔ i ≠ j := by
  unfold AllowedPair
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {E : Finset (Sym2 V)}

theorem isIntDiv_iff_physDiv_F0 {p : V → Fin 2} (hG : IsCompleteBlowup p F0 G) (R : Reps p 5)
    (hE : E ⊆ G.edgeFinset) : IsIntDiv p F0 E ↔ PhysDiv p F0 G E :=
  isIntDiv_iff_physDiv_uniform hG card_F0 R hE

theorem isIntDiv_iff_physDiv_F1 {p : V → Fin 4} (hG : IsCompleteBlowup p F1 G) (R : Reps p 5)
    (hE : E ⊆ G.edgeFinset) : IsIntDiv p F1 E ↔ PhysDiv p F1 G E :=
  isIntDiv_iff_physDiv_uniform hG card_F1 R hE

theorem isIntDiv_iff_physDiv_F2 {p : V → Fin 4} (hG : IsCompleteBlowup p F2 G) (R : Reps p 5)
    (hE : E ⊆ G.edgeFinset) : IsIntDiv p F2 E ↔ PhysDiv p F2 G E :=
  isIntDiv_iff_physDiv_uniform hG card_F2 R hE

theorem isIntDiv_iff_physDiv_F3 {p : V → Fin 4} (hG : IsCompleteBlowup p F3 G) (R : Reps p 5)
    (hE : E ⊆ G.edgeFinset) : IsIntDiv p F3 E ↔ PhysDiv p F3 G E :=
  isIntDiv_iff_physDiv_uniform hG card_F3 R hE

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The four-class host `G.Adj a b ↔ cls a ≠ cls b` is the complete `F₃`-blowup. -/
theorem isCompleteBlowup_F3_of_cls {cls : V → Fin 4} (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) :
    IsCompleteBlowup cls F3 G := by
  intro u v
  rw [hG, allowedPair_F3_iff]
  constructor
  · intro h; exact ⟨fun e => h (by rw [e]), h⟩
  · intro h; exact h.2

/-- **F₃ on the four-class host.** With at least `5` vertices per class, an edge set of the
four-class host is integrally `F₃`-divisible iff it is in the physical lattice of the copies. -/
theorem isIntDiv_iff_physDiv_F3_cls {cls : V → Fin 4} (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    (R : Reps cls 5) (hE : E ⊆ G.edgeFinset) : IsIntDiv cls F3 E ↔ PhysDiv cls F3 G E :=
  isIntDiv_iff_physDiv_F3 (isCompleteBlowup_F3_of_cls hG) R hE

end PartitionedTriangleAbsorption.BlowupB
