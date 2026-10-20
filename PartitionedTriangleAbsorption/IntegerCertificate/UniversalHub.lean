/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Assembly

/-! # Task 1: the physical universal-hub certificate

Five pairwise adjacent hubs `A0, A1, A2 ∈ V₀`, `C0, C1 ∈ V₁` (`Hubs.Good`), with every
vertex of the source `P` attached to the frame (`InW`: a vertex of `V₀` is adjacent to
`A0, C0, C1`, a vertex of `V₁` to `A0, A1, C0`). Then every physical F0-divisible source
`P ⊆ E(G)` has a signed physical integer certificate of weight `≤ 27|P|`.

This replaces the requested six-universal-hub statement by a stronger explicit one: the sixth
hub `C2` is never used, `A2` need not be adjacent to `V(P)`, and each source vertex needs only
three hub neighbours. The six-hub hypothesis of the Stage 61 note implies it. The weight bound
`27|P|` is below the contract `1100|P|`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin 2} {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem not_isDiag_of_subset [Fintype V] [DecidableRel G.Adj] {P : Finset (Sym2 V)}
    (hPG : P ⊆ G.edgeFinset) : ∀ e ∈ P, ¬ e.IsDiag := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
  have hab : G.Adj a b := by simpa using hPG he
  simpa using hab.ne

omit [Fintype V] in
theorem exists_mem_of_deg_pos {P : Finset (Sym2 V)} {y : V} (h : 0 < deg P y) :
    ∃ e ∈ P, y ∈ e := by
  obtain ⟨e, he⟩ := card_pos.mp h
  exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩

/-- Sum over the two endpoints of an edge. -/
theorem sum_filter_mem_mk {a b : V} (hab : a ≠ b) (D : V → Sym2 V → ℤ) :
    ∑ y ∈ univ.filter (· ∈ s(a, b)), D y = D a + D b := by
  rw [filter_mem_mk, sum_pair hab]

/-- **Universal-hub certificate (Task 1, explicit replacement).** -/
theorem universal_hub_certificate [DecidableRel G.Adj] (H : Hubs V) (hH : H.Good p G)
    {P : Finset (Sym2 V)} (hPG : P ⊆ G.edgeFinset) (hdiv : IsIntDiv p F0 P)
    (hattach : ∀ e ∈ P, ∀ y ∈ e, InW p G H y) :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
      IsSignedCert p G P t c ∧ certWeight c ≤ 27 * P.card := by
  have hP := not_isDiag_of_subset hPG
  have hE : ∀ e ∈ P, HubReduces p G H
      (edgeOf e + ∑ y ∈ univ.filter (· ∈ e), spoke p H y) 3 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
    have huv : G.Adj u v := by simpa using hPG he
    rw [sum_filter_mem_mk huv.ne, ← add_assoc]
    exact hubReduces_edge hH (hattach _ he u (Sym2.mem_mk_left u v))
      (hattach _ he v (Sym2.mem_mk_right u v)) huv
  have hV : ∀ y, 0 < deg P y → HubReduces p G H (2 • spoke p H y) 3 1 := by
    intro y hy
    obtain ⟨e, he, hye⟩ := exists_mem_of_deg_pos hy
    exact hubReduces_double_spoke hH (hattach e he y hye)
  exact (signedCert_of_reductions hH hP hdiv _ hE hV).mono (le_of_eq (by ring))
    |>.signedCert

end PartitionedTriangleAbsorption.IntegerCertificate
