/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedWeights

set_option maxHeartbeats 200000

/-! # The supplied finite edge set as a host graph -/

namespace PaddedInputs

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V] {t K : ℕ}

abbrev edgeGraph (J : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (J : Set (Sym2 V))

omit [Fintype V] in
theorem edgeGraph_edges (J : Finset (Sym2 V)) [Fintype (edgeGraph J).edgeSet]
    (hloop : ∀ e ∈ J, ¬ e.IsDiag) :
    (edgeGraph J).edgeFinset = J := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change (s(x, y) ∈ J ∧ x ≠ y) ↔ s(x, y) ∈ J
    exact ⟨fun h => h.1, fun h => ⟨h, by simpa only [Sym2.mk_isDiag_iff] using hloop _ h⟩⟩

theorem edgeGraph_allowed (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V))
    (hallowed : ∀ x y, s(x, y) ∈ J → AllowedPair F (p x) (p y)) :
    ∀ x y, (edgeGraph J).Adj x y → ∃ k, Link F (p x) (p y) k := by
  intro x y hxy
  exact (allowedPair_iff_link F _ _).mp (hallowed x y hxy.1)

theorem guardedSupply_of_padded (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V)) (hloop : ∀ e ∈ J, ¬ e.IsDiag) (ω : ℝ) (D : ℕ)
    (hK : D + 1 ≤ K) (hext : ExtendableT K p F J ω) :
    GuardedSupply p (edgeGraph J) (fun i j => ∃ k, Link F i j k) D
      (ω * Fintype.card V) := by
  apply guardedSupply_of_extendable p F (edgeGraph J) ω D hK
  have hJ : @SimpleGraph.edgeFinset V (edgeGraph J) ((edgeGraph J).fintypeEdgeSet) = J :=
    @edgeGraph_edges V _ J ((edgeGraph J).fintypeEdgeSet) hloop
  simpa only [hJ] using hext

/-- Direct bridge from the exact finite-edge-set hypotheses in `KeevashPaddedSpec`. -/
theorem physical_weights_of_padded (m : ℕ) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (J : Finset (Sym2 V)) (hloop : ∀ e ∈ J, ¬ e.IsDiag) (ω c : ℝ)
    (hω : 0 < ω) (hn : 0 < Fintype.card V) (hq : 3 ≤ qT t m) (hK : qT t m ≤ K)
    (hreg : PaddedRegularT m p F J ω c) (hext : ExtendableT K p F J ω) :
    ∃ φ : Finset V → ℝ,
      (∀ s, IsCopy p F (edgeGraph J) s → ω ^ 2 / Fintype.card V ≤ φ s ∧
        φ s ≤ 27 / (ω * Fintype.card V)) ∧
      ∀ e ∈ J,
        |(∑ s ∈ copies p F (edgeGraph J) with e ∈ triEdges s, φ s) - 1| ≤ c := by
  letI : Fintype (edgeGraph J).edgeSet := (edgeGraph J).fintypeEdgeSet
  have hreg' : PaddedRegularT m p F (edgeGraph J).edgeFinset ω c := by
    simpa only [edgeGraph_edges J hloop] using hreg
  have hext' : ExtendableT K p F (edgeGraph J).edgeFinset ω := by
    simpa only [edgeGraph_edges J hloop] using hext
  simpa only [edgeGraph_edges J hloop] using
    physical_weights_of_regular_extendable m p F hF (edgeGraph J) ω c
      hω hn hq hK hreg' hext'

#print axioms guardedSupply_of_padded
#print axioms physical_weights_of_padded

end PaddedInputs
