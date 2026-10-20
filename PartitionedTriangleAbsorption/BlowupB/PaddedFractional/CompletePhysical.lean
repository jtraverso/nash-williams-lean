/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompleteModes
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.LinkModes
public import PartitionedTriangleAbsorption.TypedPieceConditions

@[expose] public section

/-!
# Physical ternary weights in the complete graph of allowed pairs
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer

variable {V : Type*} {t : ℕ}

def activeCompleteGraph (p : V → Fin t) (F : Finset (Multiset (Fin t))) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ k, Link F (p a) (p b) k
  symm := ⟨by
    intro a b h
    obtain ⟨hab, k, hk⟩ := h
    exact ⟨hab.symm, k, (link_root_swap F _ _ _).mp hk⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance activeCompleteGraph_decidable [DecidableEq V]
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    DecidableRel (activeCompleteGraph p F).Adj := by
  intro a b
  change Decidable (a ≠ b ∧ ∃ k, Link F (p a) (p b) k)
  unfold Link
  infer_instance

def AdmissibleTriple (p : V → Fin t) (F : Finset (Multiset (Fin t))) (a b c : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Link F (p a) (p b) (p c)

def TernarySymmetric (w : V → V → V → ℝ) : Prop :=
  (∀ a b c, w a b c = w b a c) ∧ (∀ a b c, w a b c = w a c b)

def TernarySupported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (w : V → V → V → ℝ) : Prop :=
  ∀ a b c, ¬ AdmissibleTriple p F a b c → w a b c = 0

def ternaryLoad [Fintype V] (w : V → V → V → ℝ) (a b : V) : ℝ := ∑ c, w a b c

theorem TernarySymmetric.rotate {w : V → V → V → ℝ} (h : TernarySymmetric w)
    (a b c : V) : w a b c = w b c a := by
  rw [h.1 a b c, h.2 b a c]

theorem TernarySupported.diag {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {w : V → V → V → ℝ} (h : TernarySupported p F w) (a b : V) : w a a b = 0 :=
  h a a b (fun h' => h'.1 rfl)

theorem TernarySupported.load_diag [Fintype V] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} {w : V → V → V → ℝ}
    (h : TernarySupported p F w) (a : V) : ternaryLoad w a a = 0 := by
  unfold ternaryLoad
  exact sum_eq_zero fun b _ => h.diag a b

theorem ternaryLoad_add [Fintype V] (w w' : V → V → V → ℝ) (a b : V) :
    ternaryLoad (fun a b c => w a b c + w' a b c) a b =
      ternaryLoad w a b + ternaryLoad w' a b := by
  simp only [ternaryLoad, sum_add_distrib]

#print axioms activeCompleteGraph
#print axioms TernarySupported.load_diag

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
