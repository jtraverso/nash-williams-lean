/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalMovesStage86

/-! # The finite three-move exchange skeleton

Six roots are x1,x2,a,b,c,d. Positions 6 and 7 are the two new carriers;
8--13 are six gadget auxiliaries. This verifies the complete edge history of
the exchange. Embedding this skeleton into a supplied host is still separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairExchangeStage86

open Finset PhysicalHingeSupply PairMoveStage85 PhysicalMovesStage86

def first : Fin 6 ↪ Fin 14 := ⟨![0, 6, 2, 3, 8, 9], by decide⟩
def second : Fin 6 ↪ Fin 14 := ⟨![1, 6, 4, 5, 10, 11], by decide⟩
def third : Fin 6 ↪ Fin 14 := ⟨![6, 7, 3, 5, 12, 13], by decide⟩

def Q₁ := source.map (edgeEmb first)
def Q₂ := source.map (edgeEmb second)
def Q₃ := source.map (edgeEmb third)
def R₁ := target.map (edgeEmb first)
def R₂ := target.map (edgeEmb second)
def R₃ := target.map (edgeEmb third)
def H₁ := gadget.map (edgeEmb first)
def H₂ := gadget.map (edgeEmb second)
def H₃ := gadget.map (edgeEmb third)

def initial := Q₁ ∪ Q₂
def final : Finset (Sym2 (Fin 14)) := {s(6, 2), s(6, 4), s(7, 3), s(7, 5)}
def added := H₁ ∪ R₁ ∪ H₂ ∪ R₂ ∪ H₃ ∪ R₃
def host := initial ∪ added
def X₁ := (initial \ Q₁) ∪ R₁
def U₁ := initial ∪ H₁ ∪ R₁
def X₂ := (X₁ \ Q₂) ∪ R₂
def U₂ := U₁ ∪ H₂ ∪ R₂

theorem history_checks :
    Q₁ ⊆ initial ∧ Q₂ ⊆ X₁ ∧ Q₃ ⊆ X₂ ∧
    X₁ ⊆ U₁ ∧ X₂ ⊆ U₂ ∧ (X₂ \ Q₃) ∪ R₃ = final ∧
    Disjoint (H₁ ∪ R₁) initial ∧ Disjoint (H₂ ∪ R₂) U₁ ∧
    Disjoint (H₃ ∪ R₃) U₂ := by
  unfold Q₁ Q₂ Q₃ R₁ R₂ R₃ H₁ H₂ H₃ initial final X₁ X₂ U₁ U₂
    source target gadget first second third edgeEmb
  decide

theorem cardinal_checks :
    initial.card = 4 ∧ final.card = 4 ∧ added.card = 27 ∧
    H₁.card = 7 ∧ H₂.card = 7 ∧ H₃.card = 7 ∧
    R₁.card = 2 ∧ R₂.card = 2 ∧ R₃.card = 2 := by
  unfold initial final added Q₁ Q₂ R₁ R₂ R₃ H₁ H₂ H₃
    source target gadget first second third edgeEmb
  decide

/-- The exact ordered-parent budget for embedding the new edges is four. -/
theorem parent_budget : ∀ v : Fin 14,
    ((univ : Finset (Fin 14)).filter (fun u => u < v ∧ s(u, v) ∈ added)).card ≤ 4 := by
  unfold added H₁ H₂ H₃ R₁ R₂ R₃ gadget target first second third edgeEmb
  decide

/-- Three typed local certificates give an actual fresh, physically supported
trace on the finite skeleton. It is not yet a host-selection theorem. -/
theorem exchange_trace {t : ℕ} {p : Fin 14 → Fin t}
    {F : Finset (Multiset (Fin t))}
    (h₁ : IsTransformer (p := p) (F := F) H₁ Q₁ R₁)
    (h₂ : IsTransformer (p := p) (F := F) H₂ Q₂ R₂)
    (h₃ : IsTransformer (p := p) (F := F) H₃ Q₃ R₃) :
    PhysicalMoves p F host ∅ initial initial final 3 := by
  rcases history_checks with ⟨hq₁, hq₂, hq₃, hx₁, hx₂, hend, hf₁, hf₂, hf₃⟩
  rcases cardinal_checks with ⟨_, _, _, hh₁, hh₂, hh₃, hr₁, hr₂, hr₃⟩
  have hs₁ : H₁ ∪ R₁ ⊆ host := by
    unfold host initial added H₁ R₁ H₂ R₂ H₃ R₃ Q₁ Q₂
      source target gadget first second third edgeEmb
    decide
  have hs₂ : H₂ ∪ R₂ ⊆ host := by
    unfold host initial added H₁ R₁ H₂ R₂ H₃ R₃ Q₁ Q₂
      source target gadget first second third edgeEmb
    decide
  have hs₃ : H₃ ∪ R₃ ⊆ host := by
    unfold host initial added H₁ R₁ H₂ R₂ H₃ R₃ Q₁ Q₂
      source target gadget first second third edgeEmb
    decide
  have ht : PhysicalMoves p F host ∅ U₂ X₂ final 1 := by
    refine .step hx₂ hq₃ (by simpa using hf₃) hs₃ h₃ (by omega) (by omega) ?_
    rw [hend]
    exact .stop _ _
  have hm : PhysicalMoves p F host ∅ U₁ X₁ final 2 :=
    .step hx₁ hq₂ (by simpa using hf₂) hs₂ h₂ (by omega) (by omega) ht
  exact .step (Subset.refl initial) hq₁ (by simpa using hf₁) hs₁ h₁
    (by omega) (by omega) hm

end PartitionedTriangleAbsorption.PairExchangeStage86
