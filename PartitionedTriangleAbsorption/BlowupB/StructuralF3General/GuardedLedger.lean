/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedTerminal
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.PrivateFamily

/-! # The terminal placement step in an extendible host

Vertices of ledger degree above T form the external exclusion set.  The
handshake bound gives at most a/2 such vertices when 4|L| <= T*a.  A bounded
template is therefore embeddable whenever S+S*D < a/2.  Roots remain fixed
even when their ledger degree exceeds T.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily

open Finset AntiEdgeSelection TypedTransformer

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_incidentLoad_le (E : Finset (Sym2 V)) : ∑ v, incidentLoad E v ≤ 2 * E.card := by
  have hswap : ∑ v, incidentLoad E v = ∑ e ∈ E, (univ.filter fun v => v ∈ e).card := by
    simp only [incidentLoad, card_filter]
    exact sum_comm
  rw [hswap]
  calc ∑ e ∈ E, (univ.filter fun v => v ∈ e).card ≤ ∑ _e ∈ E, 2 := by
        refine sum_le_sum fun e _ => ?_
        induction e using Sym2.ind with
        | _ a b =>
          calc (univ.filter fun v => v ∈ s(a, b)).card ≤ ({a, b} : Finset V).card :=
                card_le_card fun v hv => by simpa using hv
            _ ≤ 2 := card_le_two
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem card_highLoad_le (E : Finset (Sym2 V)) (T : ℝ) :
    ((univ.filter fun v => T < incidentLoad E v).card : ℝ) * T ≤ 2 * E.card := by
  set H := univ.filter fun v => T < (incidentLoad E v : ℝ)
  have h1 : (H.card : ℝ) * T ≤ ∑ v ∈ H, (incidentLoad E v : ℝ) := by
    rw [← nsmul_eq_mul]
    exact card_nsmul_le_sum H _ T fun v hv => (mem_filter.mp hv).2.le
  have h2 : ∑ v ∈ H, (incidentLoad E v : ℝ) ≤ ∑ v, (incidentLoad E v : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  have h3 : ∑ v, (incidentLoad E v : ℝ) ≤ 2 * E.card := by
    exact_mod_cast sum_incidentLoad_le E
  linarith

/-- The actual coloured-hub theorem supplies the private step uniformly in the
piece and in the physical host. -/
theorem guarded_privateStep {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hF : ThreeStepLinks F) (m : ℕ) :
    ∃ B : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj] (a T D : ℝ),
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (terminalOrder m B t) a →
      0 ≤ D → 0 < T →
      (terminalOrder m B t : ℝ) + terminalOrder m B t * D < a / 2 →
      PrivateStep p F G m (terminalSize m B) T D a := by
  obtain ⟨B, hB⟩ := guarded_terminal_absorber F hF3 hF m
  refine ⟨B, fun {V} _ _ p G _ a T D hs hD0 hT hbudget => ?_⟩
  intro L hL hLc P hPG hm hdiv
  classical
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ a / 2 := by
    have hc := card_highLoad_le L T
    change (High.card : ℝ) * T ≤ 2 * L.card at hc
    nlinarith
  have hbudget' : (terminalOrder m B t : ℝ) + High.card + terminalOrder m B t * D < a := by
    linarith
  have hloop : ∀ e ∈ P, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hPG he)
      intro hd
      exact G.ne_of_adj hxy (by simpa using hd)
  obtain ⟨A, hA⟩ := hB p G a D L High hs hL hD0 hbudget' P hm hloop hdiv
  refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
  intro v hv
  rcases hA.vertices v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

#print axioms card_highLoad_le
#print axioms guarded_privateStep

end PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
