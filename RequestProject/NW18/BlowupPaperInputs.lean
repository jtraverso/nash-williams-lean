/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.F0Producer
import RequestProject.NW18.Case126.FracDivF1
import RequestProject.NW18.Case127.FracDivF2
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.RoutedPaper

/-!
# Typed blowup inputs for the Nash-Williams application

These adapters identify the actual NW18 hypotheses with the Paper II definitions.
They derive the F1/F2 results from the general routed-producer theorem
without using the global `Theorem1316Statement` or the final Nash-Williams theorem.
The F0 input uses the separate nonextreme two-part theorem, not the
near-complete blowup geometry. These inputs do not replace the existing
public proof or its independent F1 vortex proof.
-/

namespace NashWilliams18.PaperII

/-- The actual NW host and Paper II host have definitionally identical hypotheses. -/
theorem idealized_iff_paperII {V : Type} [Fintype V] [DecidableEq V]
    {t : ℕ} (F : Finset (Multiset (Fin t))) (ε : ℝ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) :
    NashWilliams18.IsIdealizedT F ε G p ↔
      PartitionedTriangleAbsorption.BlowupB.IsIdealizedNW F ε G p := Iff.rfl

/-- The separate nonextreme F0 input, with no remaining producer hypothesis. -/
theorem theorem146_F0 : NashWilliams18.Theorem146Statement :=
  NashWilliams18.theorem146Statement_holds

theorem theorem147_F1 : NashWilliams18.Theorem147F1Statement := by
  obtain ⟨ε, hε, n₀, h⟩ := PaddedGeneral.RealInverse.idealized_F12 (Or.inl rfl)
  exact ⟨ε, hε, n₀, fun V _ _ p G _ hn hint hid =>
    h V p G hn hint ((idealized_iff_paperII _ ε G p).mp hid)⟩

theorem theorem147_F2 : NashWilliams18.Theorem147F2Statement := by
  obtain ⟨ε, hε, n₀, h⟩ := PaddedGeneral.RealInverse.idealized_F12 (Or.inr rfl)
  exact ⟨ε, hε, n₀, fun V _ _ p G _ hn hint hid =>
    h V p G hn hint ((idealized_iff_paperII _ ε G p).mp hid)⟩

theorem typed_inputs :
    NashWilliams18.Theorem147F1Statement ∧ NashWilliams18.Theorem147F2Statement :=
  ⟨theorem147_F1, theorem147_F2⟩

end NashWilliams18.PaperII

#print axioms NashWilliams18.PaperII.theorem146_F0
#print axioms NashWilliams18.PaperII.theorem147_F1
#print axioms NashWilliams18.PaperII.theorem147_F2
#print axioms NashWilliams18.PaperII.typed_inputs
