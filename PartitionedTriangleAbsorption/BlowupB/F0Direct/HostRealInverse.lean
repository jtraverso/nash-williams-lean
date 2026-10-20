/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealGeometry
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealCoordinates
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteInverse
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.DiscardedCopies

@[expose] public section

/-! # The balanced physical inverse from the original geometric hypotheses

The good internal part supplies the real signless inverse.  The complete
crossing supergraph supplies physical coordinates, and the quantified bound
on discarded triangles repairs the restriction back to the actual host.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open TypedApplicationLinks F0RigidBoost HostHinges
open PartitionedTriangleAbsorption.F0Direct.RealComplete

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε : ℝ}

/-- A bounded balanced inverse on the actual graph, with no additional
geometric hypothesis.  Here the normalized triangle parameter is `θ / 100`. -/
theorem HostHyp.balancedInverse (hG : HostHyp p G α ε) (hε0 : 0 ≤ ε)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hscale : 100 * θ ≤ α)
    (hn : 4096 ≤ θ * Fintype.card V) (hsmall : 307200 * ε ≤ θ) :
    HasBoundedBalancedInverse p G (1024 / (θ / 100)) := by
  classical
  have b : Budget α ε θ (Fintype.card V) :=
    ⟨hε0, hθ0, hθ1, by linarith, hscale, hn⟩
  obtain ⟨i, hsize, hAU, hcount⟩ := HostRealGeometry.exists_geometry b hG
  have hnR : (0 : ℝ) < Fintype.card V := hsize.npos
  have hnN : 0 < Fintype.card V := by exact_mod_cast hnR
  obtain ⟨S, hS, hNorm⟩ := exists_completeInverse
    (HostRealCoordinates.partGraph p G i) (HostRealCoordinates.partGraph p G (other0 i))
    p (CrossCompletion.complete p G) (HostRealCoordinates.coordinates p G i)
    (θ / 100) (by positivity) (by linarith) hsize hAU hcount
  have hError : 3 * ε * (512 / (θ / 100)) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (show 0 < θ / 100 by positivity)]
    nlinarith only [hsmall]
  have h := hG.balancedInverse_of_completion hε0 (512 / (θ / 100))
    (by positivity) hnN S hS hNorm hError
  convert h using 1 <;> ring

#print axioms HostHyp.balancedInverse

end PartitionedTriangleAbsorption.BlowupB.F0Direct
