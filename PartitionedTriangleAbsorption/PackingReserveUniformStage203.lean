/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingReserveAssemblyStage202
public import PartitionedTriangleAbsorption.ClassReserveStage65.Threshold

/-! # Uniform packing-triangle reserve producer

Constants precede the host. A small uncovered degree supplies the packing's
anti-edgefulness; no good reserve is assumed. Final absorption is separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingReserveUniformStage203

open Finset Filter Topology SparseReserveGeometry

theorem exists_uniform_threshold (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (t : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ≤ γ * n ∧
      (n : ℝ) * Real.exp (-ρ ^ 2 * n) +
        (n : ℝ) ^ 2 * t * Real.exp (-ρ ^ 4 * γ * n / 12) < 1 := by
  have h₁ := ClassReserveStage65.tendsto_pow_mul_exp_neg (ρ ^ 2) (by positivity) 1
  have h₂ := ClassReserveStage65.tendsto_pow_mul_exp_neg (ρ ^ 4 * γ / 12) (by positivity) 2
  have h := h₁.add (h₂.const_mul (t : ℝ))
  simp only [add_zero, mul_zero] at h
  have heq : (fun n : ℕ => (n : ℝ) ^ 1 * Real.exp (-(ρ ^ 2 * n)) +
      (t : ℝ) * ((n : ℝ) ^ 2 * Real.exp (-(ρ ^ 4 * γ / 12 * n)))) =
      (fun n : ℕ => (n : ℝ) * Real.exp (-ρ ^ 2 * n) +
        (n : ℝ) ^ 2 * t * Real.exp (-ρ ^ 4 * γ * n / 12)) := by
    funext n
    have he₁ : -(ρ ^ 2 * (n : ℝ)) = -ρ ^ 2 * n := by ring
    have he₂ : -(ρ ^ 4 * γ / 12 * (n : ℝ)) = -ρ ^ 4 * γ * n / 12 := by ring
    rw [he₁, he₂]
    ring
  rw [heq] at h
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) * Real.exp (-ρ ^ 2 * n) +
      (n : ℝ) ^ 2 * t * Real.exp (-ρ ^ 4 * γ * n / 12) < 1 :=
    h.eventually (gt_mem_nhds one_pos)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / γ)
  refine ⟨max N₁ N₂, fun n hn => ⟨?_, hN₁ n ((le_max_left _ _).trans hn)⟩⟩
  have hn₂ : (N₂ : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have := (div_lt_iff₀ hγ).mp (hN₂.trans_le hn₂)
  linarith

theorem packing_antiEdgeful {V : Type} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset (Sym2 V)) (hQ : Q ⊆ G.edgeFinset)
    (γ : ℝ) (hG : AntiEdgeful p F G γ)
    (hR : DegBounded (G.edgeFinset \ Q) (γ / 4 * Fintype.card V)) :
    AntiEdgeful p F (ReserveCoverDown.reserveGraph Q) (γ / 2) := by
  classical
  have h := antiEdgeful_withoutEdges p F G (G.edgeFinset \ Q) γ (γ / 2)
    (γ / 4 * Fintype.card V) hG hR (by linarith)
  have heq : G.edgeFinset \ (G.edgeFinset \ Q) = Q := by
    apply Subset.antisymm
    · intro e he
      obtain ⟨heG, hebad⟩ := mem_sdiff.mp he
      by_contra heQ
      exact hebad (mem_sdiff.mpr ⟨heG, heQ⟩)
    · intro e heQ
      exact mem_sdiff.mpr ⟨hQ heQ, fun he => (mem_sdiff.mp he).2 heQ⟩
  simpa only [withoutEdges, heq] using h

theorem exists_reserve_uniform (t : ℕ) (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin t) (F : Finset (Multiset (Fin t)))
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (Q : Finset (Sym2 V)) (D : Finset (Finset V)),
      N ≤ Fintype.card V → IsDecomp p F Q D → Q ⊆ G.edgeFinset →
      AntiEdgeful p F G γ → DegBounded (G.edgeFinset \ Q) (γ / 4 * Fintype.card V) →
      ∃ B : Finset (Finset V), B ⊆ D ∧
        DegBounded (B.biUnion triEdges) (2 * ρ * Fintype.card V) ∧
        AntiEdgeful p F (ReserveCoverDown.reserveGraph (B.biUnion triEdges)) (γ * ρ ^ 2 / 24) ∧
        HasDecomp p F (B.biUnion triEdges) ∧
        (∀ v, ReserveConfinementStage195.outsideCharge D (B.biUnion triEdges) v = 0) := by
  classical
  obtain ⟨N, hN⟩ := exists_uniform_threshold (γ / 2) ρ (by positivity) hρ t
  refine ⟨N, ?_⟩
  intro V _ _ p F G _ Q D hn hD hQ hG hR
  obtain ⟨hscale, hbudget⟩ := hN (Fintype.card V) hn
  have hpack := packing_antiEdgeful p F G Q hQ γ hG hR
  obtain ⟨B, hBD, hd, ha, hdecomp, hcharge⟩ :=
    PackingReserveAssemblyStage202.exists_reserve_of_budget p F Q D hD
      (γ / 2) ρ hρ hρ1 hscale hpack hbudget
  refine ⟨B, hBD, hd, ?_, hdecomp, hcharge⟩
  have heq : (γ / 2) * ρ ^ 2 / 12 = γ * ρ ^ 2 / 24 := by ring
  rw [heq] at ha
  exact ha


end PartitionedTriangleAbsorption.PackingReserveUniformStage203
