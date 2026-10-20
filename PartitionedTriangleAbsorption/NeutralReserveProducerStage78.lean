/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.NeutralAugmentationStage77
public import PartitionedTriangleAbsorption.SparseReserveAssembly
public import PartitionedTriangleAbsorption.StructuralF3.HostCycles

/-! # Producing a neutral four-class reserve before the residual

The random sparse reserve is an accepted producer. Its physical augmentation
is deterministic and preserves its anti-edgeful supply by inclusion. All
rates and thresholds in the final statement precede the host graph.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NeutralReserveProducerStage78

open Finset AntiEdgeSelection ClassRepresentativesStage65 TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem antiEdgeful_delete (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset (Sym2 V)) (alpha d : ℝ)
    (hG : AntiEdgeful p TypedApplicationLinks.F3 G alpha)
    (hB : DegBounded B (d * Fintype.card V)) :
    AntiEdgeful p TypedApplicationLinks.F3 (G.deleteEdges (B : Set (Sym2 V)))
      (alpha - 2 * d) := by
  classical
  intro tau ht i j k hijk u v huv hu hv
  let W := univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)
  let good := W \ (blockedNeighbours B u ∪ blockedNeighbours B v)
  have hcount : W.card ≤ good.card + incidentLoad B u + incidentLoad B v := by
    simpa only [card_empty, empty_union, Nat.add_zero] using
      available_card_budget W ∅ B u v
  have hs : good ⊆ univ.filter (fun w =>
      (G.deleteEdges (B : Set (Sym2 V))).Adj u w ∧
      (G.deleteEdges (B : Set (Sym2 V))).Adj w v ∧ p w = k) := by
    intro w hw
    obtain ⟨hwW,hwbad⟩ := mem_sdiff.mp hw
    obtain ⟨_,huw,hwv,hp⟩ := mem_filter.mp hwW
    have hwu : s(u,w) ∉ B := by
      intro he
      exact hwbad (mem_union_left _ (mem_filter.mpr ⟨mem_univ w,he⟩))
    have hwv' : s(w,v) ∉ B := by
      intro he
      exact hwbad (mem_union_right _ (mem_filter.mpr
        ⟨mem_univ w, by simpa only [Sym2.eq_swap] using he⟩))
    exact mem_filter.mpr ⟨mem_univ w, by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨huw,hwu⟩, by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hwv,hwv'⟩,hp⟩
  have hw := hG tau ht i j k hijk u v huv hu hv
  have hc : (W.card : ℝ) ≤ good.card + (incidentLoad B u : ℝ) + incidentLoad B v := by
    exact_mod_cast hcount
  have hcs : (good.card : ℝ) ≤ ((univ.filter (fun w =>
      (G.deleteEdges (B : Set (Sym2 V))).Adj u w ∧
      (G.deleteEdges (B : Set (Sym2 V))).Adj w v ∧ p w = k)).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hs)
  have hdu := hB u
  have hdv := hB v
  change (incidentLoad B u : ℝ) ≤ d * Fintype.card V at hdu
  change (incidentLoad B v : ℝ) ≤ d * Fintype.card V at hdv
  change alpha * Fintype.card V ≤ (W.card : ℝ) at hw
  nlinarith

/-- A sparse neutral anti-edgeful reserve, chosen before every future leftover.
No absorber, fractional correction or reserve is an input to this producer. -/
theorem exists_neutral_reserve (gamma rho : ℝ) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (hrho : 0 < rho) :
    ∃ delta alpha : ℝ, 0 < delta ∧ 0 < alpha ∧ alpha ≤ 1 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
          (F : Finset (Sym2 V)),
          (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
          (∀ i, gamma * Fintype.card V ≤ ((classSet p i).card : ℝ)) →
          DegBounded F (delta * Fintype.card V) →
          ∃ X : Finset (Sym2 V),
            X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset ∧
            DegBounded X (rho * Fintype.card V) ∧
            AntiEdgeful p TypedApplicationLinks.F3 (ReserveCoverDown.reserveGraph X) alpha ∧
            ∀ l : Fin 4 → Fin 4 → ℤ, Annihilates TypedApplicationLinks.F3 l →
              ∑ e ∈ X, (pairFun l (pairVec p e) : ℝ) = 0 := by
  let r := min (gamma ^ 2 / 2048) (min (rho * gamma / 392) (gamma / 8))
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hrsmall : r ≤ gamma ^ 2 / 2048 := min_le_left _ _
  have hrrho : r ≤ rho * gamma / 392 := (min_le_right _ _).trans (min_le_left _ _)
  have hrga : r ≤ gamma / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hr1 : r / 2 ≤ 1 := by linarith
  let alpha := (gamma / 2) * (r / 2) ^ 2 / 2
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have halpha1 : alpha ≤ 1 := by
    have hs : (r / 2) ^ 2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ gamma / 2 by positivity)
    dsimp [alpha]
    nlinarith
  let N := max ⌈1 / r⌉₊
    (max ⌈384 / ((gamma / 2) ^ 3 * (r / 2) ^ 12)⌉₊ ⌈2 / (r / 2) ^ 4⌉₊)
  refine ⟨r,alpha,hr,halpha,halpha1,N,?_⟩
  intro V _ _ hN p G0 _ F hG0 hsize hF
  classical
  let n : ℝ := Fintype.card V
  have hn1 : 1 / r ≤ n := (Nat.le_ceil _).trans (by
    dsimp [n]
    exact_mod_cast (le_max_left _ _).trans hN)
  have hn2 : 384 / ((gamma / 2) ^ 3 * (r / 2) ^ 12) ≤ n :=
    (Nat.le_ceil _).trans (by
      dsimp [n]
      exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hn3 : 2 / (r / 2) ^ 4 ≤ n := (Nat.le_ceil _).trans (by
    dsimp [n]
    exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hN)
  have hlarge : 1 ≤ r * n := by
    have hh := (div_le_iff₀ hr).mp hn1
    nlinarith
  have hn : 0 < n := by nlinarith
  have hbase := StructuralF3.antiEdgeful_host p G0 hG0 gamma hsize
  have hdel := antiEdgeful_delete p G0 F gamma r hbase hF
  have hanti : AntiEdgeful p TypedApplicationLinks.F3
      (G0.deleteEdges (F : Set (Sym2 V))) (gamma / 2) := by
    intro tau ht i j k he u v huv hu hv
    have hh := hdel tau ht i j k he u v huv hu hv
    have hweak := mul_le_mul_of_nonneg_right (show gamma / 2 ≤ gamma - 2 * r by linarith) hn.le
    exact hweak.trans hh
  have hsz : 96 * (4 : ℝ) ≤ (gamma / 2) ^ 3 * (r / 2) ^ 12 * n := by
    have hh := (div_le_iff₀ (show 0 < (gamma / 2) ^ 3 * (r / 2) ^ 12 by positivity)).mp hn2
    nlinarith
  have hdegrees : 2 ≤ (r / 2) ^ 4 * n := by
    have hh := (div_le_iff₀ (show 0 < (r / 2) ^ 4 by positivity)).mp hn3
    nlinarith
  obtain ⟨X0,hX0,hdX0,hantiX0⟩ := SparseReserveAssembly.exists_sparse_reserve
    (G0.deleteEdges (F : Set (Sym2 V))) p TypedApplicationLinks.F3 (gamma / 2)
    (r / 2) (by positivity) (by positivity) hr1 hn hanti hsz hdegrees
  have hdX : DegBounded X0 (r * n) := by
    convert hdX0 using 1
    ring
  obtain ⟨X,hX0X,hX,hd,hneutral⟩ := NeutralAugmentationStage77.physical_augmentation
    p G0 F X0 gamma r hg hg1 hr hG0 hsize hlarge (by nlinarith [sq_nonneg gamma]) hF hX0 hdX
  refine ⟨X,hX,?_,TypedLoadReserveObstruction.antiEdgeful_mono p
    TypedApplicationLinks.F3 hX0X hantiX0,hneutral⟩
  intro v
  apply (hd v).trans
  have hh : 196 * r / gamma ≤ rho := by
    apply (div_le_iff₀ hg).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hh hn.le
  convert hmul using 1
  ring

end PartitionedTriangleAbsorption.NeutralReserveProducerStage78
