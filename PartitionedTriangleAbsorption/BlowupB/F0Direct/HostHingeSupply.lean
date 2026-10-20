/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostBadHinges
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostCrossHinges
public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Supply

@[expose] public section

/-! # Literal physical hinge supply for the nonextremal F₀ host

The supply counts distinct physical edge sets.  Its two possible support
orders are six and eight; both modes are exact simple typed decompositions.
The quantitative assumptions are gathered in `HostHinges.Budget`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks HostHinges HingeCounting PhysicalHingeSupply

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε θ : ℝ}

theorem countedHinges_comm (S S' : Finset V) (i : ℕ) :
    countedHinges p F0 G S S' i = countedHinges p F0 G S' S i := by
  classical
  ext E
  simp only [mem_countedHinges, IsHinge]
  rw [union_comm (triEdges S) (triEdges S')]
  tauto

private theorem internal_third (i k : Fin 2)
    (hk : ({i, i, k} : Multiset (Fin 2)) ∈ F0) : k = other0 i := by
  revert i k
  decide

private theorem other_other (i : Fin 2) : other0 (other0 i) = i := by
  revert i
  decide

theorem cross_count (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε)
    (u v x y : V) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) (hp : p u ≠ p v) :
    θ / 2^30 * (Fintype.card V : ℝ)^2 ≤
      (countedHinges p F0 G {u, v, x} {u, v, y} 6).card := by
  have pv : p v = other0 (p u) := (eq_or_eq_other0 (p u) (p v)).resolve_left hp.symm
  rcases eq_or_eq_other0 (p u) (p x) with px | px <;>
    rcases eq_or_eq_other0 (p u) (p y) with py | py
  · exact cross_same_count b h (p u) u v x y huv hux huy hvx hvy hxy rfl pv px py
  · exact cross_mixed_count b h (p u) u v x y huv hux huy hvx hvy hxy rfl pv px py
  · rw [countedHinges_comm]
    exact cross_mixed_count b h (p u) u v y x huv huy hux hvy hvx hxy.symm rfl pv py px
  · have hc := cross_same_count b h (other0 (p u)) v u x y huv.symm hvx hvy hux huy hxy
      pv (other_other (p u)).symm px py
    have hx : ({v, u, x} : Finset V) = {u, v, x} := by rw [insert_comm]
    have hy : ({v, u, y} : Finset V) = {u, v, y} := by rw [insert_comm]
    rw [hx, hy] at hc
    exact hc

/-- The geometric assumptions alone supply sufficiently many distinct
physical hinges, with six or eight vertices. -/
theorem HostHyp.hingeSupply (h : HostHyp p G α ε)
    (b : Budget α ε θ (Fintype.card V)) :
    SignedHinge.HingeSupply p F0 G (θ / 2^30) 8 := by
  classical
  intro S S' hS hS' hshared
  obtain ⟨u, v, x, y, huv, hux, huy, hvx, hvy, hxy, rfl, rfl⟩ :=
    roots_of_shared_edge hS.1.card_eq hS'.1.card_eq hshared
  by_cases hp : p u = p v
  · have hxF := hS.2
    have hyF := hS'.2
    rw [map_three p huv hux hvx, ← hp] at hxF
    rw [map_three p huv huy hvy, ← hp] at hyF
    have px := internal_third (p u) (p x) hxF
    have py := internal_third (p u) (p y) hyF
    have huxG : G.Adj u x := hS.1.isClique (by simp) (by simp) hux
    have huyG : G.Adj u y := hS'.1.isClique (by simp) (by simp) huy
    have hvxG : G.Adj v x := hS.1.isClique (by simp) (by simp) hvx
    have hvyG : G.Adj v y := hS'.1.isClique (by simp) (by simp) hvy
    obtain ⟨i, hext⟩ := h.good_part
    rcases eq_or_eq_other0 (p u) i with hi | hi
    · refine ⟨6, by decide, ?_⟩
      subst i
      have hc := good_internal_count b h (p u) hext u v x y huv hux huy hvx hvy hxy
        rfl hp.symm px py huxG huyG hvxG hvyG
      simpa only [show (6 : ℕ) - 4 = 2 from rfl, countedHinges] using hc
    · refine ⟨8, by decide, ?_⟩
      subst i
      have hc := bad_internal_count b h (p u) hext u v x y huv hux huy hvx hvy hxy
        rfl hp.symm px py huxG huyG hvxG hvyG
      simpa only [show (8 : ℕ) - 4 = 4 from rfl, countedHinges] using hc
  · refine ⟨6, by decide, ?_⟩
    have hc := cross_count b h u v x y huv hux huy hvx hvy hxy hp
    simpa only [show (6 : ℕ) - 4 = 2 from rfl, countedHinges] using hc

#print axioms cross_count
#print axioms HostHyp.hingeSupply

end PartitionedTriangleAbsorption.BlowupB.F0Direct
