/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeSelection

/-! # Construct the four-move triangle walk from actual two-root supply

All new vertices avoid a supplied set containing the three roots; all eight
new edges avoid the blocked edges. This proves the walk, not hinge supply.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourMoveWalkStage51

open Finset AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [Fintype V] in
theorem copy_three (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) {a b c : V} (hab : G.Adj a b)
    (hac : G.Adj a c) (hbc : G.Adj b c)
    (hτ : ({p a,p b,p c} : Multiset (Fin t)) ∈ F) :
    IsCopy p F G {a,b,c} := by
  have ha := hab.ne
  have hb := hac.ne
  have hc := hbc.ne
  refine ⟨⟨?_, by simp [ha,hb,hc]⟩, ?_⟩
  · intro u hu v hv huv
    simp only [mem_coe, mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      simp_all [G.adj_symm]
  · simpa only [insert_val_of_notMem (a := a) (s := {b,c}) (by simp [ha,hb]),
      insert_val_of_notMem (a := b) (s := {c}) (by simp [hc]), singleton_val,
      Multiset.map_cons, Multiset.map_singleton, Multiset.insert_eq_cons] using hτ

/-- Blocked adjacency to the vertex being replaced costs one more degree,
not a third-root common-neighbour hypothesis. -/
theorem exists_replacement (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α d : ℝ)
    (hanti : AntiEdgeful p F G α) (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (Z : Finset V) (a b old : V) (hab : a ≠ b)
    (hτ : ({p a,p b,p old} : Multiset (Fin t)) ∈ F)
    (hbudget : (Z.card : ℝ) + 3 * d < α * Fintype.card V) :
    ∃ x, G.Adj a x ∧ G.Adj x b ∧ p x = p old ∧ x ∉ Z ∧
      s(a,x) ∉ B ∧ s(b,x) ∉ B ∧ s(old,x) ∉ B := by
  have hblocked : ((blockedNeighbours B old).card : ℝ) ≤ d := by
    have h := blockedNeighbours_card_le B old
    have hr : ((blockedNeighbours B old).card : ℝ) ≤ incidentLoad B old := by
      exact_mod_cast h
    exact hr.trans (hB old)
  have hsize : ((Z ∪ blockedNeighbours B old).card : ℝ) ≤ Z.card + d := by
    have h := card_union_le Z (blockedNeighbours B old)
    have hr : ((Z ∪ blockedNeighbours B old).card : ℝ) ≤
        Z.card + (blockedNeighbours B old).card := by exact_mod_cast h
    linarith
  obtain ⟨x,hax,hxb,hpart,hfresh,haB,hbB⟩ :=
    exists_avoiding_of_degree_bound p F G α d hanti (p a) (p b) (p old)
      hτ a b hab rfl rfl B (Z ∪ blockedNeighbours B old) hB (by linarith)
  refine ⟨x,hax,hxb,hpart,fun hx => hfresh (mem_union_left _ hx),haB,hbB,?_⟩
  intro he
  exact hfresh (mem_union_right Z (mem_filter.mpr ⟨mem_univ x,he⟩))

theorem exists_four_move_walk (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α d : ℝ)
    (hanti : AntiEdgeful p F G α) (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (Z : Finset V) (a b c : V) (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hτ : ({p a,p b,p c} : Multiset (Fin t)) ∈ F)
    (hbudget : (Z.card : ℝ) + 3 + 3 * d < α * Fintype.card V) :
    ∃ x y z w : V,
      x ∉ Z ∧ y ∉ insert x Z ∧ z ∉ insert y (insert x Z) ∧
      w ∉ insert z (insert y (insert x Z)) ∧
      Disjoint ({x,y,z,w} : Finset V) ({a,b,c} : Finset V) ∧
      p x = p c ∧ p y = p b ∧ p z = p a ∧ p w = p c ∧
      IsCopy p F G {a,b,x} ∧ IsCopy p F G {a,x,y} ∧
      IsCopy p F G {x,y,z} ∧ IsCopy p F G {z,y,w} ∧
      s(a,x) ∉ B ∧ s(b,x) ∉ B ∧ s(a,y) ∉ B ∧ s(x,y) ∉ B ∧
      s(x,z) ∉ B ∧ s(y,z) ∉ B ∧ s(z,w) ∉ B ∧ s(y,w) ∉ B ∧
      s(c,x) ∉ B ∧ s(b,y) ∉ B ∧ s(a,z) ∉ B ∧ s(x,w) ∉ B := by
  obtain ⟨x,hax,hxb,hpx,hx,haxB,hbxB,hcxB⟩ :=
    exists_replacement p F G α d hanti B hB Z a b c hab.ne hτ (by linarith)
  have hτ₂ : ({p a,p c,p b} : Multiset (Fin t)) ∈ F := by
    convert hτ using 1
    ext k
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    omega
  have hcard₁ : ((insert x Z).card : ℝ) ≤ Z.card + 1 := by
    exact_mod_cast card_insert_le x Z
  obtain ⟨y,hay,hyx,hpy,hy,hayB,hxyB,hbyB⟩ :=
    exists_replacement p F G α d hanti B hB (insert x Z) a x b hax.ne
      (by simpa only [hpx] using hτ₂) (by linarith)
  have hτ₃ : ({p c,p b,p a} : Multiset (Fin t)) ∈ F := by
    convert hτ using 1
    ext k
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    omega
  have hcard₂ : ((insert y (insert x Z)).card : ℝ) ≤ Z.card + 2 := by
    have h := card_insert_le y (insert x Z)
    have hr : ((insert y (insert x Z)).card : ℝ) ≤ (insert x Z).card + 1 := by
      exact_mod_cast h
    linarith
  obtain ⟨z,hxz,hzy,hpz,hz,hxzB,hyzB,hazB⟩ :=
    exists_replacement p F G α d hanti B hB (insert y (insert x Z)) x y a
      hyx.ne.symm (by simpa only [hpx,hpy] using hτ₃) (by linarith)
  have hcard₃ : ((insert z (insert y (insert x Z))).card : ℝ) ≤ Z.card + 3 := by
    have h := card_insert_le z (insert y (insert x Z))
    have hr : ((insert z (insert y (insert x Z))).card : ℝ) ≤
        (insert y (insert x Z)).card + 1 := by exact_mod_cast h
    linarith
  obtain ⟨w,hzw,hwy,hpw,hw,hzwB,hywB,hxwB⟩ :=
    exists_replacement p F G α d hanti B hB (insert z (insert y (insert x Z)))
      z y x hzy.ne (by simpa only [hpz,hpy,hpx] using hτ) (by linarith)
  have hpw' : p w = p c := hpw.trans hpx
  have hyZ : y ∉ Z := fun h => hy (mem_insert_of_mem h)
  have hzZ : z ∉ Z := fun h => hz (mem_insert_of_mem (mem_insert_of_mem h))
  have hwZ : w ∉ Z := fun h => hw (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem h)))
  have hfresh : Disjoint ({x,y,z,w} : Finset V) Z := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hx,hyZ,hzZ,hwZ⟩
  have hroots : ({a,b,c} : Finset V) ⊆ Z := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    exacts [ha,hb,hc]
  refine ⟨x,y,z,w,hx,hy,hz,hw,hfresh.mono_right hroots,hpx,hpy,hpz,hpw',?_,?_,?_,?_,
    haxB,hbxB,hayB,hxyB,hxzB,hyzB,hzwB,hywB,hcxB,hbyB,hazB,hxwB⟩
  · exact copy_three p F G hab hax hxb.symm (by simpa only [hpx] using hτ)
  · exact copy_three p F G hax hay hyx.symm (by simpa only [hpx,hpy] using hτ₂)
  · exact copy_three p F G hyx.symm hxz hzy.symm (by simpa only [hpx,hpy,hpz] using hτ₃)
  · exact copy_three p F G hzy hzw hwy.symm (by simpa only [hpz,hpy,hpw'] using hτ)

end PartitionedTriangleAbsorption.FourMoveWalkStage51
