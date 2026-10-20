/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Supply

/-! # Physical hinges from class-aware fibres, without universal root queries

The graph is complete between distinct structural classes. Labels are constant
on these classes. A hinge uses new vertices in the classes of its shared edge;
no common-neighbour condition for arbitrary four, five or six roots is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassAwareHingesStage64

open Finset PhysicalHingeSupply SignedHinge

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj]

def fibre (cls : V → C) (v : V) : Finset V := univ.filter (fun x => cls x = cls v)

open Classical in
theorem hinge_count_of_class_fibres (cls : V → C)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    (hp : ∀ a b, cls a = cls b → p a = p b)
    {u v w z : V} (huv : G.Adj u v) (huw : G.Adj u w) (huz : G.Adj u z)
    (hvw : G.Adj v w) (hvz : G.Adj v z) (hwz : w ≠ z)
    (hS : ({u, v, w} : Finset V).val.map p ∈ F)
    (hS' : ({u, v, z} : Finset V).val.map p ∈ F) :
    ((fibre cls u).card - 1) * ((fibre cls v).card - 1) ≤
      (G.edgeFinset.powerset.filter (fun H =>
        IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)).card := by
  classical
  let X := (fibre cls u).erase u
  let Y := (fibre cls v).erase v
  let P := X ×ˢ Y
  let K := G.edgeFinset.powerset.filter (fun H =>
    IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)
  have hX : ∀ x ∈ X, x ≠ u ∧ cls x = cls u := by
    intro x hx
    simpa [X, fibre] using hx
  have hY : ∀ y ∈ Y, y ≠ v ∧ cls y = cls v := by
    intro y hy
    simpa [Y, fibre] using hy
  have hdata : ∀ q ∈ P, SixDistinct u v w z q.1 q.2 ∧
      p q.1 = p u ∧ p q.2 = p v ∧
      G.Adj u q.2 ∧ G.Adj v q.1 ∧ G.Adj q.1 w ∧ G.Adj q.2 w ∧
      G.Adj q.1 z ∧ G.Adj q.2 z ∧ G.Adj q.1 q.2 := by
    intro q hq
    obtain ⟨hx, hy⟩ := mem_product.mp hq
    obtain ⟨hxu, hcx⟩ := hX q.1 hx
    obtain ⟨hyv, hcy⟩ := hY q.2 hy
    have ha : G.Adj u q.2 := (hG _ _).mpr (by simpa [hcy] using (hG _ _).mp huv)
    have hb : G.Adj v q.1 := (hG _ _).mpr (by
      simpa [hcx] using ((hG _ _).mp huv).symm)
    have hc : G.Adj q.1 w := (hG _ _).mpr (by simpa [hcx] using (hG _ _).mp huw)
    have hd : G.Adj q.2 w := (hG _ _).mpr (by simpa [hcy] using (hG _ _).mp hvw)
    have he : G.Adj q.1 z := (hG _ _).mpr (by simpa [hcx] using (hG _ _).mp huz)
    have hf : G.Adj q.2 z := (hG _ _).mpr (by simpa [hcy] using (hG _ _).mp hvz)
    have hg : G.Adj q.1 q.2 := (hG _ _).mpr (by simpa [hcx, hcy] using (hG _ _).mp huv)
    exact ⟨⟨huv.ne, huw.ne, huz.ne, hxu.symm, ha.ne, hvw.ne, hvz.ne,
      hb.ne, hyv.symm, hwz, hc.ne.symm, hd.ne.symm, he.ne.symm, hf.ne.symm, hg.ne⟩,
      hp _ _ hcx, hp _ _ hcy, ha, hb, hc, hd, he, hf, hg⟩
  have hmaps : ∀ q ∈ P, hingeEdges u v w z q.1 q.2 ∈ K := by
    intro q hq
    obtain ⟨hsix, hpx, hpy, ha, hb, hc, hd, he, hf, hg⟩ := hdata q hq
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_, hingeEdges_isHinge hsix hpx hpy hS hS',
      card_vertSet_hingeEdges hsix⟩
    intro e hee
    simp only [hingeEdges, mem_insert, mem_singleton] at hee
    rcases hee with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exacts [ha, hb, hc, hd, he, hf, hg]
  have hinj : Set.InjOn (fun q : V × V => hingeEdges u v w z q.1 q.2) P := by
    intro q hq q' hq' heq
    obtain ⟨hx, hy⟩ := hingeEdges_inj (hdata q hq).1 (hdata q' hq').1 heq
    exact Prod.ext hx hy
  have hPK := card_le_card_of_injOn _ hmaps hinj
  have hu : u ∈ fibre cls u := by simp [fibre]
  have hv : v ∈ fibre cls v := by simp [fibre]
  simpa [P, X, Y, card_product, card_erase_of_mem hu, card_erase_of_mem hv] using hPK

theorem hingeSupply_of_class_fibres (cls : V → C)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    (hp : ∀ a b, cls a = cls b → p a = p b) (a : ℕ)
    (hsize : ∀ v, a + 1 ≤ (fibre cls v).card) (β : ℝ)
    (hbudget : β * (Fintype.card V : ℝ) ^ 2 ≤ (a : ℝ) ^ 2) :
    HingeSupply p F G β 6 := by
  classical
  intro S S' hS hS' h1
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, rfl, rfl⟩ :=
    roots_of_shared_edge hS.1.card_eq hS'.1.card_eq h1
  have hcl : G.Adj u v ∧ G.Adj u w ∧ G.Adj v w :=
    SimpleGraph.is3Clique_triple_iff.mp hS.1
  have hcl' : G.Adj u v ∧ G.Adj u z ∧ G.Adj v z :=
    SimpleGraph.is3Clique_triple_iff.mp hS'.1
  have hcount := hinge_count_of_class_fibres cls hG hp hcl.1 hcl.2.1 hcl'.2.1
    hcl.2.2 hcl'.2.2 hwz hS.2 hS'.2
  have hu : a ≤ (fibre cls u).card - 1 := by have := hsize u; omega
  have hv : a ≤ (fibre cls v).card - 1 := by have := hsize v; omega
  have hnat : a * a ≤
      (G.edgeFinset.powerset.filter (fun H =>
        IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)).card :=
    (Nat.mul_le_mul hu hv).trans hcount
  refine ⟨6, by decide, ?_⟩
  norm_num
  exact hbudget.trans (by exact_mod_cast (show a ^ 2 ≤ _ by simpa [pow_two] using hnat))

end PartitionedTriangleAbsorption.ClassAwareHingesStage64
