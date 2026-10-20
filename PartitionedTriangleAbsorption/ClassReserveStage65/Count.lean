/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassReserveStage65.Tails
public import PartitionedTriangleAbsorption.ClassAwareHingesStage64

/-! # Deterministic hinge count inside one sampled reserve

For the roots `S = {u,v,w}`, `S' = {u,v,z}` of the original class graph, put

* `xCand = fibre(u) \ {u}` with roots `{v, w, z}`;
* `yCand = fibre(v) \ {v}` with roots `{u, w, z}`.

If `x` is marked (edges `vx, wx, zx` sampled), `y` is marked (edges `uy, wy, zy` sampled)
and the connector `xy` is sampled, then all seven edges of
`hingeEdges u v w z x y = {uy, vx, xw, yw, xz, yz, xy}` lie in the sampled reserve.
Different pairs `(x, y)` give different edge sets (`hingeEdges_inj`), so the number of
six-vertex physical hinges inside the reserve is at least the number of sampled cross pairs
between the two marked sets.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Finset PhysicalHingeSupply SignedHinge BernoulliBlocks ClassAwareHingesStage64

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Candidates for `x`, of the class of `u`. -/
def xCand (cls : V → Fin 4) (u : V) : Finset V := (fibre cls u).erase u

theorem mem_xCand {cls : V → Fin 4} {u x : V} : x ∈ xCand cls u ↔ x ≠ u ∧ cls x = cls u := by
  simp [xCand, fibre]

theorem xCand_disjoint_roots {cls : V → Fin 4} {a b w z : V} (hb : cls b ≠ cls a)
    (hw : cls w ≠ cls a) (hz : cls z ≠ cls a) : Disjoint (xCand cls a) {b, w, z} := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨-, hcx⟩ := mem_xCand.mp hx
  simp only [mem_insert, mem_singleton] at hx'
  rcases hx' with rfl | rfl | rfl <;> simp_all

theorem xCand_card_ge {cls : V → Fin 4} (a : V) {k : ℝ} (hk : k ≤ ((fibre cls a).card : ℝ)) :
    k - 1 ≤ ((xCand cls a).card : ℝ) := by
  have ha : a ∈ fibre cls a := by simp [fibre]
  rw [xCand, card_erase_of_mem ha]
  have : 1 ≤ (fibre cls a).card := card_pos.mpr ⟨a, ha⟩
  push_cast [this]
  linarith

theorem xCand_disjoint_cross {cls : V → Fin 4} {a b : V} (hab : cls a ≠ cls b) :
    Disjoint (xCand cls a) (xCand cls b) := by
  rw [disjoint_left]
  intro x hx hx'
  exact hab ((mem_xCand.mp hx).2.symm.trans (mem_xCand.mp hx').2)

open Classical in
/-- **Each sampled connector between marked candidates is a physical hinge in the reserve.**
The pair `(x, y)` gives six distinct vertices, and all seven edges of
`hingeEdges u v w z x y` are sampled graph edges. -/
theorem cross_pair_hinge {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] (cls : V → Fin 4)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (hp : ∀ a b, cls a = cls b → p a = p b)
    {u v w z : V} (huv : G.Adj u v) (huw : G.Adj u w) (huz : G.Adj u z)
    (hvw : G.Adj v w) (hvz : G.Adj v z) (hwz : w ≠ z)
    (hS : ({u, v, w} : Finset V).val.map p ∈ F)
    (hS' : ({u, v, z} : Finset V).val.map p ∈ F) (ω : Sym2 V → Bool) {q : V × V}
    (hq : q ∈ crossSampled (marked (xCand cls u) {v, w, z} ω)
      (marked (xCand cls v) {u, w, z} ω) ω) :
    SixDistinct u v w z q.1 q.2 ∧
      hingeEdges u v w z q.1 q.2 ∈ (sampledEdges G ω).powerset.filter (fun H =>
        IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6) := by
  simp only [crossSampled, marked, mem_filter, mem_product] at hq
  obtain ⟨⟨⟨hx, hmx⟩, ⟨hy, hmy⟩⟩, hxy⟩ := hq
  obtain ⟨hxu, hcx⟩ := mem_xCand.mp hx
  obtain ⟨hyv, hcy⟩ := mem_xCand.mp hy
  have ha : G.Adj u q.2 := (hG _ _).mpr (by simpa [hcy] using (hG _ _).mp huv)
  have hb : G.Adj v q.1 := (hG _ _).mpr (by
    simpa [hcx] using ((hG _ _).mp huv).symm)
  have hc : G.Adj q.1 w := (hG _ _).mpr (by simpa [hcx] using (hG _ _).mp huw)
  have hd : G.Adj q.2 w := (hG _ _).mpr (by simpa [hcy] using (hG _ _).mp hvw)
  have he : G.Adj q.1 z := (hG _ _).mpr (by simpa [hcx] using (hG _ _).mp huz)
  have hf : G.Adj q.2 z := (hG _ _).mpr (by simpa [hcy] using (hG _ _).mp hvz)
  have hg : G.Adj q.1 q.2 := (hG _ _).mpr (by simpa [hcx, hcy] using (hG _ _).mp huv)
  have m1 := hmx v (by simp)
  have m2 := hmx w (by simp)
  have m3 := hmx z (by simp)
  have m4 := hmy u (by simp)
  have m5 := hmy w (by simp)
  have m6 := hmy z (by simp)
  rw [Sym2.eq_swap] at m2 m3 m5 m6
  have hsix : SixDistinct u v w z q.1 q.2 :=
    ⟨huv.ne, huw.ne, huz.ne, hxu.symm, ha.ne, hvw.ne, hvz.ne,
      hb.ne, hyv.symm, hwz, hc.ne.symm, hd.ne.symm, he.ne.symm, hf.ne.symm, hg.ne⟩
  refine ⟨hsix, mem_filter.mpr ⟨mem_powerset.mpr ?_,
    hingeEdges_isHinge hsix (hp _ _ hcx) (hp _ _ hcy) hS hS', card_vertSet_hingeEdges hsix⟩⟩
  intro e hee
  simp only [hingeEdges, mem_insert, mem_singleton] at hee
  simp only [sampledEdges, mem_filter, SimpleGraph.mem_edgeFinset]
  rcases hee with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨ha, m4⟩, ⟨hb, m1⟩, ⟨hc, m2⟩, ⟨hd, m5⟩, ⟨he, m3⟩, ⟨hf, m6⟩, ⟨hg, hxy⟩]

open Classical in
/-- **Hinges in the reserve from marked pairs.** -/
theorem hinge_count_of_marked {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] (cls : V → Fin 4)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (hp : ∀ a b, cls a = cls b → p a = p b)
    {u v w z : V} (huv : G.Adj u v) (huw : G.Adj u w) (huz : G.Adj u z)
    (hvw : G.Adj v w) (hvz : G.Adj v z) (hwz : w ≠ z)
    (hS : ({u, v, w} : Finset V).val.map p ∈ F)
    (hS' : ({u, v, z} : Finset V).val.map p ∈ F) (ω : Sym2 V → Bool) :
    (crossSampled (marked (xCand cls u) {v, w, z} ω) (marked (xCand cls v) {u, w, z} ω) ω).card ≤
      ((sampledEdges G ω).powerset.filter (fun H =>
        IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)).card := by
  have h := fun q (hq : q ∈ _) =>
    cross_pair_hinge (p := p) (F := F) cls hG hp huv huw huz hvw hvz hwz hS hS' ω hq
  refine card_le_card_of_injOn (fun q : V × V => hingeEdges u v w z q.1 q.2)
    (fun q hq => (h q hq).2) ?_
  intro q hq q' hq' heq
  obtain ⟨hx, hy⟩ := hingeEdges_inj (h q hq).1 (h q' hq').1 heq
  exact Prod.ext hx hy

end PartitionedTriangleAbsorption.ClassReserveStage65
