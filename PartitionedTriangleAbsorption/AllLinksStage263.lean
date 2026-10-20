/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoreAssemblyStage262
public import PartitionedTriangleAbsorption.LinkTransportStage259

/-! Complete the triangle-containing-link branch and combine both branches.
This proves physical reachability, not bounded diameter or absorption. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.AllLinksStage263

open Finset TriangleFreeCoreStage260 OppositeEdgeTransportStage259

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem common_link_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hm : 7 * q < 2 * Fintype.card V) (u v : V)
    (w : G.commonNeighbors u v) :
    Fintype.card (G.commonNeighbors u v) <
      3 * (G.induce (G.commonNeighbors u v)).degree w := by
  classical
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hS : (↑S : Set V) = G.commonNeighbors u v := by
    ext x
    simp [S, SimpleGraph.commonNeighbors]
  have hc : Fintype.card (G.commonNeighbors u v) = S.card := by
    calc
      _ = Fintype.card (↑S : Set V) :=
        Fintype.card_congr (Equiv.cast (congrArg (fun A : Set V => ↥A) hS.symm))
      _ = S.card := by simp
  have hd : (G.induce (G.commonNeighbors u v)).degree w =
      (S.filter (G.Adj w.val)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine card_bij (fun y _ => y.val) ?_ ?_ ?_
    · intro y hy
      exact mem_filter.mpr ⟨by
        simp only [S, mem_filter, mem_univ, true_and]
        exact (G.mem_commonNeighbors).mp y.property,
        ((G.induce (G.commonNeighbors u v)).mem_neighborFinset w y).mp hy⟩
    · intro y _ z _ hyz
      exact Subtype.ext hyz
    · intro y hy
      obtain ⟨hyS, hwy⟩ := mem_filter.mp hy
      let z : G.commonNeighbors u v := ⟨y, (mem_filter.mp hyS).2⟩
      exact ⟨z, ((G.induce (G.commonNeighbors u v)).mem_neighborFinset w z).mpr hwy, rfl⟩
  have hlo := common_link_size_lower G q hdeg u v
  have hres := restricted_degree_lower G q hdeg S w.val
  change (Fintype.card V : ℝ) - 2 * q ≤ S.card at hlo
  rw [hc, hd]
  have : (S.card : ℝ) < 3 * (S.filter (G.Adj w.val)).card := by linarith
  exact_mod_cast this

omit [DecidableEq V] in
theorem common_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hm : 3 * q < Fintype.card V) (u v w : V) :
    ∃ z, G.Adj u z ∧ G.Adj v z ∧ G.Adj w z := by
  classical
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hlo := common_link_size_lower G q hdeg u v
  have hres := restricted_degree_lower G q hdeg S w
  change (Fintype.card V : ℝ) - 2 * q ≤ S.card at hlo
  have hp : 0 < (S.filter (G.Adj w)).card := by
    have : (0 : ℝ) < (S.filter (G.Adj w)).card := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := card_pos.mp hp
  obtain ⟨hzS, hwz⟩ := mem_filter.mp hz
  exact ⟨z, (mem_filter.mp hzS).2.1, (mem_filter.mp hzS).2.2, hwz⟩

theorem incident_reachable (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hm : 7 * q < 2 * Fintype.card V)
    (htri : ∀ u v, ∃ a b c : G.commonNeighbors u v,
      G.Adj a.val b.val ∧ G.Adj a.val c.val ∧ G.Adj b.val c.val)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) :
    (oppositeEdgeGraph G).Reachable (edge G huv) (edge G huw) := by
  have h3 : 3 * q < (Fintype.card V : ℝ) := by linarith
  obtain ⟨z, huz, hvz, hwz⟩ := common_three G q hdeg h3 u v w
  have hv := spokes_of_link_triangle G huv (common_link_degree G q hdeg hm u v)
    (htri u v) ⟨z, huz, hvz⟩
  have hw := spokes_of_link_triangle G huw (common_link_degree G q hdeg hm u w)
    (htri u w) ⟨z, huz, hwz⟩
  exact hv.1.trans hw.1.symm

theorem opposite_reachable_of_all_links (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hm : 7 * q < 2 * Fintype.card V)
    (htri : ∀ u v, ∃ a b c : G.commonNeighbors u v,
      G.Adj a.val b.val ∧ G.Adj a.val c.val ∧ G.Adj b.val c.val) :
    ∀ p s r t, ∀ hps : G.Adj p s, ∀ hrt : G.Adj r t,
      (oppositeEdgeGraph G).Reachable (edge G hps) (edge G hrt) := by
  intro p s r t hps hrt
  have h3 : 3 * q < (Fintype.card V : ℝ) := by linarith
  obtain ⟨z, hpz, hrz, _⟩ := common_three G q hdeg h3 p r p
  have h₁ := incident_reachable G q hq hdeg hm htri hps hpz
  have h₂ := incident_reachable G q hq hdeg hm htri hpz.symm hrz.symm
  have h₃ := incident_reachable G q hq hdeg hm htri hrz hrt
  have hp : edge G hpz.symm = edge G hpz := Subtype.ext Sym2.eq_swap
  have hr : edge G hrz.symm = edge G hrz := Subtype.ext Sym2.eq_swap
  rw [hp, hr] at h₂
  exact h₁.trans (h₂.trans h₃)

/-- Both link branches, with the non-extremality and degree assumptions of
the robust transport route. No connectivity hypothesis remains. -/
theorem opposite_reachable_nonextremal (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V)
    (hnot : ¬ ((1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ))) :
    ∀ p q r t, ∀ hpq : G.Adj p q, ∀ hrt : G.Adj r t,
      (oppositeEdgeGraph G).Reachable (edge G hpq) (edge G hrt) := by
  classical
  by_cases hall : ∀ u v, ∃ x y z : G.commonNeighbors u v,
      G.Adj x.val y.val ∧ G.Adj x.val z.val ∧ G.Adj y.val z.val
  · have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    have he1 : e ≤ 1 / 1000000 := by nlinarith
    apply opposite_reachable_of_all_links G ((1 / 4 + e) * Fintype.card V)
      (mul_nonneg (by linarith) hn'.le) hdeg
    · nlinarith
    · exact hall
  · push Not at hall
    obtain ⟨u, v, huv⟩ := hall
    apply CoreAssemblyStage262.opposite_reachable_of_triangle_free_link
      G a e (400 * e / a) ha ha1 he hn hsmall
      (by rw [mul_comm a, div_mul_cancel₀ _ ha.ne']) hdeg u v
    · intro x hx y hy z hz hxy hxz hyz
      exact huv ⟨x, (mem_filter.mp hx).2⟩ ⟨y, (mem_filter.mp hy).2⟩
        ⟨z, (mem_filter.mp hz).2⟩ hxy hxz hyz
    · exact hnot

end PartitionedTriangleAbsorption.AllLinksStage263
