/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges

open Finset CloneSupply TypedApplicationLinks HostWalkQueries HingeCounting HingeTemplates
open PhysicalHingeSupply

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε θ : ℝ}

private theorem sixDistinct_of_fresh {u v x y a c : V}
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (ha : a ∉ ({u, v, x, y} : Finset V))
    (hc : c ∉ ({u, v, x, y, a} : Finset V)) : SixDistinct u v x y a c := by
  simp only [mem_insert, mem_singleton, not_or] at ha hc
  exact ⟨huv, hux, huy, (Ne.symm ha.1), (Ne.symm hc.1), hvx, hvy, (Ne.symm ha.2.1),
    (Ne.symm hc.2.1), hxy, (Ne.symm ha.2.2.1), (Ne.symm hc.2.2.1), (Ne.symm ha.2.2.2),
    (Ne.symm hc.2.2.2.1), (Ne.symm hc.2.2.2.2)⟩

private theorem cross_template_count (b : Budget α ε θ (Fintype.card V))
    (u v x y : V) (i : Fin 2) (k : Fin 4) (P : Finset (Σ _a : V, V))
    (hsix : ∀ z ∈ P, SixDistinct u v x y z.1 z.2)
    (hp : ∀ z ∈ P, ∀ j : Fin 6,
      p ((![u, v, x, y, z.1, z.2] : Fin 6 → V) j) = Cross.part i k j)
    (he : ∀ z ∈ P, G.Adj u z.2 ∧ G.Adj v z.1 ∧
      G.Adj z.1 x ∧ G.Adj z.2 x ∧ G.Adj z.1 y ∧ G.Adj z.2 y ∧ G.Adj z.1 z.2)
    (hP : (Fintype.card V : ℝ)^2 / 64 ≤ P.card) :
    θ / 2^30 * (Fintype.card V : ℝ)^2 ≤
      (countedHinges p F0 G {u, v, x} {u, v, y} 6).card := by
  classical
  let f : (Σ _a : V, V) → Fin 6 → V := fun z => ![u, v, x, y, z.1, z.2]
  have hfinj : ∀ z ∈ P, Function.Injective (f z) := by
    intro z hz
    exact sixMap_injective (hsix z hz)
  have hhinge : ∀ z ∈ P,
      IsHinge p F0 {u, v, x} {u, v, y} (tmplH.image (Sym2.map (f z))) := by
    intro z hz
    have ht := isHinge_image p (Cross.part i k) F0 rootS rootS' tmplH
      (f z) (hfinj z hz) (hp z hz) (Cross.hinge i k)
    simpa [rootS, rootS', f] using ht
  have hhost : ∀ z ∈ P, tmplH.image (Sym2.map (f z)) ⊆ G.edgeFinset := by
    intro z hz e hem
    obtain ⟨hu2, hv1, h1x, h2x, h1y, h2y, h12⟩ := he z hz
    simp only [tmplH, image_insert, image_singleton, Sym2.map_mk, f,
      Matrix.cons_val_zero, mem_insert, mem_singleton] at hem
    rcases hem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exacts [hu2, hv1, h1x, h2x, h1y, h2y, h12]
  refine template_count p F0 G {u, v, x} {u, v, y} 2 6 (by decide)
    tmplH Cross.support P f ![4, 5] ?_ hfinj hhinge hhost
    (θ / 2^30 * (Fintype.card V : ℝ)^2) ?_
  · intro z hz z' hz' heq
    exact Sigma.ext (congrFun heq 0) (heq_of_eq (congrFun heq 1))
  · have ht := mul_le_mul_of_nonneg_right b.theta_le
      (sq_nonneg (Fintype.card V : ℝ))
    have hn := sq_nonneg (Fintype.card V : ℝ)
    change θ / 2^30 * (Fintype.card V : ℝ)^2 * (6 : ℝ)^2 ≤ (P.card : ℝ)
    norm_num
    nlinarith only [hP, ht, hn]

theorem cross_same_count (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2)
    (u v x y : V) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (pu : p u = i) (pv : p v = other0 i) (px : p x = i) (py : p y = i) :
    θ / 2^30 * (Fintype.card V : ℝ)^2 ≤
      (countedHinges p F0 G {u, v, x} {u, v, y} 6).card := by
  classical
  let Q := freshInternal p G (other0 i) v {x, y} {u, v, x, y}
  let R : V → Finset V := fun a =>
    freshInternal p G (other0 i) a {u, x, y} {u, v, x, y, a}
  let P : Finset (Σ _a : V, V) := Q.sigma R
  have hi : i ≠ other0 i := (other0_ne i).symm
  have hq : ∀ a ∈ Q, p a = other0 i ∧ G.Adj v a ∧
      a ∉ ({u, v, x, y} : Finset V) ∧ G.Adj x a ∧ G.Adj y a := by
    intro a ha
    obtain ⟨pa, hva, hane, hadj⟩ := (freshInternal_mem p G (other0 i) v
      {x, y} {u, v, x, y} a).mp ha
    exact ⟨pa, hva, hane, hadj x (by simp), hadj y (by simp)⟩
  have hr : ∀ a c, c ∈ R a → p c = other0 i ∧ G.Adj a c ∧
      c ∉ ({u, v, x, y, a} : Finset V) ∧ G.Adj u c ∧ G.Adj x c ∧ G.Adj y c := by
    intro a c hc
    obtain ⟨pc, hac, hcne, hcadj⟩ := (freshInternal_mem p G (other0 i) a
      {u, x, y} {u, v, x, y, a} c).mp hc
    exact ⟨pc, hac, hcne, hcadj u (by simp), hcadj x (by simp), hcadj y (by simp)⟩
  apply cross_template_count b u v x y i 0 P
  · intro z hz
    obtain ⟨hzQ, hzR⟩ := mem_sigma.mp hz
    exact sixDistinct_of_fresh huv hux huy hvx hvy hxy (hq z.1 hzQ).2.2.1
      (hr z.1 z.2 hzR).2.2.1
  · intro z hz j
    obtain ⟨hzQ, hzR⟩ := mem_sigma.mp hz
    have pa := (hq z.1 hzQ).1
    have pc := (hr z.1 z.2 hzR).1
    fin_cases j <;> simp [Cross.part, pu, pv, px, py, pa, pc]
  · intro z hz
    obtain ⟨hzQ, hzR⟩ := mem_sigma.mp hz
    obtain ⟨-, hva, -, hxa, hya⟩ := hq z.1 hzQ
    obtain ⟨-, hac, -, huc, hxc, hyc⟩ := hr z.1 z.2 hzR
    exact ⟨huc, hva, hxa.symm, hxc.symm, hya.symm, hyc.symm, hac⟩
  · have hQ : (Fintype.card V : ℝ) / 8 ≤ Q.card := by
      apply b.fresh_lower h (other0 i) v {x, y} {u, v, x, y}
        (card_le_two.trans (by decide)) _ (card_le_four.trans (by decide))
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> simpa [px, py] using hi
    have hR : ∀ a ∈ Q, (Fintype.card V : ℝ) / 8 ≤ (R a).card := by
      intro a ha
      apply b.fresh_lower h (other0 i) a {u, x, y} {u, v, x, y, a}
        card_le_three _ (card_le_five.trans (by decide))
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> simpa [pu, px, py] using hi
    have hsum := sum_le_sum hR
    simp only [sum_const, nsmul_eq_mul] at hsum
    have hP : (P.card : ℝ) = ∑ a ∈ Q, ((R a).card : ℝ) := by
      simp only [P, card_sigma, Nat.cast_sum]
    have hm := mul_le_mul_of_nonneg_right hQ
      (show (0 : ℝ) ≤ (Fintype.card V : ℝ) / 8 from
        div_nonneg (Nat.cast_nonneg _) (by norm_num))
    nlinarith only [hP, hsum, hm]

theorem cross_mixed_count (b : Budget α ε θ (Fintype.card V))
    (h : HostHyp p G α ε) (i : Fin 2)
    (u v x y : V) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (pu : p u = i) (pv : p v = other0 i) (px : p x = i) (py : p y = other0 i) :
    θ / 2^30 * (Fintype.card V : ℝ)^2 ≤
      (countedHinges p F0 G {u, v, x} {u, v, y} 6).card := by
  classical
  let Q := freshInternal p G i x {v, y} {u, v, x, y}
  let R : V → Finset V := fun a =>
    freshInternal p G (other0 i) y {u, x, a} {u, v, x, y, a}
  let P : Finset (Σ _a : V, V) := Q.sigma R
  have hi : i ≠ other0 i := (other0_ne i).symm
  have hq : ∀ a ∈ Q, p a = i ∧ G.Adj x a ∧
      a ∉ ({u, v, x, y} : Finset V) ∧ G.Adj v a ∧ G.Adj y a := by
    intro a ha
    obtain ⟨pa, hxa, hane, hadj⟩ := (freshInternal_mem p G i x
      {v, y} {u, v, x, y} a).mp ha
    exact ⟨pa, hxa, hane, hadj v (by simp), hadj y (by simp)⟩
  have hr : ∀ a c, c ∈ R a → p c = other0 i ∧ G.Adj y c ∧
      c ∉ ({u, v, x, y, a} : Finset V) ∧ G.Adj u c ∧ G.Adj x c ∧ G.Adj a c := by
    intro a c hc
    obtain ⟨pc, hyc, hcne, hcadj⟩ := (freshInternal_mem p G (other0 i) y
      {u, x, a} {u, v, x, y, a} c).mp hc
    exact ⟨pc, hyc, hcne, hcadj u (by simp), hcadj x (by simp), hcadj a (by simp)⟩
  apply cross_template_count b u v x y i 2 P
  · intro z hz
    obtain ⟨hzQ, hzR⟩ := mem_sigma.mp hz
    exact sixDistinct_of_fresh huv hux huy hvx hvy hxy (hq z.1 hzQ).2.2.1
      (hr z.1 z.2 hzR).2.2.1
  · intro z hz j
    obtain ⟨hzQ, hzR⟩ := mem_sigma.mp hz
    have pa := (hq z.1 hzQ).1
    have pc := (hr z.1 z.2 hzR).1
    fin_cases j <;> simp [Cross.part, pu, pv, px, py, pa, pc]
  · intro z hz
    obtain ⟨hzQ, hzR⟩ := mem_sigma.mp hz
    obtain ⟨-, hxa, -, hva, hya⟩ := hq z.1 hzQ
    obtain ⟨-, hyc, -, huc, hxc, hac⟩ := hr z.1 z.2 hzR
    exact ⟨huc, hva, hxa.symm, hxc.symm, hya.symm, hyc.symm, hac⟩
  · have hQ : (Fintype.card V : ℝ) / 8 ≤ Q.card := by
      apply b.fresh_lower h i x {v, y} {u, v, x, y}
        (card_le_two.trans (by decide)) _ (card_le_four.trans (by decide))
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> simpa [pv, py] using other0_ne i
    have hR : ∀ a ∈ Q, (Fintype.card V : ℝ) / 8 ≤ (R a).card := by
      intro a ha
      have pa := (hq a ha).1
      apply b.fresh_lower h (other0 i) y {u, x, a} {u, v, x, y, a}
        card_le_three _ (card_le_five.trans (by decide))
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> simpa [pu, px, pa] using hi
    have hsum := sum_le_sum hR
    simp only [sum_const, nsmul_eq_mul] at hsum
    have hP : (P.card : ℝ) = ∑ a ∈ Q, ((R a).card : ℝ) := by
      simp only [P, card_sigma, Nat.cast_sum]
    have hm := mul_le_mul_of_nonneg_right hQ
      (show (0 : ℝ) ≤ (Fintype.card V : ℝ) / 8 from
        div_nonneg (Nat.cast_nonneg _) (by norm_num))
    nlinarith only [hP, hsum, hm]

#print axioms cross_same_count
#print axioms cross_mixed_count

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHinges
