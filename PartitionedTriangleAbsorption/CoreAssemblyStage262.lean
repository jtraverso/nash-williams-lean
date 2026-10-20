/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.InducedSpokeBridgeStage262

/-! Assemble every core edge and then reattach the exceptional edges.
The conclusion concerns actual physical edges, with no core-connectivity
oracle remaining in the hypotheses. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoreAssemblyStage262

open Finset TriangleFreeCoreStage260 GoodRemaindersStage261 OppositeEdgeTransportStage259

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the non-extremal triangle-free-link branch, all physical edges lie
in the same component of the opposite-edge graph. -/
theorem opposite_reachable_of_triangle_free_link (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V)
    (hsmall : 1000000 * e ≤ a * a) (hb : a * b = 400 * e)
    (hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V)
    (u v : V)
    (htri : ∀ x ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ y ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ z ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (hnot : ¬ ((1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ))) :
    ∀ p q r t, ∀ hpq : G.Adj p q, ∀ hrt : G.Adj r t,
      (oppositeEdgeGraph G).Reachable (edge G hpq) (edge G hrt) := by
  classical
  let n : ℝ := Fintype.card V
  let d : ℝ := (1 / 4 + e) * n
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  let B := univ.filter (fun x => x ∉ S ∧ a * n / 100 <
    ((S.filter (fun s => ¬ G.Adj x s)).card : ℝ))
  let R := univ \ (S ∪ B)
  have hn' : 0 < n := by dsimp [n]; exact_mod_cast hn
  obtain ⟨hB, hR, hpaths⟩ :=
    good_remainders_have_triangles G a e b ha ha1 he hn hsmall hb hdeg u v htri hnot
  change (B.card : ℝ) ≤ b * n at hB
  obtain ⟨_, hd, _, hdense, _, _, _⟩ :=
    scaled_remainder_margins a e b n ha ha1 he hn' hsmall hb
  have h3d : 3 * d < n := by
    have hbn : 0 ≤ b := by nlinarith
    dsimp [d]
    nlinarith
  obtain ⟨_, hS, hgeom⟩ := triangle_free_link_geometry G d hd hdeg h3d u v htri
  have hBad : 3 * d + B.card < n := by
    dsimp [d]
    nlinarith [mul_nonneg he hn'.le]
  have hmiss (s : V) (hs : s ∈ S) :
      ((R.filter (fun x => ¬ G.Adj s x)).card : ℝ) ≤ 4 * e * n := by
    have hsub : R.filter (fun x => ¬ G.Adj s x) ⊆
        univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x) := by
      intro x hx
      obtain ⟨hxR, hxs⟩ := mem_filter.mp hx
      have hxS : x ∉ S := fun h => (mem_sdiff.mp hxR).2 (mem_union_left B h)
      exact mem_filter.mpr ⟨mem_univ x, hxS, hxs⟩
    have hc : ((R.filter (fun x => ¬ G.Adj s x)).card : ℝ) ≤
        (univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card := by
      exact_mod_cast card_le_card hsub
    have hg := (hgeom s hs).2
    dsimp [d] at hg
    change _ ≤ 4 * d - n at hg
    dsimp [d] at hg
    nlinarith
  have hRsize : d + 2 * (4 * e * n) < (R.card : ℝ) := by
    have hc := card_sdiff_add_card_eq_card (s := S ∪ B) (t := (univ : Finset V))
      (subset_univ _)
    have hc' : (R.card : ℝ) + (S ∪ B).card = n := by
      dsimp [R, n]
      exact_mod_cast hc
    have hu : ((S ∪ B).card : ℝ) ≤ S.card + B.card := by
      exact_mod_cast card_union_le S B
    have hm := (RobustTransportMarginsStage258.transport_margins
      a e b ha ha1 hsmall hb).2.2.2.2.2
    have hm' := mul_pos hm hn'
    change (S.card : ℝ) ≤ 2 * d at hS
    dsimp [d] at *
    nlinarith
  obtain ⟨p₀, hp₀, q₀, hq₀, _, _, hpq₀, _, _⟩ := hR.2.1
  let root := edge G hpq₀
  have hRR (x y : V) (hx : x ∈ R) (hy : y ∈ R) (hxy : G.Adj x y) :
      (oppositeEdgeGraph G).Reachable root (edge G hxy) := by
    obtain ⟨f, hf, hf'⟩ := good_edges_have_common_opposite G a e ha ha1 he hn
      hsmall hdeg u v p₀ q₀ x y hpq₀ hxy hp₀ hq₀ hx hy
    exact hf.reachable.trans hf'.reachable
  have hSR (s r : V) (hs : s ∈ S) (hr : r ∈ R) (hsr : G.Adj s r) :
      (oppositeEdgeGraph G).Reachable root (edge G hsr) := by
    let w : (↑(R.filter (G.Adj s)) : Set V) := ⟨r, mem_filter.mpr ⟨hr, hsr⟩⟩
    obtain ⟨x, y, z, p, _, hlen, hxy, hxz, hyz⟩ := (hpaths s hs).2.2 w
    have hsp := induced_good_path_spoke G a e ha ha1 he hn hsmall hdeg u v s
      w x y z p hlen hxy hxz hyz
    exact (hRR y.val z.val (mem_filter.mp y.property).1
      (mem_filter.mp z.property).1 hyz).trans hsp.symm
  have hSS (s t : V) (hs : s ∈ S) (ht : t ∈ S) (hst : G.Adj s t) :
      (oppositeEdgeGraph G).Reachable root (edge G hst) := by
    obtain ⟨x, hx, y, hy, hxy, hsx, hsy, htx, hty⟩ :=
      common_edge_in_remainder G d (4 * e * n) hd hdeg R s t
        (hmiss s hs) (hmiss t ht) hRsize
    exact (hRR x y hx hy hxy).trans
      (opposite_adj G hst hxy hsx hsy htx hty).symm.reachable
  have hcore (x y : V) (hx : x ∉ B) (hy : y ∉ B) (hxy : G.Adj x y) :
      (oppositeEdgeGraph G).Reachable root (edge G hxy) := by
    by_cases hxS : x ∈ S
    · by_cases hyS : y ∈ S
      · exact hSS x y hxS hyS hxy
      · exact hSR x y hxS (by simp [R, hyS, hy]) hxy
    · have hxR : x ∈ R := by simp [R, hxS, hx]
      by_cases hyS : y ∈ S
      · have hrev := hSR y x hyS hxR hxy.symm
        have heq : edge G hxy.symm = edge G hxy := by
          apply Subtype.ext
          exact Sym2.eq_swap
        rw [heq] at hrev
        exact hrev
      · exact hRR x y hxR (by simp [R, hyS, hy]) hxy
  have hall (x y : V) (hxy : G.Adj x y) :
      (oppositeEdgeGraph G).Reachable root (edge G hxy) := by
    obtain ⟨i, j, hi, hj, hij, hxi, hxj, hyi, hyj⟩ :=
      common_edge_avoiding_real G d hd hdeg B hBad x y
    exact (hcore i j hi hj hij).trans
      (opposite_adj G hxy hij hxi hxj hyi hyj).symm.reachable
  intro p q r t hpq hrt
  exact (hall p q hpq).symm.trans (hall r t hrt)

end PartitionedTriangleAbsorption.CoreAssemblyStage262

