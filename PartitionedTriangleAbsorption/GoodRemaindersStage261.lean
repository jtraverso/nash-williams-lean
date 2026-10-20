/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.NonextremalCoreStage260
public import PartitionedTriangleAbsorption.GoodRemainderMarginsStage261
public import PartitionedTriangleAbsorption.InducedTrianglePathsStage261

/-! Produce triangles in R_good and in R_good intersect N(s), from the
original non-extremality and degree assumptions. The exceptional set is
defined by missing-neighbor counts; it is not supplied by an oracle. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset TriangleFreeCoreStage260

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting B and then restricting to N(s) costs at most |B| plus the
number of non-neighbors of s outside S. This counts actual deleted vertices. -/
theorem good_remainder_deletion_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (S B : Finset V) (s : V) :
    let R := univ \ (S ∪ B)
    Disjoint S R ∧
    (univ \ (S ∪ R)).card ≤ B.card ∧
    Disjoint S (R.filter (G.Adj s)) ∧
    (univ \ (S ∪ R.filter (G.Adj s))).card ≤
      B.card + (univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card := by
  classical
  let R := univ \ (S ∪ B)
  have hdis : Disjoint S R := by
    rw [disjoint_left]
    intro x hxS hxR
    exact (mem_sdiff.mp hxR).2 (mem_union_left B hxS)
  have hsub : univ \ (S ∪ R) ⊆ B := by
    intro x hx
    have hn := (mem_sdiff.mp hx).2
    by_contra hxB
    have hxS : x ∉ S := fun h => hn (mem_union_left R h)
    exact hn (mem_union_right S (mem_sdiff.mpr ⟨mem_univ x, by simp [hxS, hxB]⟩))
  have hsub' : univ \ (S ∪ R.filter (G.Adj s)) ⊆
      B ∪ univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x) := by
    intro x hx
    have hn := (mem_sdiff.mp hx).2
    by_cases hxB : x ∈ B
    · exact mem_union_left _ hxB
    · have hxS : x ∉ S := fun h => hn (mem_union_left _ h)
      have hxR : x ∈ R := mem_sdiff.mpr ⟨mem_univ x, by simp [hxS, hxB]⟩
      refine mem_union_right B (mem_filter.mpr ⟨mem_univ x, hxS, ?_⟩)
      intro hadj
      exact hn (mem_union_right S (mem_filter.mpr ⟨hxR, hadj⟩))
  refine ⟨hdis, card_le_card hsub, ?_, (card_le_card hsub').trans (card_union_le _ _)⟩
  exact hdis.mono_right (filter_subset _ _)

/-- The two complementary triangle producers required by the transport
proof, with every numerical premise discharged from the original hierarchy. -/
theorem good_remainders_have_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
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
    let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
    let B := univ.filter (fun x => x ∉ S ∧ a * Fintype.card V / 100 <
      ((S.filter (fun s => ¬ G.Adj x s)).card : ℝ))
    let R := univ \ (S ∪ B)
    (B.card : ℝ) ≤ b * Fintype.card V ∧
      (3 * ((1 / 4 + e) * Fintype.card V) < 2 * (R.card : ℝ) ∧
        (∃ x ∈ R, ∃ y ∈ R, ∃ z ∈ R, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∧
        ∀ w : (↑R : Set V), ∃ x y z : (↑R : Set V),
          ∃ p : (G.induce (↑R : Set V)).Walk w x,
            p.IsPath ∧ p.length ≤ 14 ∧ G.Adj x.val y.val ∧ G.Adj x.val z.val ∧ G.Adj y.val z.val) ∧
      ∀ s ∈ S,
        3 * ((1 / 4 + e) * Fintype.card V) < 2 * ((R.filter (G.Adj s)).card : ℝ) ∧
        (∃ x ∈ R.filter (G.Adj s), ∃ y ∈ R.filter (G.Adj s),
          ∃ z ∈ R.filter (G.Adj s), G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∧
        ∀ w : (↑(R.filter (G.Adj s)) : Set V),
          ∃ x y z : (↑(R.filter (G.Adj s)) : Set V),
            ∃ p : (G.induce (↑(R.filter (G.Adj s)) : Set V)).Walk w x,
              p.IsPath ∧ p.length ≤ 14 ∧
                G.Adj x.val y.val ∧ G.Adj x.val z.val ∧ G.Adj y.val z.val := by
  classical
  let n : ℝ := Fintype.card V
  let q : ℝ := (1 / 4 + e) * n
  let d : ℝ := (b + 4 * e) * n
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  let B := univ.filter (fun x => x ∉ S ∧ a * n / 100 <
    ((S.filter (fun s => ¬ G.Adj x s)).card : ℝ))
  let R := univ \ (S ∪ B)
  have hn' : 0 < n := by dsimp [n]; exact_mod_cast hn
  obtain ⟨_, hq, hd, hdense, hlow, hcover, hcut⟩ :=
    scaled_remainder_margins a e b n ha ha1 he hn' hsmall hb
  have hdense' : 3 * q < n := by dsimp [q]; linarith
  obtain ⟨_, hScard, hgeom⟩ := triangle_free_link_geometry G q hq hdeg hdense' u v htri
  have hmiss : ∀ s ∈ S,
      ((univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card : ℝ) ≤ 4 * e * n := by
    intro s hs
    have := (hgeom s hs).2
    dsimp [q] at this
    dsimp [n]
    nlinarith
  have hB : (B.card : ℝ) ≤ b * n := by
    have hcount := exceptional_set_bound G S (a * n / 100) (4 * e * n) hmiss
    have hS : (S.card : ℝ) ≤ n := by dsimp [n]; exact_mod_cast card_le_univ (s := S)
    exact exceptional_budget a e b n S.card B.card ha hn' he hb hS hcount
  have hen : 0 ≤ e * n := mul_nonneg he hn'.le
  have hB' : (B.card : ℝ) ≤ d := by dsimp [d]; nlinarith
  have hget (J : Finset V) (hdis : Disjoint S J)
      (hremoved : ((univ \ (S ∪ J)).card : ℝ) ≤ d) :
      3 * q < 2 * (J.card : ℝ) ∧
        (∃ x ∈ J, ∃ y ∈ J, ∃ z ∈ J, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∧
        ∀ w : (↑J : Set V), ∃ x y z : (↑J : Set V),
          ∃ p : (G.induce (↑J : Set V)).Walk w x,
            p.IsPath ∧ p.length ≤ 14 ∧
              G.Adj x.val y.val ∧ G.Adj x.val z.val ∧ G.Adj y.val z.val := by
    have htriangle := triangle_in_survivor_of_small_deletion G a q d hq hd hdeg hdense u v
      htri hnot hcut hlow hcover J hdis hremoved
    have hc := card_sdiff_add_card_eq_card (s := S ∪ J) (t := (univ : Finset V)) (subset_univ _)
    rw [card_union_of_disjoint hdis] at hc
    have hc' : ((univ \ (S ∪ J)).card : ℝ) + ((S.card : ℝ) + J.card) = n := by
      dsimp [n]
      exact_mod_cast hc
    have hm := (RobustTransportMarginsStage258.transport_margins a e b ha ha1 hsmall hb).2.2.1
    have hm' := mul_lt_mul_of_pos_right hm hn'
    have hsize : 3 * q < 2 * (J.card : ℝ) := by
      change (S.card : ℝ) ≤ 2 * q at hScard
      dsimp [q, d] at *
      nlinarith
    exact ⟨hsize, htriangle, fun w => induced_short_path_to_triangle G q hdeg J hsize htriangle w⟩
  refine ⟨hB, ?_, ?_⟩
  · obtain ⟨hdis, hremoved, _, _⟩ := good_remainder_deletion_bounds G S B u
    exact hget R hdis ((by exact_mod_cast hremoved :
      ((univ \ (S ∪ R)).card : ℝ) ≤ B.card).trans hB')
  · intro s hs
    obtain ⟨_, _, hdis, hremoved⟩ := good_remainder_deletion_bounds G S B s
    apply hget (R.filter (G.Adj s)) hdis
    have hremoved' : ((univ \ (S ∪ R.filter (G.Adj s))).card : ℝ) ≤
        B.card + (univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card := by
      exact_mod_cast hremoved
    have := hmiss s hs
    dsimp [d]
    nlinarith

end PartitionedTriangleAbsorption.GoodRemaindersStage261
