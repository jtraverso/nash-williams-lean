/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AllLinksStage263
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Count physical opposite edges through common links and bound transport
paths. The result remains about walks, not signed certificates or absorbers. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.QuantitativeTransportStage264

open Finset TriangleFreeCoreStage260 OppositeEdgeTransportStage259

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
theorem link_edges_le_opposite_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    (G.induce (↑(univ.filter (fun x => G.Adj u x ∧ G.Adj v x)) : Set V)).edgeFinset.card ≤
      (oppositeEdgeGraph G).degree (edge G huv) := by
  classical
  let S : Set V := ↑(univ.filter (fun x => G.Adj u x ∧ G.Adj v x))
  let emb := (SimpleGraph.Embedding.induce (G := G) S).mapEdgeSet
  have hmem (f : (G.induce S).edgeSet) :
      (oppositeEdgeGraph G).Adj (edge G huv) (emb f) := by
    rcases f with ⟨f, hf⟩
    induction f using Sym2.ind with
    | _ x y =>
      exact opposite_adj G huv hf (mem_filter.mp x.property).2.1
        (mem_filter.mp y.property).2.1 (mem_filter.mp x.property).2.2
        (mem_filter.mp y.property).2.2
  let fn : (G.induce S).edgeSet → (oppositeEdgeGraph G).neighborSet (edge G huv) :=
    fun f => ⟨emb f, hmem f⟩
  have hinj : Function.Injective fn := by
    intro f g h
    exact emb.injective (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective fn hinj
  simpa only [SimpleGraph.edgeFinset_card, SimpleGraph.card_neighborSet_eq_degree] using hc

omit [DecidableEq V] in
theorem induced_edge_count_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S : Finset V) :
    (S.card : ℝ) * (S.card - q) ≤
      2 * (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (↑S : Set V)
  have hlo (x : (↑S : Set V)) : (S.card : ℝ) - q ≤ H.degree x := by
    have h := restricted_degree_lower G q hdeg S x.val
    rw [← GoodRemaindersStage261.induced_degree_eq_filter G S x] at h
    linarith
  have hsum := sum_le_sum (s := (univ : Finset (↑S : Set V))) (fun x _ => hlo x)
  have hs : (∑ x, (H.degree x : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  rw [hs] at hsum
  have hc : Fintype.card (↑S : Set V) = S.card := by simp
  rw [hc] at hsum
  exact hsum

open scoped Classical in
theorem opposite_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : ℝ) (he1 : e ≤ 1 / 1000000)
    (hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V)
    {u v : V} (huv : G.Adj u v) :
    (Fintype.card V : ℝ) ^ 2 / 20 ≤ (oppositeEdgeGraph G).degree (edge G huv) := by
  classical
  let n : ℝ := Fintype.card V
  let q := (1 / 4 + e) * n
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hlo := common_link_size_lower G q hdeg u v
  change n - 2 * q ≤ (S.card : ℝ) at hlo
  have hcount := induced_edge_count_lower G q hdeg S
  have hlink := link_edges_le_opposite_degree G huv
  have hlink' : ((G.induce (↑S : Set V)).edgeFinset.card : ℝ) ≤
      (oppositeEdgeGraph G).degree (edge G huv) := by exact_mod_cast hlink
  have hq : 0 ≤ n - 3 * q := by dsimp [q]; nlinarith
  have hprod : (n - 2 * q) * (n - 3 * q) ≤ (S.card : ℝ) * (S.card - q) := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ (S.card : ℝ) - q by linarith)
    have h₂ := mul_nonneg (show 0 ≤ n - 2 * q by linarith) (sub_nonneg.mpr hlo)
    nlinarith
  have hmargin := RobustTransportMarginsStage258.opposite_degree_margin e he1
  have hscaled := mul_nonneg (sub_nonneg.mpr hmargin) (sq_nonneg n)
  dsimp [q] at hprod hcount
  change n ^ 2 / 20 ≤ _
  nlinarith

open scoped Classical in
theorem reachable_walk_lt_thirty (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : ℝ) (he1 : e ≤ 1 / 1000000)
    (hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V)
    {f g : G.edgeSet} (hr : (oppositeEdgeGraph G).Reachable f g) :
    ∃ p : (oppositeEdgeGraph G).Walk f g, p.IsPath ∧ p.length < 30 := by
  classical
  apply GoodRemaindersStage261.reachable_short_walk (oppositeEdgeGraph G) 10 _ hr
  intro f
  have hlow : (Fintype.card V : ℝ) ^ 2 / 20 ≤ (oppositeEdgeGraph G).degree f := by
    rcases f with ⟨f, hf⟩
    induction f using Sym2.ind with
    | _ u v => exact opposite_degree_lower G e he1 hdeg hf
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hsumle := sum_le_sum (s := (univ : Finset V)) (fun x _ => (G.degree_lt_card_verts x).le)
  have hup : 2 * G.edgeFinset.card ≤ Fintype.card V * Fintype.card V := by
    simpa [hsum] using hsumle
  have hup' : 2 * (Fintype.card G.edgeSet : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    rw [← G.edgeFinset_card]
    simpa only [pow_two, Nat.cast_mul, Nat.cast_ofNat] using
      (show (2 * G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * Fintype.card V by exact_mod_cast hup)
  have : (Fintype.card G.edgeSet : ℝ) < 10 * ((oppositeEdgeGraph G).degree f + 1 : ℕ) := by
    push_cast
    linarith
  exact_mod_cast this

open scoped Classical in
/-- Quantitative transport for every pair of physical edges under the
non-extremal hypotheses, without an assumed connectivity certificate. -/
theorem nonextremal_walk_lt_thirty (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V)
    (hnot : ¬ ((1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)))
    {u v x y : V} (huv : G.Adj u v) (hxy : G.Adj x y) :
    ∃ p : (oppositeEdgeGraph G).Walk (edge G huv) (edge G hxy),
      p.IsPath ∧ p.length < 30 := by
  have he1 : e ≤ 1 / 1000000 := by nlinarith
  exact reachable_walk_lt_thirty G e he1 hdeg
    (AllLinksStage263.opposite_reachable_nonextremal G a e ha ha1 he hn hsmall
      hdeg hnot u v x y huv hxy)

end PartitionedTriangleAbsorption.QuantitativeTransportStage264
