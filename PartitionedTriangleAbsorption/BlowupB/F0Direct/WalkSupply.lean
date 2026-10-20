/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkCounts

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkSupply

open Finset

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

def HalfRegular (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (θ : ℝ) : Prop :=
  ∀ u ∈ D,
    (1 / 2 - θ) * D.card ≤ ((neighbors G D u).card : ℝ) ∧
    ((neighbors G D u).card : ℝ) ≤ (1 / 2 + θ) * D.card

theorem intersection_dichotomy (m θ w : ℝ) (hm : 0 < m)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 100) (hw : 0 ≤ w)
    (hq : w * ((1 / 2 - 3 * θ) * m - w) ≤ 2 * θ * m^2) :
    w ≤ 16 * θ * m ∨ (1 / 2 - 11 * θ) * m ≤ w := by
  have hθm := mul_le_mul_of_nonneg_right hθ1 hm.le
  by_cases hwm : w ≤ m / 4
  · left
    have hbracket : m / 8 ≤ (1 / 2 - 3 * θ) * m - w := by linarith
    have hmul := mul_le_mul_of_nonneg_left hbracket hw
    nlinarith
  · right
    have hwm' : m / 4 ≤ w := by linarith
    by_cases hb : (1 / 2 - 3 * θ) * m - w ≤ 0
    · have htm : 0 ≤ θ * m := mul_nonneg hθ0 hm.le
      linarith
    · have hmul := mul_le_mul_of_nonneg_right hwm' (le_of_not_ge hb)
      nlinarith

theorem complement_union_card_bound {D U W : Finset V} (hU : U ⊆ D) (hW : W ⊆ D)
    (θ : ℝ) (hUlo : (1 / 2 - θ) * D.card ≤ (U.card : ℝ))
    (hWlo : (1 / 2 - θ) * D.card ≤ (W.card : ℝ)) :
    ((D \ (U ∪ W)).card : ℝ) ≤ 2 * θ * D.card + (U ∩ W).card := by
  have h1 := card_sdiff_add_card_eq_card (union_subset hU hW)
  have h2 := card_union_add_card_inter U W
  have h1' := congrArg (fun k : ℕ => (k : ℝ)) h1
  have h2' := congrArg (fun k : ℕ => (k : ℝ)) h2
  push_cast at h1' h2'
  linarith

theorem sparse_arcs_intersection (G : SimpleGraph V) [DecidableRel G.Adj]
    {D U W : Finset V} (hU : U ⊆ D) (hW : W ⊆ D)
    (θ : ℝ) (hm : 0 < (D.card : ℝ)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 100)
    (hdeg : ∀ u ∈ D, (1 / 2 - θ) * D.card ≤ ((neighbors G D u).card : ℝ))
    (hUlo : (1 / 2 - θ) * D.card ≤ (U.card : ℝ))
    (hWlo : (1 / 2 - θ) * D.card ≤ (W.card : ℝ))
    (hc : arcs G U W ≤ θ * (D.card : ℝ)^2) :
    ((U ∩ W).card : ℝ) ≤ 16 * θ * D.card ∨
      (1 / 2 - 11 * θ) * D.card ≤ ((U ∩ W).card : ℝ) := by
  have ht := complement_union_card_bound hU hW θ hUlo hWlo
  have hl := arcs_degree_lower G (show U ∩ W ⊆ D from inter_subset_left.trans hU)
    ((1 / 2 - θ) * D.card) hdeg
  have hcover : D ⊆ ((D \ (U ∪ W)) ∪ U) ∪ W := by
    intro u hu
    by_cases h1 : u ∈ U <;> by_cases h2 : u ∈ W <;> simp [hu, h1, h2]
  have h0 := arcs_mono G (Subset.refl (U ∩ W)) hcover
  have h1 := arcs_union_right_le G (U ∩ W) ((D \ (U ∪ W)) ∪ U) W
  have h2 := arcs_union_right_le G (U ∩ W) (D \ (U ∪ W)) U
  have h3 := arcs_le_mul G (U ∩ W) (D \ (U ∪ W))
  have h4 : arcs G (U ∩ W) U ≤ arcs G U W := by
    rw [arcs_symm G (U ∩ W) U]
    exact arcs_mono G (Subset.refl U) inter_subset_right
  have h5 : arcs G (U ∩ W) W ≤ arcs G U W :=
    arcs_mono G inter_subset_left (Subset.refl W)
  have ht' := mul_le_mul_of_nonneg_left ht
    (show (0 : ℝ) ≤ (U ∩ W).card by positivity)
  have hq : ((U ∩ W).card : ℝ) *
      ((1 / 2 - 3 * θ) * D.card - (U ∩ W).card) ≤ 2 * θ * (D.card : ℝ)^2 := by
    nlinarith only [hl, h0, h1, h2, h3, h4, h5, ht', hc]
  exact intersection_dichotomy _ θ _ hm hθ0 hθ1 (Nat.cast_nonneg _) hq

/-- A deficit of length-three walks forces one of the two forbidden balanced models. -/
theorem sparse_arcs_near_model (G : SimpleGraph V) [DecidableRel G.Adj]
    {D U W : Finset V} (hU : U ⊆ D) (hW : W ⊆ D)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hm : (1 : ℝ) ≤ θ * D.card) (hreg : HalfRegular G D θ)
    (hUlo : (1 / 2 - θ) * D.card ≤ (U.card : ℝ))
    (hUhi : (U.card : ℝ) ≤ (1 / 2 + θ) * D.card)
    (hWlo : (1 / 2 - θ) * D.card ≤ (W.card : ℝ))
    (hc : arcs G U W ≤ θ * (D.card : ℝ)^2) :
    ∃ X ⊆ D, X.card = D.card / 2 ∧
      ((editDistance (inducedEdges G D) (cliqueModel D X) : ℝ) ≤ 80 * θ * (D.card : ℝ)^2 ∨
       (editDistance (inducedEdges G D) (bipartiteModel D X) : ℝ) ≤ 80 * θ * (D.card : ℝ)^2) := by
  have hm0 : 0 < (D.card : ℝ) := by
    by_contra h
    have h' := mul_nonpos_of_nonneg_of_nonpos hθ0.le (le_of_not_gt h)
    linarith
  have hm1 : (1 : ℝ) ≤ D.card := by
    have ht := mul_le_mul_of_nonneg_right hθ1 hm0.le
    linarith
  have hmlarge : (D.card : ℝ) ≤ θ * (D.card : ℝ)^2 := by
    have ht := mul_le_mul_of_nonneg_right hm hm0.le
    nlinarith
  have hdeglo := fun u hu => (hreg u hu).1
  have hdeghi := fun u hu => (hreg u hu).2
  obtain ⟨X, hX, hbal, hgap⟩ := balanced_close hU (θ * D.card) (by linarith) (by linarith)
  refine ⟨X, hX, hbal, ?_⟩
  have hmodels := model_card_bounds hX hbal hm1
  have hdist := cut_distance_identities G hX
  have hE := arcs_self_eq_twice_induced G D
  have hElow := arcs_degree_lower G (Subset.refl D) ((1 / 2 - θ) * D.card) hdeglo
  have hEup := arcs_degree_upper G (Subset.refl D) ((1 / 2 + θ) * D.card) hdeghi
  have hsd0 : (0 : ℝ) ≤ (U \ X).card := Nat.cast_nonneg _
  have hgap_one : ((X \ U).card : ℝ) ≤ θ * D.card + 1 := by linarith
  rcases sparse_arcs_intersection G hU hW θ hm0 hθ0.le hθ1 hdeglo hUlo hWlo hc with hsmall | hlarge
  · left
    have ht := complement_union_card_bound hU hW θ hUlo hWlo
    have hsub : (D \ X) \ W ⊆ (D \ (U ∪ W)) ∪ (U \ X) := by
      intro u hu
      obtain ⟨huDX, huW⟩ := mem_sdiff.mp hu
      obtain ⟨huD, huX⟩ := mem_sdiff.mp huDX
      by_cases huU : u ∈ U <;> simp [huD, huX, huW, huU]
    have hcount : (((D \ X) \ W).card : ℝ) ≤
        (D \ (U ∪ W)).card + (U \ X).card := by
      have hh := (card_le_card hsub).trans (card_union_le _ _)
      exact_mod_cast hh
    have hextra : ((X \ U).card : ℝ) + ((D \ X) \ W).card ≤ 19 * θ * D.card + 1 := by
      linarith
    have ha := arcs_perturb G hX (show D \ X ⊆ D from sdiff_subset) hU hW
    have hextram := mul_le_mul_of_nonneg_right hextra hm0.le
    have hcross : arcs G X (D \ X) ≤ 20 * θ * (D.card : ℝ)^2 + D.card := by
      nlinarith only [ha, hc, hextram]
    nlinarith only [hdist.1, hmodels.1, hE, hElow, hcross, hmlarge,
      mul_nonneg hθ0.le (sq_nonneg (D.card : ℝ))]
  · right
    have hcw := card_sdiff_add_card_inter U W
    have hcw' := congrArg (fun k : ℕ => (k : ℝ)) hcw
    push_cast at hcw'
    have hmiss : ((U \ W).card : ℝ) ≤ 12 * θ * D.card := by linarith
    have haUU := arcs_perturb G hU hU hU hW
    simp only [Finset.sdiff_self, card_empty, Nat.cast_zero, zero_add] at haUU
    have hmissm := mul_le_mul_of_nonneg_right hmiss hm0.le
    have hUU : arcs G U U ≤ 13 * θ * (D.card : ℝ)^2 := by
      nlinarith only [haUU, hc, hmissm]
    have haXX := arcs_perturb G hX hX hU hU
    have hgapm := mul_le_mul_of_nonneg_right hgap_one hm0.le
    have hXX : arcs G X X ≤ 15 * θ * (D.card : ℝ)^2 + 2 * D.card := by
      nlinarith only [haXX, hUU, hgapm]
    have hXlo : (D.card : ℝ) / 2 - 1 ≤ X.card := by
      have hn : D.card ≤ 2 * X.card + 1 := by omega
      have hn' := (Nat.cast_le (α := ℝ)).mpr hn
      push_cast at hn'
      linarith
    have hd0 : 0 ≤ (1 / 2 - θ) * (D.card : ℝ) := by
      apply mul_nonneg _ hm0.le
      linarith
    have hxmul := mul_le_mul_of_nonneg_right hXlo hd0
    have hXD := arcs_degree_lower G hX ((1 / 2 - θ) * D.card) hdeglo
    have hsplit := arcs_disjoint_union_right G X X (D \ X) disjoint_sdiff_self_right
    rw [union_sdiff_of_subset hX] at hsplit
    have hcross : (D.card : ℝ)^2 / 4 - θ * (D.card : ℝ)^2 / 2 - D.card / 2 -
        arcs G X X ≤ arcs G X (D \ X) := by
      nlinarith only [hxmul, hXD, hsplit, mul_nonneg hθ0.le hm0.le]
    nlinarith only [hdist.2, hmodels.2, hE, hEup, hcross, hXX, hmlarge,
      mul_nonneg hθ0.le (sq_nonneg (D.card : ℝ))]

/-- Every ordered pair has many length-three walks in the nonextreme part. -/
theorem arcs_neighbors_gt (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (α θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hscale : 100 * θ ≤ α) (hm : (1 : ℝ) ≤ θ * D.card)
    (hreg : HalfRegular G D θ) (hext : Nonextreme G D α)
    {u v : V} (hu : u ∈ D) (hv : v ∈ D) :
    θ * (D.card : ℝ)^2 < arcs G (neighbors G D u) (neighbors G D v) := by
  by_contra h
  have hc := le_of_not_gt h
  obtain ⟨X, hX, hbal, hbad⟩ := sparse_arcs_near_model G
    (neighbors_subset G D u) (neighbors_subset G D v) θ hθ0 hθ1 hm hreg
    (hreg u hu).1 (hreg u hu).2 (hreg v hv).1 hc
  have he := hext X hX hbal
  have hscale' := mul_le_mul_of_nonneg_right hscale (sq_nonneg (D.card : ℝ))
  have hnonneg := mul_nonneg hθ0.le (sq_nonneg (D.card : ℝ))
  rcases hbad with hC | hB
  · nlinarith only [he.2, hC, hscale', hnonneg]
  · nlinarith only [he.1, hB, hscale', hnonneg]

theorem neighbors_sdiff_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (D S : Finset V) (u : V) : neighbors G D u \ neighbors G S u ⊆ D \ S := by
  intro v hv
  obtain ⟨hvD, hvS⟩ := mem_sdiff.mp hv
  obtain ⟨hvD, huv⟩ := (mem_neighbors G D u v).mp hvD
  apply mem_sdiff.mpr
  refine ⟨hvD, ?_⟩
  intro h
  exact hvS ((mem_neighbors G S u v).mpr ⟨h, huv⟩)

/-- Deleting a small set of vertices leaves a uniform supply of length-three walks. -/
theorem arcs_neighbors_avoiding_gt (G : SimpleGraph V) [DecidableRel G.Adj]
    (D S : Finset V) (hS : S ⊆ D) (α θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hscale : 100 * θ ≤ α) (hm : (1 : ℝ) ≤ θ * D.card)
    (hreg : HalfRegular G D θ) (hext : Nonextreme G D α)
    (hsmall : ((D \ S).card : ℝ) ≤ θ * D.card / 4)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    θ * (D.card : ℝ)^2 / 2 < arcs G (neighbors G S u) (neighbors G S v) := by
  have hmain := arcs_neighbors_gt G D α θ hθ0 hθ1 hscale hm hreg hext (hS hu) (hS hv)
  have hperturb := arcs_perturb G (neighbors_subset G D u) (neighbors_subset G D v)
    ((neighbors_subset G S u).trans hS) ((neighbors_subset G S v).trans hS)
  have hu_count : ((neighbors G D u \ neighbors G S u).card : ℝ) ≤ (D \ S).card :=
    Nat.cast_le.mpr (card_le_card (neighbors_sdiff_subset G D S u))
  have hv_count : ((neighbors G D v \ neighbors G S v).card : ℝ) ≤ (D \ S).card :=
    Nat.cast_le.mpr (card_le_card (neighbors_sdiff_subset G D S v))
  have hextra : ((neighbors G D u \ neighbors G S u).card : ℝ) +
      (neighbors G D v \ neighbors G S v).card ≤ θ * D.card / 2 := by
    linarith only [hu_count, hv_count, hsmall]
  have hextram := mul_le_mul_of_nonneg_right hextra (Nat.cast_nonneg D.card : (0 : ℝ) ≤ D.card)
  nlinarith only [hmain, hperturb, hextram]

#print axioms arcs_neighbors_gt
#print axioms arcs_neighbors_avoiding_gt

end PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkSupply
