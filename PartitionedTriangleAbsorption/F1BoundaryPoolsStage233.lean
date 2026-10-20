/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1ReserveCorrectionStage231

/-! # Physical boundary pools for balance repair

The pools are constructed from graph edges between disjoint vertex sets,
after deleting the existing reserve. Their size follows from rooted missing
neighbour and reserve-degree bounds. No pool-existence premise is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1BoundaryPoolsStage233

open Finset F1BalanceGateStage228 F1ReserveCorrectionStage231

variable {V : Type*} [DecidableEq V]

def pool (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B : Finset V) : Finset (Sym2 V) :=
  ((A ×ˢ B).filter fun xy => G.Adj xy.1 xy.2 ∧ s(xy.1, xy.2) ∉ R).image
    (fun xy => s(xy.1, xy.2))

theorem mem_pool (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B : Finset V) (e : Sym2 V) :
    e ∈ pool G R A B ↔ ∃ x ∈ A, ∃ y ∈ B, G.Adj x y ∧ s(x,y) ∉ R ∧ s(x,y) = e := by
  simp only [pool, mem_image, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨x,y⟩, ⟨⟨hx,hy⟩, hxy, hr⟩, he⟩
    exact ⟨x,hx,y,hy,hxy,hr,he⟩
  · rintro ⟨x,hx,y,hy,hxy,hr,he⟩
    exact ⟨(x,y), ⟨⟨hx,hy⟩,hxy,hr⟩,he⟩

theorem pool_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B : Finset V) (hAB : Disjoint A B) :
    (pool G R A B).card = ∑ x ∈ A, (B.filter fun y => G.Adj x y ∧ s(x,y) ∉ R).card := by
  unfold pool
  rw [card_image_iff.mpr]
  · simp only [card_eq_sum_ones, sum_filter, sum_product]
  · intro x hx y hy he
    simp only [mem_coe, mem_filter, mem_product] at hx hy
    obtain ⟨⟨hxA,_⟩,_⟩ := hx
    obtain ⟨⟨_,hyB⟩,_⟩ := hy
    rcases Sym2.eq_iff.mp he with he | he
    · exact Prod.ext he.1 he.2
    · exact False.elim ((disjoint_left.mp hAB) hxA (he.1.symm ▸ hyB))

theorem reserved_neighbours_le (R : Finset (Sym2 V)) (B : Finset V) (x : V) :
    (B.filter fun y => s(x,y) ∈ R).card ≤ (R.filter fun e => x ∈ e).card := by
  apply card_le_card_of_injOn (fun y => s(x,y))
  · intro y hy
    exact mem_filter.mpr ⟨(mem_filter.mp hy).2, Sym2.mem_mk_left _ _⟩
  · intro y _ z _ he
    exact Sym2.congr_right.mp he

theorem pool_card_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B : Finset V) (hAB : Disjoint A B)
    (d r : ℝ)
    (hmiss : ∀ x ∈ A, ((B.filter fun y => ¬ G.Adj x y).card : ℝ) ≤ d)
    (hres : ∀ x ∈ A, ((R.filter fun e => x ∈ e).card : ℝ) ≤ r) :
    (A.card : ℝ) * (B.card - d - r) ≤ (pool G R A B).card := by
  have hrow : ∀ x ∈ A, (B.card : ℝ) - d - r ≤
      (B.filter fun y => G.Adj x y ∧ s(x,y) ∉ R).card := by
    intro x hx
    have hbad : B.filter (fun y => ¬ (G.Adj x y ∧ s(x,y) ∉ R)) ⊆
        (B.filter fun y => ¬ G.Adj x y) ∪ (B.filter fun y => s(x,y) ∈ R) := by
      intro y hy
      simp only [mem_filter, mem_union] at *
      tauto
    have hcount := (card_le_card hbad).trans (card_union_le _ _)
    have hcount' : ((B.filter fun y => ¬ (G.Adj x y ∧ s(x,y) ∉ R)).card : ℝ) ≤
        (B.filter fun y => ¬ G.Adj x y).card + (B.filter fun y => s(x,y) ∈ R).card := by
      exact_mod_cast hcount
    have hr' : ((B.filter fun y => s(x,y) ∈ R).card : ℝ) ≤ r :=
      (by exact_mod_cast reserved_neighbours_le R B x :
        ((B.filter fun y => s(x,y) ∈ R).card : ℝ) ≤
        (R.filter fun e => x ∈ e).card).trans (hres x hx)
    have hsplit : ((B.filter fun y => G.Adj x y ∧ s(x,y) ∉ R).card : ℝ) +
        (B.filter fun y => ¬ (G.Adj x y ∧ s(x,y) ∉ R)).card = B.card := by
      exact_mod_cast card_filter_add_card_filter_not (s := B)
        (fun y => G.Adj x y ∧ s(x,y) ∉ R)
    linarith [hmiss x hx]
  rw [pool_card G R A B hAB, Nat.cast_sum]
  simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hrow

theorem pool_charge (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B : Finset V) (label : V → Fin 4)
    (i j : Fin 4) (hA : ∀ x ∈ A, label x = i) (hB : ∀ y ∈ B, label y = j) :
    ∀ e ∈ pool G R A B, charge label e = (pairCharge i j : ℝ) := by
  intro e he
  obtain ⟨x,hx,y,hy,_,_,rfl⟩ := (mem_pool G R A B e).mp he
  simp only [charge, Sym2.lift_mk, hA x hx, hB y hy]

theorem pool_supported (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B W : Finset V) (hA : A ⊆ W) (hB : B ⊆ W) :
    ∀ e ∈ pool G R A B, ∀ v ∈ e, v ∈ W := by
  intro e he v hv
  obtain ⟨x,hx,y,hy,_,_,rfl⟩ := (mem_pool G R A B e).mp he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact hA hx
  · exact hB hy

theorem supported_degree_le (W : Finset V) (E : Finset (Sym2 V))
    (hs : ∀ e ∈ E, ∀ v ∈ e, v ∈ W) (v : V) :
    (E.filter fun e => v ∈ e).card ≤ W.card := by
  have hsub : E.filter (fun e => v ∈ e) ⊆ W.image (fun w => s(v,w)) := by
    intro e he
    obtain ⟨heE, hv⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ x y =>
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact mem_image.mpr ⟨y, hs _ heE y (Sym2.mem_mk_right _ _), rfl⟩
      · exact mem_image.mpr ⟨x, hs _ heE x (Sym2.mem_mk_left _ _), Sym2.eq_swap⟩
  exact (card_le_card hsub).trans card_image_le

theorem pool_available [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Sym2 V)) (A B U : Finset V) (hA : Disjoint A U) :
    pool G R A B ⊆ (G.edgeFinset \ (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U)) \ R := by
  intro e he
  obtain ⟨x,hx,y,_,hxy,hr,rfl⟩ := (mem_pool G R A B e).mp he
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hxy, ?_⟩,hr⟩
  intro hi
  exact disjoint_left.mp hA hx ((mem_filter.mp hi).2 x (Sym2.mem_mk_left _ _))

/-- Build the two pools on the actual boundary: one opposite-label block and
one own-label block. Missing edges and the existing reserve are deducted
before counting; in particular no edge of the protected child is used. -/
theorem boundary_pools_from_graph [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → Fin 4)
    (W U A : Finset V) (R : Finset (Sym2 V)) (i j : Fin 4)
    (hU : U ⊆ W) (hA : A ⊆ W \ U) (hlabel : ∀ x ∈ A, label x = i)
    (hcross : pairCharge i j = 1) (d r : ℝ)
    (hmiss : ∀ x ∈ A, ∀ k ∈ ({i,j} : Finset (Fin 4)),
      ((U.filter fun y => label y = k ∧ ¬ G.Adj x y).card : ℝ) ≤ d)
    (hres : ∀ x ∈ A, ((R.filter fun e => x ∈ e).card : ℝ) ≤ r) :
    ∃ P M : Finset (Sym2 V),
      P ∪ M ⊆ (G.edgeFinset \ (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U)) \ R ∧
      Disjoint P M ∧
      (∀ e ∈ P, charge label e = 1) ∧ (∀ e ∈ M, charge label e = -2) ∧
      (∀ e ∈ P ∪ M, ∃ x ∈ W \ U, ∃ y ∈ U, s(x,y) = e) ∧
      (A.card : ℝ) * ((U.filter fun y => label y = j).card - d - r) ≤ P.card ∧
      (A.card : ℝ) * ((U.filter fun y => label y = i).card - d - r) ≤ M.card ∧
      (∀ v, (P.filter fun e => v ∈ e).card ≤ W.card) ∧
      (∀ v, (M.filter fun e => v ∈ e).card ≤ W.card) := by
  let Bj := U.filter fun y => label y = j
  let Bi := U.filter fun y => label y = i
  let P := pool G R A Bj
  let M := pool G R A Bi
  have hAU : Disjoint A U := by
    rw [disjoint_left]
    intro x hx hxU
    exact (mem_sdiff.mp (hA hx)).2 hxU
  have hAW : A ⊆ W := hA.trans sdiff_subset
  have hBj : Bj ⊆ U := filter_subset _ _
  have hBi : Bi ⊆ U := filter_subset _ _
  have hP : ∀ e ∈ P, charge label e = 1 := by
    intro e he
    have hc := pool_charge G R A Bj label i j hlabel
      (fun y hy => (mem_filter.mp hy).2) e he
    simpa only [hcross, Int.cast_one] using hc
  have hM : ∀ e ∈ M, charge label e = -2 := by
    intro e he
    have hc := pool_charge G R A Bi label i i hlabel
      (fun y hy => (mem_filter.mp hy).2) e he
    simpa [pairCharge] using hc
  refine ⟨P, M, union_subset (pool_available G R A Bj U hAU)
    (pool_available G R A Bi U hAU), ?_, hP, hM, ?_, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro e heP heM
    linarith [hP e heP, hM e heM]
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨x,hx,y,hy,_,_,hxy⟩ := (mem_pool G R A Bj e).mp he
      exact ⟨x,hA hx,y,hBj hy,hxy⟩
    · obtain ⟨x,hx,y,hy,_,_,hxy⟩ := (mem_pool G R A Bi e).mp he
      exact ⟨x,hA hx,y,hBi hy,hxy⟩
  · apply pool_card_lower G R A Bj (hAU.mono_right hBj) d r _ hres
    intro x hx
    simpa only [Bj, filter_filter] using hmiss x hx j (by simp)
  · apply pool_card_lower G R A Bi (hAU.mono_right hBi) d r _ hres
    intro x hx
    simpa only [Bi, filter_filter] using hmiss x hx i (by simp)
  · exact supported_degree_le W P (pool_supported G R A Bj W hAW (hBj.trans hU))
  · exact supported_degree_le W M (pool_supported G R A Bi W hAW (hBi.trans hU))

end PartitionedTriangleAbsorption.F1BoundaryPoolsStage233
