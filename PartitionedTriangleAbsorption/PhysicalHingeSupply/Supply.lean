/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Template
public import PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour
public import PartitionedTriangleAbsorption.SignedHinge.Select
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # A physical hinge-supply producer from four-root common-neighbour richness

`hingeSupply_of_commonNbrRich`: for every `ρ > 0` there is `N` (chosen before the host)
such that every host with `N ≤ n` and `CommonNbrRich 4 p G ρ` satisfies the literal
`SignedHinge.HingeSupply p F0 G (ρ^2/4) 6`.

Construction for two actual copies sharing exactly one edge, written `S = {u,v,w}`,
`S' = {u,v,z}` (`roots_of_shared_edge`):

1. `y ∈ yCand`: part `p v`, adjacent to `u, w, z`, not one of the four roots;
2. `x ∈ xCand y`: part `p u`, adjacent to `v, w, z, y`, not one of the four roots
   (hence `x ≠ y`);
3. `H = hingeEdges u v w z x y = {uy, vx, xw, yw, xz, yz, xy} ⊆ E(G)`, a physical hinge
   (`hingeEdges_isHinge`) with `|vertSet H| = 6` (`card_vertSet_hingeEdges`);
4. distinct choices give distinct edge sets: `y` is the unique `H`-neighbour of `u` and `x`
   the unique `H`-neighbour of `v` (`hingeEdges_inj`);
5. each query has at least `ρ n - 4 ≥ ρ n / 2` answers once `ρ n ≥ 8`
   (`card_fresh_ge`), so at least `(ρ n / 2)^2 = (ρ^2/4) n^(6-4)` distinct `H`.

The count is over distinct edge subsets of `G.edgeFinset`, exactly as in `HingeSupply`;
no labelled-embedding count is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalHingeSupply

open Finset SignedHinge F0Geometric TypedApplicationLinks

universe u_V

section Support

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The support of the physical hinge is exactly its six vertices. -/
theorem vertSet_hingeEdges (u v w z x y : V) :
    vertSet (hingeEdges u v w z x y) = {u, v, w, z, x, y} := by
  ext a
  simp only [vertSet, hingeEdges, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
    exists_eq_or_imp, exists_eq_left, Sym2.mem_iff]
  tauto

/-- **Exact support order six.** -/
theorem card_vertSet_hingeEdges {u v w z x y : V} (h : SixDistinct u v w z x y) :
    (vertSet (hingeEdges u v w z x y)).card = 6 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  rw [vertSet_hingeEdges]
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

end Support

section Injectivity

variable {V : Type*} [DecidableEq V]

/-- `y` is the unique neighbour of `u` in the hinge. -/
theorem nbr_u {u v w z x y b : V} (h : SixDistinct u v w z x y) (hb : b ≠ u)
    (hm : s(u, b) ∈ hingeEdges u v w z x y) : b = y := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  simp only [hingeEdges, mem_insert, mem_singleton, Sym2.eq_iff] at hm
  rcases hm with h | h | h | h | h | h | h <;> rcases h with ⟨h', h''⟩ | ⟨h', h''⟩ <;>
    simp_all

/-- `x` is the unique neighbour of `v` in the hinge. -/
theorem nbr_v {u v w z x y b : V} (h : SixDistinct u v w z x y) (hb : b ≠ v)
    (hm : s(v, b) ∈ hingeEdges u v w z x y) : b = x := by
  obtain ⟨h1, -, -, -, -, h6, h7, h8, h9, -⟩ := h
  simp only [hingeEdges, mem_insert, mem_singleton, Sym2.eq_iff] at hm
  rcases hm with h | h | h | h | h | h | h <;> rcases h with ⟨h', h''⟩ | ⟨h', h''⟩ <;>
    simp_all

/-- **Distinct choices give distinct physical edge sets.** -/
theorem hingeEdges_inj {u v w z x y x' y' : V} (h : SixDistinct u v w z x y)
    (h' : SixDistinct u v w z x' y')
    (heq : hingeEdges u v w z x y = hingeEdges u v w z x' y') : x = x' ∧ y = y' := by
  have hy : s(u, y') ∈ hingeEdges u v w z x y := by rw [heq]; simp [hingeEdges]
  have hx : s(v, x') ∈ hingeEdges u v w z x y := by rw [heq]; simp [hingeEdges]
  exact ⟨(nbr_v h (Ne.symm h'.2.2.2.2.2.2.2.1) hx).symm,
    (nbr_u h (Ne.symm h'.2.2.2.2.1) hy).symm⟩

end Injectivity

section Roots

variable {V : Type*} [DecidableEq V]

/-- Two triangles sharing exactly one edge are `{u,v,w}` and `{u,v,z}` with four distinct
roots. -/
theorem roots_of_shared_edge {S S' : Finset V} (hS : S.card = 3) (hS' : S'.card = 3)
    (h1 : (triEdges S ∩ triEdges S').card = 1) :
    ∃ u v w z : V, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
      S = {u, v, w} ∧ S' = {u, v, z} := by
  obtain ⟨e, he⟩ := card_eq_one.mp h1
  have hmem : e ∈ triEdges S ∩ triEdges S' := by rw [he]; exact mem_singleton_self e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_inter, triEdges, mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.mk_isDiag_iff] at hmem
    obtain ⟨⟨⟨haS, hbS⟩, hab⟩, ⟨haS', hbS'⟩, -⟩ := hmem
    obtain ⟨w, hwa, hwb, rfl⟩ := third_vertex hS haS hbS hab
    obtain ⟨z, hza, hzb, rfl⟩ := third_vertex hS' haS' hbS' hab
    refine ⟨a, b, w, z, hab, Ne.symm hwa, Ne.symm hza, Ne.symm hwb, Ne.symm hzb, ?_, rfl, rfl⟩
    rintro rfl
    rw [inter_self, triEdges_three hab (Ne.symm hwa) (Ne.symm hwb)] at h1
    have : ({s(a, b), s(a, w), s(b, w)} : Finset (Sym2 V)).card = 3 := by
      rw [card_insert_of_notMem, card_pair]
      · simp [hab, hwb, Ne.symm hwa]
      · simp [hab, Ne.symm hwb, Ne.symm hwa]
    omega

end Roots

section Candidates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fresh answers to a common-neighbour query: part `i`, adjacent to all of `R`, outside `Q`. -/
def freshQuery (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)
    (i : Fin 2) (Q : Finset V) : Finset V :=
  (univ.filter fun a => p a = i ∧ ∀ r ∈ R, G.Adj r a) \ Q

/-- **Fresh query count.** With at most four roots and at most four excluded vertices,
`CommonNbrRich 4` leaves at least `ρ n - 4` fresh answers. -/
theorem card_fresh_ge {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {ρ : ℝ}
    (hG : CommonNbrRich 4 p G ρ) {R Q : Finset V} (hR : R.card ≤ 4) (hQ : Q.card ≤ 4)
    (i : Fin 2) :
    ρ * Fintype.card V - 4 ≤ ((freshQuery p G R i Q).card : ℝ) := by
  have h1 := hG R hR i
  have h2 := card_le_card_sdiff_add_card
    (s := univ.filter fun a => p a = i ∧ ∀ r ∈ R, G.Adj r a) (t := Q)
  have h3 : (((univ.filter fun a => p a = i ∧ ∀ r ∈ R, G.Adj r a).card : ℕ) : ℝ) ≤
      ((freshQuery p G R i Q).card : ℝ) + (Q.card : ℝ) := by
    unfold freshQuery; exact_mod_cast h2
  have h4 : (Q.card : ℝ) ≤ 4 := by exact_mod_cast hQ
  linarith

end Candidates

section Producer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Fixed-host producer.** If `8 ≤ ρ n` and `CommonNbrRich 4 p G ρ`, then for every type
family `F` over two parts, two actual `F`-copies sharing exactly one edge have at least
`(ρ^2/4) n^2` distinct physical hinges `H ⊆ E(G)` of exact support order `6`. -/
theorem hingeSupply_of_budget {F : Finset (Multiset (Fin 2))} {p : V → Fin 2}
    {G : SimpleGraph V} [DecidableRel G.Adj] {ρ : ℝ} (hn : 8 ≤ ρ * Fintype.card V)
    (hG : CommonNbrRich 4 p G ρ) : HingeSupply p F G (ρ ^ 2 / 4) 6 := by
  classical
  intro S S' hS hS' h1
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, rfl, rfl⟩ :=
    roots_of_shared_edge hS.1.card_eq hS'.1.card_eq h1
  refine ⟨6, mem_Icc.mpr ⟨le_rfl, le_rfl⟩, ?_⟩
  set n := Fintype.card V
  set Q : Finset V := {u, v, w, z} with hQdef
  have hQ : Q.card ≤ 4 := card_le_four
  set Y := freshQuery p G {u, w, z} (p v) Q with hYdef
  set X : V → Finset V := fun y => freshQuery p G {v, w, z, y} (p u) Q with hXdef
  set P := Y.sigma X with hPdef
  -- the counted family of physical hinges, as it appears in `HingeSupply`
  set K := G.edgeFinset.powerset.filter
    (fun H => IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6) with hKdef
  -- unpacking membership in the pair set
  have hmemP : ∀ q ∈ P, (p q.1 = p v ∧ G.Adj u q.1 ∧ G.Adj w q.1 ∧ G.Adj z q.1) ∧
      (q.1 ≠ u ∧ q.1 ≠ v ∧ q.1 ≠ w ∧ q.1 ≠ z) ∧
      (p q.2 = p u ∧ G.Adj v q.2 ∧ G.Adj w q.2 ∧ G.Adj z q.2 ∧ G.Adj q.1 q.2) ∧
      (q.2 ≠ u ∧ q.2 ≠ v ∧ q.2 ≠ w ∧ q.2 ≠ z) := by
    intro q hq
    simp only [hPdef, mem_sigma, hYdef, hXdef, freshQuery, mem_sdiff, mem_filter, mem_univ,
      true_and, hQdef, mem_insert, mem_singleton, not_or, forall_eq_or_imp,
      forall_eq] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  have hsix : ∀ q ∈ P, SixDistinct u v w z q.2 q.1 := by
    intro q hq
    obtain ⟨-, ⟨hy1, hy2, hy3, hy4⟩, ⟨-, -, -, -, hyx⟩, ⟨hx1, hx2, hx3, hx4⟩⟩ := hmemP q hq
    exact ⟨huv, huw, huz, Ne.symm hx1, Ne.symm hy1, hvw, hvz, Ne.symm hx2, Ne.symm hy2, hwz,
      Ne.symm hx3, Ne.symm hy3, Ne.symm hx4, Ne.symm hy4, (G.ne_of_adj hyx).symm⟩
  -- every pair yields a counted physical hinge
  have hmaps : ∀ q ∈ P, hingeEdges u v w z q.2 q.1 ∈ K := by
    intro q hq
    obtain ⟨⟨hpy, hyu, hyw, hyz⟩, -, ⟨hpx, hxv, hxw, hxz, hyx⟩, -⟩ := hmemP q hq
    rw [hKdef, mem_filter, mem_powerset]
    refine ⟨?_, hingeEdges_isHinge (hsix q hq) hpx hpy hS.2 hS'.2,
      card_vertSet_hingeEdges (hsix q hq)⟩
    intro e he
    simp only [hingeEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exacts [hyu, hxv, hxw.symm, hyw.symm, hxz.symm, hyz.symm, hyx.symm]
  -- distinct pairs give distinct edge sets
  have hinj : Set.InjOn (fun q : (_ : V) × V => hingeEdges u v w z q.2 q.1) P := by
    intro q hq q' hq' heq
    obtain ⟨hx, hy⟩ := hingeEdges_inj (hsix q hq) (hsix q' hq') heq
    exact Sigma.ext hy (heq_of_eq hx)
  have hPK : P.card ≤ K.card := card_le_card_of_injOn _ (fun q hq => hmaps q hq) hinj
  -- counting the pairs
  have hYc : ρ * n / 2 ≤ (Y.card : ℝ) := by
    have := card_fresh_ge hG (R := {u, w, z}) (card_le_three.trans (by norm_num)) hQ (p v)
    linarith
  have hXc : ∀ y ∈ Y, ρ * n / 2 ≤ ((X y).card : ℝ) := by
    intro y _
    have := card_fresh_ge hG (R := {v, w, z, y}) card_le_four hQ (p u)
    linarith
  have hPc : (P.card : ℝ) = ∑ y ∈ Y, ((X y).card : ℝ) := by
    rw [hPdef, card_sigma]; push_cast; rfl
  have hsum : (Y.card : ℝ) * (ρ * n / 2) ≤ ∑ y ∈ Y, ((X y).card : ℝ) := by
    have := Finset.sum_le_sum hXc
    simpa [sum_const, nsmul_eq_mul] using this
  have hfinal : ρ ^ 2 / 4 * (n : ℝ) ^ (6 - 4) ≤ (P.card : ℝ) := by
    have h0 : 0 ≤ ρ * n / 2 := by linarith
    have : (ρ * n / 2) * (ρ * n / 2) ≤ (Y.card : ℝ) * (ρ * n / 2) :=
      mul_le_mul_of_nonneg_right hYc h0
    norm_num
    nlinarith
  exact hfinal.trans (by exact_mod_cast hPK)

/-- **Physical hinge-supply producer.** For every `ρ > 0`, the threshold `N = Nat.ceil (8/ρ)`
(chosen before `V, p, G`) makes every host with `N ≤ n` and four-root common-neighbour
richness `CommonNbrRich 4 p G ρ` satisfy the literal `HingeSupply p F0 G (ρ^2/4) 6`. -/
theorem hingeSupply_of_commonNbrRich (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ (V : Type u_V) [Fintype V] [DecidableEq V] (p : V → Fin 2)
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → CommonNbrRich 4 p G ρ →
        HingeSupply p F0 G (ρ ^ 2 / 4) 6 := by
  refine ⟨Nat.ceil (8 / ρ), ?_⟩
  intro V _ _ p G _ hN hG
  apply hingeSupply_of_budget _ hG
  have h1 : 8 / ρ ≤ (Fintype.card V : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  rw [div_le_iff₀ hρ] at h1
  linarith

end Producer

end PartitionedTriangleAbsorption.PhysicalHingeSupply
