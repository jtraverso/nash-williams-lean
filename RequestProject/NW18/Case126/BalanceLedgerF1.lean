/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.RobustWeightingF1
public import RequestProject.NW18.Case126.CrossReserveF1
public import PartitionedTriangleAbsorption.F1BalanceGateStage228
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: the signed charge ledger of the ACTUAL punctured level

Coarsen the four labels into `{0,1} | {2,3}`; an internal edge has charge `-2`, a cross edge
charge `+1` (`F1BalanceGateStage228.pairCharge`).  Every `F₁` triangle has charge `0`, so any
near-unit weighting of a host forces its balance to be nearly `0`
(`F1BalanceGateStage228.near_load_requires_balance`).

This file computes the balance of the actual punctured level `punc H W U Res` from the actual
vortex data (all proved):

* `balance_eq_zero_of_intDiv`: an integrally `F₁`-divisible edge set has balance exactly `0`
  (the charge is a linear functional vanishing on the eight `F₁` type vectors).
* `punc_balance_ledger`: if the edges of `H` inside `W` are integrally divisible, then
  `balance(punc) = - balance(child) - balance(Res)` EXACTLY, for the same sampled reserve `Res`.
* `child_balance_bound`: if the child `U` was protected (no edge of `G` inside `U` is missing
  from `H`), then `|balance(child)| ≤ (2κ + ξ) |U| |W|`.
* `reserve_balance_near`: for a jointly good reserve (`CrossResGood`, clause `r4`),
  `balance(Res)` is within `6 ε |W|²` of `ρ · balance(boundary of H)`.
* `boundary_balance_eq`: the boundary balance is the typical (`(4κ+2ξ)`-small) part MINUS the
  signed charge `bdDamCharge` of the damaged boundary edges.
* `punctured_balance_defect`: altogether
  `|balance(punc) - ρ · bdDamCharge| ≤ ((2κ+ξ) + 6ε + ρ(4κ+2ξ)) |W|²`.

So the only part of the puncture defect that is NOT paid by the fresh parameters `κ, ξ, ε` is
`ρ · bdDamCharge`: the signed charge of the damage on the boundary edges between `W \ U` and `U`.
Divisibility of `H` does not control it; it is the compatibility premise that the previous level
must deliver (see `BalancedWeightingF1.lean`).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.F1BalanceGateStage228 (pairCharge charge balance)

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Generic double counting -/

/-- Weighted handshake lemma. -/
theorem sum_edges_two (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℝ) :
    2 * ∑ e ∈ G.edgeFinset, f e = ∑ v, ∑ z ∈ univ.filter (G.Adj v), f s(v, z) := by
  have h1 : ∑ d : G.Dart, f d.edge = ∑ e ∈ G.edgeFinset, 2 * f e := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun d : G.Dart => d.edge) (t := G.edgeFinset)
      (fun d _ => by simp)]
    refine sum_congr rfl fun e he => ?_
    rw [sum_congr rfl (fun d hd => by rw [(mem_filter.mp hd).2])]
    rw [sum_const, G.dart_edge_fiber_card e (SimpleGraph.mem_edgeFinset.mp he)]
    simp
  have h2 : ∑ d : G.Dart, f d.edge = ∑ v, ∑ z ∈ univ.filter (G.Adj v), f s(v, z) := by
    rw [← Finset.sum_fiberwise (g := fun d : G.Dart => d.fst)]
    refine sum_congr rfl fun v _ => ?_
    refine Finset.sum_bij (fun d _ => d.snd) ?_ ?_ ?_ ?_
    · intro d hd; simp only [mem_filter, mem_univ, true_and] at hd ⊢; rw [← hd]; exact d.adj
    · intro d hd d' hd' h
      simp only [mem_filter, mem_univ, true_and] at hd hd'
      exact SimpleGraph.Dart.ext _ _ (Prod.ext (hd.trans hd'.symm) h)
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      exact ⟨⟨(v, z), hz⟩, by simp, rfl⟩
    · intro d hd
      have hd' : d.fst = v := (mem_filter.mp hd).2
      show f s(d.fst, d.snd) = f s(v, d.snd)
      rw [hd']
  rw [mul_sum, ← h1, h2]

omit [Fintype V] in
/-- Sum over a set of edges each joining `A` to a disjoint set `B`. -/
theorem sum_bipartite_edges (A B : Finset V) (hAB : Disjoint A B) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∃ x ∈ A, ∃ z ∈ B, e = s(x, z)) (g : Sym2 V → ℝ) :
    ∑ e ∈ E, g e = ∑ x ∈ A, ∑ z ∈ B.filter (fun z => s(x, z) ∈ E), g s(x, z) := by
  symm
  rw [show (∑ x ∈ A, ∑ z ∈ B.filter (fun z => s(x, z) ∈ E), g s(x, z)) =
      ∑ xz ∈ (A ×ˢ B).filter (fun xz => s(xz.1, xz.2) ∈ E), g s(xz.1, xz.2) by
    rw [sum_filter, sum_product]
    exact sum_congr rfl fun x _ => by rw [sum_filter]]
  refine Finset.sum_bij (fun xz _ => s(xz.1, xz.2)) ?_ ?_ ?_ ?_
  · intro xz h; exact (mem_filter.mp h).2
  · intro a ha b hb hab
    obtain ⟨⟨ha1, ha2⟩, -⟩ := (mem_filter.mp ha).imp_left mem_product.mp
    obtain ⟨⟨hb1, hb2⟩, -⟩ := (mem_filter.mp hb).imp_left mem_product.mp
    rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ ha1) (disjoint_left.mp hAB.symm hb2)
  · intro e he
    obtain ⟨x, hx, z, hz, rfl⟩ := hE e he
    exact ⟨(x, z), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hz⟩, he⟩, rfl⟩
  · intro _ _; rfl

/-! ### Charge versus the edge vector, and divisibility -/

omit [Fintype V] [DecidableEq V] in
theorem charge_mk (p : V → Fin 4) (a b : V) : charge p s(a, b) = (pairCharge (p a) (p b) : ℝ) := by
  simp [charge]

omit [Fintype V] [DecidableEq V] in
/-- Twice the charge of an edge is the charge pairing of its (ordered) pair vector. -/
theorem two_charge_eq (p : V → Fin 4) (e : Sym2 V) :
    2 * charge p e = ((∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * pairVec p e i j : ℤ) : ℝ) := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [charge_mk]
    have : (∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * pairVec p s(a, b) i j) =
        pairCharge (p a) (p b) + pairCharge (p b) (p a) := by
      simp only [pairVec, Sym2.lift_mk, mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero,
        ite_and]
      simp [sum_ite_eq]
    rw [this, F1BalanceGateStage228.pairCharge_symm (p b) (p a)]
    push_cast; ring

/-- Every `F₁` type vector has charge pairing `0`. -/
theorem type_charge_zero : ∀ τ ∈ F1,
    ∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * typeEdgeVec τ i j = 0 := by decide

omit [Fintype V] in
/-- **Divisibility forces balance**: an integrally `F₁`-divisible edge set has balance `0`. -/
theorem balance_eq_zero_of_intDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hE : IsIntDiv p F1 E) : balance p E = 0 := by
  obtain ⟨⟨c, hc⟩, -⟩ := hE
  have hev : ∀ i j, edgeVec p E i j = ∑ e ∈ E, pairVec p e i j := by
    intro i j; simp [edgeVec, Finset.sum_apply]
  have h2 : 2 * balance p E =
      ((∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * edgeVec p E i j : ℤ) : ℝ) := by
    rw [balance, mul_sum, sum_congr rfl (fun e _ => two_charge_eq p e), ← Int.cast_sum]
    congr 1
    simp_rw [hev, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => by rw [sum_comm]
  have hev2 : ∀ i j, edgeVec p E i j = ∑ τ ∈ F1, c τ * typeEdgeVec τ i j := by
    intro i j; rw [hc]; simp [Finset.sum_apply]
  have h0 : (∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * edgeVec p E i j) = 0 := by
    simp_rw [hev2, mul_sum]
    calc (∑ i : Fin 4, ∑ j : Fin 4, ∑ τ ∈ F1, pairCharge i j * (c τ * typeEdgeVec τ i j))
        = ∑ i : Fin 4, ∑ τ ∈ F1, ∑ j : Fin 4, pairCharge i j * (c τ * typeEdgeVec τ i j) :=
          sum_congr rfl fun i _ => sum_comm
      _ = ∑ τ ∈ F1, ∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * (c τ * typeEdgeVec τ i j) :=
          sum_comm
      _ = 0 := sum_eq_zero fun τ hτ => by
          have := type_charge_zero τ hτ
          calc (∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * (c τ * typeEdgeVec τ i j))
              = c τ * ∑ i : Fin 4, ∑ j : Fin 4, pairCharge i j * typeEdgeVec τ i j := by
                rw [mul_sum]
                exact sum_congr rfl fun i _ => by
                  rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [this, mul_zero]
  rw [h0, Int.cast_zero] at h2
  linarith

/-! ### The exact puncture ledger -/

/-- Edges of `H` with both ends in `S`. -/
def edgesIn (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : Finset (Sym2 V) :=
  H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ S

omit [Fintype V] [DecidableEq V] in
lemma mk_all_mem (S : Finset V) (a b : V) : (∀ v ∈ s(a, b), v ∈ S) ↔ a ∈ S ∧ b ∈ S := by
  simp

/-- The punctured level is `(edges in W \ child) \ Res`. -/
theorem punc_edgeFinset_eq (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V)
    (Res : Finset (Sym2 V)) :
    (punc H W U Res).edgeFinset = (edgesIn H W \ edgesIn H U) \ Res := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, punc_adj, edgesIn,
      mem_sdiff, mem_filter, mk_all_mem]
    tauto

/-- **Exact puncture ledger** (actual level): if the edges of `H` inside `W` are integrally
`F₁`-divisible and the reserve consists of edges of `H` inside `W` and not inside `U`, then
`balance(punc) = - balance(child) - balance(Res)`. -/
theorem punc_balance_ledger (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) (Res : Finset (Sym2 V)) (hUW : U ⊆ W)
    (hdiv : IsIntDiv p F1 (edgesIn H W)) (hRes : Res ⊆ edgesIn H W \ edgesIn H U) :
    balance p (punc H W U Res).edgeFinset =
      -balance p (edgesIn H U) - balance p Res := by
  rw [punc_edgeFinset_eq]
  have hI : edgesIn H U ⊆ edgesIn H W := by
    intro e he
    simp only [edgesIn, mem_filter] at he ⊢
    exact ⟨he.1, fun v hv => hUW (he.2 v hv)⟩
  exact F1BalanceGateStage228.balanced_puncture_reserve_ledger p _ _ _ hI hRes (balance_eq_zero_of_intDiv p _ hdiv)

/-- A good cross reserve satisfies the inclusion of the ledger. -/
theorem crossRes_sub_ledger (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V)
    (Res : Finset (Sym2 V)) (ρ ε : ℝ) (hUW : U ⊆ W) (hR : CrossResGood p H W U Res ρ ε) :
    Res ⊆ edgesIn H W \ edgesIn H U := by
  intro e he
  obtain ⟨x, hx, z, hz, rfl⟩ := hR.cross e he
  have hH := hR.sub he
  rw [mem_sdiff] at hx
  simp only [edgesIn, mem_sdiff, mem_filter, mk_all_mem]
  exact ⟨⟨hH, hx.1, hUW hz⟩, fun h => hx.2 h.2.1⟩

/-! ### Charge sums at a vertex -/

omit [Fintype V] [DecidableEq V] in
/-- Fiberwise form of a vertex charge sum. -/
theorem vertex_charge_fiber (p : V → Fin 4) (v : V) (S : Finset V) :
    (∑ z ∈ S, (pairCharge (p v) (p z) : ℝ)) =
      ∑ c : Fin 4, (pairCharge (p v) c : ℝ) * ((S.filter fun z => p z = c).card : ℝ) := by
  rw [← Finset.sum_fiberwise (s := S) (g := p)]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_congr rfl (fun z hz => by rw [(mem_filter.mp hz).2]), sum_const, nsmul_eq_mul,
    mul_comm]

/-- The arithmetic core: the charge of a near-complete typed neighbourhood in a near-quarter
set is small.  `N c` is the neighbourhood count in class `c`, `s c` the class size. -/
theorem charge_core (i : Fin 4) (N s : Fin 4 → ℝ) (u κn ξn : ℝ)
    (hN0 : ∀ c, ¬ AllowedT F1 i c → N c = 0)
    (hNlo : ∀ c, AllowedT F1 i c → s c - ξn ≤ N c) (hNhi : ∀ c, N c ≤ s c)
    (hs : ∀ c, |s c - u| ≤ κn) :
    |∑ c : Fin 4, (pairCharge i c : ℝ) * N c| ≤ 4 * κn + 2 * ξn := by
  have hs' := fun c => abs_le.mp (hs c)
  rw [Fin.sum_univ_four, abs_le]
  fin_cases i <;>
  · simp only [pairCharge] at *
    norm_num at *
    have a0 := hs' 0; have a1 := hs' 1; have a2 := hs' 2; have a3 := hs' 3
    have b0 := hNhi 0; have b1 := hNhi 1; have b2 := hNhi 2; have b3 := hNhi 3
    first
    | (have z1 := hN0 1 (by decide); have l0 := hNlo 0 (by decide); have l2 := hNlo 2 (by decide);
       have l3 := hNlo 3 (by decide); constructor <;> linarith)
    | (have z0 := hN0 0 (by decide); have l1 := hNlo 1 (by decide); have l2 := hNlo 2 (by decide);
       have l3 := hNlo 3 (by decide); constructor <;> linarith)
    | (have z3 := hN0 3 (by decide); have l2 := hNlo 2 (by decide); have l0 := hNlo 0 (by decide);
       have l1 := hNlo 1 (by decide); constructor <;> linarith)
    | (have z2 := hN0 2 (by decide); have l3 := hNlo 3 (by decide); have l0 := hNlo 0 (by decide);
       have l1 := hNlo 1 (by decide); constructor <;> linarith)

omit [Fintype V] in
/-- **Vertex charge bound**: in a near-quarter set `S ⊆ W` (defect `κ`), the `G`-neighbourhood
of a `ξ`-typical vertex `v ∈ W` of an `F₁`-allowed host has charge at most `(4κ + 2ξ)|W|`. -/
theorem vertex_charge_bound (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W S : Finset V) (κ ξ u : ℝ) (v : V) (hSW : S ⊆ W)
    (hGF : ∀ a b, G.Adj a b → AllowedT F1 (p a) (p b))
    (htyp : ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card)
    (hS : ∀ j : Fin 4, |((S.filter fun z => p z = j).card : ℝ) - u| ≤ κ * W.card) :
    |∑ z ∈ S.filter (G.Adj v), (pairCharge (p v) (p z) : ℝ)| ≤ (4 * κ + 2 * ξ) * W.card := by
  rw [vertex_charge_fiber]
  have key := charge_core (p v) (fun c => (((S.filter (G.Adj v)).filter fun z => p z = c).card : ℝ))
    (fun c => ((S.filter fun z => p z = c).card : ℝ)) u (κ * W.card) (ξ * W.card) ?_ ?_ ?_ hS
  · calc _ ≤ 4 * (κ * W.card) + 2 * (ξ * W.card) := key
      _ = _ := by ring
  · intro c hc
    rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro z hz hzc
    exact hc (hzc ▸ hGF v z (mem_filter.mp hz).2)
  · intro c hc
    have hsplit : ((S.filter fun z => p z = c).card : ℝ) ≤
        (((S.filter (G.Adj v)).filter fun z => p z = c).card : ℝ) +
          ((W.filter fun z => p z = c ∧ ¬ G.Adj v z).card : ℝ) := by
      have : S.filter (fun z => p z = c) ⊆ ((S.filter (G.Adj v)).filter fun z => p z = c) ∪
          (W.filter fun z => p z = c ∧ ¬ G.Adj v z) := by
        intro z hz
        obtain ⟨hzS, hzc⟩ := mem_filter.mp hz
        by_cases hA : G.Adj v z
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hzS, hA⟩, hzc⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hSW hzS, hzc, hA⟩)
      exact_mod_cast (card_le_card this).trans (card_union_le _ _)
    linarith [htyp c hc]
  · intro c
    exact Nat.cast_le.mpr (card_le_card (filter_subset_filter _ (filter_subset _ _)))

/-! ### The child -/

/-- `H` restricted to a set (as a graph). -/
def restr (H : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

instance (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : DecidableRel (restr H S).Adj :=
  fun a b => by unfold restr; infer_instance

theorem restr_edgeFinset (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    (restr H S).edgeFinset = edgesIn H S := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, edgesIn, mem_filter,
      mk_all_mem]
    rfl

/-- **The child defect**: if no edge of `G` inside `U` is missing from `H` (the child was
protected by the previous level), then `|balance(child)| ≤ (2κ + ξ) |U| |W|`. -/
theorem child_balance_bound {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] {W U : Finset V} {Res : Finset (Sym2 V)} {κ ξ ζ ε q : ℝ}
    (h : PuncHyp p G H W U Res κ ξ ζ ε q)
    (hprot : ∀ a ∈ U, ∀ b ∈ U, G.Adj a b → H.Adj a b) :
    |balance p (edgesIn H U)| ≤ (2 * κ + ξ) * U.card * W.card := by
  have h2 : 2 * balance p (edgesIn H U) =
      ∑ v ∈ U, ∑ z ∈ U.filter (G.Adj v), (pairCharge (p v) (p z) : ℝ) := by
    rw [balance, ← restr_edgeFinset, sum_edges_two]
    rw [← sum_subset (subset_univ U)]
    · refine sum_congr rfl fun v hv => ?_
      apply sum_congr
      · ext z
        change z ∈ (univ.filter fun b => H.Adj v b ∧ v ∈ U ∧ b ∈ U) ↔
          z ∈ U.filter (G.Adj v)
        rw [mem_filter, mem_filter]
        simp only [mem_univ, true_and]
        constructor
        · rintro ⟨hH, -, hz⟩; exact ⟨hz, h.hHG hH⟩
        · rintro ⟨hz, hG⟩; exact ⟨hprot v hv z hz hG, hv, hz⟩
      · intro z _; exact charge_mk p v z
    · intro v _ hv
      refine sum_eq_zero fun z hz => ?_
      exact absurd (mem_filter.mp hz).2.2.1 hv
  have hb : ∀ v ∈ U, |∑ z ∈ U.filter (G.Adj v), (pairCharge (p v) (p z) : ℝ)| ≤
      (4 * κ + 2 * ξ) * W.card := fun v hv =>
    vertex_charge_bound p G W U κ ξ (uOf U) v h.hUW h.hGF (h.htyp v (h.hUW hv)) h.hin
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hb)
  rw [← h2, sum_const, nsmul_eq_mul, abs_mul, abs_two] at hsum
  linarith

/-! ### The reserve and the boundary -/

/-- The boundary edges of `H` between `W \ U` and `U`. -/
def bdEdges (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V) : Finset (Sym2 V) :=
  H.edgeFinset.filter fun e => ∃ x ∈ W \ U, ∃ z ∈ U, e = s(x, z)

/-- Signed charge of the damaged boundary edges: `G`-edges from roots `x ∈ W \ U` into `U`
that are missing from `H`. -/
noncomputable def bdDamCharge (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U : Finset V) : ℝ :=
  ∑ x ∈ W \ U, ∑ z ∈ U.filter (fun z => G.Adj x z ∧ ¬ H.Adj x z), (pairCharge (p x) (p z) : ℝ)

omit [Fintype V] in
lemma sdiff_disj (W U : Finset V) : Disjoint (W \ U) U := disjoint_sdiff_self_left

/-- Root form of the reserve balance. -/
theorem reserve_balance_roots (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) (Res : Finset (Sym2 V)) (ρ ε : ℝ) (hR : CrossResGood p H W U Res ρ ε) :
    balance p Res = ∑ x ∈ W \ U, ∑ c : Fin 4, (pairCharge (p x) c : ℝ) *
      ((U.filter fun z => p z = c ∧ H.Adj x z ∧ s(x, z) ∈ Res).card : ℝ) := by
  rw [balance, sum_bipartite_edges (W \ U) U (sdiff_disj W U) Res hR.cross]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_congr rfl (fun z _ => charge_mk p x z), vertex_charge_fiber]
  refine sum_congr rfl fun c _ => ?_
  congr 3
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hz, hR'⟩, hc⟩
    exact ⟨hz, hc, SimpleGraph.mem_edgeFinset.mp (hR.sub hR'), hR'⟩
  · rintro ⟨hz, hc, -, hR'⟩; exact ⟨⟨hz, hR'⟩, hc⟩

/-- Root form of the boundary balance. -/
theorem boundary_balance_roots (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) :
    balance p (bdEdges H W U) = ∑ x ∈ W \ U, ∑ c : Fin 4, (pairCharge (p x) c : ℝ) *
      ((U.filter fun z => p z = c ∧ H.Adj x z).card : ℝ) := by
  rw [balance, sum_bipartite_edges (W \ U) U (sdiff_disj W U) (bdEdges H W U)
    (fun e he => (mem_filter.mp he).2)]
  refine sum_congr rfl fun x hx => ?_
  rw [sum_congr rfl (fun z _ => charge_mk p x z), vertex_charge_fiber]
  refine sum_congr rfl fun c _ => ?_
  congr 3
  ext z
  simp only [bdEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨⟨hz, hH, -⟩, hc⟩; exact ⟨hz, hc, hH⟩
  · rintro ⟨hz, hc, hH⟩; exact ⟨⟨hz, hH, x, hx, z, hz, rfl⟩, hc⟩

/-- **Reserve balance** (`CrossResGood.r4`): `|balance(Res) - ρ balance(boundary)| ≤ 6 ε |W|²`. -/
theorem reserve_balance_near (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) (Res : Finset (Sym2 V)) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hR : CrossResGood p H W U Res ρ ε) :
    |balance p Res - ρ * balance p (bdEdges H W U)| ≤ 6 * ε * W.card * W.card := by
  rw [reserve_balance_roots p H W U Res ρ ε hR, boundary_balance_roots, mul_sum, ← sum_sub_distrib]
  have hroot : ∀ x ∈ W \ U, |(∑ c : Fin 4, (pairCharge (p x) c : ℝ) *
      ((U.filter fun z => p z = c ∧ H.Adj x z ∧ s(x, z) ∈ Res).card : ℝ)) -
      ρ * ∑ c : Fin 4, (pairCharge (p x) c : ℝ) *
      ((U.filter fun z => p z = c ∧ H.Adj x z).card : ℝ)| ≤ 6 * ε * W.card := by
    intro x hx
    rw [mem_sdiff] at hx
    have hc := fun c => hR.r4 x hx.1 hx.2 c
    rw [mul_sum, ← sum_sub_distrib]
    have : ∀ c : Fin 4, |(pairCharge (p x) c : ℝ) *
        ((U.filter fun z => p z = c ∧ H.Adj x z ∧ s(x, z) ∈ Res).card : ℝ) -
        ρ * ((pairCharge (p x) c : ℝ) * ((U.filter fun z => p z = c ∧ H.Adj x z).card : ℝ))| ≤
        |(pairCharge (p x) c : ℝ)| * (ε * W.card) := by
      intro c
      rw [show ∀ a b r d : ℝ, a * b - r * (a * d) = a * (b - r * d) from fun a b r d => by ring]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hc c) (abs_nonneg _)
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun c _ => this c).trans (le_of_eq ?_))
    rw [← sum_mul]
    have h6 : ∀ i : Fin 4, (∑ c : Fin 4, |(pairCharge i c : ℝ)|) = 6 := by
      intro i; fin_cases i <;> simp [Fin.sum_univ_four, pairCharge] <;> norm_num
    rw [h6]; ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hroot).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hc : ((W \ U).card : ℝ) ≤ W.card := by exact_mod_cast card_le_card sdiff_subset
  have : 0 ≤ 6 * ε * (W.card : ℝ) := by positivity
  nlinarith

/-- Direct root form of the boundary balance. -/
theorem boundary_balance_direct (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) :
    balance p (bdEdges H W U) =
      ∑ x ∈ W \ U, ∑ z ∈ U.filter (H.Adj x), (pairCharge (p x) (p z) : ℝ) := by
  rw [boundary_balance_roots]
  refine sum_congr rfl fun x _ => ?_
  rw [vertex_charge_fiber]
  refine sum_congr rfl fun c _ => ?_
  congr 3
  ext z; simp only [mem_filter]; tauto

/-- **Boundary balance** = typical part − signed charge of the damaged boundary. -/
theorem boundary_balance_eq (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U : Finset V) (hHG : H ≤ G) :
    balance p (bdEdges H W U) =
      (∑ x ∈ W \ U, ∑ z ∈ U.filter (G.Adj x), (pairCharge (p x) (p z) : ℝ)) -
        bdDamCharge p G H W U := by
  rw [boundary_balance_direct, bdDamCharge, eq_sub_iff_add_eq, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_filter_add_sum_filter_not (U.filter (G.Adj x)) (fun z => H.Adj x z)]
  congr 1
  · apply sum_congr _ (fun _ _ => rfl)
    ext z; simp only [mem_filter]
    exact ⟨fun h => ⟨⟨h.1, hHG h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  · apply sum_congr _ (fun _ _ => rfl)
    ext z; simp only [mem_filter]; tauto

/-- **The puncture defect of the actual level** (proved).  Under the actual level premises —
`PuncHyp`, integral divisibility of the edges of `H` inside `W`, protection of the child `U`, and
a jointly good reserve (`CrossResGood`, the SAME reserve that is deleted) — the balance of the
punctured level differs from `ρ · bdDamCharge` by at most `((2κ+ξ) + 6ε' + ρ(4κ+2ξ)) |W|²`. -/
theorem punctured_balance_defect {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] {W U : Finset V} {Res : Finset (Sym2 V)} {κ ξ ζ ε q ρ ε' : ℝ}
    (h : PuncHyp p G H W U Res κ ξ ζ ε q) (hdiv : IsIntDiv p F1 (edgesIn H W))
    (hprot : ∀ a ∈ U, ∀ b ∈ U, G.Adj a b → H.Adj a b)
    (hR : CrossResGood p H W U Res ρ ε') (hρ : 0 ≤ ρ) (hε' : 0 ≤ ε') :
    |balance p (punc H W U Res).edgeFinset - ρ * bdDamCharge p G H W U| ≤
      ((2 * κ + ξ) + 6 * ε' + ρ * (4 * κ + 2 * ξ)) * W.card * W.card := by
  have hled := punc_balance_ledger p H W U Res h.hUW hdiv (crossRes_sub_ledger p H W U Res ρ ε' h.hUW hR)
  have hchild := child_balance_bound h hprot
  have hres := reserve_balance_near p H W U Res ρ ε' hε' hR
  have hbd := boundary_balance_eq p G H W U h.hHG
  set A := ∑ x ∈ W \ U, ∑ z ∈ U.filter (G.Adj x), (pairCharge (p x) (p z) : ℝ) with hA
  have hAb : |A| ≤ (4 * κ + 2 * ξ) * W.card * W.card := by
    have hx : ∀ x ∈ W \ U, |∑ z ∈ U.filter (G.Adj x), (pairCharge (p x) (p z) : ℝ)| ≤
        (4 * κ + 2 * ξ) * W.card := fun x hx =>
      vertex_charge_bound p G W U κ ξ (uOf U) x h.hUW h.hGF
        (h.htyp x (mem_sdiff.mp hx).1) h.hin
    have := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hx)
    rw [sum_const, nsmul_eq_mul] at this
    have hc : ((W \ U).card : ℝ) ≤ W.card := by exact_mod_cast card_le_card sdiff_subset
    have h0 : 0 ≤ (4 * κ + 2 * ξ) * (W.card : ℝ) := by have := h.hκ; have := h.hξ; positivity
    nlinarith
  have hU : (U.card : ℝ) ≤ W.card := by exact_mod_cast card_le_card h.hUW
  have hc0 : 0 ≤ (2 * κ + ξ) * (W.card : ℝ) := by have := h.hκ; have := h.hξ; positivity
  have hchild' : |balance p (edgesIn H U)| ≤ (2 * κ + ξ) * W.card * W.card := by
    refine hchild.trans ?_
    nlinarith
  rw [hbd] at hres
  have hρA : |ρ * A| ≤ ρ * ((4 * κ + 2 * ξ) * W.card * W.card) := by
    rw [abs_mul, abs_of_nonneg hρ]; exact mul_le_mul_of_nonneg_left hAb hρ
  rw [hled]
  have e : -balance p (edgesIn H U) - balance p Res - ρ * bdDamCharge p G H W U =
      -balance p (edgesIn H U) - (balance p Res - ρ * (A - bdDamCharge p G H W U)) - ρ * A := by
    ring
  rw [e]
  calc _ ≤ |-balance p (edgesIn H U) - (balance p Res - ρ * (A - bdDamCharge p G H W U))| +
        |ρ * A| := abs_sub _ _
    _ ≤ |balance p (edgesIn H U)| + |balance p Res - ρ * (A - bdDamCharge p G H W U)| +
        |ρ * A| := by
        gcongr
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
    _ ≤ _ := by nlinarith

end NashWilliams18.SpreadF1
