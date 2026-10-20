/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.TrivialLattice

/-!
# Systems of edge-disjoint physical paths of length four

Families WITHOUT common neighbour classes cannot feed the ordinary refiner directly: two classes
at distance three have no common neighbours in the host `G`. We run the ordinary refiner in the
complete graph instead and then replace every (virtual) refiner edge `uv` by a physical path
`u x y z v` of length four in `G`. A path of length four has the same endpoint parities as the
edge `uv` and `4 ≡ 1 (mod 3)` edges, so even degrees and `3 ∣ e` are preserved.

This module provides the greedy selection of such paths (`exists_path_system`): they are
pairwise edge-disjoint, avoid the reserve `X`, and every vertex is internal to paths of bounded
total weight. It only needs guarded supply of order `2` and a walk of length four between every
two classes in the allowed-pair graph (`Walk4`).
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Paths of length four -/

/-- The edge set of the walk `u x y z v`. -/
def pathEdges (u x y z v : V) : Finset (Sym2 V) := {s(u, x), s(x, y), s(y, z), s(z, v)}

/-- `u x y z v` is a path of length four in `G` (endpoints may coincide only if `u = v`). -/
structure IsPath4 (G : SimpleGraph V) (u x y z v : V) : Prop where
  ux : G.Adj u x
  xy : G.Adj x y
  yz : G.Adj y z
  zv : G.Adj z v
  xv : x ≠ v
  zu : z ≠ u
  xz : x ≠ z
  yu : y ≠ u
  yv : y ≠ v

theorem incidentLoad_eq_sum (B : Finset (Sym2 V)) (w : V) :
    incidentLoad B w = ∑ e ∈ B, if w ∈ e then 1 else 0 := by
  unfold incidentLoad
  rw [card_filter]

theorem pathEdges_subset {G : SimpleGraph V} [DecidableRel G.Adj] {u x y z v : V}
    (h : IsPath4 G u x y z v) : pathEdges u x y z v ⊆ G.edgeFinset := by
  intro e he
  simp only [pathEdges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> rw [SimpleGraph.mem_edgeFinset]
  · exact h.ux
  · exact h.xy
  · exact h.yz
  · exact h.zv

theorem pathEdges_card {G : SimpleGraph V} {u x y z v : V} (huv : u ≠ v)
    (h : IsPath4 G u x y z v) : (pathEdges u x y z v).card = 4 := by
  have hux := G.ne_of_adj h.ux
  have hxy := G.ne_of_adj h.xy
  have hyz := G.ne_of_adj h.yz
  have hzv := G.ne_of_adj h.zv
  have := h.xv; have := h.zu; have := h.xz; have := h.yu; have := h.yv
  unfold pathEdges
  rw [card_insert_of_notMem, card_insert_of_notMem, card_pair]
  · intro he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  · intro he
    simp only [mem_insert, mem_singleton, Sym2.eq_iff] at he
    rcases he with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  · intro he
    simp only [mem_insert, mem_singleton, Sym2.eq_iff] at he
    rcases he with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      simp_all

/-- The incidence of a path of length four: that of its virtual edge plus `2` at the
internal vertices. -/
theorem pathEdges_incidentLoad {G : SimpleGraph V} {u x y z v : V} (huv : u ≠ v)
    (h : IsPath4 G u x y z v) (w : V) :
    incidentLoad (pathEdges u x y z v) w =
      incidentLoad {s(u, v)} w + 2 * (if w = x ∨ w = y ∨ w = z then 1 else 0) := by
  have hux := G.ne_of_adj h.ux
  have hxy := G.ne_of_adj h.xy
  have hyz := G.ne_of_adj h.yz
  have hzv := G.ne_of_adj h.zv
  have h1 := h.xv; have h2 := h.zu; have h3 := h.xz; have h4 := h.yu; have h5 := h.yv
  have hc := pathEdges_card huv h
  rw [incidentLoad_eq_sum, incidentLoad_eq_sum, sum_singleton]
  unfold pathEdges at hc ⊢
  have n1 : s(u, x) ∉ ({s(x, y), s(y, z), s(z, v)} : Finset (Sym2 V)) := by
    intro hm
    have := card_insert_of_mem hm
    rw [this] at hc
    have := card_le_three (a := s(x, y)) (b := s(y, z)) (c := s(z, v))
    omega
  have n2 : s(x, y) ∉ ({s(y, z), s(z, v)} : Finset (Sym2 V)) := by
    intro hm
    rw [card_insert_of_notMem n1, card_insert_of_mem hm] at hc
    have := card_le_two (a := s(y, z)) (b := s(z, v))
    omega
  have n3 : s(y, z) ≠ s(z, v) := by
    intro he
    rw [card_insert_of_notMem n1, card_insert_of_notMem n2, he, pair_eq_singleton,
      card_singleton] at hc
    omega
  rw [sum_insert n1, sum_insert n2, sum_pair n3]
  simp only [Sym2.mem_iff]
  by_cases hwu : w = u
  · subst hwu
    simp [hux, Ne.symm h4, h2.symm, huv]
  by_cases hwv : w = v
  · subst hwv
    simp [h1.symm, h5.symm, hzv.symm, hwu]
  by_cases hwx : w = x
  · subst hwx
    simp [hwu, hwv, hxy, h3]
  by_cases hwy : w = y
  · subst hwy
    simp [hwu, hwv, hwx, hyz]
  by_cases hwz : w = z
  · subst hwz
    simp [hwu, hwv, hwx, hwy]
  simp [hwu, hwv, hwx, hwy, hwz]

/-! ### Orientation of virtual edges -/

/-- A fixed orientation of an unordered pair. -/
noncomputable def endU (e : Sym2 V) : V := (Quot.out e).1

/-- A fixed orientation of an unordered pair. -/
noncomputable def endV (e : Sym2 V) : V := (Quot.out e).2

theorem mk_ends (e : Sym2 V) : s(endU e, endV e) = e := by
  unfold endU endV
  exact Quot.out_eq e

theorem ends_ne {e : Sym2 V} (he : ¬ e.IsDiag) : endU e ≠ endV e := by
  intro h
  apply he
  rw [← mk_ends e, h]
  exact Sym2.mk_isDiag_iff.mpr rfl

/-- The physical path replacing `e`. -/
noncomputable def physPath (x y z : Sym2 V → V) (e : Sym2 V) : Finset (Sym2 V) :=
  pathEdges (endU e) (x e) (y e) (z e) (endV e)

/-- Weighted number of paths of `S` having `w` as an internal vertex. -/
def intLoad (wt : Sym2 V → ℕ) (S : Finset (Sym2 V)) (x y z : Sym2 V → V) (w : V) : ℕ :=
  ∑ e ∈ S, if w = x e ∨ w = y e ∨ w = z e then wt e else 0

/-- Walks of length four between any two classes (orientation as used by guarded supply). -/
def Walk4 {t : ℕ} (A : Fin t → Fin t → Prop) : Prop :=
  ∀ a b, ∃ c1 c2 c3, A a c1 ∧ A c2 c1 ∧ A c2 c3 ∧ A b c3

theorem sum_intLoad_le (wt : Sym2 V → ℕ) (S : Finset (Sym2 V)) (x y z : Sym2 V → V) :
    ∑ w, intLoad wt S x y z w ≤ 3 * ∑ e ∈ S, wt e := by
  unfold intLoad
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun e _ => ?_
  calc ∑ w, (if w = x e ∨ w = y e ∨ w = z e then wt e else 0)
      ≤ ∑ w, ((if w = x e then wt e else 0) + (if w = y e then wt e else 0) +
          (if w = z e then wt e else 0)) := by
        refine sum_le_sum fun w _ => ?_
        split_ifs <;> first | omega | (exfalso; tauto)
    _ = 3 * wt e := by
        rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', sum_ite_eq']
        simp only [mem_univ, if_true]
        ring

theorem card_highIntLoad_le (wt : Sym2 V → ℕ) (S : Finset (Sym2 V)) (x y z : Sym2 V → V)
    (Q : ℝ) :
    ((univ.filter fun w => Q < (intLoad wt S x y z w : ℝ)).card : ℝ) * Q ≤
      3 * ∑ e ∈ S, (wt e : ℝ) := by
  set H := univ.filter fun w => Q < (intLoad wt S x y z w : ℝ)
  have h1 : (H.card : ℝ) * Q ≤ ∑ w ∈ H, (intLoad wt S x y z w : ℝ) := by
    rw [← nsmul_eq_mul]
    exact card_nsmul_le_sum H _ Q fun w hw => (mem_filter.mp hw).2.le
  have h2 : ∑ w ∈ H, (intLoad wt S x y z w : ℝ) ≤ ∑ w, (intLoad wt S x y z w : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  have h3 : ∑ w, (intLoad wt S x y z w : ℝ) ≤ 3 * ∑ e ∈ S, (wt e : ℝ) := by
    exact_mod_cast sum_intLoad_le wt S x y z
  linarith

/-- The incidence of a union of paths is controlled by the virtual incidence and the
(weighted) internal load. -/
theorem incidentLoad_biUnion_physPath_le {G : SimpleGraph V} (S : Finset (Sym2 V))
    (x y z : Sym2 V → V) (hloop : ∀ e ∈ S, ¬ e.IsDiag)
    (hpath : ∀ e ∈ S, IsPath4 G (endU e) (x e) (y e) (z e) (endV e))
    (wt : Sym2 V → ℕ) (hwt : ∀ e ∈ S, 1 ≤ wt e) (w : V) :
    incidentLoad (S.biUnion (physPath x y z)) w ≤
      incidentLoad S w + 2 * intLoad wt S x y z w := by
  have h1 : incidentLoad (S.biUnion (physPath x y z)) w ≤
      ∑ e ∈ S, incidentLoad (physPath x y z e) w := by
    unfold incidentLoad
    rw [filter_biUnion]
    exact card_biUnion_le
  refine h1.trans ?_
  rw [incidentLoad_eq_sum S w, intLoad, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun e he => ?_
  unfold physPath
  rw [pathEdges_incidentLoad (ends_ne (hloop e he)) (hpath e he), incidentLoad_eq_sum,
    sum_singleton, mk_ends]
  have := hwt e he
  split_ifs <;> omega

theorem degBounded_of_card_le (E : Finset (Sym2 V)) (k : ℕ) (hk : E.card ≤ k) :
    DegBounded E k := by
  intro v
  have h : (E.filter fun e => v ∈ e).card ≤ E.card := card_filter_le _ _
  exact_mod_cast h.trans hk

/-! ### The greedy path system -/

/-- **Greedy system of physical paths.** Every virtual edge of `R` receives a path of length four
in `G`; the paths are pairwise edge-disjoint and avoid `X`, and every vertex is internal to paths of
total weight at most `Q + M`. -/
theorem exists_path_system {t : ℕ} (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Fin t → Fin t → Prop) (a : ℝ) (hs : GuardedSupply p G A 2 a) (hwalk : Walk4 A)
    (X R : Finset (Sym2 V)) (hRloop : ∀ e ∈ R, ¬ e.IsDiag)
    (dX dR : ℝ) (hX : DegBounded X dX) (hR : DegBounded R dR)
    (wt : Sym2 V → ℕ) (M W Q : ℝ) (hwt1 : ∀ e ∈ R, 1 ≤ wt e)
    (hwtM : ∀ e ∈ R, (wt e : ℝ) ≤ M) (hW : ∑ e ∈ R, (wt e : ℝ) ≤ W)
    (hdX : 0 ≤ dX) (hdR : 0 ≤ dR) (hM : 0 ≤ M) (hQ : 0 < Q)
    (hbudget : 3 * W / Q + 3 + 2 * (dX + dR + 2 * (Q + M) + 2) < a) :
    ∃ x y z : Sym2 V → V, (∀ e ∈ R, IsPath4 G (endU e) (x e) (y e) (z e) (endV e)) ∧
      (∀ e ∈ R, Disjoint (physPath x y z e) X) ∧
      (∀ e ∈ R, ∀ e' ∈ R, e ≠ e' → Disjoint (physPath x y z e) (physPath x y z e')) ∧
      (∀ w, (intLoad wt R x y z w : ℝ) ≤ Q + M) := by
  classical
  have hW0 : 0 ≤ W := le_trans (sum_nonneg fun _ _ => Nat.cast_nonneg _) hW
  suffices hmain : ∀ S : Finset (Sym2 V), S ⊆ R →
      ∃ x y z : Sym2 V → V, (∀ e ∈ S, IsPath4 G (endU e) (x e) (y e) (z e) (endV e)) ∧
        (∀ e ∈ S, Disjoint (physPath x y z e) X) ∧
        (∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → Disjoint (physPath x y z e) (physPath x y z e')) ∧
        (∀ w, (intLoad wt S x y z w : ℝ) ≤ Q + M) from hmain R subset_rfl
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun e => endU e, fun e => endU e, fun e => endU e, by simp, by simp, by simp, ?_⟩
    intro w
    simp only [intLoad, sum_empty, Nat.cast_zero]
    linarith
  | insert e0 S he0 ih =>
    intro hsub
    have hSR : S ⊆ R := (subset_insert _ _).trans hsub
    have he0R : e0 ∈ R := hsub (mem_insert_self _ _)
    obtain ⟨x, y, z, hpath, hdisX, hdis, hload⟩ := ih hSR
    set u := endU e0 with hu
    set v := endV e0 with hv
    -- the high-load vertices
    set Hi := univ.filter fun w => Q < (intLoad wt S x y z w : ℝ) with hHi
    have hHi : (Hi.card : ℝ) ≤ 3 * W / Q := by
      have h1 := card_highIntLoad_le wt S x y z Q
      have h2 : ∑ e ∈ S, (wt e : ℝ) ≤ W :=
        le_trans (sum_le_sum_of_subset_of_nonneg hSR fun _ _ _ => Nat.cast_nonneg _) hW
      rw [le_div_iff₀ hQ]
      linarith
    set Z : Finset V := insert u (insert v Hi) with hZ
    have hZcard : (Z.card : ℝ) ≤ 3 * W / Q + 2 := by
      have h1 : Z.card ≤ Hi.card + 2 := by
        calc Z.card ≤ (insert v Hi).card + 1 := card_insert_le _ _
          _ ≤ Hi.card + 1 + 1 := by have := card_insert_le v Hi; omega
      have h2 : (Z.card : ℝ) ≤ Hi.card + 2 := by exact_mod_cast h1
      linarith
    -- the forbidden edges
    set Bs := X ∪ S.biUnion (physPath x y z) with hBs
    set dB := dX + dR + 2 * (Q + M) with hdB
    have hdB0 : 0 ≤ dB := by positivity
    have hBdeg : DegBounded Bs dB := by
      have hP : DegBounded (S.biUnion (physPath x y z)) (dR + 2 * (Q + M)) := by
        intro w
        have h1 := incidentLoad_biUnion_physPath_le S x y z
          (fun e he => hRloop e (hSR he)) hpath wt (fun e he => hwt1 e (hSR he)) w
        have h2 : (incidentLoad S w : ℝ) ≤ dR :=
          le_trans (by exact_mod_cast PrivateFamily.incidentLoad_mono hSR w) (hR w)
        have h3 := hload w
        change ((incidentLoad _ w : ℕ) : ℝ) ≤ _
        have h1' : ((incidentLoad (S.biUnion (physPath x y z)) w : ℕ) : ℝ) ≤
            incidentLoad S w + 2 * (intLoad wt S x y z w : ℝ) := by exact_mod_cast h1
        linarith
      have := degBounded_union hX hP
      rw [show dB = dX + (dR + 2 * (Q + M)) by ring]
      exact this
    obtain ⟨c1, c2, c3, hA1, hA2, hA3, hA4⟩ := hwalk (p u) (p v)
    -- the middle vertex
    obtain ⟨y0, hy0c, -, hy0Z, -⟩ := guarded_exists_avoiding p G A 2 a dB hs ∅ Z (by simp) Bs
      hBdeg hdB0 (by push_cast; linarith) c2 (by simp)
    -- the first internal vertex
    obtain ⟨x0, hx0c, hx0adj, hx0Z, hx0B⟩ := guarded_exists_avoiding p G A 2 a dB hs {u, y0} Z
      card_le_two Bs hBdeg hdB0 (by push_cast; linarith) c1 (by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hA1
        · rw [mem_singleton.mp hw, hy0c]; exact hA2)
    -- the last internal vertex
    set B2 := Bs ∪ {s(u, x0), s(x0, y0)} with hB2
    have hB2deg : DegBounded B2 (dB + 2) := by
      have h := degBounded_union hBdeg (degBounded_of_card_le {s(u, x0), s(x0, y0)} 2 card_le_two)
      exact_mod_cast h
    have hZ2 : ((insert x0 Z).card : ℝ) ≤ 3 * W / Q + 3 := by
      have h1 : ((insert x0 Z).card : ℝ) ≤ Z.card + 1 := by exact_mod_cast card_insert_le _ _
      linarith
    obtain ⟨z0, hz0c, hz0adj, hz0Z, hz0B⟩ := guarded_exists_avoiding p G A 2 a (dB + 2) hs
      {y0, v} (insert x0 Z) card_le_two B2 hB2deg (by positivity) (by push_cast; linarith) c3 (by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · rw [hy0c]; exact hA3
        · rw [mem_singleton.mp hw]; exact hA4)
    have hux0 : G.Adj u x0 := hx0adj u (by simp)
    have hy0x0 : G.Adj y0 x0 := hx0adj y0 (by simp)
    have hy0z0 : G.Adj y0 z0 := hz0adj y0 (by simp)
    have hvz0 : G.Adj v z0 := hz0adj v (by simp)
    have hux0B : s(u, x0) ∉ Bs := hx0B u (by simp)
    have hy0x0B : s(y0, x0) ∉ Bs := hx0B y0 (by simp)
    have hy0z0B : s(y0, z0) ∉ B2 := hz0B y0 (by simp)
    have hvz0B : s(v, z0) ∉ B2 := hz0B v (by simp)
    have hZu : u ∈ Z := mem_insert_self _ _
    have hZv : v ∈ Z := mem_insert_of_mem (mem_insert_self _ _)
    have hpath0 : IsPath4 G u x0 y0 z0 v :=
      { ux := hux0, xy := hy0x0.symm, yz := hy0z0, zv := hvz0.symm
        xv := fun h => hx0Z (h ▸ hZv)
        zu := fun h => hz0Z (mem_insert_of_mem (h ▸ hZu))
        xz := fun h => hz0Z (h ▸ mem_insert_self _ _)
        yu := fun h => hy0Z (h ▸ hZu)
        yv := fun h => hy0Z (h ▸ hZv) }
    -- edges of the new path avoid `Bs`
    have hnew : ∀ f ∈ pathEdges u x0 y0 z0 v, f ∉ Bs := by
      intro f hf
      simp only [pathEdges, mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact hux0B
      · rw [Sym2.eq_swap]; exact hy0x0B
      · exact fun h => hy0z0B (mem_union_left _ h)
      · rw [Sym2.eq_swap]; exact fun h => hvz0B (mem_union_left _ h)
    let x' : Sym2 V → V := fun e => if e = e0 then x0 else x e
    let y' : Sym2 V → V := fun e => if e = e0 then y0 else y e
    let z' : Sym2 V → V := fun e => if e = e0 then z0 else z e
    have hold : ∀ e ∈ S, physPath x' y' z' e = physPath x y z e := by
      intro e he
      have hne : e ≠ e0 := fun h => he0 (h ▸ he)
      simp only [physPath, x', y', z', if_neg hne]
    have hnew' : physPath x' y' z' e0 = pathEdges u x0 y0 z0 v := by
      simp only [physPath, x', y', z', if_pos rfl, hu, hv]
    refine ⟨x', y', z', ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · simpa only [x', y', z', if_pos rfl] using hpath0
      · have hne : e ≠ e0 := fun h => he0 (h ▸ he)
        simpa only [x', y', z', if_neg hne] using hpath e he
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · rw [hnew']
        exact disjoint_left.mpr fun f hf hfX => hnew f hf (mem_union_left _ hfX)
      · rw [hold e he]; exact hdisX e he
    · have hnewdis : ∀ e ∈ S, Disjoint (physPath x' y' z' e0) (physPath x' y' z' e) := by
        intro e he
        rw [hnew', hold e he]
        exact disjoint_left.mpr fun f hf hfe =>
          hnew f hf (mem_union_right _ (mem_biUnion.mpr ⟨e, he, hfe⟩))
      intro e he e' he' hne
      rcases mem_insert.mp he with h1 | h1 <;> rcases mem_insert.mp he' with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1]; exact hnewdis e' h2
      · rw [h2]; exact (hnewdis e h1).symm
      · rw [hold e h1, hold e' h2]; exact hdis e h1 e' h2 hne
    · intro w
      have hsplit : intLoad wt (insert e0 S) x' y' z' w =
          (if w = x0 ∨ w = y0 ∨ w = z0 then wt e0 else 0) + intLoad wt S x y z w := by
        unfold intLoad
        rw [sum_insert he0]
        congr 1
        · simp only [x', y', z', if_pos rfl]
        · refine sum_congr rfl fun e he => ?_
          have hne : e ≠ e0 := fun h => he0 (h ▸ he)
          simp only [x', y', z', if_neg hne]
      rw [hsplit]
      by_cases hw : w = x0 ∨ w = y0 ∨ w = z0
      · rw [if_pos hw]
        have hwZ : w ∉ Hi := by
          rcases hw with rfl | rfl | rfl
          · exact fun h => hx0Z (mem_insert_of_mem (mem_insert_of_mem h))
          · exact fun h => hy0Z (mem_insert_of_mem (mem_insert_of_mem h))
          · exact fun h => hz0Z (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem h)))
        have hle : (intLoad wt S x y z w : ℝ) ≤ Q := by
          by_contra hc
          exact hwZ (mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hc⟩)
        have := hwtM e0 he0R
        push_cast
        linarith
      · rw [if_neg hw, zero_add]
        exact hload w

end PaddedNoCommon
