/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.UniversalHub
public import PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour

/-! # Task 2: localized certificates from `CN6` alone

**Theorem (`cn6_certificate`).** If `CN6 p G β` holds and `β n > 0`, then every physical
F0-divisible source `P ⊆ E(G)` has a signed physical integer certificate of weight
`≤ 137 |P|`. No universal hub is used: every auxiliary vertex is a common neighbour of at most
six previously fixed vertices.

**Construction.** Fix a frame of five pairwise adjacent hubs (`exists_good_hubs`, at most
four roots per query). A vertex is *attached* if it is adjacent to the three hubs of its part,
so an attached vertex with at most three further prescribed neighbours costs one `CN6` query.
For every vertex `y` choose attached `X y, Y y, S y` in the other part, forming a triangle
with `y`; for every edge `uv` an attached common neighbour `w` of `u, v` in the part
opposite `u`; for every endpoint `y` of `uv` an attached common neighbour `z` of
`y, w, X y` in the part opposite `y`. Then, with `D y = [y X y] - spoke (X y)`:

* edge step: `[uv] + D u + D v` hub-reduces (one source triangle, two spoke-transfer
  pairs, four attached-edge reductions, one doubled spoke);
* vertex step: `2·D y` hub-reduces (three frame triangles, three attached-edge
  reductions).

Assembly cancels all `D`-terms (even degrees), and zero charge closes the hub pattern.
Original source vertices are never required to be adjacent to a hub.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks F0Geometric

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin 2} {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem not_mono_of_ne {a b c : V} (h : p c ≠ p a) : ¬ (p a = p b ∧ p b = p c) :=
  fun h' => h (h'.2.symm.trans h'.1.symm)

/-! ### Local gadgets at non-attached vertices -/

/-- Source triangle `u v w`. -/
theorem realizes_source_step {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hvw : G.Adj v w) (hw : p w ≠ p u) :
    Realizes p G (edgeInd u v + edgeInd u w + edgeInd v w) 1 :=
  realizes_triangle huv huw hvw (not_mono_of_ne hw)

/-- Spoke transfer: `[yw] - [yx] + [wz] - [xz]` is the difference of the triangles `ywz` and
`yxz`. -/
theorem realizes_spoke_transfer {y w x z : V} (hyw : G.Adj y w) (hyx : G.Adj y x)
    (hyz : G.Adj y z) (hwz : G.Adj w z) (hxz : G.Adj x z) (hz : p z ≠ p y) :
    Realizes p G (edgeInd y w - edgeInd y x + edgeInd w z - edgeInd x z) 2 := by
  have t1 := realizes_triangle (p := p) hyw hyz hwz (not_mono_of_ne hz)
  have t2 := realizes_triangle (p := p) hyx hyz hxz (not_mono_of_ne hz)
  refine (t1.sub t2).congr ?_
  funext e; simp only [Pi.add_apply, Pi.sub_apply]; ring

/-- Doubled spoke at `y` through the triangle `x y' s` adjacent to `y`. -/
theorem realizes_frame {y x y' s : V} (hyx : G.Adj y x) (hyy' : G.Adj y y') (hys : G.Adj y s)
    (hy'x : G.Adj y' x) (hxs : G.Adj x s) (hy's : G.Adj y' s) (hx : p x ≠ p y)
    (hs : p s ≠ p y) :
    Realizes p G (2 • edgeInd y x + edgeInd y' x + edgeInd x s - edgeInd y' s) 3 := by
  have t1 := realizes_triangle (p := p) hyy' hyx hy'x (not_mono_of_ne hx)
  have t2 := realizes_triangle (p := p) hyx hys hxs (not_mono_of_ne hs)
  have t3 := realizes_triangle (p := p) hyy' hys hy's (not_mono_of_ne hs)
  refine ((t1.add t2).sub t3).congr ?_
  funext e; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]; simp; ring

/-! ### Choices from `CN6` -/

/-- A common neighbour in part `i` of at most six prescribed vertices. -/
theorem exists_common_nbr [DecidableRel G.Adj] {β : ℝ} (hG : CN6 p G β)
    (hpos : 0 < β * Fintype.card V) (R : Finset V) (hR : R.card ≤ 6) (i : Fin 2) :
    ∃ w, p w = i ∧ ∀ u ∈ R, G.Adj u w := by
  have h := hG R hR i
  have : 0 < (univ.filter (fun w => p w = i ∧ ∀ u ∈ R, G.Adj u w)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨w, hw⟩ := card_pos.mp this
  exact ⟨w, (mem_filter.mp hw).2⟩

/-- `CN6` supplies a frame of five pairwise adjacent hubs. -/
theorem exists_good_hubs [DecidableRel G.Adj] {β : ℝ} (hG : CN6 p G β)
    (hpos : 0 < β * Fintype.card V) : ∃ H : Hubs V, H.Good p G := by
  obtain ⟨a0, pa0, -⟩ := exists_common_nbr hG hpos ∅ (by simp) 0
  obtain ⟨c0, pc0, hc0⟩ := exists_common_nbr hG hpos {a0} (by simp) 1
  obtain ⟨a1, pa1, ha1⟩ := exists_common_nbr hG hpos {a0, c0}
    (card_le_two.trans (by norm_num)) 0
  obtain ⟨c1, pc1, hc1⟩ := exists_common_nbr hG hpos {a0, c0, a1}
    (card_le_three.trans (by norm_num)) 1
  obtain ⟨a2, pa2, ha2⟩ := exists_common_nbr hG hpos {a0, c0, a1, c1}
    (card_le_four.trans (by norm_num)) 0
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hc0 ha1 hc1 ha2
  exact ⟨⟨a0, a1, a2, c0, c1⟩, pa0, pa1, pa2, pc0, pc1, ha1.1, ha2.1, ha2.2.2.1, hc0,
    hc1.1, ha1.2.symm, hc1.2.2, ha2.2.1.symm, ha2.2.2.2.symm, hc1.2.1⟩

/-- The three hubs an attached vertex of part `i` must see. -/
def hubs3 (H : Hubs V) (i : Fin 2) : Finset V :=
  if i = 0 then {H.A0, H.C0, H.C1} else {H.A0, H.A1, H.C0}

omit [Fintype V] in
theorem card_hubs3 (H : Hubs V) (i : Fin 2) : (hubs3 H i).card ≤ 3 := by
  unfold hubs3; split_ifs <;> exact card_le_three

/-- `CN6` supplies an attached vertex of part `i` adjacent to at most three prescribed
vertices. -/
theorem exists_attached [DecidableRel G.Adj] {β : ℝ} (hG : CN6 p G β)
    (hpos : 0 < β * Fintype.card V) (H : Hubs V) (R : Finset V) (hR : R.card ≤ 3)
    (i : Fin 2) : ∃ w, p w = i ∧ InW p G H w ∧ ∀ u ∈ R, G.Adj u w := by
  obtain ⟨w, hw, hadj⟩ := exists_common_nbr hG hpos (R ∪ hubs3 H i)
    ((card_union_le _ _).trans (by have := card_hubs3 H i; omega)) i
  refine ⟨w, hw, ⟨fun h0 => ?_, fun h1 => ?_⟩, fun u hu => hadj u (mem_union_left _ hu)⟩
  · have hi : i = 0 := hw ▸ h0
    have hm : ∀ v ∈ ({H.A0, H.C0, H.C1} : Finset V), G.Adj v w := fun v hv =>
      hadj v (mem_union_right _ (by simpa [hubs3, hi] using hv))
    exact ⟨(hm _ (by simp)).symm, (hm _ (by simp)).symm, (hm _ (by simp)).symm⟩
  · have hi : i = 1 := hw ▸ h1
    have hm : ∀ v ∈ ({H.A0, H.A1, H.C0} : Finset V), G.Adj v w := fun v hv =>
      hadj v (mem_union_right _ (by simpa [hubs3, hi] using hv))
    exact ⟨(hm _ (by simp)).symm, (hm _ (by simp)).symm, (hm _ (by simp)).symm⟩

theorem exists_attached_other [DecidableRel G.Adj] {β : ℝ} (hG : CN6 p G β)
    (hpos : 0 < β * Fintype.card V) (H : Hubs V) (y : V) (R : Finset V) (hR : R.card ≤ 3) :
    ∃ w, p w ≠ p y ∧ InW p G H w ∧ ∀ u ∈ R, G.Adj u w := by
  obtain ⟨w, hw, h1, h2⟩ := exists_attached hG hpos H R hR (if p y = 0 then 1 else 0)
  refine ⟨w, ?_, h1, h2⟩
  rw [hw]; rcases fin2_cases (p y) with h | h <;> simp [h]

/-! ### The localized certificate -/

/-- **Localized certificate (Task 2).** `CN6` with `β n > 0` gives every physical F0-divisible
source a signed physical integer certificate of weight `≤ 137|P|`. -/
theorem cn6_certificate [DecidableRel G.Adj] {β : ℝ} (hG : CN6 p G β)
    (hpos : 0 < β * Fintype.card V) {P : Finset (Sym2 V)} (hPG : P ⊆ G.edgeFinset)
    (hdiv : IsIntDiv p F0 P) :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
      IsSignedCert p G P t c ∧ certWeight c ≤ 137 * P.card := by
  obtain ⟨H, hH⟩ := exists_good_hubs hG hpos
  have att := exists_attached_other hG hpos H
  -- vertex frames
  have hX : ∀ y, ∃ x, p x ≠ p y ∧ InW p G H x ∧ G.Adj y x := fun y => by
    obtain ⟨x, h1, h2, h3⟩ := att y {y} (by simp)
    exact ⟨x, h1, h2, h3 y (by simp)⟩
  choose X hXp hXW hXa using hX
  have hY : ∀ y, ∃ y', p y' ≠ p y ∧ InW p G H y' ∧ G.Adj y y' ∧ G.Adj (X y) y' := fun y => by
    obtain ⟨x, h1, h2, h3⟩ := att y {y, X y} (card_le_two.trans (by norm_num))
    exact ⟨x, h1, h2, h3 y (by simp), h3 (X y) (by simp)⟩
  choose Y hYp hYW hYa hYX using hY
  have hS : ∀ y, ∃ s, p s ≠ p y ∧ InW p G H s ∧ G.Adj y s ∧ G.Adj (X y) s ∧
      G.Adj (Y y) s := fun y => by
    obtain ⟨x, h1, h2, h3⟩ := att y {y, X y, Y y} card_le_three
    exact ⟨x, h1, h2, h3 y (by simp), h3 (X y) (by simp), h3 (Y y) (by simp)⟩
  choose S hSp hSW hSa hSX hSY using hS
  -- edge centres
  have hW : ∀ u v, ∃ w, p w ≠ p u ∧ InW p G H w ∧ G.Adj u w ∧ G.Adj v w := fun u v => by
    obtain ⟨x, h1, h2, h3⟩ := att u {u, v} (card_le_two.trans (by norm_num))
    exact ⟨x, h1, h2, h3 u (by simp), h3 v (by simp)⟩
  choose Wc hWp hWW hWu hWv using hW
  -- spoke-transfer centres
  have hZ : ∀ y w, ∃ z, p z ≠ p y ∧ InW p G H z ∧ G.Adj y z ∧ G.Adj w z ∧
      G.Adj (X y) z := fun y w => by
    obtain ⟨x, h1, h2, h3⟩ := att y {y, w, X y} card_le_three
    exact ⟨x, h1, h2, h3 y (by simp), h3 w (by simp), h3 (X y) (by simp)⟩
  choose Z hZp hZW hZy hZw hZX using hZ
  let D : V → Sym2 V → ℤ := fun y => edgeInd y (X y) - spoke p H (X y)
  have hP := not_isDiag_of_subset hPG
  have hE : ∀ e ∈ P, HubReduces p G H (edgeOf e + ∑ y ∈ univ.filter (· ∈ e), D y) 20 9 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
    have huv : G.Adj u v := by simpa using hPG he
    rw [sum_filter_mem_mk huv.ne]
    set w := Wc u v
    set zu := Z u w
    set zv := Z v w
    have a := realizes_source_step huv (hWu u v) (hWv u v) (hWp u v)
    have bu := realizes_spoke_transfer (hWu u v) (hXa u) (hZy u w) (hZw u w) (hZX u w)
      (hZp u w)
    have bv := realizes_spoke_transfer (hWv u v) (hXa v) (hZy v w) (hZw v w) (hZX v w)
      (hZp v w)
    have c1 := hubReduces_edge hH (hWW u v) (hZW u w) (hZw u w)
    have c2 := hubReduces_edge hH (hXW u) (hZW u w) (hZX u w)
    have c3 := hubReduces_edge hH (hWW u v) (hZW v w) (hZw v w)
    have c4 := hubReduces_edge hH (hXW v) (hZW v w) (hZX v w)
    have d := hubReduces_double_spoke hH (hWW u v)
    have hab := HubReduces.of_realizes (p := p) (G := G) (H := H) ((a.sub bu).sub bv)
    refine ((((((hab.add c1).sub c2).add c3).sub c4).sub d).congr ?_).mono
      (by norm_num) (by norm_num)
    funext e
    simp only [D, edgeOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    simp only [edgeInd, edgeOf]
    ring
  have hV : ∀ y, 0 < deg P y → HubReduces p G H (2 • D y) 12 6 := by
    intro y _
    have f := realizes_frame (hXa y) (hYa y) (hSa y) (hYX y).symm (hSX y) (hSY y) (hXp y)
      (hSp y)
    have g1 := hubReduces_edge hH (hYW y) (hXW y) (hYX y).symm
    have g2 := hubReduces_edge hH (hXW y) (hSW y) (hSX y)
    have g3 := hubReduces_edge hH (hYW y) (hSW y) (hSY y)
    refine ((((HubReduces.of_realizes (H := H) f).sub g1).sub g2).add g3 |>.congr ?_).mono
      (by norm_num) (by norm_num)
    funext e
    simp only [D, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    simp
    ring
  exact (signedCert_of_reductions hH hP hdiv D hE hV).mono (le_of_eq (by ring)) |>.signedCert

end PartitionedTriangleAbsorption.IntegerCertificate
