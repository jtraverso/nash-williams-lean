/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Combination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-! # A five-hub frame and reduction to hub patterns

A *frame* consists of five pairwise adjacent hubs `A0, A1, A2` (part `0`) and `C0, C1`
(part `1`) (`Hubs.Good`). A vertex `x` is *frame-attached* (`InW`) if it is adjacent to
`A0, C0, C1` (when `x ∈ V₀`) or to `A0, A1, C0` (when `x ∈ V₁`); its *anchor spoke* is
`x C0` resp. `x A0`.

`HubReduces f w M` says that `f` minus some hub pattern
`α·[A0C0] + β·π₀ + γ·π₁` (with `|α| + |β| + |γ| ≤ M`) is a physical triangle combination
of weight `≤ w`. The three gadgets are:

* `hubReduces_double_spoke`: twice an anchor spoke reduces with cost `(3, 1)`;
* `hubReduces_edge`: an edge between two attached vertices plus both anchor spokes reduces
  with cost `(3, 2)`;
* `realizes_of_hubReduces`: a charge-zero function that hub-reduces with cost `(w, M)` is
  realizable with weight `w + 7M` (the third hub `A2` supplies the rectangle).

Every identity is an identity of functions on all of `Sym2 V`, hence checks every edge.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

/-- Five hub vertices. -/
structure Hubs (V : Type*) where
  A0 : V
  A1 : V
  A2 : V
  C0 : V
  C1 : V

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 2} {G : SimpleGraph V}

/-- The five hubs have the prescribed parts and are pairwise adjacent. -/
structure Hubs.Good (p : V → Fin 2) (G : SimpleGraph V) (H : Hubs V) : Prop where
  pA0 : p H.A0 = 0
  pA1 : p H.A1 = 0
  pA2 : p H.A2 = 0
  pC0 : p H.C0 = 1
  pC1 : p H.C1 = 1
  a0a1 : G.Adj H.A0 H.A1
  a0a2 : G.Adj H.A0 H.A2
  a1a2 : G.Adj H.A1 H.A2
  a0c0 : G.Adj H.A0 H.C0
  a0c1 : G.Adj H.A0 H.C1
  a1c0 : G.Adj H.A1 H.C0
  a1c1 : G.Adj H.A1 H.C1
  a2c0 : G.Adj H.A2 H.C0
  a2c1 : G.Adj H.A2 H.C1
  c0c1 : G.Adj H.C0 H.C1

/-- `x` is attached to the frame. -/
def InW (p : V → Fin 2) (G : SimpleGraph V) (H : Hubs V) (x : V) : Prop :=
  (p x = 0 → G.Adj x H.A0 ∧ G.Adj x H.C0 ∧ G.Adj x H.C1) ∧
    (p x = 1 → G.Adj x H.A0 ∧ G.Adj x H.A1 ∧ G.Adj x H.C0)

/-- The anchor hub of `x`. -/
def anchor (p : V → Fin 2) (H : Hubs V) (x : V) : V := if p x = 0 then H.C0 else H.A0

/-- The anchor spoke of `x`. -/
def spoke (p : V → Fin 2) (H : Hubs V) (x : V) : Sym2 V → ℤ := edgeInd x (anchor p H x)

/-- Hub pattern `π₀ = -[A0C0] - [C0C1] + [A0C1]`. -/
def pi0 (H : Hubs V) : Sym2 V → ℤ := -edgeInd H.A0 H.C0 - edgeInd H.C0 H.C1 + edgeInd H.A0 H.C1

/-- Hub pattern `π₁ = -[A0C0] - [A0A1] + [A1C0]`. -/
def pi1 (H : Hubs V) : Sym2 V → ℤ := -edgeInd H.A0 H.C0 - edgeInd H.A0 H.A1 + edgeInd H.A1 H.C0

/-- The hub pattern `α·[A0C0] + β·π₀ + γ·π₁`. -/
def hubForm (H : Hubs V) (α β γ : ℤ) : Sym2 V → ℤ :=
  α • edgeInd H.A0 H.C0 + β • pi0 H + γ • pi1 H

/-- `f` reduces to a hub pattern of size `≤ M` with triangle weight `≤ w`. -/
def HubReduces (p : V → Fin 2) (G : SimpleGraph V) (H : Hubs V) (f : Sym2 V → ℤ)
    (w M : ℤ) : Prop :=
  ∃ α β γ : ℤ, |α| + |β| + |γ| ≤ M ∧ Realizes p G (f - hubForm H α β γ) w

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

namespace HubReduces

variable {H : Hubs V}

theorem of_realizes {f : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) :
    HubReduces p G H f w 0 :=
  ⟨0, 0, 0, by simp, h.congr (by funext e; simp [hubForm])⟩

theorem congr {f g : Sym2 V → ℤ} {w M : ℤ} (h : HubReduces p G H f w M) (hfg : f = g) :
    HubReduces p G H g w M := hfg ▸ h

theorem mono {f : Sym2 V → ℤ} {w M w' M' : ℤ} (h : HubReduces p G H f w M) (hw : w ≤ w')
    (hM : M ≤ M') : HubReduces p G H f w' M' := by
  obtain ⟨α, β, γ, h1, h2⟩ := h
  exact ⟨α, β, γ, h1.trans hM, h2.mono hw⟩

theorem add {f g : Sym2 V → ℤ} {w M w' M' : ℤ} (hf : HubReduces p G H f w M)
    (hg : HubReduces p G H g w' M') : HubReduces p G H (f + g) (w + w') (M + M') := by
  obtain ⟨α, β, γ, h1, h2⟩ := hf
  obtain ⟨α', β', γ', k1, k2⟩ := hg
  refine ⟨α + α', β + β', γ + γ', ?_, (h2.add k2).congr ?_⟩
  · have := abs_add_le α α'; have := abs_add_le β β'; have := abs_add_le γ γ'
    linarith
  · funext e; simp only [hubForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem smul {f : Sym2 V → ℤ} {w M : ℤ} (k : ℤ) (h : HubReduces p G H f w M) :
    HubReduces p G H (k • f) (|k| * w) (|k| * M) := by
  obtain ⟨α, β, γ, h1, h2⟩ := h
  refine ⟨k * α, k * β, k * γ, ?_, (h2.smul k).congr ?_⟩
  · simp only [abs_mul]
    nlinarith [abs_nonneg k]
  · funext e; simp only [hubForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem neg {f : Sym2 V → ℤ} {w M : ℤ} (h : HubReduces p G H f w M) :
    HubReduces p G H (-f) w M := by
  simpa using h.smul (-1)

theorem sub {f g : Sym2 V → ℤ} {w M w' M' : ℤ} (hf : HubReduces p G H f w M)
    (hg : HubReduces p G H g w' M') : HubReduces p G H (f - g) (w + w') (M + M') := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sum {α : Type*} (S : Finset α) (f : α → Sym2 V → ℤ) (w M : α → ℤ)
    (h : ∀ i ∈ S, HubReduces p G H (f i) (w i) (M i)) :
    HubReduces p G H (∑ i ∈ S, f i) (∑ i ∈ S, w i) (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (of_realizes (H := H) (Realizes.zero : Realizes p G 0 0))
  | insert a S ha ih =>
    rw [sum_insert ha, sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a S)).add (ih fun i hi => h i (mem_insert_of_mem hi))

end HubReduces

variable {H : Hubs V}

/-- **Doubled anchor spoke.** `2·spoke x` reduces to `π₀` or `π₁` with three triangles. -/
theorem hubReduces_double_spoke (hH : H.Good p G) {x : V} (hx : InW p G H x) :
    HubReduces p G H (2 • spoke p H x) 3 1 := by
  rcases fin2_cases (p x) with h0 | h1
  · obtain ⟨xa0, xc0, xc1⟩ := hx.1 h0
    have t1 := realizes_triangle (p := p) xa0 xc0 hH.a0c0 (by simp [h0, hH.pA0, hH.pC0])
    have t2 := realizes_triangle (p := p) xc0 xc1 hH.c0c1 (by simp [h0, hH.pC0, hH.pC1])
    have t3 := realizes_triangle (p := p) xa0 xc1 hH.a0c1 (by simp [h0, hH.pA0, hH.pC1])
    refine ⟨0, 1, 0, by simp, ((t1.add t2).sub t3).congr ?_⟩
    funext e
    simp only [spoke, anchor, h0, ite_true, hubForm, pi0, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  · obtain ⟨xa0, xa1, xc0⟩ := hx.2 h1
    have t1 := realizes_triangle (p := p) xa0 xc0 hH.a0c0 (by simp [h1, hH.pA0, hH.pC0])
    have t2 := realizes_triangle (p := p) xa0 xa1 hH.a0a1 (by simp [h1, hH.pA0, hH.pA1])
    have t3 := realizes_triangle (p := p) xa1 xc0 hH.a1c0 (by simp [h1, hH.pA1, hH.pC0])
    refine ⟨0, 0, 1, by simp, ((t1.add t2).sub t3).congr ?_⟩
    funext e
    simp only [spoke, anchor, h1, Fin.one_eq_zero_iff, hubForm, pi1, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    simp
    ring

theorem hubReduces_edge_cross (hH : H.Good p G) {x y : V} (hx : InW p G H x)
    (hy : InW p G H y) (hxy : G.Adj x y) (hx0 : p x = 0) (hy1 : p y = 1) :
    HubReduces p G H (edgeInd x y + spoke p H x + spoke p H y) 3 2 := by
  obtain ⟨-, xc0, -⟩ := hx.1 hx0
  obtain ⟨ya0, ya1, yc0⟩ := hy.2 hy1
  have t1 := realizes_triangle (p := p) hxy xc0 yc0 (by simp [hx0, hy1])
  have t2 := realizes_triangle (p := p) ya0 ya1 hH.a0a1 (by simp [hy1, hH.pA0, hH.pA1])
  have t3 := realizes_triangle (p := p) ya1 yc0 hH.a1c0 (by simp [hy1, hH.pA1, hH.pC0])
  refine ⟨1, 0, 1, by simp, ((t1.add t2).sub t3).congr ?_⟩
  funext e
  simp only [spoke, anchor, hx0, hy1, Fin.one_eq_zero_iff, hubForm, pi1,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  simp
  ring

/-- **Edge between attached vertices.** `[xy] + spoke x + spoke y` reduces with cost `(3, 2)`. -/
theorem hubReduces_edge (hH : H.Good p G) {x y : V} (hx : InW p G H x) (hy : InW p G H y)
    (hxy : G.Adj x y) :
    HubReduces p G H (edgeInd x y + spoke p H x + spoke p H y) 3 2 := by
  rcases fin2_cases (p x) with hx0 | hx1 <;> rcases fin2_cases (p y) with hy0 | hy1
  · obtain ⟨-, xc0, -⟩ := hx.1 hx0
    obtain ⟨-, yc0, -⟩ := hy.1 hy0
    have t := realizes_triangle (p := p) hxy xc0 yc0 (by simp [hx0, hy0, hH.pC0])
    refine (HubReduces.of_realizes t).mono (by norm_num) (by norm_num) |>.congr ?_
    funext e; simp [spoke, anchor, hx0, hy0]
  · exact hubReduces_edge_cross hH hx hy hxy hx0 hy1
  · refine (hubReduces_edge_cross hH hy hx hxy.symm hy0 hx1).congr ?_
    rw [edgeInd_comm y x]; abel
  · obtain ⟨xa0, -, -⟩ := hx.2 hx1
    obtain ⟨ya0, -, -⟩ := hy.2 hy1
    have t := realizes_triangle (p := p) hxy xa0 ya0 (by simp [hx1, hy1, hH.pA0])
    refine (HubReduces.of_realizes t).mono (by norm_num) (by norm_num) |>.congr ?_
    funext e; simp [spoke, anchor, hx1, hy1]

/-- `π₀ - 2[A0C0]` is realizable with seven triangles. -/
theorem realizes_pi0_sub (hH : H.Good p G) :
    Realizes p G (pi0 H - 2 • edgeInd H.A0 H.C0) 7 := by
  have q1 := realizes_triangle (p := p) hH.a1a2.symm hH.a2c1 hH.a1c1
    (by simp [hH.pA1, hH.pA2, hH.pC1])
  have q2 := realizes_triangle (p := p) hH.a1a2.symm hH.a2c0 hH.a1c0
    (by simp [hH.pA1, hH.pA2, hH.pC0])
  have q3 := realizes_triangle (p := p) hH.a0a2.symm hH.a2c1 hH.a0c1
    (by simp [hH.pA0, hH.pA2, hH.pC1])
  have q4 := realizes_triangle (p := p) hH.a0a2.symm hH.a2c0 hH.a0c0
    (by simp [hH.pA0, hH.pA2, hH.pC0])
  have r1 := realizes_triangle (p := p) hH.a0a1 hH.a0c1 hH.a1c1
    (by simp [hH.pA0, hH.pA1, hH.pC1])
  have r2 := realizes_triangle (p := p) hH.a0a1 hH.a0c0 hH.a1c0
    (by simp [hH.pA0, hH.pA1, hH.pC0])
  have r3 := realizes_triangle (p := p) hH.a0c0 hH.a0c1 hH.c0c1
    (by simp [hH.pA0, hH.pC0, hH.pC1])
  refine ((((((r1.sub r2).sub q1).add q2).add q3).sub q4).sub r3).mono (by norm_num)
    |>.congr ?_
  funext e
  simp only [pi0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
  simp
  ring

/-- `π₁ - 2[A0C0]` is realizable with seven triangles. -/
theorem realizes_pi1_sub (hH : H.Good p G) :
    Realizes p G (pi1 H - 2 • edgeInd H.A0 H.C0) 7 := by
  have q1 := realizes_triangle (p := p) hH.a1a2.symm hH.a2c1 hH.a1c1
    (by simp [hH.pA1, hH.pA2, hH.pC1])
  have q2 := realizes_triangle (p := p) hH.a1a2.symm hH.a2c0 hH.a1c0
    (by simp [hH.pA1, hH.pA2, hH.pC0])
  have q3 := realizes_triangle (p := p) hH.a0a2.symm hH.a2c1 hH.a0c1
    (by simp [hH.pA0, hH.pA2, hH.pC1])
  have q4 := realizes_triangle (p := p) hH.a0a2.symm hH.a2c0 hH.a0c0
    (by simp [hH.pA0, hH.pA2, hH.pC0])
  have r1 := realizes_triangle (p := p) hH.a1c0 hH.a1c1 hH.c0c1
    (by simp [hH.pA1, hH.pC0, hH.pC1])
  have r2 := realizes_triangle (p := p) hH.a0c0 hH.a0c1 hH.c0c1
    (by simp [hH.pA0, hH.pC0, hH.pC1])
  have r3 := realizes_triangle (p := p) hH.a0a1 hH.a0c0 hH.a1c0
    (by simp [hH.pA0, hH.pA1, hH.pC0])
  refine ((((((r1.sub r2).sub q1).add q2).add q3).sub q4).sub r3).mono (by norm_num)
    |>.congr ?_
  funext e
  simp only [pi1, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
  simp
  ring

theorem charge_hubForm (hH : H.Good p G) (α β γ : ℤ) :
    charge p (hubForm H α β γ) = α + 2 * β + 2 * γ := by
  simp only [hubForm, pi0, pi1, charge_add, charge_smul, sub_eq_add_neg,
    ← neg_one_smul ℤ (edgeInd _ _ : Sym2 V → ℤ), charge_edgeInd, hH.pA0, hH.pA1, hH.pC0,
    hH.pC1]
  simp
  ring

/-- **Closing the frame.** A charge-zero edge function that hub-reduces with cost `(w, M)` is
an actual triangle combination of weight `≤ w + 7M`. -/
theorem realizes_of_hubReduces (hH : H.Good p G) {f : Sym2 V → ℤ} {w M : ℤ}
    (h : HubReduces p G H f w M) (hf : charge p f = 0) : Realizes p G f (w + 7 * M) := by
  obtain ⟨α, β, γ, hM, hr⟩ := h
  have hc := hr.charge_eq_zero
  rw [charge_sub, hf, charge_hubForm hH] at hc
  have hα : α = -2 * β - 2 * γ := by linarith
  have h0 := (realizes_pi0_sub hH).smul β
  have h1 := (realizes_pi1_sub hH).smul γ
  have hsum := (hr.add (h0.add h1)).congr (show _ = f by
    funext e
    simp only [hubForm, hα, pi0, pi1, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    ring)
  refine hsum.mono ?_
  have := abs_nonneg α
  nlinarith [abs_nonneg β, abs_nonneg γ]

end PartitionedTriangleAbsorption.IntegerCertificate
