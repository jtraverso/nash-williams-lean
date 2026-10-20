/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.QuadParity
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Complete bounded signed triangle certificates in the non-extremal branch

Combining the robust quadrilateral parity filling (`QuadParity.lean`, Stage 256) with the
doubled-edge transport of Stage 265 (`SignedTransportStage265.nonextremal_transport_cost`), we
prove: under exactly the hypotheses of Stage 265 (`δ ≥ (3/4 - e) n`, not `a`-extremal,
`0 < a ≤ 1`, `0 ≤ e`, `10⁶ e ≤ a²`, `n > 0`), every integer edge function `w` supported on `E(G)`
with all weighted degrees even and total weight divisible by `3` has a physical certificate
`w = ∑ c_j · [T_j]` by actual triangles `T_j` of `G`, of cost `∑ |c_j| ≤ 16741 · ‖w‖₁`.

Construction.
* *Parity.*  A root `r` and, for each vertex `v`, a common neighbour `m(v)` of `r, v` give, for
  every edge `uv`, the closed walk `r m(u) u v m(v)` of length five.  Each closed 5-walk is
  `quad + triangle + quad` modulo two (using a common neighbour of three of its vertices), so it
  is `g + 2h` with `g` of cost `≤ 57`.  Summing `w(uv)` times these walks gives
  `w + ∑_v deg_w(v) π_v`, and `deg_w(v)` is even, so `w = G' + 2U`.
* *Doubled edges.*  `2U = ∑_f U(f) · 2([f] - [f₀]) + 2(∑U)[f₀]`; the first part is Stage 265
  transport, and `∑U ≡ 0 (mod 3)` because `w` and `G'` have total weight `≡ 0 (mod 3)`; finally
  `6[f₀] = 2Δ − 2([f₁] - [f₀]) − 2([f₂] - [f₀])` for a triangle `Δ = f₀f₁f₂`.

This is a signed (integer) certificate: it is not a nonnegative decomposition and it does not
construct absorbers.
-/

namespace NashWilliams18.ParityFill

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.BlowupB
  PartitionedTriangleAbsorption.OnePart

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closed walk `v₀ v₁ v₂ v₃ v₄` as an integer edge function. -/
def pent (v₀ v₁ v₂ v₃ v₄ : V) : Sym2 V → ℤ :=
  ind1 s(v₀, v₁) + ind1 s(v₁, v₂) + ind1 s(v₂, v₃) + ind1 s(v₃, v₄) + ind1 s(v₄, v₀)

/-- The weighted degree of `v` in the integer edge function `w`. -/
def degw (w : Sym2 V → ℤ) (v : V) : ℤ := ∑ e, if v ∈ e then w e else 0

/-- The `ℓ¹` norm of an integer edge function. -/
def l1 (w : Sym2 V → ℤ) : ℤ := ∑ e, |w e|

/-! ### Basic facts on physical certificates -/

theorem sum_indZ (E : Finset (Sym2 V)) : ∑ e, indZ E e = E.card := by
  simp [indZ, sum_ite_mem]

omit [Fintype V] in
theorem card_triEdges_of_card {s : Finset V} (hs : s.card = 3) : (triEdges s).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs
  rw [triEdges_three hab hac hbc]
  have h1 : s(a, b) ∉ ({s(a, c), s(b, c)} : Finset (Sym2 V)) := by simp [hab, hac, hbc]
  have h2 : s(a, c) ∉ ({s(b, c)} : Finset (Sym2 V)) := by simp [hab, hac]
  rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]

/-- A physical certificate of cost `K` has `ℓ¹` norm at most `3K` and total weight divisible
by `3`. -/
theorem physCostZ_l1_le_and_dvd {G : SimpleGraph V} {g : Sym2 V → ℤ} {K : ℤ}
    (h : PhysCostZ part1 triFam G g K) : l1 g ≤ 3 * K ∧ (3 : ℤ) ∣ ∑ e, g e := by
  obtain ⟨ι, _, T, c, ⟨hT, hg⟩, hK⟩ := h
  have hcard : ∀ j, ∑ e, indZ (triEdges (T j)) e = 3 := by
    intro j
    rw [sum_indZ, card_triEdges_of_card (hT j).1.card_eq]; rfl
  constructor
  · calc l1 g = ∑ e, |∑ j, c j * indZ (triEdges (T j)) e| := by
          simp only [l1, hg]
      _ ≤ ∑ e, ∑ j, |c j| * indZ (triEdges (T j)) e := by
          refine sum_le_sum fun e _ => (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine sum_congr rfl fun j _ => ?_
          rw [abs_mul]
          congr 1
          simp only [indZ]; split_ifs <;> simp
      _ = ∑ j, |c j| * 3 := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [← mul_sum, hcard]
      _ ≤ 3 * K := by rw [← sum_mul]; linarith
  · refine ⟨∑ j, c j, ?_⟩
    calc ∑ e, g e = ∑ e, ∑ j, c j * indZ (triEdges (T j)) e := by simp only [hg]
      _ = ∑ j, c j * 3 := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [← mul_sum, hcard]
      _ = 3 * ∑ j, c j := by rw [← sum_mul, mul_comm]

/-- Every integer edge function is the sum of its weighted indicators. -/
theorem eq_sum_ind1 (w : Sym2 V → ℤ) : w = ∑ e, w e • ind1 e := by
  funext f
  rw [Finset.sum_apply]
  simp [ind1_apply]

/-! ### The hypotheses of Stage 265 -/

/-- The Stage 265 hypotheses on `G`: `δ(G) ≥ (3/4 - e) n` (as `n ≤ deg v + (1/4 + e) n`),
`G` not `a`-extremal (raw Definition 12.2), `0 < a ≤ 1`, `0 ≤ e`, `10⁶ e ≤ a²`, `n > 0`. -/
structure NonextHyp (G : SimpleGraph V) [DecidableRel G.Adj] (a e : ℝ) : Prop where
  ha : 0 < a
  ha1 : a ≤ 1
  he : 0 ≤ e
  hn : 0 < Fintype.card V
  hsmall : 1000000 * e ≤ a * a
  hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V
  hnot : ¬ ExtrF G a

namespace NonextHyp

variable {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ}

theorem e_le (H : NonextHyp G a e) : e ≤ 1 / 1000000 := by
  have := H.hsmall; have := H.ha; have := H.ha1; nlinarith

theorem eight_e_le (H : NonextHyp G a e) : 8 * e ≤ a := by
  have := H.hsmall; have := H.ha; have := H.ha1; have := H.he; nlinarith

/-- Stage 265 doubled-edge transport. -/
theorem transport (H : NonextHyp G a e) {u v x y : V} (huv : G.Adj u v) (hxy : G.Adj x y) :
    PhysCostZ part1 triFam G ((2 : ℤ) • (ind1 s(u, v) - ind1 s(x, y))) 116 :=
  SignedTransportStage265.nonextremal_transport_cost G a e H.ha H.ha1 H.he H.hn H.hsmall
    H.hdeg H.hnot huv hxy

/-- Stage 256 quadrilateral filling under the Stage 265 hypotheses. -/
theorem quad (H : NonextHyp G a e) {v₀ v₁ v₂ v₃ : V} (h01 : G.Adj v₀ v₁) (h12 : G.Adj v₁ v₂)
    (h23 : G.Adj v₂ v₃) (h30 : G.Adj v₃ v₀) :
    ∃ g h : Sym2 V → ℤ, PhysCostZ part1 triFam G g 28 ∧ GEdge G h ∧
      quad v₀ v₁ v₂ v₃ = g + (2 : ℤ) • h :=
  quad_fill G e a H.he (by linarith [H.e_le]) H.eight_e_le H.hdeg H.hnot h01 h12 h23 h30

/-- Any three vertices have a common neighbour. -/
theorem common3 (H : NonextHyp G a e) (u v w : V) :
    ∃ z, G.Adj u z ∧ G.Adj v z ∧ G.Adj w z := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast H.hn
  have := H.e_le
  exact AllLinksStage263.common_three G ((1 / 4 + e) * Fintype.card V) H.hdeg
    (by nlinarith) u v w

end NonextHyp

/-- **Parity filling of a closed 5-walk**: `pent = g + 2h`, `g` of cost `≤ 57`. -/
theorem pent_fill {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ} (H : NonextHyp G a e)
    {v₀ v₁ v₂ v₃ v₄ : V} (h01 : G.Adj v₀ v₁) (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃)
    (h34 : G.Adj v₃ v₄) (h40 : G.Adj v₄ v₀) :
    ∃ g h : Sym2 V → ℤ, PhysCostZ part1 triFam G g 57 ∧ GEdge G h ∧
      pent v₀ v₁ v₂ v₃ v₄ = g + (2 : ℤ) • h := by
  obtain ⟨y, h0y, h2y, h3y⟩ := H.common3 v₀ v₂ v₃
  obtain ⟨g₁, k₁, hg₁, hk₁, e₁⟩ := H.quad h01 h12 h2y h0y.symm
  obtain ⟨g₂, k₂, hg₂, hk₂, e₂⟩ := H.quad h0y h3y.symm h34 h40
  have ht := tri_cost G h2y.symm h3y.symm h23
  refine ⟨g₁ + _ + g₂, k₁ + k₂ - (ind1 s(v₂, y) + ind1 s(v₀, y) + ind1 s(v₃, y)),
    ((hg₁.add ht).add hg₂).mono (by norm_num), ?_, ?_⟩
  · exact (hk₁.add hk₂).sub (((GEdge.ind1 h2y).add (GEdge.ind1 h0y)).add (GEdge.ind1 h3y))
  · have f₁ := congrFun e₁
    have f₂ := congrFun e₂
    funext x
    have := f₁ x
    have := f₂ x
    simp only [pent, quad, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [Sym2.eq_swap (a := y) (b := v₀), Sym2.eq_swap (a := y) (b := v₂),
      Sym2.eq_swap (a := y) (b := v₃)] at *
    linarith

/-! ### Hub walks and the parity reduction -/

/-- The hub path `r - m(v) - v`. -/
def hubPath (r : V) (m : V → V) (v : V) : Sym2 V → ℤ := ind1 s(r, m v) + ind1 s(m v, v)

/-- Sum of the hub paths of the endpoints of `e`. -/
def hubPhi (r : V) (m : V → V) (e : Sym2 V) : Sym2 V → ℤ :=
  ∑ x, if x ∈ e then hubPath r m x else 0

theorem sum_smul_hubPhi (r : V) (m : V → V) (w : Sym2 V → ℤ) :
    ∑ e, w e • hubPhi r m e = ∑ v, degw w v • hubPath r m v := by
  simp only [hubPhi, degw, smul_sum, sum_smul]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem hubPhi_mk (r : V) (m : V → V) {u v : V} (huv : u ≠ v) :
    hubPhi r m s(u, v) = hubPath r m u + hubPath r m v := by
  have : (univ.filter (fun x => x ∈ s(u, v))) = {u, v} := by
    ext x; simp
  rw [hubPhi, ← sum_filter, this, sum_pair huv]

theorem ind1_add_hubPhi (r : V) (m : V → V) {u v : V} (huv : u ≠ v) :
    ind1 s(u, v) + hubPhi r m s(u, v) = pent r (m u) u v (m v) := by
  rw [hubPhi_mk r m huv]
  funext x
  simp only [hubPath, pent, Pi.add_apply, Sym2.eq_swap (a := v) (b := m v),
    Sym2.eq_swap (a := m v) (b := r)]
  ring

theorem NonextHyp.common2 {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ}
    (H : NonextHyp G a e) (u v : V) : ∃ z, G.Adj u z ∧ G.Adj v z := by
  obtain ⟨z, h1, h2, _⟩ := H.common3 u v v
  exact ⟨z, h1, h2⟩

/-- **Parity reduction.**  An integer edge function `w` supported on `E(G)` with all weighted
degrees even is `G' + 2U`, where `G'` has a physical certificate of cost `≤ 57‖w‖₁` and `U` is
supported on `E(G)`. -/
theorem parity_reduction {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ}
    (H : NonextHyp G a e) (w : Sym2 V → ℤ) (hw : GEdge G w) (hdeg2 : ∀ v, 2 ∣ degw w v) :
    ∃ g U : Sym2 V → ℤ, PhysCostZ part1 triFam G g (57 * l1 w) ∧ GEdge G U ∧
      w = g + (2 : ℤ) • U := by
  classical
  obtain ⟨r⟩ : Nonempty V := Fintype.card_pos_iff.mp H.hn
  choose m hm using fun v => H.common2 r v
  have key : ∀ f : Sym2 V, ∃ g h : Sym2 V → ℤ, PhysCostZ part1 triFam G g 57 ∧ GEdge G h ∧
      (f ∈ G.edgeSet → ind1 f + hubPhi r m f = g + (2 : ℤ) • h) := by
    intro f
    induction f using Sym2.ind with
    | _ u v =>
      by_cases huv : G.Adj u v
      · obtain ⟨g, h, hg, hh, he⟩ :=
          pent_fill H (hm u).1 (hm u).2.symm huv (hm v).2 (hm v).1.symm
        exact ⟨g, h, hg, hh, fun _ => by rw [ind1_add_hubPhi r m huv.ne, he]⟩
      · exact ⟨0, 0, (PhysCostZ.zero part1 triFam G).mono (by norm_num), GEdge.zero G,
          fun h => absurd h huv⟩
  choose g h hg hh heq using key
  refine ⟨∑ f, w f • g f, ∑ f, w f • h f - ∑ v, (degw w v / 2) • hubPath r m v, ?_, ?_, ?_⟩
  · refine (PhysCostZ.sum univ (fun f => w f • g f) (fun f => |w f| * 57)
      (fun f _ => (hg f).smul (w f))).mono (le_of_eq ?_)
    rw [l1, mul_sum]; exact sum_congr rfl fun f _ => mul_comm _ _
  · refine (GEdge.sum _ _ fun f _ => (hh f).smul (w f)).sub
      (GEdge.sum _ _ fun v _ => ((GEdge.ind1 (hm v).1).add (GEdge.ind1 (hm v).2.symm)).smul _)
  · have h1 : ∑ f, w f • (ind1 f + hubPhi r m f) = ∑ f, w f • (g f + (2 : ℤ) • h f) := by
      refine sum_congr rfl fun f _ => ?_
      by_cases hwf : w f = 0
      · simp [hwf]
      · rw [heq f (hw f hwf)]
    simp only [smul_add, sum_add_distrib, ← eq_sum_ind1, sum_smul_hubPhi] at h1
    have h2 : ∑ v, degw w v • hubPath r m v =
        (2 : ℤ) • ∑ v, (degw w v / 2) • hubPath r m v := by
      rw [smul_sum]
      refine sum_congr rfl fun v _ => ?_
      rw [smul_smul, Int.mul_ediv_cancel' (hdeg2 v)]
    have h3 : ∑ f, w f • (2 : ℤ) • h f = (2 : ℤ) • ∑ f, w f • h f := by
      rw [smul_sum]; exact sum_congr rfl fun f _ => smul_comm _ _ _
    rw [h2, h3] at h1
    rw [smul_sub]
    have h4 := eq_sub_of_add_eq h1
    calc w = _ := h4
      _ = _ := by abel

/-! ### Doubled edge functions and the complete certificate -/

/-- **Doubled edge functions.**  If `U` is supported on `E(G)` and `3 ∣ ∑ U`, then `2U` has a
physical certificate of cost `≤ 194 ‖U‖₁` (Stage 265 transport to a fixed edge `f₀`, plus
`6[f₀] = 2Δ − 2([f₁]-[f₀]) − 2([f₂]-[f₀])`). -/
theorem doubled_cert {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ}
    (H : NonextHyp G a e) (U : Sym2 V → ℤ) (hU : GEdge G U) (h3 : (3 : ℤ) ∣ ∑ f, U f) :
    PhysCostZ part1 triFam G ((2 : ℤ) • U) (194 * l1 U) := by
  classical
  obtain ⟨x₀⟩ : Nonempty V := Fintype.card_pos_iff.mp H.hn
  obtain ⟨y₀, hxy, _⟩ := H.common2 x₀ x₀
  obtain ⟨z₀, hxz, hyz, _⟩ := H.common3 x₀ y₀ y₀
  have h6 : PhysCostZ part1 triFam G ((6 : ℤ) • ind1 s(x₀, y₀)) 234 := by
    have := (((tri_cost G hxy hxz hyz).smul 2).sub (H.transport hxz hxy)).sub
      (H.transport hyz hxy)
    refine (this.congr ?_).mono (by norm_num)
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨k, hk⟩ := h3
  have hterm : ∀ f, PhysCostZ part1 triFam G (U f • ((2 : ℤ) • (ind1 f - ind1 s(x₀, y₀))))
      (|U f| * 116) := by
    intro f
    induction f using Sym2.ind with
    | _ u v =>
      by_cases hz : U s(u, v) = 0
      · rw [hz, zero_smul, abs_zero, zero_mul]; exact PhysCostZ.zero part1 triFam G
      · exact (H.transport (hU _ hz) hxy).smul _
  have hsum := PhysCostZ.sum univ _ _ (fun f _ => hterm f)
  have htot := hsum.add (h6.smul k)
  have hid : ∑ f, U f • ((2 : ℤ) • (ind1 f - ind1 s(x₀, y₀))) +
      k • (6 : ℤ) • ind1 s(x₀, y₀) = (2 : ℤ) • U := by
    have hU' := eq_sum_ind1 U
    have : ∑ f, U f • ((2 : ℤ) • (ind1 f - ind1 s(x₀, y₀))) =
        (2 : ℤ) • ∑ f, U f • ind1 f - (2 * ∑ f, U f) • ind1 s(x₀, y₀) := by
      simp only [smul_sub, sum_sub_distrib, smul_sum, smul_comm (U _) (2 : ℤ)]
      congr 1
      rw [mul_smul, sum_smul, smul_sum]
    rw [this, ← hU', hk, smul_smul, show (2 : ℤ) * (3 * k) = k * 6 by ring, sub_add_cancel]
  rw [hid] at htot
  refine htot.mono ?_
  have habs : 3 * |k| ≤ l1 U := by
    have : |∑ f, U f| ≤ l1 U := abs_sum_le_sum_abs _ _
    rw [hk, abs_mul] at this
    simpa using this
  have hsumK : ∑ f, |U f| * 116 = 116 * l1 U := by rw [l1, mul_sum]; simp [mul_comm]
  rw [hsumK]
  linarith

/-- **Complete bounded signed certificate (non-extremal branch).**  Under the Stage 265
hypotheses, every integer edge function `w` supported on `E(G)`, with every weighted degree even
and total weight divisible by `3`, is an integer combination of actual triangles of `G` with
total coefficient size at most `16741 ‖w‖₁`. -/
theorem signed_certificate {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ}
    (H : NonextHyp G a e) (w : Sym2 V → ℤ) (hw : GEdge G w) (hdeg2 : ∀ v, 2 ∣ degw w v)
    (h3 : (3 : ℤ) ∣ ∑ f, w f) :
    PhysCostZ part1 triFam G w (16741 * l1 w) := by
  obtain ⟨g, U, hg, hU, hwgU⟩ := parity_reduction H w hw hdeg2
  obtain ⟨hgl1, hg3⟩ := physCostZ_l1_le_and_dvd hg
  have hsum : ∑ f, w f = ∑ f, g f + 2 * ∑ f, U f := by
    conv_lhs => rw [hwgU]
    simp [sum_add_distrib, mul_sum]
  have hU3 : (3 : ℤ) ∣ ∑ f, U f := by omega
  have hl1U : 2 * l1 U ≤ l1 w + l1 g := by
    rw [l1, l1, l1, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun f _ => ?_
    have := congrFun hwgU f
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    have := abs_sub_le_iff.mp (le_refl |g f + 2 * U f - g f|)
    cases abs_cases (U f) <;> cases abs_cases (g f) <;> cases abs_cases (g f + 2 * U f) <;>
      linarith
  have hd := doubled_cert H U hU hU3
  have htot := hg.add hd
  rw [← hwgU] at htot
  refine htot.mono ?_
  have : 0 ≤ l1 w := sum_nonneg fun f _ => abs_nonneg _
  linarith

end NashWilliams18.ParityFill
