/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.PairSumTail
public import RequestProject.NW18.Case126.PuncturedLoadF1

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: sampling the protected cross reserve of a vortex level (producer)

Producer obligation 1 for the cross reserve.  Every cross pair `(x, z)`, `x ∈ W \ U`, `z ∈ U`,
`xz ∈ E(H)`, is put into the reserve `Res` independently with probability `ρ`
(`crossRes H W U ω`, `ω : V × V → Bool`, Bernoulli(`ρ`) coordinates).  All reserve densities are
the same number `ρ` BY DESIGN of the sampling (not by assumption on the host).

`cross_reserve_exists` (proved): for every `ε > 0` there is `N` such that for every level with
`|W| ≥ N` and every `ρ ∈ [0, 1]`, some outcome `Res ⊆ E(H)` of cross edges satisfies, with
`n = |W|` and every class `l`:

* (R1) for distinct outside `a, b`: the common `H`-neighbours of `a, b` in `U_l` with both edges
  unreserved number `(1-ρ)² |C| ± εn`;
* (R2) for outside `a` and child `b`: the common `H`-neighbours in `(W \ U)_l` with `bz`
  unreserved number `(1-ρ) |C| ± εn`;
* (R3) for distinct outside `a, b`: those with BOTH edges reserved number `ρ² |C| ± εn`
  (apex supply and pairwise overlaps of the cross neighbourhoods);
* (R4) for outside `x`: the reserved neighbours of `x` in `U_l` number `ρ |N_H(x) ∩ U_l| ± εn`
  (margins of the cross neighbourhoods);
* (R5) for a child `v`: the reserved neighbours of `v` in `W \ U` number `ρ |N_H(v) ∖ U| ± εn`
  (visit load of the pairing step).

(R1), (R2) and "no reserved edge outside `U`" are exactly the reserve hypotheses of `PuncHyp`
with `q = 1 - ρ`.
-/

namespace NashWilliams18.SpreadF1

open Finset Pseudorandom NashWilliams18.Sampling

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The sampled cross reserve. -/
def crossRes (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V) (ω : V × V → Bool) :
    Finset (Sym2 V) :=
  (((W \ U) ×ˢ U).filter fun xz => H.Adj xz.1 xz.2 ∧ ω xz = true).image fun xz => s(xz.1, xz.2)

section Res

variable (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V) (ω : V × V → Bool)

omit [Fintype V] in
lemma mem_crossRes_iff {a z : V} (haU : a ∉ U) (hzU : z ∈ U) :
    s(a, z) ∈ crossRes H W U ω ↔ a ∈ W ∧ H.Adj a z ∧ ω (a, z) = true := by
  unfold crossRes
  simp only [mem_image, mem_filter, mem_product, mem_sdiff, Prod.exists]
  constructor
  · rintro ⟨x, z', ⟨⟨⟨hxW, hxU⟩, hz'U⟩, hH, hω⟩, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hxW, hH, hω⟩
    · exact absurd hzU hxU
  · rintro ⟨haW, hH, hω⟩
    exact ⟨a, z, ⟨⟨⟨haW, haU⟩, hzU⟩, hH, hω⟩, rfl⟩

omit [Fintype V] in
lemma crossRes_not_out {x z : V} (hx : x ∉ U) (hz : z ∉ U) : s(x, z) ∉ crossRes H W U ω := by
  unfold crossRes
  simp only [mem_image, mem_filter, mem_product, mem_sdiff, Prod.exists, not_exists, not_and]
  intro a b ⟨⟨_, hbU⟩, _⟩ he
  rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact hz (h2 ▸ hbU)
  · exact hx (h2 ▸ hbU)

lemma crossRes_sub : crossRes H W U ω ⊆ H.edgeFinset := by
  intro e he
  unfold crossRes at he
  obtain ⟨⟨x, z⟩, hxz, rfl⟩ := mem_image.mp he
  exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp hxz).2.1

omit [Fintype V] in
lemma crossRes_cross : ∀ e ∈ crossRes H W U ω, ∃ x ∈ W \ U, ∃ z ∈ U, e = s(x, z) := by
  intro e he
  unfold crossRes at he
  obtain ⟨⟨x, z⟩, hxz, rfl⟩ := mem_image.mp he
  obtain ⟨hp, -⟩ := mem_filter.mp hxz
  exact ⟨x, (mem_product.mp hp).1, z, (mem_product.mp hp).2, rfl⟩

end Res

/-! ### Indicator kernels -/

/-- Both coordinates unreserved. -/
noncomputable def gFF : Bool → Bool → ℝ := fun x y => if x = false ∧ y = false then 1 else 0
/-- Both coordinates reserved. -/
noncomputable def gTT : Bool → Bool → ℝ := fun x y => if x = true ∧ y = true then 1 else 0
/-- First coordinate unreserved. -/
noncomputable def gF : Bool → Bool → ℝ := fun x _ => if x = false then 1 else 0
/-- First coordinate reserved. -/
noncomputable def gT : Bool → Bool → ℝ := fun x _ => if x = true then 1 else 0

lemma g01 (g : Bool → Bool → ℝ) (hg : g = gFF ∨ g = gTT ∨ g = gF ∨ g = gT) :
    (∀ x y, 0 ≤ g x y) ∧ ∀ x y, g x y ≤ 1 := by
  rcases hg with rfl | rfl | rfl | rfl <;>
  · refine ⟨fun x y => ?_, fun x y => ?_⟩ <;>
    · cases x <;> cases y <;> simp [gFF, gTT, gF, gT]

omit [Fintype V] [DecidableEq V] in
/-- A filtered count is a sum of indicators. -/
lemma card_filter_eq_sum (C : Finset V) (P : V → Prop) [DecidablePred P] :
    ((C.filter P).card : ℝ) = ∑ z ∈ C, if P z then (1 : ℝ) else 0 := by
  rw [card_filter]; push_cast; rfl

/-! ### Expectations -/

section Expect

variable {ρ : ℝ}

lemma pE_pairSum (k₁ k₂ : V → V × V) (C : Finset V) (g : Bool → Bool → ℝ) :
    pE (bern ρ) (pairSum k₁ k₂ C g) =
      ∑ z ∈ C, pE (bern ρ) (fun ω => g (ω (k₁ z)) (ω (k₂ z))) := by
  unfold pairSum; rw [pE_sum]

lemma pE_term_pair (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (i j : V × V) (hij : i ≠ j)
    (g : Bool → Bool → ℝ) :
    pE (bern ρ) (fun ω => g (ω i) (ω j)) =
      ρ * ρ * g true true + ρ * (1 - ρ) * g true false + (1 - ρ) * ρ * g false true +
        (1 - ρ) * (1 - ρ) * g false false := by
  rw [pE_pair (bern_isPMF hρ0 hρ1) hij]
  simp [bern]; ring

lemma pE_term_single (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (i j : V × V) (g : Bool → Bool → ℝ)
    (h : Bool → ℝ) (hg : ∀ x y, g x y = h x) :
    pE (bern ρ) (fun ω => g (ω i) (ω j)) = ρ * h true + (1 - ρ) * h false := by
  have e : (fun ω : V × V → Bool => g (ω i) (ω j)) = fun ω => h (ω i) :=
    funext fun ω => hg _ _
  rw [e, pE_coord (bern_isPMF hρ0 hρ1)]
  simp [bern]

end Expect

/-! ### Family tails -/

lemma family_tail {κ : Type*} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Idx : Finset κ)
    (k₁ k₂ : κ → V → V × V) (C : κ → Finset V) (g : κ → Bool → Bool → ℝ)
    (hg0 : ∀ i, ∀ x y, 0 ≤ g i x y) (hg1 : ∀ i, ∀ x y, g i x y ≤ 1)
    (hk₁ : ∀ i, Set.InjOn (k₁ i) (C i)) (hk₂ : ∀ i, Set.InjOn (k₂ i) (C i))
    (hk : ∀ i, ∀ z ∈ C i, ∀ z' ∈ C i, k₁ i z = k₂ i z' → z = z')
    (n t : ℝ) (ht : 0 < t) (hC : ∀ i, ((C i).card : ℝ) ≤ n) :
    pProb (bern ρ) (fun ω => ∃ i ∈ Idx,
        t ≤ |pairSum (k₁ i) (k₂ i) (C i) (g i) ω - pE (bern ρ) (pairSum (k₁ i) (k₂ i) (C i) (g i))|)
      ≤ Idx.card * (2 * Real.exp (-(t ^ 2 / (2 * (2 * n + t))))) := by
  refine (pProb_exists_le (bern_isPMF hρ0 hρ1) Idx _).trans ?_
  have hb : ∀ i ∈ Idx, pProb (bern ρ) (fun ω =>
      t ≤ |pairSum (k₁ i) (k₂ i) (C i) (g i) ω - pE (bern ρ) (pairSum (k₁ i) (k₂ i) (C i) (g i))|)
        ≤ 2 * Real.exp (-(t ^ 2 / (2 * (2 * n + t)))) := by
    intro i _
    refine (pairSum_tail (bern_isPMF hρ0 hρ1) (k₁ i) (k₂ i) (C i) (g i) (hg0 i) (hg1 i)
      (hk₁ i) (hk₂ i) (hk i) t ht).trans ?_
    have h0 : (0 : ℝ) ≤ (C i).card := Nat.cast_nonneg _
    have := exp_mono_aux (t := t) (A := 2 * ((C i).card : ℝ)) (B := 2 * n) (by linarith)
      (by linarith [hC i])
    linarith
  calc _ ≤ ∑ _i ∈ Idx, 2 * Real.exp (-(t ^ 2 / (2 * (2 * n + t)))) := sum_le_sum hb
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-! ### The good reserve -/

/-- The properties of a good sampled cross reserve (see the module docstring). -/
structure CrossResGood (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V)
    (Res : Finset (Sym2 V)) (ρ ε : ℝ) : Prop where
  sub : Res ⊆ H.edgeFinset
  cross : ∀ e ∈ Res, ∃ x ∈ W \ U, ∃ z ∈ U, e = s(x, z)
  out : ∀ x z, x ∉ U → z ∉ U → s(x, z) ∉ Res
  r1 : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → a ∉ U → b ∉ U → ∀ l : Fin 4,
    |((U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∉ Res ∧ s(b, z) ∉ Res).card
        : ℝ) - (1 - ρ) ^ 2 * (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| ≤
      ε * W.card
  r2 : ∀ a ∈ W, ∀ b ∈ U, a ∉ U → ∀ l : Fin 4,
    |(((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(b, z) ∉ Res).card : ℝ) -
        (1 - ρ) * ((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| ≤ ε * W.card
  r3 : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → a ∉ U → b ∉ U → ∀ l : Fin 4,
    |((U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ Res ∧ s(b, z) ∈ Res).card
        : ℝ) - ρ ^ 2 * (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| ≤ ε * W.card
  r4 : ∀ x ∈ W, x ∉ U → ∀ c : Fin 4,
    |((U.filter fun z => p z = c ∧ H.Adj x z ∧ s(x, z) ∈ Res).card : ℝ) -
        ρ * (U.filter fun z => p z = c ∧ H.Adj x z).card| ≤ ε * W.card
  r5 : ∀ v ∈ U,
    |(((W \ U).filter fun z => H.Adj v z ∧ s(v, z) ∈ Res).card : ℝ) -
        ρ * ((W \ U).filter fun z => H.Adj v z).card| ≤ ε * W.card

omit [Fintype V] [DecidableEq V] in
lemma count_eq_pairSum (ω : V × V → Bool) (C : Finset V) (Q : V → Prop) [DecidablePred Q]
    (k₁ k₂ : V → V × V) (g : Bool → Bool → ℝ)
    (h : ∀ z ∈ C, (if Q z then (1 : ℝ) else 0) = g (ω (k₁ z)) (ω (k₂ z))) :
    ((C.filter Q).card : ℝ) = pairSum k₁ k₂ C g ω := by
  rw [card_filter_eq_sum]; exact sum_congr rfl h

lemma pE_pairSum_const {ρ : ℝ} (k₁ k₂ : V → V × V) (C : Finset V) (g : Bool → Bool → ℝ) (m : ℝ)
    (h : ∀ z ∈ C, pE (bern ρ) (fun ω => g (ω (k₁ z)) (ω (k₂ z))) = m) :
    pE (bern ρ) (pairSum k₁ k₂ C g) = C.card * m := by
  rw [pE_pairSum, sum_congr rfl h, sum_const, nsmul_eq_mul]

/-- From a good sample to a deviation bound. -/
lemma dev_of_good {X Y E m c t : ℝ} (hX : X = Y) (hE : E = c * m) (hg : ¬ t ≤ |Y - E|) :
    |X - m * c| ≤ t := by
  rw [hX, mul_comm, ← hE]; push_neg at hg; exact hg.le

/-- **Sampling the cross reserve** (producer, proved). -/
theorem cross_reserve_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (H : SimpleGraph V)
      [DecidableRel H.Adj] (W U : Finset V) (ρ : ℝ), U ⊆ W → 0 ≤ ρ → ρ ≤ 1 → N ≤ W.card →
      ∃ Res : Finset (Sym2 V), CrossResGood p H W U Res ρ ε := by
  set c : ℝ := ε ^ 2 / (4 + 2 * ε) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨m₀, hm₀⟩ := eventually_pow_mul_exp_le 2 hc0 (ε := 1 / 10) (by norm_num)
  refine ⟨max m₀ 1, ?_⟩
  intro V _ _ p H _ W U ρ hUW hρ0 hρ1 hN
  classical
  have hP := bern_isPMF (ι := V × V) hρ0 hρ1
  have hn1 : 1 ≤ W.card := le_trans (le_max_right _ _) hN
  set n : ℝ := (W.card : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast hn1
  set t : ℝ := ε * n with ht
  have ht0 : 0 < t := by positivity
  -- the exponent
  have hexp : t ^ 2 / (2 * (2 * n + t)) = c * n := by
    rw [ht, hc]; field_simp; ring
  have hsmall : (2 * n) ^ 2 * Real.exp (-(c * n)) ≤ 1 / 10 := by
    have := hm₀ W.card (le_trans (le_max_left _ _) hN)
    simpa [hndef] using this
  -- the families
  let I1 : Finset ((V × V) × Fin 4) := (W ×ˢ W) ×ˢ univ
  let I4 : Finset (V × Fin 4) := W ×ˢ univ
  let C1 : (V × V) × Fin 4 → Finset V := fun i =>
    U.filter fun z => p z = i.2 ∧ H.Adj i.1.1 z ∧ H.Adj i.1.2 z
  let C2 : (V × V) × Fin 4 → Finset V := fun i =>
    (W \ U).filter fun z => p z = i.2 ∧ H.Adj i.1.1 z ∧ H.Adj i.1.2 z
  let C4 : V × Fin 4 → Finset V := fun i => U.filter fun z => p z = i.2 ∧ H.Adj i.1 z
  let C5 : V → Finset V := fun v => (W \ U).filter fun z => H.Adj v z
  let A1 : (V × V) × Fin 4 → V → V × V := fun i z => (i.1.1, z)
  let B1 : (V × V) × Fin 4 → V → V × V := fun i z => (i.1.2, z)
  let A2 : (V × V) × Fin 4 → V → V × V := fun i z => (z, i.1.2)
  let B2 : (V × V) × Fin 4 → V → V × V := fun i z => (i.1.2, z)
  let A4 : V × Fin 4 → V → V × V := fun i z => (i.1, z)
  let B4 : V × Fin 4 → V → V × V := fun i z => (z, i.1)
  let A5 : V → V → V × V := fun v z => (z, v)
  let B5 : V → V → V × V := fun v z => (v, z)
  have hW : ∀ S : Finset V, S ⊆ W → (S.card : ℝ) ≤ n := fun S hS => by
    rw [hndef]; exact_mod_cast card_le_card hS
  have hC1 : ∀ i, ((C1 i).card : ℝ) ≤ n := fun i => hW _ ((filter_subset _ _).trans hUW)
  have hC2 : ∀ i, ((C2 i).card : ℝ) ≤ n := fun i => hW _ ((filter_subset _ _).trans sdiff_subset)
  have hC4 : ∀ i, ((C4 i).card : ℝ) ≤ n := fun i => hW _ ((filter_subset _ _).trans hUW)
  have hC5 : ∀ i, ((C5 i).card : ℝ) ≤ n := fun i => hW _ ((filter_subset _ _).trans sdiff_subset)
  have inj2 : ∀ a : V, Set.InjOn (fun z : V => (a, z)) (Set.univ : Set V) :=
    fun a x _ y _ h => (Prod.mk.inj h).2
  have inj1 : ∀ a : V, Set.InjOn (fun z : V => (z, a)) (Set.univ : Set V) :=
    fun a x _ y _ h => (Prod.mk.inj h).1
  have T1 := family_tail hρ0 hρ1 I1 A1 B1 C1 (fun _ => gFF)
    (fun _ => (g01 gFF (Or.inl rfl)).1) (fun _ => (g01 gFF (Or.inl rfl)).2)
    (fun i => (inj2 i.1.1).mono (Set.subset_univ _)) (fun i => (inj2 i.1.2).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).2) n t ht0 hC1
  have T2 := family_tail hρ0 hρ1 I1 A2 B2 C2 (fun _ => gF)
    (fun _ => (g01 gF (Or.inr (Or.inr (Or.inl rfl)))).1)
    (fun _ => (g01 gF (Or.inr (Or.inr (Or.inl rfl)))).2)
    (fun i => (inj1 i.1.2).mono (Set.subset_univ _)) (fun i => (inj2 i.1.2).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).1.trans (Prod.mk.inj h).2) n t ht0 hC2
  have T3 := family_tail hρ0 hρ1 I1 A1 B1 C1 (fun _ => gTT)
    (fun _ => (g01 gTT (Or.inr (Or.inl rfl))).1) (fun _ => (g01 gTT (Or.inr (Or.inl rfl))).2)
    (fun i => (inj2 i.1.1).mono (Set.subset_univ _)) (fun i => (inj2 i.1.2).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).2) n t ht0 hC1
  have T4 := family_tail hρ0 hρ1 I4 A4 B4 C4 (fun _ => gT)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).1)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).2)
    (fun i => (inj2 i.1).mono (Set.subset_univ _)) (fun i => (inj1 i.1).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).2.trans (Prod.mk.inj h).1) n t ht0 hC4
  have T5 := family_tail hρ0 hρ1 W A5 B5 C5 (fun _ => gT)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).1)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).2)
    (fun i => (inj1 i).mono (Set.subset_univ _)) (fun i => (inj2 i).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).1.trans (Prod.mk.inj h).2) n t ht0 hC5
  rw [hexp] at T1 T2 T3 T4 T5
  set e := Real.exp (-(c * n)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hI1 : (I1.card : ℝ) = n ^ 2 * 4 := by
    simp only [I1, card_product, card_univ, Fintype.card_fin]; push_cast; ring
  have hI4 : (I4.card : ℝ) = n * 4 := by
    simp only [I4, card_product, card_univ, Fintype.card_fin]; push_cast; ring
  rw [hI1] at T1 T2 T3
  rw [hI4] at T4
  -- union bound
  set E1 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ I1, t ≤ |pairSum (A1 i) (B1 i) (C1 i) gFF ω -
        pE (bern ρ) (pairSum (A1 i) (B1 i) (C1 i) gFF)| with hE1
  set E2 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ I1, t ≤ |pairSum (A2 i) (B2 i) (C2 i) gF ω -
        pE (bern ρ) (pairSum (A2 i) (B2 i) (C2 i) gF)| with hE2
  set E3 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ I1, t ≤ |pairSum (A1 i) (B1 i) (C1 i) gTT ω -
        pE (bern ρ) (pairSum (A1 i) (B1 i) (C1 i) gTT)| with hE3
  set E4 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ I4, t ≤ |pairSum (A4 i) (B4 i) (C4 i) gT ω -
        pE (bern ρ) (pairSum (A4 i) (B4 i) (C4 i) gT)| with hE4
  set E5 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ W, t ≤ |pairSum (A5 i) (B5 i) (C5 i) gT ω -
        pE (bern ρ) (pairSum (A5 i) (B5 i) (C5 i) gT)| with hE5
  have hBadP : pProb (bern ρ) (fun ω => (E1 ω ∨ E2 ω) ∨ (E3 ω ∨ E4 ω) ∨ E5 ω) < 1 := by
    have u1 := pProb_or_le hP (fun ω => E1 ω ∨ E2 ω) (fun ω => (E3 ω ∨ E4 ω) ∨ E5 ω)
    have u2 := pProb_or_le hP E1 E2
    have u3 := pProb_or_le hP (fun ω => E3 ω ∨ E4 ω) E5
    have u4 := pProb_or_le hP E3 E4
    have hsum : n ^ 2 * 4 * (2 * e) * 3 + n * 4 * (2 * e) + n * (2 * e) < 1 := by
      have hn1' : 1 ≤ n := by rw [hndef]; exact_mod_cast hn1
      have h1 : n * e ≤ n ^ 2 * e := mul_le_mul_of_nonneg_right (by nlinarith) he0
      have h2 : (2 * n) ^ 2 * e ≤ 1 / 10 := hsmall
      nlinarith
    have T5' : pProb (bern ρ) E5 ≤ n * (2 * e) := by
      simpa [hndef] using T5
    linarith
  obtain ⟨ω, -, hω⟩ := exists_of_pProb_lt_one hP hBadP
  simp only [not_or] at hω
  obtain ⟨⟨g1', g2'⟩, ⟨g3', g4'⟩, g5'⟩ := hω
  have g1 : ∀ i ∈ I1, ¬ t ≤ |pairSum (A1 i) (B1 i) (C1 i) gFF ω -
      pE (bern ρ) (pairSum (A1 i) (B1 i) (C1 i) gFF)| := fun i hi h => g1' ⟨i, hi, h⟩
  have g2 : ∀ i ∈ I1, ¬ t ≤ |pairSum (A2 i) (B2 i) (C2 i) gF ω -
      pE (bern ρ) (pairSum (A2 i) (B2 i) (C2 i) gF)| := fun i hi h => g2' ⟨i, hi, h⟩
  have g3 : ∀ i ∈ I1, ¬ t ≤ |pairSum (A1 i) (B1 i) (C1 i) gTT ω -
      pE (bern ρ) (pairSum (A1 i) (B1 i) (C1 i) gTT)| := fun i hi h => g3' ⟨i, hi, h⟩
  have g4 : ∀ i ∈ I4, ¬ t ≤ |pairSum (A4 i) (B4 i) (C4 i) gT ω -
      pE (bern ρ) (pairSum (A4 i) (B4 i) (C4 i) gT)| := fun i hi h => g4' ⟨i, hi, h⟩
  have g5 : ∀ i ∈ W, ¬ t ≤ |pairSum (A5 i) (B5 i) (C5 i) gT ω -
      pE (bern ρ) (pairSum (A5 i) (B5 i) (C5 i) gT)| := fun i hi h => g5' ⟨i, hi, h⟩
  refine ⟨crossRes H W U ω, crossRes_sub H W U ω, crossRes_cross H W U ω,
    fun x z hx hz => crossRes_not_out H W U ω hx hz, ?_, ?_, ?_, ?_, ?_⟩
  · -- r1
    intro a ha b hb hab haU hbU l
    have hi : ((a, b), l) ∈ I1 := by simp [I1, ha, hb]
    refine dev_of_good ?_ ?_ (g1 _ hi)
    · have : (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧
          s(a, z) ∉ crossRes H W U ω ∧ s(b, z) ∉ crossRes H W U ω) =
          (C1 ((a, b), l)).filter (fun z => s(a, z) ∉ crossRes H W U ω ∧
            s(b, z) ∉ crossRes H W U ω) := by
        ext z; simp only [C1, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzU, -, hHa, hHb⟩ := mem_filter.mp hz
      simp only [mem_crossRes_iff H W U ω haU hzU, mem_crossRes_iff H W U ω hbU hzU, A1, B1,
        gFF, ha, hb, hHa, hHb, true_and]
      cases ω (a, z) <;> cases ω (b, z) <;> simp
    · refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
      rw [pE_term_pair hρ0 hρ1 _ _ (fun h => hab (Prod.mk.inj h).1)]
      simp [gFF]; ring
  · -- r2
    intro a ha b hbU haU l
    have hb : b ∈ W := hUW hbU
    have hi : ((a, b), l) ∈ I1 := by simp [I1, ha, hb]
    refine dev_of_good ?_ ?_ (g2 _ hi)
    · have : ((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧
          s(b, z) ∉ crossRes H W U ω) =
          (C2 ((a, b), l)).filter (fun z => s(b, z) ∉ crossRes H W U ω) := by
        ext z; simp only [C2, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzWU, -, -, hHb⟩ := mem_filter.mp hz
      obtain ⟨hzW, hzU⟩ := mem_sdiff.mp hzWU
      rw [Sym2.eq_swap]
      simp only [mem_crossRes_iff H W U ω hzU hbU, A2, gF, hzW, hHb.symm, true_and]
      cases ω (z, b) <;> simp
    · refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
      rw [pE_term_single hρ0 hρ1 _ _ gF (fun x => if x = false then (1 : ℝ) else 0)
        (fun _ _ => rfl)]
      simp
  · -- r3
    intro a ha b hb hab haU hbU l
    have hi : ((a, b), l) ∈ I1 := by simp [I1, ha, hb]
    refine dev_of_good ?_ ?_ (g3 _ hi)
    · have : (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧
          s(a, z) ∈ crossRes H W U ω ∧ s(b, z) ∈ crossRes H W U ω) =
          (C1 ((a, b), l)).filter (fun z => s(a, z) ∈ crossRes H W U ω ∧
            s(b, z) ∈ crossRes H W U ω) := by
        ext z; simp only [C1, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzU, -, hHa, hHb⟩ := mem_filter.mp hz
      simp only [mem_crossRes_iff H W U ω haU hzU, mem_crossRes_iff H W U ω hbU hzU, A1, B1,
        gTT, ha, hb, hHa, hHb, true_and]
    · refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
      rw [pE_term_pair hρ0 hρ1 _ _ (fun h => hab (Prod.mk.inj h).1)]
      simp [gTT]; ring
  · -- r4
    intro x hx hxU c'
    have hi : (x, c') ∈ I4 := by simp [I4, hx]
    refine dev_of_good ?_ ?_ (g4 _ hi)
    · have : (U.filter fun z => p z = c' ∧ H.Adj x z ∧ s(x, z) ∈ crossRes H W U ω) =
          (C4 (x, c')).filter (fun z => s(x, z) ∈ crossRes H W U ω) := by
        ext z; simp only [C4, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzU, -, hHx⟩ := mem_filter.mp hz
      simp only [mem_crossRes_iff H W U ω hxU hzU, A4, gT, hx, hHx, true_and]
    · refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
      rw [pE_term_single hρ0 hρ1 _ _ gT (fun x => if x = true then (1 : ℝ) else 0)
        (fun _ _ => rfl)]
      simp
  · -- r5
    intro v hvU
    have hv : v ∈ W := hUW hvU
    refine dev_of_good ?_ ?_ (g5 _ hv)
    · have : ((W \ U).filter fun z => H.Adj v z ∧ s(v, z) ∈ crossRes H W U ω) =
          (C5 v).filter (fun z => s(v, z) ∈ crossRes H W U ω) := by
        ext z; simp only [C5, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzWU, hHv⟩ := mem_filter.mp hz
      obtain ⟨hzW, hzU⟩ := mem_sdiff.mp hzWU
      rw [Sym2.eq_swap]
      simp only [mem_crossRes_iff H W U ω hzU hvU, A5, gT, hzW, hHv.symm, true_and]
    · refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
      rw [pE_term_single hρ0 hρ1 _ _ gT (fun x => if x = true then (1 : ℝ) else 0)
        (fun _ _ => rfl)]
      simp

end NashWilliams18.SpreadF1
