/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.CrossReserveF1

@[expose] public section

/-!
# Sampling the radial cross reserve of a protected `K₃` round

Every available cross pair `(x, z)`, `x ∈ X` (a root, outside the child) and `z ∈ S` (child minus
grandchild), with `xz` in the available edge set `EH`, is put into the reserve independently with
probability `ρ`.  `crossResK3_exists` (proved) fixes one outcome satisfying simultaneously, with
`n = |V|` and error `ε n`:

* (k1) the reserved degree of every root into `S` is `ρ`-proportional;
* (k2) for every root `x` and every vertex `v`, the reserved neighbours of `x` adjacent to `v` are
  `ρ`-proportional (Dirac typicality of the radial targets, for EVERY `v`);
* (k3) for distinct roots, the common reserved neighbours are `ρ²`-proportional (apex supply and
  pairwise overlap of the radial targets);
* (k4) for every `v ∈ S`, the reserved roots at `v` are `ρ`-proportional (visit load).

The tails are those of `SpreadF1.family_tail` (Bernstein for sums of independent indicators of one
or two coordinates), and a union bound over `≤ 2n + 2n²` monitors.
-/

namespace NashWilliams18.SpreadK3

open Finset Pseudorandom NashWilliams18.Sampling NashWilliams18.SpreadF1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The sampled radial reserve. -/
def crossResK3 (EH : Finset (Sym2 V)) (X S : Finset V) (ω : V × V → Bool) :
    Finset (Sym2 V) :=
  ((X ×ˢ S).filter fun xz => s(xz.1, xz.2) ∈ EH ∧ ω xz = true).image fun xz => s(xz.1, xz.2)

omit [Fintype V] in
lemma mem_crossResK3_iff {EH : Finset (Sym2 V)} {X S : Finset V} (hXS : Disjoint X S)
    (ω : V × V → Bool) {x z : V} (hx : x ∈ X) (hz : z ∈ S) :
    s(x, z) ∈ crossResK3 EH X S ω ↔ s(x, z) ∈ EH ∧ ω (x, z) = true := by
  unfold crossResK3
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hE, hω⟩, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hE, hω⟩
    · exact absurd hb (disjoint_left.mp hXS hx)
  · rintro ⟨hE, hω⟩
    exact ⟨x, z, ⟨⟨hx, hz⟩, hE, hω⟩, rfl⟩

omit [Fintype V] in
lemma crossResK3_sub (EH : Finset (Sym2 V)) (X S : Finset V) (ω : V × V → Bool) :
    crossResK3 EH X S ω ⊆ EH := by
  intro e he
  unfold crossResK3 at he
  obtain ⟨⟨x, z⟩, hxz, rfl⟩ := mem_image.mp he
  exact (mem_filter.mp hxz).2.1

omit [Fintype V] in
lemma crossResK3_cross (EH : Finset (Sym2 V)) (X S : Finset V) (ω : V × V → Bool) :
    ∀ e ∈ crossResK3 EH X S ω, ∃ x ∈ X, ∃ z ∈ S, e = s(x, z) := by
  intro e he
  unfold crossResK3 at he
  obtain ⟨⟨x, z⟩, hxz, rfl⟩ := mem_image.mp he
  obtain ⟨hp, -⟩ := mem_filter.mp hxz
  exact ⟨x, (mem_product.mp hp).1, z, (mem_product.mp hp).2, rfl⟩

/-- The properties of a good sampled radial reserve. -/
structure CrossResK3Good (G : SimpleGraph V) [DecidableRel G.Adj] (EH : Finset (Sym2 V))
    (X S : Finset V) (Res : Finset (Sym2 V)) (ρ ε : ℝ) : Prop where
  sub : Res ⊆ EH
  cross : ∀ e ∈ Res, ∃ x ∈ X, ∃ z ∈ S, e = s(x, z)
  k1 : ∀ x ∈ X,
    |((S.filter fun z => s(x, z) ∈ EH ∧ s(x, z) ∈ Res).card : ℝ) -
      ρ * (S.filter fun z => s(x, z) ∈ EH).card| ≤ ε * Fintype.card V
  k2 : ∀ x ∈ X, ∀ v : V,
    |((S.filter fun z => s(x, z) ∈ EH ∧ G.Adj v z ∧ s(x, z) ∈ Res).card : ℝ) -
      ρ * (S.filter fun z => s(x, z) ∈ EH ∧ G.Adj v z).card| ≤ ε * Fintype.card V
  k3 : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    |((S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH ∧ s(x, z) ∈ Res ∧ s(y, z) ∈ Res).card
        : ℝ) - ρ ^ 2 * (S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH).card| ≤
      ε * Fintype.card V
  k4 : ∀ v ∈ S,
    |((X.filter fun x => s(x, v) ∈ EH ∧ s(x, v) ∈ Res).card : ℝ) -
      ρ * (X.filter fun x => s(x, v) ∈ EH).card| ≤ ε * Fintype.card V

set_option maxHeartbeats 1000000 in
/-- **Sampling the radial reserve** (proved). -/
theorem crossResK3_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (EH : Finset (Sym2 V)) (X S : Finset V) (ρ : ℝ), Disjoint X S →
      0 ≤ ρ → ρ ≤ 1 → N ≤ Fintype.card V →
      ∃ Res : Finset (Sym2 V), CrossResK3Good G EH X S Res ρ ε := by
  set c : ℝ := ε ^ 2 / (4 + 2 * ε) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨m₀, hm₀⟩ := eventually_pow_mul_exp_le 2 hc0 (ε := 1 / 10) (by norm_num)
  refine ⟨max m₀ 1, ?_⟩
  intro V _ _ G _ EH X S ρ hXS hρ0 hρ1 hN
  classical
  have hP := bern_isPMF (ι := V × V) hρ0 hρ1
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_max_right _ _) hN
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast hn1
  set t : ℝ := ε * n with ht
  have ht0 : 0 < t := by positivity
  have hexp : t ^ 2 / (2 * (2 * n + t)) = c * n := by
    rw [ht, hc]; field_simp; ring
  have hsmall : (2 * n) ^ 2 * Real.exp (-(c * n)) ≤ 1 / 10 := by
    have := hm₀ (Fintype.card V) (le_trans (le_max_left _ _) hN)
    simpa [hndef] using this
  -- the families
  let I2 : Finset (V × V) := X ×ˢ univ
  let I3 : Finset (V × V) := X ×ˢ X
  let C1 : V → Finset V := fun x => S.filter fun z => s(x, z) ∈ EH
  let C2 : V × V → Finset V := fun i => S.filter fun z => s(i.1, z) ∈ EH ∧ G.Adj i.2 z
  let C3 : V × V → Finset V := fun i => S.filter fun z => s(i.1, z) ∈ EH ∧ s(i.2, z) ∈ EH
  let C4 : V → Finset V := fun v => X.filter fun x => s(x, v) ∈ EH
  let A1 : V → V → V × V := fun x z => (x, z)
  let A2 : V × V → V → V × V := fun i z => (i.1, z)
  let B3 : V × V → V → V × V := fun i z => (i.2, z)
  let A4 : V → V → V × V := fun v x => (x, v)
  have hU : ∀ T : Finset V, (T.card : ℝ) ≤ n := fun T => by
    rw [hndef]; exact_mod_cast card_le_univ T
  have inj2 : ∀ a : V, Set.InjOn (fun z : V => (a, z)) (Set.univ : Set V) :=
    fun a x _ y _ h => (Prod.mk.inj h).2
  have inj1 : ∀ a : V, Set.InjOn (fun z : V => (z, a)) (Set.univ : Set V) :=
    fun a x _ y _ h => (Prod.mk.inj h).1
  have T1 := family_tail hρ0 hρ1 X A1 A1 C1 (fun _ => gT)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).1)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).2)
    (fun i => (inj2 i).mono (Set.subset_univ _)) (fun i => (inj2 i).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).2) n t ht0 (fun i => hU _)
  have T2 := family_tail hρ0 hρ1 I2 A2 A2 C2 (fun _ => gT)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).1)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).2)
    (fun i => (inj2 i.1).mono (Set.subset_univ _)) (fun i => (inj2 i.1).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).2) n t ht0 (fun i => hU _)
  have T3 := family_tail hρ0 hρ1 I3 A2 B3 C3 (fun _ => gTT)
    (fun _ => (g01 gTT (Or.inr (Or.inl rfl))).1) (fun _ => (g01 gTT (Or.inr (Or.inl rfl))).2)
    (fun i => (inj2 i.1).mono (Set.subset_univ _)) (fun i => (inj2 i.2).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).2) n t ht0 (fun i => hU _)
  have T4 := family_tail hρ0 hρ1 S A4 A4 C4 (fun _ => gT)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).1)
    (fun _ => (g01 gT (Or.inr (Or.inr (Or.inr rfl)))).2)
    (fun i => (inj1 i).mono (Set.subset_univ _)) (fun i => (inj1 i).mono (Set.subset_univ _))
    (fun i z _ z' _ h => (Prod.mk.inj h).1) n t ht0 (fun i => hU _)
  rw [hexp] at T1 T2 T3 T4
  set e := Real.exp (-(c * n)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hXn : (X.card : ℝ) ≤ n := hU X
  have hSn : (S.card : ℝ) ≤ n := hU S
  have hI2 : (I2.card : ℝ) ≤ n ^ 2 := by
    simp only [I2, card_product, card_univ]; push_cast
    rw [← hndef]; nlinarith
  have hI3 : (I3.card : ℝ) ≤ n ^ 2 := by
    simp only [I3, card_product]; push_cast
    have : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    nlinarith
  set E1 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ X, t ≤ |pairSum (A1 i) (A1 i) (C1 i) gT ω -
        pE (bern ρ) (pairSum (A1 i) (A1 i) (C1 i) gT)| with hE1
  set E2 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ I2, t ≤ |pairSum (A2 i) (A2 i) (C2 i) gT ω -
        pE (bern ρ) (pairSum (A2 i) (A2 i) (C2 i) gT)| with hE2
  set E3 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ I3, t ≤ |pairSum (A2 i) (B3 i) (C3 i) gTT ω -
        pE (bern ρ) (pairSum (A2 i) (B3 i) (C3 i) gTT)| with hE3
  set E4 : (V × V → Bool) → Prop := fun ω => ∃ i ∈ S, t ≤ |pairSum (A4 i) (A4 i) (C4 i) gT ω -
        pE (bern ρ) (pairSum (A4 i) (A4 i) (C4 i) gT)| with hE4
  have hBadP : pProb (bern ρ) (fun ω => (E1 ω ∨ E2 ω) ∨ (E3 ω ∨ E4 ω)) < 1 := by
    have u1 := pProb_or_le hP (fun ω => E1 ω ∨ E2 ω) (fun ω => E3 ω ∨ E4 ω)
    have u2 := pProb_or_le hP E1 E2
    have u3 := pProb_or_le hP E3 E4
    have h1 : pProb (bern ρ) E1 ≤ n * (2 * e) :=
      T1.trans (mul_le_mul_of_nonneg_right hXn (by positivity))
    have h2 : pProb (bern ρ) E2 ≤ n ^ 2 * (2 * e) :=
      T2.trans (mul_le_mul_of_nonneg_right hI2 (by positivity))
    have h3 : pProb (bern ρ) E3 ≤ n ^ 2 * (2 * e) :=
      T3.trans (mul_le_mul_of_nonneg_right hI3 (by positivity))
    have h4 : pProb (bern ρ) E4 ≤ n * (2 * e) :=
      T4.trans (mul_le_mul_of_nonneg_right hSn (by positivity))
    have hsum : n * (2 * e) + n ^ 2 * (2 * e) + (n ^ 2 * (2 * e) + n * (2 * e)) < 1 := by
      have hn1' : 1 ≤ n := by rw [hndef]; exact_mod_cast hn1
      have h1 : n * e ≤ n ^ 2 * e := mul_le_mul_of_nonneg_right (by nlinarith) he0
      have h2 : (2 * n) ^ 2 * e ≤ 1 / 10 := hsmall
      nlinarith
    linarith
  obtain ⟨ω, -, hω⟩ := exists_of_pProb_lt_one hP hBadP
  simp only [not_or] at hω
  obtain ⟨⟨g1', g2'⟩, ⟨g3', g4'⟩⟩ := hω
  have g1 : ∀ i ∈ X, ¬ t ≤ |pairSum (A1 i) (A1 i) (C1 i) gT ω -
      pE (bern ρ) (pairSum (A1 i) (A1 i) (C1 i) gT)| := fun i hi h => g1' ⟨i, hi, h⟩
  have g2 : ∀ i ∈ I2, ¬ t ≤ |pairSum (A2 i) (A2 i) (C2 i) gT ω -
      pE (bern ρ) (pairSum (A2 i) (A2 i) (C2 i) gT)| := fun i hi h => g2' ⟨i, hi, h⟩
  have g3 : ∀ i ∈ I3, ¬ t ≤ |pairSum (A2 i) (B3 i) (C3 i) gTT ω -
      pE (bern ρ) (pairSum (A2 i) (B3 i) (C3 i) gTT)| := fun i hi h => g3' ⟨i, hi, h⟩
  have g4 : ∀ i ∈ S, ¬ t ≤ |pairSum (A4 i) (A4 i) (C4 i) gT ω -
      pE (bern ρ) (pairSum (A4 i) (A4 i) (C4 i) gT)| := fun i hi h => g4' ⟨i, hi, h⟩
  have hsingle : ∀ (k : V → V × V) (C : Finset V),
      pE (bern ρ) (pairSum k k C gT) = C.card * ρ := by
    intro k C
    refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
    rw [pE_term_single hρ0 hρ1 _ _ gT (fun x => if x = true then (1 : ℝ) else 0)
      (fun _ _ => rfl)]
    simp
  refine ⟨crossResK3 EH X S ω, crossResK3_sub EH X S ω, crossResK3_cross EH X S ω,
    ?_, ?_, ?_, ?_⟩
  · -- k1
    intro x hx
    refine dev_of_good ?_ (hsingle _ _) (g1 _ hx)
    have : (S.filter fun z => s(x, z) ∈ EH ∧ s(x, z) ∈ crossResK3 EH X S ω) =
        (C1 x).filter (fun z => s(x, z) ∈ crossResK3 EH X S ω) := by
      ext z; simp only [C1, mem_filter]; tauto
    rw [this]
    refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
    obtain ⟨hzS, hE⟩ := mem_filter.mp hz
    simp only [mem_crossResK3_iff hXS ω hx hzS, A1, gT, hE, true_and]
  · -- k2
    intro x hx v
    have hi : (x, v) ∈ I2 := mem_product.mpr ⟨hx, mem_univ _⟩
    have hg := g2 _ hi
    have hEq := hsingle (A2 (x, v)) (C2 (x, v))
    have hcnt : ((S.filter fun z => s(x, z) ∈ EH ∧ G.Adj v z ∧
        s(x, z) ∈ crossResK3 EH X S ω).card : ℝ) =
        pairSum (A2 (x, v)) (A2 (x, v)) (C2 (x, v)) gT ω := by
      have : (S.filter fun z => s(x, z) ∈ EH ∧ G.Adj v z ∧ s(x, z) ∈ crossResK3 EH X S ω) =
          (C2 (x, v)).filter (fun z => s(x, z) ∈ crossResK3 EH X S ω) := by
        ext z; simp only [C2, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzS, hE, -⟩ := mem_filter.mp hz
      simp only [mem_crossResK3_iff hXS ω hx hzS, A2, gT, hE, true_and]
    have h := dev_of_good hcnt hEq hg
    exact h
  · -- k3
    intro x hx y hy hxy
    have hi : (x, y) ∈ I3 := by simp [I3, hx, hy]
    refine dev_of_good ?_ ?_ (g3 _ hi)
    · have : (S.filter fun z => s(x, z) ∈ EH ∧ s(y, z) ∈ EH ∧
          s(x, z) ∈ crossResK3 EH X S ω ∧ s(y, z) ∈ crossResK3 EH X S ω) =
          (C3 (x, y)).filter (fun z => s(x, z) ∈ crossResK3 EH X S ω ∧
            s(y, z) ∈ crossResK3 EH X S ω) := by
        ext z; simp only [C3, mem_filter]; tauto
      rw [this]
      refine count_eq_pairSum ω _ _ _ _ _ fun z hz => ?_
      obtain ⟨hzS, hEx, hEy⟩ := mem_filter.mp hz
      simp only [mem_crossResK3_iff hXS ω hx hzS, mem_crossResK3_iff hXS ω hy hzS, A2, B3,
        gTT, hEx, hEy, true_and]
    · refine pE_pairSum_const _ _ _ _ _ fun z _ => ?_
      rw [pE_term_pair hρ0 hρ1 _ _ (fun h => hxy (Prod.mk.inj h).1)]
      simp [gTT]; ring
  · -- k4
    intro v hv
    refine dev_of_good ?_ (hsingle _ _) (g4 _ hv)
    have : (X.filter fun x => s(x, v) ∈ EH ∧ s(x, v) ∈ crossResK3 EH X S ω) =
        (C4 v).filter (fun x => s(x, v) ∈ crossResK3 EH X S ω) := by
      ext z; simp only [C4, mem_filter]; tauto
    rw [this]
    refine count_eq_pairSum ω _ _ _ _ _ fun x hx => ?_
    obtain ⟨hxX, hE⟩ := mem_filter.mp hx
    simp only [mem_crossResK3_iff hXS ω hxX hv, A4, gT, hE, true_and]

end NashWilliams18.SpreadK3
