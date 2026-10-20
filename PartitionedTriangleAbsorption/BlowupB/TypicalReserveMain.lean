/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TypicalReserve

/-! # BlowupB.TypicalReserveMain — `TypicalReserveSpec` for every family of 3-element types

See `TypicalReserve` for the tools. Constants: `θ = eta / (4 (t+1))`, `ρ ≥ ρmin = θ γ / 2` on
allowed pairs, `ωC = (γ/4) ρmin^h`. Bad events (deviation of a block count from its mean):
degrees (`n` events, deviation `eta n / 2`), common neighbourhoods (`≤ (h+1) n^h 2^h t` events,
deviation `ωC n`), typed thirds (`n² |F|` events, deviation `ε₁ n / 2`). Their total probability
is `< 1` for large `n`, so a good outcome exists.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {t : ℕ}

section Instance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class pair of an edge. -/
def pmE (p : V → Fin t) (e : Sym2 V) : Multiset (Fin t) :=
  Sym2.lift ⟨fun u v => ({p u, p v} : Multiset (Fin t)), fun u v => Multiset.pair_comm _ _⟩ e

@[simp] theorem pmE_mk (p : V → Fin t) (u v : V) : pmE p s(u, v) = {p u, p v} := rfl

/-- Class sizes. -/
def clsz (p : V → Fin t) (c : Fin t) : ℝ := ((univ.filter fun v => p v = c).card : ℝ)

theorem card_filter_ne_ne_le (p : V → Fin t) (u v : V) (c : Fin t) :
    ((univ.filter fun w => p w = c ∧ w ≠ u ∧ w ≠ v).card : ℝ) ≤ clsz p c := by
  unfold clsz
  exact_mod_cast card_le_card fun w hw => by
    simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.1

theorem clsz_le_card_filter_ne_ne (p : V → Fin t) (u v : V) (c : Fin t) :
    clsz p c ≤ ((univ.filter fun w => p w = c ∧ w ≠ u ∧ w ≠ v).card : ℝ) + 2 := by
  unfold clsz
  have hsub : (univ.filter fun w => p w = c) ⊆
      (univ.filter fun w => p w = c ∧ w ≠ u ∧ w ≠ v) ∪ {u, v} := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_insert, mem_singleton] at hw ⊢
    by_cases hu : w = u
    · exact Or.inr (Or.inl hu)
    by_cases hv : w = v
    · exact Or.inr (Or.inr hv)
    exact Or.inl ⟨hw, hu, hv⟩
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 : ({u, v} : Finset V).card ≤ 2 := card_le_two
  have : (univ.filter fun w => p w = c).card ≤
      (univ.filter fun w => p w = c ∧ w ≠ u ∧ w ≠ v).card + 2 := by omega
  exact_mod_cast this

theorem count_pair_le_two (a b c : Fin t) : (({a, b} : Multiset (Fin t)).count c : ℝ) ≤ 2 := by
  have := Multiset.count_le_card c ({a, b} : Multiset (Fin t))
  have h2 : Multiset.card ({a, b} : Multiset (Fin t)) = 2 := by simp
  rw [h2] at this
  exact_mod_cast this

end Instance



section Bounds

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clsz_le (p : V → Fin t) (c : Fin t) : clsz p c ≤ Fintype.card V := by
  unfold clsz; exact_mod_cast card_le_univ _

theorem count_nonneg' (s : Multiset (Fin t)) (c : Fin t) : (0 : ℝ) ≤ (s.count c : ℝ) :=
  Nat.cast_nonneg _

theorem rhoM_nonneg (F : Finset (Multiset (Fin t))) (p : V → Fin t) {γ θ : ℝ} (hθ : 0 ≤ θ)
    (hn : 0 < (Fintype.card V : ℝ)) (hn2 : 2 ≤ γ * Fintype.card V)
    (hcls : ∀ i, γ * Fintype.card V ≤ clsz p i) (a b : Fin t) :
    0 ≤ rhoM F (clsz p) (Fintype.card V) θ {a, b} := by
  unfold rhoM
  refine div_nonneg (mul_nonneg hθ (sum_nonneg fun c _ => ?_)) hn.le
  unfold nPrime; linarith [hcls c, count_pair_le_two a b c]

theorem rhoM_le (F : Finset (Multiset (Fin t))) (p : V → Fin t) {θ : ℝ} (hθ : 0 ≤ θ)
    (hn : 0 < (Fintype.card V : ℝ)) (s : Multiset (Fin t)) :
    rhoM F (clsz p) (Fintype.card V) θ s ≤ θ * t := by
  unfold rhoM
  rw [div_le_iff₀ hn]
  have h1 : ∑ c ∈ univ.filter (fun c => c ::ₘ s ∈ F), nPrime (clsz p) s c ≤
      ∑ _c ∈ univ.filter (fun c => c ::ₘ s ∈ F), (Fintype.card V : ℝ) :=
    sum_le_sum fun c _ => by unfold nPrime; linarith [clsz_le p c, count_nonneg' s c]
  have h2 : ∑ _c ∈ univ.filter (fun c => c ::ₘ s ∈ F), (Fintype.card V : ℝ) ≤
      t * Fintype.card V := by
    rw [sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hn.le
    have := card_filter_le (univ : Finset (Fin t)) (fun c => c ::ₘ s ∈ F)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  calc θ * ∑ c ∈ univ.filter (fun c => c ::ₘ s ∈ F), nPrime (clsz p) s c
      ≤ θ * (t * Fintype.card V) := mul_le_mul_of_nonneg_left (h1.trans h2) hθ
    _ = θ * t * Fintype.card V := by ring

theorem rhoM_ge (F : Finset (Multiset (Fin t))) (p : V → Fin t) {γ θ : ℝ} (hθ : 0 ≤ θ)
    (hn : 0 < (Fintype.card V : ℝ)) (hn4 : 4 ≤ γ * Fintype.card V)
    (hcls : ∀ i, γ * Fintype.card V ≤ clsz p i) {a b : Fin t} (hab : AllowedPair F a b) :
    θ * γ / 2 ≤ rhoM F (clsz p) (Fintype.card V) θ {a, b} := by
  obtain ⟨c, hc⟩ := exists_third_cons hab
  unfold rhoM
  rw [le_div_iff₀ hn]
  have hterm : γ * Fintype.card V / 2 ≤ nPrime (clsz p) {a, b} c := by
    unfold nPrime; linarith [hcls c, count_pair_le_two a b c]
  have hsum : nPrime (clsz p) {a, b} c ≤
      ∑ x ∈ univ.filter (fun x => x ::ₘ ({a, b} : Multiset (Fin t)) ∈ F),
        nPrime (clsz p) {a, b} x :=
    single_le_sum (f := fun x => nPrime (clsz p) {a, b} x)
      (fun x _ => by unfold nPrime; linarith [hcls x, count_pair_le_two a b x])
      (mem_filter.mpr ⟨mem_univ _, hc⟩)
  have := mul_le_mul_of_nonneg_left (hterm.trans hsum) hθ
  linarith

/-- Pairs of a 3-element type are allowed. -/
theorem allowed_of_cons {F : Finset (Multiset (Fin t))} {a b c : Fin t}
    (hc : c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F) :
    AllowedPair F a b ∧ AllowedPair F c a ∧ AllowedPair F c b := by
  have h3 : Multiset.card (c ::ₘ ({a, b} : Multiset (Fin t))) = 3 := by simp
  refine ⟨⟨_, hc, h3, Multiset.le_cons_self _ _⟩, ⟨_, hc, h3, ?_⟩, ⟨_, hc, h3, ?_⟩⟩
  · simp only [Multiset.insert_eq_cons]
    exact Multiset.cons_le_cons c (Multiset.singleton_le.mpr (by simp))
  · simp only [Multiset.insert_eq_cons]
    exact Multiset.cons_le_cons c (Multiset.singleton_le.mpr (by simp))

/-- Weight bounds for a 3-element type. -/
theorem wtT_bounds (F : Finset (Multiset (Fin t))) (p : V → Fin t) {γ θ : ℝ} (hθ : 0 < θ)
    (hn : 0 < (Fintype.card V : ℝ)) (hn4 : 4 ≤ γ * Fintype.card V) (hγ : 0 < γ)
    (hcls : ∀ i, γ * Fintype.card V ≤ clsz p i) {τ : Multiset (Fin t)} (hτ : τ ∈ F)
    (hτ3 : Multiset.card τ = 3) :
    1 / (θ ^ 2 * t ^ 3) ≤ wtT θ (rhoM F (clsz p) (Fintype.card V) θ) τ ∧
      wtT θ (rhoM F (clsz p) (Fintype.card V) θ) τ ≤ θ / (θ * γ / 2) ^ 3 := by
  obtain ⟨x, y, z, rfl⟩ := Multiset.card_eq_three.mp hτ3
  have e : ({x, y, z} : Multiset (Fin t)) = x ::ₘ {y, z} := Multiset.insert_eq_cons _ _
  rw [e] at hτ ⊢
  obtain ⟨h1, h2, h3⟩ := allowed_of_cons hτ
  set ρ := rhoM F (clsz p) (Fintype.card V) θ with hρ
  have l1 := rhoM_ge F p hθ.le hn hn4 hcls h1
  have l2 := rhoM_ge F p hθ.le hn hn4 hcls h2
  have l3 := rhoM_ge F p hθ.le hn hn4 hcls h3
  have u1 := rhoM_le F p hθ.le hn {y, z}
  have u2 := rhoM_le F p hθ.le hn {x, y}
  have u3 := rhoM_le F p hθ.le hn {x, z}
  have hm : 0 < θ * γ / 2 := by positivity
  unfold wtT
  rw [piT_triple]
  have a1 : 0 < ρ {y, z} := lt_of_lt_of_le hm l1
  have a2 : 0 < ρ {x, y} := lt_of_lt_of_le hm l2
  have a3 : 0 < ρ {x, z} := lt_of_lt_of_le hm l3
  have hP0 : 0 < ρ {y, z} * (ρ {x, y} * ρ {x, z}) := by positivity
  have hPu : ρ {y, z} * (ρ {x, y} * ρ {x, z}) ≤ (θ * t) ^ 3 := by
    calc ρ {y, z} * (ρ {x, y} * ρ {x, z}) ≤ (θ * t) * ((θ * t) * (θ * t)) :=
          mul_le_mul u1 (mul_le_mul u2 u3 a3.le (a2.le.trans u2)) (mul_nonneg a2.le a3.le)
            (a1.le.trans u1)
      _ = (θ * t) ^ 3 := by ring
  have hPl : (θ * γ / 2) ^ 3 ≤ ρ {y, z} * (ρ {x, y} * ρ {x, z}) := by
    calc (θ * γ / 2) ^ 3 = (θ * γ / 2) * ((θ * γ / 2) * (θ * γ / 2)) := by ring
      _ ≤ _ := mul_le_mul l1 (mul_le_mul l2 l3 hm.le a2.le) (by positivity) a1.le
  have ht0 : 0 < (θ * t) ^ 3 := lt_of_lt_of_le hP0 hPu
  have htne : (t : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ht0; simp at ht0
  constructor
  · calc 1 / (θ ^ 2 * t ^ 3) = θ / (θ * t) ^ 3 := by
          field_simp
      _ ≤ θ / (ρ {y, z} * (ρ {x, y} * ρ {x, z})) :=
          div_le_div_of_nonneg_left hθ.le hP0 hPu
  · exact div_le_div_of_nonneg_left hθ.le (by positivity) hPl

/-- Allowed non-edges of `E = G \ (B ∪ X)` at a vertex. -/
theorem card_miss_le (F : Finset (Multiset (Fin t))) (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B X : Finset (Sym2 V)) (d : ℕ) (δ : ℝ) (K : ℕ)
    (hmiss : ∀ v, missDeg p F G v ≤ d) (hB : DegBounded B (δ * Fintype.card V))
    (hXK : X.card ≤ K) (u : V) :
    ((univ.filter fun w => w ≠ u ∧ AllowedPair F (p u) (p w) ∧
        s(u, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ) ≤ d + δ * Fintype.card V + K := by
  have hsub : (univ.filter fun w => w ≠ u ∧ AllowedPair F (p u) (p w) ∧
        s(u, w) ∉ G.edgeFinset \ (B ∪ X)) ⊆
      missSet p F G u ∪ ((univ.filter fun w => s(u, w) ∈ B) ∪
        univ.filter fun w => s(u, w) ∈ X) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_union, not_and, not_not,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hw
    obtain ⟨hwu, hal, hE⟩ := hw
    by_cases hadj : G.Adj u w
    · have := hE hadj
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases this with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, Ne.symm hwu, hal, hadj⟩)
  have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_union_le _ _) _))
  have hM : ((missSet p F G u).card : ℝ) ≤ d := by exact_mod_cast hmiss u
  have hBu : ((univ.filter fun w => s(u, w) ∈ B).card : ℝ) ≤ δ * Fintype.card V :=
    le_trans (by exact_mod_cast card_filter_star_le B u) (hB u)
  have hXu : ((univ.filter fun w => s(u, w) ∈ X).card : ℝ) ≤ K := by
    exact_mod_cast (card_filter_pair_le X u).trans hXK
  have h1' : ((univ.filter fun w => w ≠ u ∧ AllowedPair F (p u) (p w) ∧
        s(u, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ) ≤ (missSet p F G u).card +
      (((univ.filter fun w => s(u, w) ∈ B).card : ℝ) +
        (univ.filter fun w => s(u, w) ∈ X).card) := by
    exact_mod_cast h1
  linarith

end Bounds


section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem card_small_finsets_le (h : ℕ) (hn : 1 ≤ Fintype.card V) :
    ((univ.filter fun S : Finset V => S.card ≤ h).card : ℝ) ≤
      ((h : ℝ) + 1) * (Fintype.card V : ℝ) ^ h := by
  have hsub : (univ.filter fun S : Finset V => S.card ≤ h) ⊆
      (range (h + 1)).biUnion fun k => powersetCard k (univ : Finset V) := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    exact mem_biUnion.mpr ⟨S.card, mem_range.mpr (by omega),
      mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ k ∈ range (h + 1), (powersetCard k (univ : Finset V)).card ≤
      ∑ _k ∈ range (h + 1), Fintype.card V ^ h := by
    refine sum_le_sum fun k hk => ?_
    rw [card_powersetCard, card_univ]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hn (by
      have := mem_range.mp hk; omega))
  rw [sum_const, card_range, smul_eq_mul] at h2
  have := h1.trans h2
  exact_mod_cast this

end Counting

set_option maxHeartbeats 4000000 in
/-- **The typical reserve exists**, for every family of 3-element types. -/
theorem typicalReserveSpec {F : Finset (Multiset (Fin t))}
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (h : ℕ) : TypicalReserveSpec F h := by
  intro K gamma eta hg he he2
  set g : ℝ := min gamma 1 with hgdef
  have hg0 : 0 < g := lt_min hg one_pos
  have hg1 : g ≤ 1 := min_le_right _ _
  set θ : ℝ := eta / (4 * ((t : ℝ) + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hθt : θ * t ≤ eta / 4 := by
    rw [hθdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set ρmin : ℝ := θ * g / 2 with hρmin
  have hρmin0 : 0 < ρmin := by positivity
  have hρmin1 : ρmin ≤ 1 := by
    have : θ ≤ 1 := by
      rw [hθdef, div_le_one (by positivity)]; nlinarith
    rw [hρmin]; nlinarith
  set ωC : ℝ := g / 4 * ρmin ^ h with hωC
  have hωC0 : 0 < ωC := by positivity
  have hωC1 : ωC ≤ 1 := by
    have : ρmin ^ h ≤ 1 := pow_le_one₀ hρmin0.le hρmin1
    rw [hωC]; nlinarith
  set ωT : ℝ := min ωC (min (1 / (θ ^ 2 * ((t : ℝ) + 1) ^ 3)) ((θ * g / 2) ^ 3 / θ)) with hωT
  have hωT0 : 0 < ωT := lt_min hωC0 (lt_min (by positivity) (by positivity))
  refine ⟨ωT, hωT0, fun ε hε => ?_⟩
  set ε1 : ℝ := min ε 1 with hε1
  have hε10 : 0 < ε1 := lt_min hε one_pos
  set c1 : ℝ := (eta / 2) ^ 2 / (4 * (eta / 2 + 1)) with hc1
  set c2 : ℝ := ωC ^ 2 / (4 * (ωC + h)) with hc2
  set c3 : ℝ := (ε1 / 2) ^ 2 / (4 * (ε1 / 2 + 2)) with hc3
  set c : ℝ := min c1 (min c2 c3) with hc
  have hc0 : 0 < c := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set Cst : ℝ := 2 * (1 + ((h : ℝ) + 1) * 2 ^ h * t + F.card) with hCst
  have hCst0 : 0 < Cst := by positivity
  obtain ⟨N0, hN0⟩ := exists_pow_mul_exp_lt' (h + 2) c Cst hc0 hCst0
  set δ : ℝ := min (g / (8 * ((h : ℝ) + 1))) (ε1 / 32) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨max N0 (max ⌈8 * ((h : ℝ) + 1) * ((K : ℝ) + 1) / g⌉₊
    (max ⌈32 * ((K : ℝ) + t + 1) / ε1⌉₊ 1)), δ, hδ0, ?_⟩
  intro V _ _ G _ p d hN hadj hmiss hd hcls B X hB hXG hXB hXK
  classical
  -- numeric facts about `n`
  have hN0' : N0 ≤ Fintype.card V := le_trans (le_max_left _ _) hN
  have hNA : ⌈8 * ((h : ℝ) + 1) * ((K : ℝ) + 1) / g⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNB : ⌈32 * ((K : ℝ) + t + 1) / ε1⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hn1 : 1 ≤ Fintype.card V :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hnA : 8 * ((h : ℝ) + 1) * ((K : ℝ) + 1) / g ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNA)
  have hnB : 32 * ((K : ℝ) + t + 1) / ε1 ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNB)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  have hgn : 8 * ((h : ℝ) + 1) * ((K : ℝ) + 1) ≤ g * Fintype.card V := by
    have := (div_le_iff₀ hg0).mp hnA; linarith
  have hεn : 32 * ((K : ℝ) + t + 1) ≤ ε1 * Fintype.card V := by
    have := (div_le_iff₀ hε10).mp hnB; linarith
  have hn4 : 4 ≤ g * Fintype.card V := by
    have : (8 : ℝ) ≤ 8 * ((h : ℝ) + 1) * ((K : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (h : ℝ) + 1 := by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
      have h2 : (1 : ℝ) ≤ (K : ℝ) + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
      nlinarith
    linarith
  have hcls' : ∀ i, g * Fintype.card V ≤ clsz p i := fun i =>
    le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le) (hcls i)
  have hdδ : (d : ℝ) ≤ δ * Fintype.card V := hd
  -- the random graph
  set E : Finset (Sym2 V) := G.edgeFinset \ (B ∪ X) with hEdef
  set ρ := rhoM F (clsz p) (Fintype.card V) θ with hρdef
  set qe : Sym2 V → ℝ := fun e => ρ (pmE p e) with hqedef
  have hqe : ∀ e, 0 ≤ qe e ∧ qe e ≤ θ * t := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      exact ⟨rhoM_nonneg F p hθ.le hn (by linarith) hcls' (p u) (p v),
        rhoM_le F p hθ.le hn _⟩
  set q : Fin E.card → ℝ := fun i => qe (edgeOf E i) with hqdef
  have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := fun i =>
    ⟨(hqe _).1, (hqe _).2.trans (by linarith)⟩
  -- blocks
  let K1 : V → Finset V := fun v => univ.filter fun w => s(v, w) ∈ E
  let T1 : V → V → Finset (Sym2 V) := fun v w => ({s(v, w)} : Finset (Sym2 V)).filter (· ∈ E)
  let K2 : Finset V → Finset V → Fin t → Finset V := fun S A i =>
    univ.filter fun x => p x = i ∧ x ∉ S ∧ ∀ a ∈ A, s(a, x) ∈ E
  let T2 : Finset V → V → Finset (Sym2 V) := fun A x => (A.image fun a => s(a, x)).filter (· ∈ E)
  let K3 : V → V → Multiset (Fin t) → Finset V := fun u v τ =>
    univ.filter fun w => w ≠ u ∧ w ≠ v ∧ s(u, w) ∈ E ∧ s(v, w) ∈ E ∧
      ({p u, p v, p w} : Multiset (Fin t)) = τ
  let T3 : V → V → V → Finset (Sym2 V) := fun u v w =>
    ({s(u, w), s(v, w)} : Finset (Sym2 V)).filter (· ∈ E)
  have hT1E : ∀ v w, T1 v w ⊆ E := fun v w e he => (mem_filter.mp he).2
  have hT2E : ∀ A x, T2 A x ⊆ E := fun A x e he => (mem_filter.mp he).2
  have hT3E : ∀ u v w, T3 u v w ⊆ E := fun u v w e he => (mem_filter.mp he).2
  have hT1 : ∀ v, ∀ z ∈ K1 v, ∀ e ∈ T1 v z, z ∈ e := by
    intro v z _ e he
    rw [mem_singleton.mp (mem_filter.mp he).1]; exact Sym2.mem_mk_right _ _
  have hT2 : ∀ S A i, ∀ z ∈ K2 S A i, ∀ e ∈ T2 A z, z ∈ e := by
    intro S A i z _ e he
    obtain ⟨a, -, rfl⟩ := mem_image.mp (mem_filter.mp he).1
    exact Sym2.mem_mk_right _ _
  have hT3 : ∀ u v τ, ∀ z ∈ K3 u v τ, ∀ e ∈ T3 u v z, z ∈ e := by
    intro u v τ z _ e he
    rcases mem_insert.mp (mem_filter.mp he).1 with rfl | he'
    · exact Sym2.mem_mk_right _ _
    · rw [mem_singleton.mp he']; exact Sym2.mem_mk_right _ _
  -- block sizes
  have hM1 : ∀ v, ∑ z ∈ K1 v, ((T1 v z).card : ℝ) ≤ 1 * Fintype.card V := by
    intro v
    calc ∑ z ∈ K1 v, ((T1 v z).card : ℝ) ≤ ∑ _z ∈ K1 v, (1 : ℝ) :=
          sum_le_sum fun z _ => by
            have := (card_filter_le ({s(v, z)} : Finset (Sym2 V)) (· ∈ E)).trans
              (card_singleton _).le
            exact_mod_cast this
      _ ≤ 1 * Fintype.card V := by
          rw [sum_const, nsmul_eq_mul, mul_one, one_mul]; exact_mod_cast card_le_univ _
  have hM2 : ∀ S A i, A.card ≤ h → ∑ z ∈ K2 S A i, ((T2 A z).card : ℝ) ≤ h * Fintype.card V := by
    intro S A i hA
    calc ∑ z ∈ K2 S A i, ((T2 A z).card : ℝ) ≤ ∑ _z ∈ K2 S A i, (h : ℝ) :=
          sum_le_sum fun z _ => by
            have : (T2 A z).card ≤ h := ((card_filter_le _ _).trans card_image_le).trans hA
            exact_mod_cast this
      _ ≤ h * Fintype.card V := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ _) (Nat.cast_nonneg _)
  have hM3 : ∀ u v τ, ∑ z ∈ K3 u v τ, ((T3 u v z).card : ℝ) ≤ 2 * Fintype.card V := by
    intro u v τ
    calc ∑ z ∈ K3 u v τ, ((T3 u v z).card : ℝ) ≤ ∑ _z ∈ K3 u v τ, (2 : ℝ) :=
          sum_le_sum fun z _ => by
            have : (T3 u v z).card ≤ 2 :=
              (card_filter_le _ _).trans (card_le_two (a := s(u, z)) (b := s(v, z)))
            exact_mod_cast this
      _ ≤ 2 * Fintype.card V := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ _) (by norm_num)
  -- deviation events
  let D1 : V → (Fin E.card → Bool) → Prop := fun v ω =>
    eta / 2 * Fintype.card V ≤ |blockCount (K1 v) (fun z => coinsOf E (T1 v z)) ω -
      ∑ z ∈ K1 v, ∏ i ∈ coinsOf E (T1 v z), q i|
  let D2 : Finset V → Finset V → Fin t → (Fin E.card → Bool) → Prop := fun S A i ω =>
    ωC * Fintype.card V ≤ |blockCount (K2 S A i) (fun z => coinsOf E (T2 A z)) ω -
      ∑ z ∈ K2 S A i, ∏ j ∈ coinsOf E (T2 A z), q j|
  let D3 : V → V → Multiset (Fin t) → (Fin E.card → Bool) → Prop := fun u v τ ω =>
    ε1 / 2 * Fintype.card V ≤ |blockCount (K3 u v τ) (fun z => coinsOf E (T3 u v z)) ω -
      ∑ z ∈ K3 u v τ, ∏ j ∈ coinsOf E (T3 u v z), q j|
  have hexp : ∀ {a b : ℝ}, 0 < a → 0 ≤ b → a ^ 2 / (4 * (a + b)) ≥ c → ∀ M : ℝ, 0 ≤ M →
      M ≤ b * Fintype.card V →
      2 * Real.exp (-((a * Fintype.card V) ^ 2 / (4 * (M + a * Fintype.card V)))) ≤
        2 * Real.exp (-(c * Fintype.card V)) := by
    intro a b ha hb hca M hM0 hM
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_right hca hn.le) (tail_rate ha hb hn hM0 hM)
  have hP1 : ∀ v, cubeProb q (D1 v) ≤ 2 * Real.exp (-(c * Fintype.card V)) := by
    intro v
    have := vertexBlocks_tail E q hq (K1 v) (T1 v) (hT1E v) (hT1 v) _ (hM1 v)
      (eta / 2 * Fintype.card V) (by positivity)
    refine this.trans ?_
    have e : eta / 2 * (Fintype.card V : ℝ) = (eta / 2) * Fintype.card V := rfl
    exact hexp (by positivity) zero_le_one (min_le_left _ _) _ (by positivity) le_rfl
  have hP2 : ∀ S A i, A.card ≤ h → cubeProb q (D2 S A i) ≤ 2 * Real.exp (-(c * Fintype.card V)) := by
    intro S A i hA
    refine (vertexBlocks_tail E q hq (K2 S A i) (T2 A) (hT2E A) (hT2 S A i) _ (hM2 S A i hA)
      (ωC * Fintype.card V) (by positivity)).trans ?_
    exact hexp hωC0 (Nat.cast_nonneg h) ((min_le_right _ _).trans (min_le_left _ _)) _
      (by positivity) le_rfl
  have hP3 : ∀ u v τ, cubeProb q (D3 u v τ) ≤ 2 * Real.exp (-(c * Fintype.card V)) := by
    intro u v τ
    refine (vertexBlocks_tail E q hq (K3 u v τ) (T3 u v) (hT3E u v) (hT3 u v τ) _ (hM3 u v τ)
      (ε1 / 2 * Fintype.card V) (by positivity)).trans ?_
    exact hexp (by positivity) (by norm_num) ((min_le_right _ _).trans (min_le_right _ _)) _
      (by positivity) le_rfl
  -- the union bound
  set Sfam : Finset (Finset V) := univ.filter fun S : Finset V => S.card ≤ h with hSfam
  set e0 : ℝ := 2 * Real.exp (-(c * Fintype.card V)) with he0
  have he00 : 0 ≤ e0 := by positivity
  let Bad : (Fin E.card → Bool) → Prop := fun ω =>
    (∃ v ∈ (univ : Finset V), D1 v ω) ∨
      ((∃ S ∈ Sfam, ∃ A ∈ S.powerset, ∃ i ∈ (univ : Finset (Fin t)), D2 S A i ω) ∨
        (∃ u ∈ (univ : Finset V), ∃ v ∈ (univ : Finset V), ∃ τ ∈ F, D3 u v τ ω))
  have hB1 : cubeProb q (fun ω => ∃ v ∈ (univ : Finset V), D1 v ω) ≤ Fintype.card V * e0 := by
    refine (cubeProb_exists_le q hq _ _).trans ?_
    calc ∑ v ∈ (univ : Finset V), cubeProb q (D1 v) ≤ ∑ _v ∈ (univ : Finset V), e0 :=
          sum_le_sum fun v _ => hP1 v
      _ = Fintype.card V * e0 := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hB2 : cubeProb q (fun ω => ∃ S ∈ Sfam, ∃ A ∈ S.powerset, ∃ i ∈ (univ : Finset (Fin t)),
      D2 S A i ω) ≤ Sfam.card * (2 ^ h * (t * e0)) := by
    refine (cubeProb_exists_le q hq _ _).trans ?_
    calc ∑ S ∈ Sfam, cubeProb q (fun ω => ∃ A ∈ S.powerset, ∃ i ∈ (univ : Finset (Fin t)),
          D2 S A i ω) ≤ ∑ _S ∈ Sfam, (2 ^ h * (t * e0) : ℝ) := by
          refine sum_le_sum fun S hS => ?_
          have hSh : S.card ≤ h := (mem_filter.mp hS).2
          refine (cubeProb_exists_le q hq _ _).trans ?_
          calc ∑ A ∈ S.powerset, cubeProb q (fun ω => ∃ i ∈ (univ : Finset (Fin t)),
                D2 S A i ω) ≤ ∑ _A ∈ S.powerset, (t * e0 : ℝ) := by
                refine sum_le_sum fun A hA => ?_
                have hAh : A.card ≤ h := (card_le_card (mem_powerset.mp hA)).trans hSh
                refine (cubeProb_exists_le q hq _ _).trans ?_
                calc ∑ i ∈ (univ : Finset (Fin t)), cubeProb q (D2 S A i)
                    ≤ ∑ _i ∈ (univ : Finset (Fin t)), e0 := sum_le_sum fun i _ => hP2 S A i hAh
                  _ = t * e0 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ = S.powerset.card * (t * e0) := by rw [sum_const, nsmul_eq_mul]
            _ ≤ 2 ^ h * (t * e0) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                rw [card_powerset]
                exact_mod_cast Nat.pow_le_pow_right (by norm_num) hSh
      _ = Sfam.card * (2 ^ h * (t * e0)) := by rw [sum_const, nsmul_eq_mul]
  have hB3 : cubeProb q (fun ω => ∃ u ∈ (univ : Finset V), ∃ v ∈ (univ : Finset V), ∃ τ ∈ F,
      D3 u v τ ω) ≤ Fintype.card V * (Fintype.card V * (F.card * e0)) := by
    refine (cubeProb_exists_le q hq _ _).trans ?_
    calc ∑ u ∈ (univ : Finset V), cubeProb q (fun ω => ∃ v ∈ (univ : Finset V), ∃ τ ∈ F,
          D3 u v τ ω) ≤ ∑ _u ∈ (univ : Finset V), (Fintype.card V * (F.card * e0) : ℝ) := by
          refine sum_le_sum fun u _ => (cubeProb_exists_le q hq _ _).trans ?_
          calc ∑ v ∈ (univ : Finset V), cubeProb q (fun ω => ∃ τ ∈ F, D3 u v τ ω)
              ≤ ∑ _v ∈ (univ : Finset V), (F.card * e0 : ℝ) := by
                refine sum_le_sum fun v _ => (cubeProb_exists_le q hq _ _).trans ?_
                calc ∑ τ ∈ F, cubeProb q (D3 u v τ) ≤ ∑ _τ ∈ F, e0 :=
                      sum_le_sum fun τ _ => hP3 u v τ
                  _ = F.card * e0 := by rw [sum_const, nsmul_eq_mul]
            _ = Fintype.card V * (F.card * e0) := by rw [sum_const, card_univ, nsmul_eq_mul]
      _ = Fintype.card V * (Fintype.card V * (F.card * e0)) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
  have hSc := card_small_finsets_le (V := V) h hn1
  have hone : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hpow1 : (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) ^ (h + 2) := by
    calc (Fintype.card V : ℝ) = (Fintype.card V : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hone (by omega)
  have hpowh : (Fintype.card V : ℝ) ^ h ≤ (Fintype.card V : ℝ) ^ (h + 2) :=
    pow_le_pow_right₀ hone (by omega)
  have hpow2 : (Fintype.card V : ℝ) * Fintype.card V ≤ (Fintype.card V : ℝ) ^ (h + 2) := by
    calc (Fintype.card V : ℝ) * Fintype.card V = (Fintype.card V : ℝ) ^ 2 := (sq _).symm
      _ ≤ _ := pow_le_pow_right₀ hone (by omega)
  have hBad : cubeProb q Bad < 1 := by
    have h12 := cubeProb_or_le q hq (fun ω => ∃ v ∈ (univ : Finset V), D1 v ω)
      (fun ω => (∃ S ∈ Sfam, ∃ A ∈ S.powerset, ∃ i ∈ (univ : Finset (Fin t)), D2 S A i ω) ∨
        (∃ u ∈ (univ : Finset V), ∃ v ∈ (univ : Finset V), ∃ τ ∈ F, D3 u v τ ω))
    have h23 := cubeProb_or_le q hq
      (fun ω => ∃ S ∈ Sfam, ∃ A ∈ S.powerset, ∃ i ∈ (univ : Finset (Fin t)), D2 S A i ω)
      (fun ω => ∃ u ∈ (univ : Finset V), ∃ v ∈ (univ : Finset V), ∃ τ ∈ F, D3 u v τ ω)
    have hfin := hN0 (Fintype.card V) hN0'
    have hE := Real.exp_pos (-(c * Fintype.card V))
    have hX1 : (Fintype.card V : ℝ) * e0 ≤ 2 * (Fintype.card V : ℝ) ^ (h + 2) *
        Real.exp (-(c * Fintype.card V)) := by
      rw [he0]
      calc (Fintype.card V : ℝ) * (2 * Real.exp (-(c * Fintype.card V)))
          ≤ (Fintype.card V : ℝ) ^ (h + 2) * (2 * Real.exp (-(c * Fintype.card V))) :=
            mul_le_mul_of_nonneg_right hpow1 (by positivity)
        _ = _ := by ring
    have hX2 : (Sfam.card : ℝ) * (2 ^ h * (t * e0)) ≤ 2 * (((h : ℝ) + 1) * 2 ^ h * t) *
        (Fintype.card V : ℝ) ^ (h + 2) * Real.exp (-(c * Fintype.card V)) := by
      have h1 : (Sfam.card : ℝ) ≤ ((h : ℝ) + 1) * (Fintype.card V : ℝ) ^ (h + 2) :=
        hSc.trans (mul_le_mul_of_nonneg_left hpowh (by positivity))
      rw [he0]
      calc (Sfam.card : ℝ) * (2 ^ h * (t * (2 * Real.exp (-(c * Fintype.card V)))))
          ≤ (((h : ℝ) + 1) * (Fintype.card V : ℝ) ^ (h + 2)) *
            (2 ^ h * (t * (2 * Real.exp (-(c * Fintype.card V))))) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by ring
    have hX3 : (Fintype.card V : ℝ) * (Fintype.card V * (F.card * e0)) ≤
        2 * (F.card : ℝ) * (Fintype.card V : ℝ) ^ (h + 2) * Real.exp (-(c * Fintype.card V)) := by
      rw [he0]
      calc (Fintype.card V : ℝ) * (Fintype.card V * (F.card * (2 * Real.exp (-(c * Fintype.card V)))))
          = ((Fintype.card V : ℝ) * Fintype.card V) *
            ((F.card : ℝ) * (2 * Real.exp (-(c * Fintype.card V)))) := by ring
        _ ≤ (Fintype.card V : ℝ) ^ (h + 2) *
            ((F.card : ℝ) * (2 * Real.exp (-(c * Fintype.card V)))) :=
            mul_le_mul_of_nonneg_right hpow2 (by positivity)
        _ = _ := by ring
    have hsum : Cst * (Fintype.card V : ℝ) ^ (h + 2) * Real.exp (-(c * Fintype.card V)) =
        2 * (Fintype.card V : ℝ) ^ (h + 2) * Real.exp (-(c * Fintype.card V)) +
        2 * (((h : ℝ) + 1) * 2 ^ h * t) * (Fintype.card V : ℝ) ^ (h + 2) *
          Real.exp (-(c * Fintype.card V)) +
        2 * (F.card : ℝ) * (Fintype.card V : ℝ) ^ (h + 2) * Real.exp (-(c * Fintype.card V)) := by
      rw [hCst]; ring
    calc cubeProb q Bad ≤ _ := h12
      _ ≤ Fintype.card V * e0 + (Sfam.card * (2 ^ h * (t * e0)) +
          Fintype.card V * (Fintype.card V * (F.card * e0))) := by
          linarith [hB1, hB2, hB3]
      _ < 1 := by linarith
  obtain ⟨ω, hω⟩ := exists_not_of_cubeProb_lt_one q Bad hBad
  simp only [Bad, not_or, not_exists, not_and] at hω
  obtain ⟨hω1, hω2, hω3⟩ := hω
  set R := randE E ω with hRdef
  have hRE : R ⊆ E := randE_subset E ω
  have hEG : E ⊆ G.edgeFinset := sdiff_subset
  have hblk : ∀ (K' : Finset V) (T : V → Finset (Sym2 V)), (∀ z, T z ⊆ E) →
      blockCount K' (fun z => coinsOf E (T z)) ω = ((K'.filter fun z => T z ⊆ R).card : ℝ) :=
    fun K' T hT => blockCount_coinsOf E ω K' T hT
  have hmean : ∀ (K' : Finset V) (T : V → Finset (Sym2 V)), (∀ z, T z ⊆ E) →
      ∑ z ∈ K', ∏ j ∈ coinsOf E (T z), q j = ∑ z ∈ K', ∏ e ∈ T z, qe e :=
    fun K' T hT => sum_congr rfl fun z _ => prod_q_coinsOf E qe (hT z)
  have hrho0 : ∀ a b, 0 ≤ ρ {a, b} := fun a b => rhoM_nonneg F p hθ.le hn (by linarith) hcls' a b
  have hrho1 : ∀ a b, ρ {a, b} ≤ 1 := fun a b => (rhoM_le F p hθ.le hn _).trans (by linarith)
  have hrhoge : ∀ {a b}, AllowedPair F a b → ρmin ≤ ρ {a, b} :=
    fun hab => rhoM_ge F p hθ.le hn hn4 hcls' hab
  have hδg : (h : ℝ) * δ ≤ g / 8 := by
    have h1 : δ ≤ g / (8 * ((h : ℝ) + 1)) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hδε : δ ≤ ε1 / 32 := min_le_right _ _
  have hRG : R ⊆ G.edgeFinset := hRE.trans hEG
  have hRd : Disjoint R (B ∪ X) := disjoint_of_subset_left hRE sdiff_disjoint
  refine ⟨R, hRG, hRd, ?_, ?_,
    wtT θ ρ, fun τ a b => kappaT ρ (clsz p) (Fintype.card V) τ a b, ?_, ?_, ?_⟩
  · -- degrees
    intro v
    have hdev := hω1 v (mem_univ _)
    simp only [D1, not_le] at hdev
    rw [hblk _ _ (hT1E v), hmean _ _ (hT1E v)] at hdev
    have hmean1 : ∑ z ∈ K1 v, ∏ e ∈ T1 v z, qe e ≤ eta / 4 * Fintype.card V := by
      calc ∑ z ∈ K1 v, ∏ e ∈ T1 v z, qe e ≤ ∑ _z ∈ K1 v, eta / 4 := by
            refine sum_le_sum fun z hz => ?_
            have hzE : s(v, z) ∈ E := (mem_filter.mp hz).2
            have : T1 v z = {s(v, z)} := by
              ext e; simp only [T1, mem_filter, mem_singleton]
              constructor
              · exact fun h => h.1
              · rintro rfl; exact ⟨rfl, hzE⟩
            rw [this, prod_singleton]
            exact (hqe _).2.trans hθt
        _ ≤ eta / 4 * Fintype.card V := by
            rw [sum_const, nsmul_eq_mul, mul_comm]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ _) (by positivity)
    have hstar : ((R.filter fun e => v ∈ e).card : ℝ) ≤
        (((K1 v).filter fun z => T1 v z ⊆ R).card : ℝ) := by
      have hsub : R.filter (fun e => v ∈ e) ⊆
          ((K1 v).filter fun z => T1 v z ⊆ R).image fun w => s(v, w) := by
        intro e he
        obtain ⟨heR, hve⟩ := mem_filter.mp he
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
        refine mem_image.mpr ⟨w, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hRE heR⟩, ?_⟩, rfl⟩
        intro e' he'
        rw [mem_singleton.mp (mem_filter.mp he').1]; exact heR
      exact_mod_cast (card_le_card hsub).trans card_image_le
    have := (abs_sub_lt_iff.mp hdev).1
    show ((R.filter fun e => v ∈ e).card : ℝ) ≤ eta * Fintype.card V
    nlinarith
  · -- common neighbourhoods
    intro S A i hS hA hal
    have hAh : A.card ≤ h := (card_le_card hA).trans hS
    have hdev := hω2 S (mem_filter.mpr ⟨mem_univ _, hS⟩) A (mem_powerset.mpr hA) i (mem_univ _)
    simp only [D2, not_le] at hdev
    rw [hblk _ _ (hT2E A), hmean _ _ (hT2E A)] at hdev
    -- the product over a block
    have hprod : ∀ x ∈ K2 S A i, ρmin ^ h ≤ ∏ e ∈ T2 A x, qe e := by
      intro x hx
      obtain ⟨hxi, hxS, hxE⟩ := (mem_filter.mp hx).2
      have hT : T2 A x = A.image fun a => s(a, x) := by
        ext e; simp only [T2, mem_filter, mem_image]
        constructor
        · exact fun h => h.1
        · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha, rfl⟩, hxE a ha⟩
      rw [hT, prod_image (fun a _ b _ hab => Sym2.congr_left.mp hab)]
      have hge : ∀ a ∈ A, ρmin ≤ qe s(a, x) := by
        intro a ha
        show ρmin ≤ ρ (pmE p s(a, x))
        rw [pmE_mk, hxi]
        exact hrhoge (hal a ha)
      refine (pow_le_pow_of_le_one hρmin0.le hρmin1 hAh).trans ?_
      rw [← prod_const]
      exact prod_le_prod₀ (fun _ _ => hρmin0.le) hge
    -- the size of the candidate set
    have hK2 : g * Fintype.card V / 2 ≤ ((K2 S A i).card : ℝ) := by
      have hsub : (univ.filter fun x => p x = i) ⊆ (K2 S A i ∪ S) ∪
          A.biUnion (fun a => univ.filter fun w => w ≠ a ∧ AllowedPair F (p a) (p w) ∧
            s(a, w) ∉ G.edgeFinset \ (B ∪ X)) := by
        intro x hx
        have hxi : p x = i := (mem_filter.mp hx).2
        by_cases hxS : x ∈ S
        · exact mem_union_left _ (mem_union_right _ hxS)
        by_cases hall : ∀ a ∈ A, s(a, x) ∈ E
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hxi, hxS, hall⟩))
        · push Not at hall
          obtain ⟨a, ha, haE⟩ := hall
          refine mem_union_right _ (mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨mem_univ _, ?_, ?_, haE⟩⟩)
          · rintro rfl; exact hxS (hA ha)
          · rw [hxi]; exact hal a ha
      have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _))
      have h2 := card_biUnion_le (s := A) (t := fun a => univ.filter fun w => w ≠ a ∧
        AllowedPair F (p a) (p w) ∧ s(a, w) ∉ G.edgeFinset \ (B ∪ X))
      have h3 : (∑ a ∈ A, ((univ.filter fun w => w ≠ a ∧ AllowedPair F (p a) (p w) ∧
          s(a, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ)) ≤ A.card * (d + δ * Fintype.card V + K) := by
        have := sum_le_card_nsmul A (fun a => ((univ.filter fun w => w ≠ a ∧
          AllowedPair F (p a) (p w) ∧ s(a, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ))
          (d + δ * Fintype.card V + K) fun a _ => card_miss_le F p G B X d δ K hmiss hB hXK a
        rwa [nsmul_eq_mul] at this
      have hA' : (A.card : ℝ) ≤ h := by exact_mod_cast hAh
      have hS' : (S.card : ℝ) ≤ h := by exact_mod_cast hS
      have h1' : (clsz p i) ≤ ((K2 S A i).card : ℝ) + S.card +
          ∑ a ∈ A, ((univ.filter fun w => w ≠ a ∧ AllowedPair F (p a) (p w) ∧
            s(a, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ) := by
        have : ((univ.filter fun x => p x = i).card : ℝ) ≤ ((K2 S A i).card : ℝ) + S.card +
            ((A.biUnion (fun a => univ.filter fun w => w ≠ a ∧ AllowedPair F (p a) (p w) ∧
              s(a, w) ∉ G.edgeFinset \ (B ∪ X))).card : ℝ) := by exact_mod_cast h1
        have h2' : ((A.biUnion (fun a => univ.filter fun w => w ≠ a ∧ AllowedPair F (p a) (p w) ∧
            s(a, w) ∉ G.edgeFinset \ (B ∪ X))).card : ℝ) ≤
            ∑ a ∈ A, ((univ.filter fun w => w ≠ a ∧ AllowedPair F (p a) (p w) ∧
              s(a, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ) := by exact_mod_cast h2
        unfold clsz; linarith
      have h4 : (A.card : ℝ) * (d + δ * Fintype.card V + K) ≤
          h * (2 * δ * Fintype.card V + K) := by
        have : (d : ℝ) + δ * Fintype.card V + K ≤ 2 * δ * Fintype.card V + K := by linarith
        exact mul_le_mul hA' this (by positivity) (Nat.cast_nonneg _)
      have h5 : (h : ℝ) * (2 * δ * Fintype.card V + K) + h ≤ g * Fintype.card V / 4 +
          g * Fintype.card V / 8 := by
        have e1 : (h : ℝ) * (2 * δ * Fintype.card V) ≤ g / 4 * Fintype.card V := by
          have := mul_le_mul_of_nonneg_right hδg hn.le
          nlinarith
        have e2 : (h : ℝ) * K + h ≤ g * Fintype.card V / 8 := by
          have : (h : ℝ) * K + h ≤ ((h : ℝ) + 1) * ((K : ℝ) + 1) := by
            nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
          linarith
        nlinarith
      linarith [hcls' i]
    have hmean2 : 2 * ωC * Fintype.card V ≤ ∑ z ∈ K2 S A i, ∏ e ∈ T2 A z, qe e := by
      calc 2 * ωC * Fintype.card V = (g * Fintype.card V / 2) * ρmin ^ h := by rw [hωC]; ring
        _ ≤ ((K2 S A i).card : ℝ) * ρmin ^ h :=
            mul_le_mul_of_nonneg_right hK2 (by positivity)
        _ = ∑ _z ∈ K2 S A i, ρmin ^ h := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum hprod
    have htarget : (((K2 S A i).filter fun z => T2 A z ⊆ R).card : ℝ) ≤
        ((univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ R).card : ℝ) := by
      have hsub : (K2 S A i).filter (fun z => T2 A z ⊆ R) ⊆
          univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ R := by
        intro x hx
        obtain ⟨hxK, hxT⟩ := mem_filter.mp hx
        obtain ⟨hxi, hxS, hxE⟩ := (mem_filter.mp hxK).2
        refine mem_filter.mpr ⟨mem_univ _, hxi, hxS, fun a ha => hxT ?_⟩
        exact mem_filter.mpr ⟨mem_image.mpr ⟨a, ha, rfl⟩, hxE a ha⟩
      exact_mod_cast card_le_card hsub
    have := (abs_sub_lt_iff.mp hdev).2
    have hωTC : ωT ≤ ωC := min_le_left _ _
    have : ωT * Fintype.card V ≤ ωC * Fintype.card V := mul_le_mul_of_nonneg_right hωTC hn.le
    linarith
  · -- weights
    intro τ hτ
    obtain ⟨hl, hu⟩ := wtT_bounds F p hθ hn hn4 hg0 hcls' hτ (hcard τ hτ)
    have ht1 : (1 : ℝ) ≤ t := by
      obtain ⟨x, -⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hcard τ hτ]; norm_num)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact x.elim0)
    constructor
    · have h1 : ωT ≤ 1 / (θ ^ 2 * ((t : ℝ) + 1) ^ 3) := (min_le_right _ _).trans (min_le_left _ _)
      have h2 : 1 / (θ ^ 2 * ((t : ℝ) + 1) ^ 3) ≤ 1 / (θ ^ 2 * (t : ℝ) ^ 3) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (t : ℝ) ^ 3 ≤ ((t : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
        exact mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    · have h1 : ωT ≤ (θ * g / 2) ^ 3 / θ := (min_le_right _ _).trans (min_le_right _ _)
      have h2 : θ / (θ * g / 2) ^ 3 = 1 / ((θ * g / 2) ^ 3 / θ) := by rw [one_div_div]
      rw [h2] at hu
      exact hu.trans (one_div_le_one_div_of_le hωT0 h1)
  · -- loads
    intro a b hab
    have hpos : ∀ c, c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F →
        ρ {a, b} ≠ 0 ∧ ρ {c, a} ≠ 0 ∧ ρ {c, b} ≠ 0 := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := allowed_of_cons hc
      exact ⟨(lt_of_lt_of_le hρmin0 (hrhoge h1)).ne', (lt_of_lt_of_le hρmin0 (hrhoge h2)).ne',
        (lt_of_lt_of_le hρmin0 (hrhoge h3)).ne'⟩
    rcases load_identity F (clsz p) (Fintype.card V) θ hn a b hpos with h1 | h1
    · rw [h1, sub_self, abs_zero]; exact hε.le
    · obtain ⟨c, hc⟩ := exists_third_cons hab
      have : c ∈ (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F) :=
        mem_filter.mpr ⟨mem_univ _, hc⟩
      rw [h1] at this
      exact absurd this (notMem_empty _)
  · -- typed thirds
    intro u v huv hal τ hτ
    show |((thirdsT p R u v τ).card : ℝ) - kappaT ρ (clsz p) (Fintype.card V) τ (p u) (p v) *
      Fintype.card V| ≤ ε * Fintype.card V
    have hdev := hω3 u (mem_univ _) v (mem_univ _) τ hτ
    simp only [D3, not_le] at hdev
    rw [hblk _ _ (hT3E u v), hmean _ _ (hT3E u v)] at hdev
    -- the count is the block count
    have hcnt : thirdsT p R u v τ = (K3 u v τ).filter fun z => T3 u v z ⊆ R := by
      ext w
      simp only [thirdsT, K3, T3, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine ⟨⟨h1, h2, hRE h3, hRE h4, h5⟩, fun e he => ?_⟩
        rcases mem_insert.mp (mem_filter.mp he).1 with rfl | he'
        · exact h3
        · rw [mem_singleton.mp he']; exact h4
      · rintro ⟨⟨h1, h2, h3, h4, h5⟩, hT⟩
        exact ⟨h1, h2, hT (mem_filter.mpr ⟨mem_insert_self _ _, h3⟩),
          hT (mem_filter.mpr ⟨mem_insert_of_mem (mem_singleton_self _), h4⟩), h5⟩
    rw [← hcnt] at hdev
    -- the mean over the candidates
    set f : V → ℝ := fun w => ρ {p u, p w} * ρ {p v, p w} with hf
    have hf01 : ∀ w, 0 ≤ f w ∧ f w ≤ 1 := fun w =>
      ⟨mul_nonneg (hrho0 _ _) (hrho0 _ _),
        mul_le_one₀ (hrho1 _ _) (hrho0 _ _) (hrho1 _ _)⟩
    have hmean3 : ∑ z ∈ K3 u v τ, ∏ e ∈ T3 u v z, qe e = ∑ z ∈ K3 u v τ, f z := by
      refine sum_congr rfl fun z hz => ?_
      obtain ⟨hzu, hzv, hzE1, hzE2, -⟩ := (mem_filter.mp hz).2
      have hT : T3 u v z = {s(u, z), s(v, z)} := by
        ext e; simp only [T3, mem_filter, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hzE1⟩
          · exact ⟨Or.inr rfl, hzE2⟩
      have hne : s(u, z) ≠ s(v, z) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact huv h1
        · exact hzu h1.symm
      rw [hT, prod_pair hne]
      rfl
    rw [hmean3] at hdev
    -- full candidates (no deletions)
    set K3f : Finset V := univ.filter fun w => w ≠ u ∧ w ≠ v ∧
      ({p u, p v, p w} : Multiset (Fin t)) = τ with hK3f
    have hK3sub : K3 u v τ ⊆ K3f := by
      intro w hw
      obtain ⟨h1, h2, -, -, h5⟩ := (mem_filter.mp hw).2
      exact mem_filter.mpr ⟨mem_univ _, h1, h2, h5⟩
    have hdiff : ((K3f \ K3 u v τ).card : ℝ) ≤ 2 * (d + δ * Fintype.card V + K) := by
      have hsub : K3f \ K3 u v τ ⊆
          (univ.filter fun w => w ≠ u ∧ AllowedPair F (p u) (p w) ∧
            s(u, w) ∉ G.edgeFinset \ (B ∪ X)) ∪
          (univ.filter fun w => w ≠ v ∧ AllowedPair F (p v) (p w) ∧
            s(v, w) ∉ G.edgeFinset \ (B ∪ X)) := by
        intro w hw
        obtain ⟨hwf, hwK⟩ := mem_sdiff.mp hw
        obtain ⟨h1, h2, h5⟩ := (mem_filter.mp hwf).2
        have hτ' : p w ::ₘ ({p u, p v} : Multiset (Fin t)) ∈ F := by
          rw [← triRot3, h5]; exact hτ
        obtain ⟨-, hwu, hwv⟩ := allowed_of_cons hτ'
        by_cases hu : s(u, w) ∈ E
        · by_cases hv : s(v, w) ∈ E
          · exact absurd (mem_filter.mpr ⟨mem_univ _, h1, h2, hu, hv, h5⟩) hwK
          · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h2, hwv.symm, hv⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h1, hwu.symm, hu⟩)
      have h1 := (card_le_card hsub).trans (card_union_le _ _)
      have hu' := card_miss_le F p G B X d δ K hmiss hB hXK u
      have hv' := card_miss_le F p G B X d δ K hmiss hB hXK v
      have : ((K3f \ K3 u v τ).card : ℝ) ≤
          ((univ.filter fun w => w ≠ u ∧ AllowedPair F (p u) (p w) ∧
            s(u, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ) +
          ((univ.filter fun w => w ≠ v ∧ AllowedPair F (p v) (p w) ∧
            s(v, w) ∉ G.edgeFinset \ (B ∪ X)).card : ℝ) := by exact_mod_cast h1
      linarith
    have hfull1 : |(∑ z ∈ K3 u v τ, f z) - ∑ z ∈ K3f, f z| ≤ 2 * (d + δ * Fintype.card V + K) := by
      have hsd := sum_sdiff hK3sub (f := f)
      have h0 : 0 ≤ ∑ z ∈ K3f \ K3 u v τ, f z := sum_nonneg fun z _ => (hf01 z).1
      have h1 : ∑ z ∈ K3f \ K3 u v τ, f z ≤ ((K3f \ K3 u v τ).card : ℝ) := by
        calc ∑ z ∈ K3f \ K3 u v τ, f z ≤ ∑ _z ∈ K3f \ K3 u v τ, (1 : ℝ) :=
              sum_le_sum fun z _ => (hf01 z).2
          _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]
      rw [abs_sub_le_iff]
      constructor <;> linarith
    -- the full sum against `κ n`
    set Wc : Fin t → Finset V := fun c => univ.filter fun w => p w = c ∧ w ≠ u ∧ w ≠ v with hWc
    have hfib : ∑ z ∈ K3f, f z = ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
        ρ {p u, c} * ρ {p v, c} * (Wc c).card := by
      rw [← sum_fiberwise_of_maps_to (g := p) (t := (univ : Finset (Fin t))) (fun _ _ => mem_univ _)]
      rw [sum_filter]
      refine sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · have e : K3f.filter (fun w => p w = c) = Wc c := by
          ext w
          simp only [hK3f, hWc, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨⟨h1, h2, -⟩, h4⟩; exact ⟨h4, h1, h2⟩
          · rintro ⟨h4, h1, h2⟩
            refine ⟨⟨h1, h2, ?_⟩, h4⟩
            rw [triRot3, h4]; exact hc
        rw [e, sum_congr rfl (g := fun _ => ρ {p u, c} * ρ {p v, c}) fun w hw => by
          simp only [hf, (mem_filter.mp hw).2.1]]
        rw [sum_const, nsmul_eq_mul, mul_comm]
      · refine sum_eq_zero fun w hw => ?_
        exfalso
        obtain ⟨hwf, hwc⟩ := mem_filter.mp hw
        obtain ⟨-, -, h5⟩ := (mem_filter.mp hwf).2
        apply hc
        rw [← hwc, ← triRot3]; exact h5
    have hkap : kappaT ρ (clsz p) (Fintype.card V) τ (p u) (p v) * Fintype.card V =
        ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
          ρ {p u, c} * ρ {p v, c} * nPrime (clsz p) {p u, p v} c := by
      unfold kappaT
      rw [sum_mul]
      exact sum_congr rfl fun c _ => div_mul_cancel₀ _ hn.ne'
    have hfull2 : |(∑ z ∈ K3f, f z) -
        kappaT ρ (clsz p) (Fintype.card V) τ (p u) (p v) * Fintype.card V| ≤ 2 * t := by
      rw [hfib, hkap, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
          |ρ {p u, c} * ρ {p v, c} * (Wc c).card -
            ρ {p u, c} * ρ {p v, c} * nPrime (clsz p) {p u, p v} c| ≤ 2 := by
        intro c _
        rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg (hrho0 _ _) (hrho0 _ _))]
        have hw1 := card_filter_ne_ne_le p u v c
        have hw2 := clsz_le_card_filter_ne_ne p u v c
        have hc2 := count_pair_le_two (p u) (p v) c
        have hc0 := count_nonneg' ({p u, p v} : Multiset (Fin t)) c
        have hab : |((Wc c).card : ℝ) - nPrime (clsz p) {p u, p v} c| ≤ 2 := by
          unfold nPrime
          rw [abs_sub_le_iff]; constructor <;> linarith
        calc ρ {p u, c} * ρ {p v, c} * |((Wc c).card : ℝ) - nPrime (clsz p) {p u, p v} c|
            ≤ 1 * 2 := mul_le_mul (mul_le_one₀ (hrho1 _ _) (hrho0 _ _) (hrho1 _ _)) hab
              (abs_nonneg _) zero_le_one
          _ = 2 := one_mul 2
      calc ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
            |ρ {p u, c} * ρ {p v, c} * (Wc c).card -
              ρ {p u, c} * ρ {p v, c} * nPrime (clsz p) {p u, p v} c|
          ≤ ∑ _c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ), (2 : ℝ) :=
            sum_le_sum hterm
        _ ≤ 2 * t := by
            rw [sum_const, nsmul_eq_mul, mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            have := card_filter_le (univ : Finset (Fin t))
              (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ)
            rw [card_univ, Fintype.card_fin] at this
            exact_mod_cast this
    -- assemble
    have hdev' := abs_sub_lt_iff.mp hdev
    have hsl : 2 * ((d : ℝ) + δ * Fintype.card V + K) + 2 * t ≤ ε1 / 4 * Fintype.card V := by
      have e1 : 4 * δ * (Fintype.card V : ℝ) ≤ ε1 / 8 * Fintype.card V := by
        have := mul_le_mul_of_nonneg_right hδε hn.le
        linarith
      have e2 : 2 * (K : ℝ) + 2 * t ≤ ε1 / 16 * Fintype.card V := by
        have : 2 * (K : ℝ) + 2 * t ≤ 2 * ((K : ℝ) + t + 1) := by linarith
        linarith
      linarith
    have hεε : ε1 * Fintype.card V ≤ ε * Fintype.card V :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le
    rw [abs_sub_le_iff] at hfull1 hfull2 ⊢
    constructor <;> linarith [hfull1.1, hfull1.2, hfull2.1, hfull2.2, hdev'.1, hdev'.2]


/-- **Nearly-complete absorbers for every family of 3-element types, from the typed Keevash
interface alone.** The reserve (binomial graph + typed nibble) is proved here. -/
theorem nearlyAbsorbing_of_keevashTyped {F : Finset (Multiset (Fin t))}
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hK : KeevashTypedSpec F) : NearlyAbsorbing F :=
  nearlyAbsorbing_of_keevash_typical hK fun h => typicalReserveSpec hcard h

end PartitionedTriangleAbsorption.BlowupB
