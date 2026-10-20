/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.ReserveWeights
public import PartitionedTriangleAbsorption.BlowupB.CubeBlocks

/-! # BlowupB.TypicalReserve — the typical reserve exists (binomial random graph)

**`typicalReserveSpec`**: for every family of 3-element types, `TypicalReserveSpec F h` holds.
The reserve is the random subgraph of `E = G \ (B ∪ X)` keeping the pair `uv` with probability
`ρ {p u, p v}` (`rhoM`, scale `θ = eta / (4 t)`), on the finite Bernoulli cube of
`BernoulliExposure`. Degrees, common neighbourhoods and typed-thirds counts are block counts
(`CubeBlocks`); `blockCount_tail` and the union bound over `n + (h+1) 2^h t n^h + |F| n²` events
leave a good outcome for large `n`. Weights and loads come from `ReserveWeights`
(`load_identity`: exact unit loads).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {t : ℕ}

/-! ### Asymptotics -/

theorem exists_pow_mul_exp_lt' (k : ℕ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ k0 : ℕ, ∀ n : ℕ, k0 ≤ n → C * (n : ℝ) ^ k * Real.exp (-(c * n)) < 1 := by
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hev : ∀ᶠ x : ℝ in Filter.atTop, x ^ k * Real.exp (-x) < c ^ k / C :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨k0, hk0⟩ := exists_nat_ge (X / c)
  refine ⟨k0, fun n hn => ?_⟩
  have hnX : X ≤ c * n := by
    have : X / c ≤ n := hk0.trans (by exact_mod_cast hn)
    rwa [div_le_iff₀ hc, mul_comm] at this
  have h := hX (c * n) hnX
  rw [mul_pow] at h
  have hck : 0 < c ^ k := by positivity
  have h1 : (n : ℝ) ^ k * Real.exp (-(c * n)) < 1 / C := by
    have h' : c ^ k * ((n : ℝ) ^ k * Real.exp (-(c * n))) < c ^ k * (1 / C) := by
      calc c ^ k * ((n : ℝ) ^ k * Real.exp (-(c * n)))
          = c ^ k * (n : ℝ) ^ k * Real.exp (-(c * n)) := by ring
        _ < c ^ k / C := h
        _ = c ^ k * (1 / C) := by ring
    exact lt_of_mul_lt_mul_left h' hck.le
  calc C * (n : ℝ) ^ k * Real.exp (-(c * n)) = C * ((n : ℝ) ^ k * Real.exp (-(c * n))) := by
        ring
    _ < C * (1 / C) := mul_lt_mul_of_pos_left h1 hC
    _ = 1 := by field_simp

/-- Tail exponent: `(a n)² / (4 (M + a n)) ≥ a² / (4 (a + b)) · n` when `M ≤ b n`. -/
theorem tail_rate {a b M n : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hn : 0 < n) (hM0 : 0 ≤ M)
    (hM : M ≤ b * n) :
    a ^ 2 / (4 * (a + b)) * n ≤ (a * n) ^ 2 / (4 * (M + a * n)) := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : a ^ 2 * n * (4 * (M + a * n)) ≤ a ^ 2 * n * (4 * (b * n + a * n)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-! ### Edge coins -/

section Coins

variable {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))

/-- The edge of a coin. -/
noncomputable def edgeOf (i : Fin E.card) : Sym2 V := (E.equivFin.symm i).1

theorem edgeOf_mem (i : Fin E.card) : edgeOf E i ∈ E := (E.equivFin.symm i).2

theorem edgeOf_injective : Function.Injective (edgeOf E) := by
  intro i j h
  exact E.equivFin.symm.injective (Subtype.ext h)

theorem edgeOf_coinOf {e : Sym2 V} (he : e ∈ E) : edgeOf E (E.equivFin ⟨e, he⟩) = e := by
  simp [edgeOf]

/-- The random edge set of an outcome. -/
noncomputable def randE (ω : Fin E.card → Bool) : Finset (Sym2 V) :=
  (univ.filter fun i => ω i = true).image (edgeOf E)

theorem randE_subset (ω : Fin E.card → Bool) : randE E ω ⊆ E := by
  intro e he
  obtain ⟨i, -, rfl⟩ := mem_image.mp he
  exact edgeOf_mem E i

theorem mem_randE_iff (ω : Fin E.card → Bool) (i : Fin E.card) :
    edgeOf E i ∈ randE E ω ↔ ω i = true := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := mem_image.mp h
    rw [edgeOf_injective E hji] at hj
    exact (mem_filter.mp hj).2
  · intro h
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, h⟩, rfl⟩

/-- Coins of a set of edges. -/
noncomputable def coinsOf (T : Finset (Sym2 V)) : Finset (Fin E.card) := univ.filter fun i => edgeOf E i ∈ T

theorem prod_coin_coinsOf (ω : Fin E.card → Bool) {T : Finset (Sym2 V)} (hT : T ⊆ E) :
    ∏ i ∈ coinsOf E T, coin ω i = if T ⊆ randE E ω then 1 else 0 := by
  split_ifs with h
  · refine prod_eq_one fun i hi => ?_
    have hiT : edgeOf E i ∈ T := (mem_filter.mp hi).2
    have := (mem_randE_iff E ω i).mp (h hiT)
    simp [coin, this]
  · obtain ⟨e, heT, heR⟩ := not_subset.mp h
    have he := hT heT
    refine prod_eq_zero (i := E.equivFin ⟨e, he⟩) ?_ ?_
    · exact mem_filter.mpr ⟨mem_univ _, by rw [edgeOf_coinOf E he]; exact heT⟩
    · have : ω (E.equivFin ⟨e, he⟩) ≠ true := by
        intro hω
        apply heR
        have := (mem_randE_iff E ω _).mpr hω
        rwa [edgeOf_coinOf E he] at this
      simp [coin, this]

theorem prod_q_coinsOf (qe : Sym2 V → ℝ) {T : Finset (Sym2 V)} (hT : T ⊆ E) :
    ∏ i ∈ coinsOf E T, qe (edgeOf E i) = ∏ e ∈ T, qe e := by
  refine prod_nbij (edgeOf E) (fun i hi => (mem_filter.mp hi).2)
    (fun i _ j _ h => edgeOf_injective E h) ?_ (fun _ _ => rfl)
  intro e he
  have hm : E.equivFin ⟨e, hT he⟩ ∈ coinsOf E T := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [edgeOf_coinOf E (hT he)]
    exact he
  exact ⟨_, hm, edgeOf_coinOf E (hT he)⟩

theorem card_coinsOf {T : Finset (Sym2 V)} (hT : T ⊆ E) : (coinsOf E T).card = T.card := by
  refine card_nbij (edgeOf E) (fun i hi => (mem_filter.mp hi).2)
    (fun i _ j _ h => edgeOf_injective E h) ?_
  intro e he
  have hm : E.equivFin ⟨e, hT he⟩ ∈ coinsOf E T := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [edgeOf_coinOf E (hT he)]
    exact he
  exact ⟨_, hm, edgeOf_coinOf E (hT he)⟩

theorem card_mem_sym2_le (e : Sym2 V) : (univ.filter fun z : V => z ∈ e).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ x y =>
    have : (univ.filter fun z : V => z ∈ s(x, y)) ⊆ {x, y} := by
      intro z hz
      simp only [mem_filter, mem_univ, true_and, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp
    exact (card_le_card this).trans (card_insert_le _ _)

/-- Coins of blocks attached to vertices lie in at most two blocks. -/
theorem coinLoad_le_two (K : Finset V) (T : V → Finset (Sym2 V))
    (hT : ∀ z ∈ K, ∀ e ∈ T z, z ∈ e) (i : Fin E.card) :
    coinLoad K (fun z => coinsOf E (T z)) i ≤ 2 := by
  unfold coinLoad
  have hsub : K.filter (fun z => i ∈ coinsOf E (T z)) ⊆ univ.filter fun z : V => z ∈ edgeOf E i := by
    intro z hz
    obtain ⟨hzK, hzi⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_univ _, hT z hzK _ (mem_filter.mp hzi).2⟩
  have := (card_le_card hsub).trans (card_mem_sym2_le (edgeOf E i))
  exact_mod_cast this

theorem sum_coinLoad_sq_le {ι : Type*} (q : Fin E.card → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (K : Finset ι) (B : ι → Finset (Fin E.card)) (L : ℝ) (hL : ∀ i, coinLoad K B i ≤ L) :
    ∑ i, q i * coinLoad K B i ^ 2 ≤ L * ∑ z ∈ K, ((B z).card : ℝ) := by
  have h1 : ∀ i, q i * coinLoad K B i ^ 2 ≤ L * coinLoad K B i := by
    intro i
    have h0 : 0 ≤ coinLoad K B i := Nat.cast_nonneg _
    have : coinLoad K B i ^ 2 ≤ L * coinLoad K B i := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hL i) h0
    calc q i * coinLoad K B i ^ 2 ≤ 1 * coinLoad K B i ^ 2 :=
          mul_le_mul_of_nonneg_right (hq i).2 (sq_nonneg _)
      _ ≤ L * coinLoad K B i := by rw [one_mul]; exact this
  refine (sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  unfold coinLoad
  have : ∑ i, (K.filter fun z => i ∈ B z).card = ∑ z ∈ K, (B z).card := by
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_boole]
    simp
  exact_mod_cast this

/-- Clean tail for vertex-indexed block counts of edge coins. -/
theorem vertexBlocks_tail (q : Fin E.card → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (K : Finset V) (T : V → Finset (Sym2 V)) (hTE : ∀ z, T z ⊆ E)
    (hT : ∀ z ∈ K, ∀ e ∈ T z, z ∈ e) (M : ℝ) (hM : ∑ z ∈ K, ((T z).card : ℝ) ≤ M)
    (s : ℝ) (hs : 0 < s) :
    cubeProb q (fun ω => s ≤ |blockCount K (fun z => coinsOf E (T z)) ω -
        ∑ z ∈ K, ∏ i ∈ coinsOf E (T z), q i|) ≤
      2 * Real.exp (-(s ^ 2 / (4 * (M + s)))) := by
  refine (blockCount_tail q hq K _ 2 (by norm_num) (coinLoad_le_two E K T hT) s hs).trans ?_
  have hV := sum_coinLoad_sq_le E q hq K (fun z => coinsOf E (T z)) 2 (coinLoad_le_two E K T hT)
  have hcard : ∑ z ∈ K, ((coinsOf E (T z)).card : ℝ) = ∑ z ∈ K, ((T z).card : ℝ) :=
    sum_congr rfl fun z _ => by rw [card_coinsOf E (hTE z)]
  rw [hcard] at hV
  have hV0 : 0 ≤ ∑ i, q i * coinLoad K (fun z => coinsOf E (T z)) i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hq i).1 (sq_nonneg _)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (sq_nonneg s) (by linarith)
  linarith

theorem blockCount_coinsOf (ω : Fin E.card → Bool) (K : Finset V) (T : V → Finset (Sym2 V))
    (hTE : ∀ z, T z ⊆ E) :
    blockCount K (fun z => coinsOf E (T z)) ω =
      ((K.filter fun z => T z ⊆ randE E ω).card : ℝ) := by
  unfold blockCount
  rw [sum_congr rfl fun z _ => prod_coin_coinsOf E ω (hTE z), ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]

end Coins

/-! ### Multiset bookkeeping -/

theorem triRot3 (a b c : Fin t) : ({a, b, c} : Multiset (Fin t)) = c ::ₘ {a, b} := by
  simp only [Multiset.insert_eq_cons]
  rw [← Multiset.cons_zero c, ← Multiset.cons_zero b, Multiset.cons_swap b c,
    Multiset.cons_swap a c]

theorem exists_third_cons {F : Finset (Multiset (Fin t))} {a b : Fin t} (h : AllowedPair F a b) :
    ∃ c, c ::ₘ ({a, b} : Multiset (Fin t)) ∈ F := by
  obtain ⟨τ, hτ, hc, hle⟩ := h
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hle
  have hu1 : Multiset.card u = 1 := by
    have := congrArg Multiset.card hu
    rw [Multiset.card_add, hc] at this
    simp at this
    omega
  obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp hu1
  refine ⟨c, ?_⟩
  rw [hu, add_comm, Multiset.singleton_add] at hτ
  exact hτ

end PartitionedTriangleAbsorption.BlowupB
