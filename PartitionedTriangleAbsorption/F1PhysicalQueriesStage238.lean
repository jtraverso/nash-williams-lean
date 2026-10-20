/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1JointQueriesStage235
public import PartitionedTriangleAbsorption.F1CompatibleBudgetStage237

/-! # A single edge reserve with physical vertex tests and charge tests

The vertex tests include arbitrary predetermined bad sets. Thus a protected
grandchild and a missing neighbourhood can be tested on the SAME reserve as
the pairs and the global charge counts. No independent resampling is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1PhysicalQueriesStage238

open Finset F1JointQueriesStage235
open scoped NNReal

variable {V K : Type*} [DecidableEq V]

/-- Two distinct stars give two edges per query vertex. -/
theorem pair_card (x y z : V) (hxy : x ≠ y) :
    ({s(x, z), s(y, z)} : Finset (Sym2 V)).card = 2 := by
  have h : s(x, z) ≠ s(y, z) := by
    intro he
    rcases Sym2.eq_iff.mp he with he | he
    · exact hxy he.1
    · exact hxy (he.1.trans he.2)
  simp [h]

/-- A finite list of unary or two-root vertex tests, together with two
global edge tests. The proof constructs one physical subset of `host`.

`Y k` is selected before sampling and can depend on all the host geometry.
`pair k = false` includes degree, class-size, and sampled bad-set tests.
`pair k = true` includes overlaps and common reserved neighbours.
The two global sets can be the positive and negative charge classes.
-/
theorem exists_physical_queries [Finite V]
    (host : Finset (Sym2 V)) (ρ : ℝ≥0) (hρ : ρ ≤ 1)
    (I : Finset K) (Y : K → Finset V) (x y : K → V) (pair : K → Bool)
    (P : Bool → Finset (Sym2 V)) (t m : K → ℝ) (tE mE : ℝ)
    (hsub : ∀ k ∈ I, ∀ z ∈ Y k, s(x k, z) ∈ host)
    (hsub₂ : ∀ k ∈ I, pair k = true → ∀ z ∈ Y k, s(y k, z) ∈ host)
    (hneq : ∀ k ∈ I, pair k = true → x k ≠ y k)
    (hroots : ∀ k ∈ I, pair k = true → x k ∉ Y k ∧ y k ∉ Y k)
    (hP : ∀ b, P b ⊆ host)
    (ht : ∀ k ∈ I, 0 < t k) (hm : ∀ k ∈ I, 0 < m k)
    (hYm : ∀ k ∈ I, ((Y k).card : ℝ) ≤ m k)
    (htE : 0 < tE) (hmE : 0 < mE) (hPm : ∀ b, ((P b).card : ℝ) ≤ mE)
    (htail : (∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k)) +
      2 * (2 * Real.exp (-2 * tE ^ 2 / mE)) < 1) :
    ∃ R ⊆ host,
      (∀ k ∈ I,
        |(((Y k).filter fun z => s(x k, z) ∈ R ∧
            (pair k = true → s(y k, z) ∈ R)).card : ℝ) -
          (ρ : ℝ) ^ (if pair k then 2 else 1) * (Y k).card| < t k) ∧
      (∀ b, |((P b ∩ R).card : ℝ) - (ρ : ℝ) * (P b).card| < tE) := by
  classical
  let J := I.disjSum (univ : Finset Bool)
  let Z : K ⊕ Bool → Finset (V ⊕ Sym2 V)
    | .inl k => (Y k).map Function.Embedding.inl
    | .inr b => (P b).map Function.Embedding.inr
  let B : K ⊕ Bool → V ⊕ Sym2 V → Finset (Sym2 V)
    | .inl k, .inl z => if pair k then {s(x k, z), s(y k, z)} else {s(x k, z)}
    | .inr _, .inr e => {e}
    | _, _ => ∅
  let d : K ⊕ Bool → ℕ
    | .inl k => if pair k then 2 else 1
    | .inr _ => 1
  let a : K ⊕ Bool → ℝ := Sum.elim t (fun _ => tE)
  let b : K ⊕ Bool → ℝ := Sum.elim m (fun _ => mE)
  have htail' : ∑ k ∈ J, 2 * Real.exp (-2 * a k ^ 2 / b k) < 1 := by
    simpa [J, a, b, sum_disjSum, Fintype.sum_bool] using htail
  obtain ⟨R, hR, hgood⟩ := exists_joint_block_reserve host ρ hρ J Z B d a b
    (by
      intro k hk z hz'
      cases k with
      | inl k =>
        have hk : k ∈ I := by simpa [J] using hk
        obtain ⟨z, hzY, rfl⟩ := mem_map.mp hz'
        change (if pair k then {s(x k, z), s(y k, z)} else {s(x k, z)}) ⊆ host
        split
        · rename_i hp
          exact insert_subset (hsub k hk z hzY) (singleton_subset_iff.mpr (hsub₂ k hk hp z hzY))
        · exact singleton_subset_iff.mpr (hsub k hk z hzY)
      | inr c =>
        obtain ⟨e, heP, rfl⟩ := mem_map.mp hz'
        exact singleton_subset_iff.mpr (hP c heP))
    (by
      intro k hk z hz'
      cases k with
      | inl k =>
        have hk : k ∈ I := by simpa [J] using hk
        obtain ⟨z, _, rfl⟩ := mem_map.mp hz'
        change (if pair k then {s(x k, z), s(y k, z)} else {s(x k, z)} : Finset (Sym2 V)).card =
          (if pair k then 2 else 1)
        split
        · rename_i hp
          exact pair_card _ _ _ (hneq k hk hp)
        · exact card_singleton _
      | inr c =>
        obtain ⟨e, _, rfl⟩ := mem_map.mp hz'
        exact card_singleton e)
    (by
      intro k hk z hz' w hw' hzw
      cases k with
      | inl k =>
        have hk : k ∈ I := by simpa [J] using hk
        obtain ⟨z, hzY, rfl⟩ := mem_map.mp hz'
        obtain ⟨w, hwY, rfl⟩ := mem_map.mp hw'
        have hzw' : z ≠ w := fun h => hzw (by cases h; rfl)
        change Disjoint (if pair k then {s(x k, z), s(y k, z)} else {s(x k, z)})
          (if pair k then {s(x k, w), s(y k, w)} else {s(x k, w)})
        split
        · rename_i hp
          exact star_pair_disjoint (Y k) (x k) (y k)
            (hroots k hk hp).1 (hroots k hk hp).2 hzY hzw'
        · simp only [disjoint_singleton_left, mem_singleton]
          intro hs
          rcases Sym2.eq_iff.mp hs with hs | hs
          · exact hzw' hs.2
          · exact hzw' (hs.2.trans hs.1)
      | inr c =>
        obtain ⟨e, _, rfl⟩ := mem_map.mp hz'
        obtain ⟨f, _, rfl⟩ := mem_map.mp hw'
        simpa [B] using (show e ≠ f from fun h => hzw (by cases h; rfl)))
    (by
      intro k hk
      cases k with
      | inl k => exact ht k (by simpa [J] using hk)
      | inr _ => exact htE)
    (by
      intro k hk
      cases k with
      | inl k => exact hm k (by simpa [J] using hk)
      | inr _ => exact hmE)
    (by
      intro k hk
      cases k with
      | inl k => simpa [Z, b] using hYm k (by simpa [J] using hk)
      | inr c => simpa [Z, b] using hPm c) htail'
  refine ⟨R, hR, ?_, ?_⟩
  · intro k hk
    have h := hgood (.inl k) (by simpa [J] using hk)
    have hc : (((Z (.inl k)).filter fun w => B (.inl k) w ⊆ R).card) =
        ((Y k).filter fun z => s(x k, z) ∈ R ∧ (pair k = true → s(y k, z) ∈ R)).card := by
      simp only [Z, filter_map, card_map]
      congr 1
      apply filter_congr
      intro z _
      cases hp : pair k <;> simp [B, hp, insert_subset_iff]
    rw [hc] at h
    cases hp : pair k <;> simpa [Z, d, a, hp] using h
  · intro c
    have h := hgood (.inr c) (by simp [J])
    have hc : (((Z (.inr c)).filter fun w => B (.inr c) w ⊆ R).card) = (P c ∩ R).card := by
      simp only [Z, filter_map, card_map]
      congr 1
      ext e
      simp [B]
    rw [hc] at h
    simpa [Z, d, a] using h

/-- Index all the graph queries, including an uncoloured option for degrees.
Modes: full degree, child target, protected/missing bad set, pair overlap,
outer common-neighbour test, child common-neighbour test. -/
abbrev Query (V : Type*) := Fin 6 × V × V × Option (Fin 4)

def queryIndices (W : Finset V) : Finset (Query V) :=
  ((univ : Finset (Fin 6)) ×ˢ (W ×ˢ (W ×ˢ (univ : Finset (Option (Fin 4)))))).filter
    fun k => k.1 = 3 → k.2.1 ≠ k.2.2.1

def queryVertices (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (W U U' : Finset V) (host : Finset (Sym2 V)) (k : Query V) : Finset V :=
  (if k.1 = 0 then W else if k.1 = 4 then W \ U else U).filter fun z =>
    (k.2.2.2 = none ∨ k.2.2.2 = some (p z)) ∧ s(k.2.1, z) ∈ host ∧
    (k.1 = 3 → s(k.2.2.1, z) ∈ host) ∧
    (k.1 = 2 → z ∈ U' ∨ ¬ G.Adj k.2.2.1 z) ∧
    (k.1 = 4 → G.Adj k.2.2.1 z) ∧ (k.1 = 5 → s(k.2.2.1, z) ∈ host)

theorem query_count (W : Finset V) : (queryIndices W).card ≤ 30 * W.card ^ 2 := by
  apply (card_filter_le _ _).trans
  simp only [card_product, card_univ, Fintype.card_fin, Fintype.card_option]
  exact le_of_eq (by ring)

/-- The whole graph-derived query family has at most 30 n² members.
Together with two charge tests, a single explicit tail bound supplies one
reserve. `P` may be any two prescribed subsets of the same physical host. -/
theorem exists_graph_tests [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (W U U' : Finset V) (hU : U ⊆ W)
    (host : Finset (Sym2 V)) (hhost : host ⊆ G.edgeFinset)
    (hsize : (host.card : ℝ) ≤ (W.card : ℝ) ^ 2)
    (P : Bool → Finset (Sym2 V)) (hP : ∀ b, P b ⊆ host)
    (ρ : ℝ≥0) (hρ : ρ ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hW : 0 < W.card)
    (htail : (30 * (W.card : ℝ) ^ 2 + 2) *
      (2 * Real.exp (-(2 * ε ^ 2) * W.card)) < 1) :
    ∃ R ⊆ host,
      (∀ k ∈ queryIndices W,
        |(((queryVertices G p W U U' host k).filter fun z => s(k.2.1, z) ∈ R ∧
            (k.1 = 3 → s(k.2.2.1, z) ∈ R)).card : ℝ) -
          (ρ : ℝ) ^ (if k.1 = 3 then 2 else 1) *
            (queryVertices G p W U U' host k).card| < ε * W.card) ∧
      (∀ b, |((P b ∩ R).card : ℝ) - (ρ : ℝ) * (P b).card| < ε * (W.card : ℝ) ^ 2) := by
  classical
  let Y := queryVertices G p W U U' host
  have hn : (0 : ℝ) < W.card := by exact_mod_cast hW
  have hn1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW
  have hY : ∀ k, Y k ⊆ W := by
    intro k
    apply (filter_subset _ _).trans
    split_ifs
    · exact Subset.rfl
    · exact sdiff_subset
    · exact hU
  have hlocal : -2 * (ε * (W.card : ℝ)) ^ 2 / W.card = -(2 * ε ^ 2) * W.card := by
    field_simp
  have hglobal : -2 * (ε * (W.card : ℝ) ^ 2) ^ 2 / (W.card : ℝ) ^ 2 =
      -(2 * ε ^ 2) * (W.card : ℝ) ^ 2 := by
    field_simp
  have hpow : (W.card : ℝ) ≤ (W.card : ℝ) ^ 2 := by nlinarith
  have hexp : 2 * Real.exp (-2 * (ε * (W.card : ℝ) ^ 2) ^ 2 / (W.card : ℝ) ^ 2) ≤
      2 * Real.exp (-(2 * ε ^ 2) * W.card) := by
    rw [hglobal]
    have harg : -(2 * ε ^ 2) * (W.card : ℝ) ^ 2 ≤ -(2 * ε ^ 2) * W.card :=
      mul_le_mul_of_nonpos_left hpow (by nlinarith [sq_nonneg ε])
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  have hnum : ((queryIndices W).card : ℝ) ≤ 30 * (W.card : ℝ) ^ 2 := by
    exact_mod_cast query_count W
  have ht : (∑ _k ∈ queryIndices W,
      2 * Real.exp (-2 * (ε * (W.card : ℝ)) ^ 2 / W.card)) +
      2 * (2 * Real.exp (-2 * (ε * (W.card : ℝ) ^ 2) ^ 2 / (W.card : ℝ) ^ 2)) < 1 := by
    simp only [hlocal, sum_const, nsmul_eq_mul]
    have hm := mul_le_mul_of_nonneg_right hnum
      (show 0 ≤ 2 * Real.exp (-(2 * ε ^ 2) * W.card) by positivity)
    nlinarith
  obtain ⟨R, hR, hv, he⟩ := exists_physical_queries host ρ hρ (queryIndices W) Y
    (fun k => k.2.1) (fun k => k.2.2.1) (fun k => decide (k.1 = 3)) P
    (fun _ => ε * W.card) (fun _ => W.card) (ε * (W.card : ℝ) ^ 2) ((W.card : ℝ) ^ 2)
    (by
      intro k _ z hz
      exact (mem_filter.mp hz).2.2.1)
    (by
      intro k _ hk z hz
      exact (mem_filter.mp hz).2.2.2.1 (of_decide_eq_true hk))
    (by
      intro k hk hp
      exact (mem_filter.mp hk).2 (of_decide_eq_true hp))
    (by
      intro k _ hp
      have hp' : k.1 = 3 := of_decide_eq_true hp
      constructor
      · intro hz
        have he := (mem_filter.mp hz).2.2.1
        exact G.irrefl (SimpleGraph.mem_edgeFinset.mp (hhost he))
      · intro hz
        have he := (mem_filter.mp hz).2.2.2.1 hp'
        exact G.irrefl (SimpleGraph.mem_edgeFinset.mp (hhost he)))
    hP (by intros; positivity) (by intros; exact hn)
    (by intro k _; change ((Y k).card : ℝ) ≤ (W.card : ℝ); exact_mod_cast card_le_card (hY k))
    (by positivity) (by positivity)
    (by
      intro b
      have hb : ((P b).card : ℝ) ≤ host.card := by exact_mod_cast card_le_card (hP b)
      exact hb.trans hsize) ht
  exact ⟨R, hR, by simpa [Y] using hv, he⟩

/-- The order threshold depends only on the accuracy, not on the graph,
the reserve density, the protected grandchild, or the prescribed tests. -/
theorem uniform_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (30 * (n : ℝ) ^ 2 + 2) * (2 * Real.exp (-(2 * ε ^ 2) * n)) < 1 := by
  obtain ⟨N, hN⟩ := F1CompatibleBudgetStage237.joint_query_threshold ε hε
  refine ⟨max N 1, by omega, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hn
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
  have hcoef : 30 * (n : ℝ) ^ 2 + 2 ≤ 32 * (n : ℝ) ^ 3 + 2 := by nlinarith [sq_nonneg (n : ℝ)]
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans_lt
    (hN n ((le_max_left N 1).trans hn))

/-- The bad-set query is restricted to physical host edges. This is enough
for an upper bound on the REAL sampled obstruction, including missing edges
and the protected grandchild. It does not assume concentration around the
larger, unfiltered bad set. -/
theorem sampled_bad_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (W U U' : Finset V) (host R : Finset (Sym2 V))
    (hR : R ⊆ host) (x v : V) (c : Fin 4) (ρ t : ℝ) (hρ : 0 ≤ ρ)
    (hquery :
      |(((queryVertices G p W U U' host (2, x, v, some c)).filter
          fun z => s(x, z) ∈ R).card : ℝ) -
        ρ * (queryVertices G p W U U' host (2, x, v, some c)).card| ≤ t) :
    ((U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z) ∧ s(x, z) ∈ R).card : ℝ) ≤
      ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ G.Adj v z).card) + t := by
  classical
  let Y := queryVertices G p W U U' host (2, x, v, some c)
  have heq : Y.filter (fun z => s(x, z) ∈ R) =
      U.filter (fun z => p z = c ∧ (z ∈ U' ∨ ¬ G.Adj v z) ∧ s(x, z) ∈ R) := by
    ext z
    simp only [Y, queryVertices, Fin.reduceEq, ite_false, mem_filter]
    have h := fun hz : s(x, z) ∈ R => hR hz
    simp only [Option.some.injEq, reduceCtorEq, false_or, false_implies, and_true]
    aesop
  have hs : Y ⊆ U' ∪ (U.filter fun z => p z = c ∧ ¬ G.Adj v z) := by
    intro z hz
    have hz' : z ∈ U ∧ p z = c ∧ s(x, z) ∈ host ∧ (z ∈ U' ∨ ¬ G.Adj v z) := by
      simpa [Y, queryVertices, eq_comm, and_assoc] using hz
    rcases hz'.2.2.2 with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.mpr ⟨hz'.1, hz'.2.1, h⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hcR : (Y.card : ℝ) ≤ U'.card + (U.filter fun z => p z = c ∧ ¬ G.Adj v z).card := by
    exact_mod_cast hc
  have hu := (abs_le.mp hquery).2
  change ((Y.filter fun z => s(x, z) ∈ R).card : ℝ) - ρ * Y.card ≤ t at hu
  rw [heq] at hu
  have hm := mul_le_mul_of_nonneg_left hcR hρ
  linarith

/-- The tests on two singleton stars and on their intersection also
control the unreserved pair, without a second random choice. -/
theorem unreserved_pair_error (U A B : Finset V) (ρ tx ty txy : ℝ)
    (hx : |((U ∩ A).card : ℝ) - ρ * U.card| ≤ tx)
    (hy : |((U ∩ B).card : ℝ) - ρ * U.card| ≤ ty)
    (hxy : |((U ∩ A ∩ B).card : ℝ) - ρ ^ 2 * U.card| ≤ txy) :
    |((U \ (A ∪ B)).card : ℝ) - (1-ρ) ^ 2 * U.card| ≤ tx + ty + txy := by
  have hc := complement_pair_count U A B
  have hcR : ((U \ (A ∪ B)).card : ℝ) + (U ∩ A).card + (U ∩ B).card =
      U.card + (U ∩ A ∩ B).card := by exact_mod_cast hc
  rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
  rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
  rcases abs_le.mp hxy with ⟨hxy₁, hxy₂⟩
  apply abs_le.mpr
  constructor <;> nlinarith

open F1BalanceGateStage228

omit [DecidableEq V] in
/-- The two global counts are the actual signed balance, not just a proxy
on a separate sampled graph. -/
theorem balance_counts (p : V → Fin 4) (E : Finset (Sym2 V)) :
    balance p E = ((E.filter fun e => charge p e = 1).card : ℝ) -
      2 * (E.filter fun e => charge p e = -2).card := by
  classical
  simp only [balance, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ x y =>
    simp only [charge, Sym2.lift_mk, pairCharge]
    split <;> norm_num

/-- Simultaneous concentration of the two charge classes controls the
charge to be repaired, with the correct coefficient three. -/
theorem sampled_balance_error (p : V → Fin 4) (host R : Finset (Sym2 V))
    (hR : R ⊆ host) (ρ t : ℝ)
    (hp : |(((host.filter fun e => charge p e = 1) ∩ R).card : ℝ) -
      ρ * (host.filter fun e => charge p e = 1).card| ≤ t)
    (hm : |(((host.filter fun e => charge p e = -2) ∩ R).card : ℝ) -
      ρ * (host.filter fun e => charge p e = -2).card| ≤ t) :
    |balance p R - ρ * balance p host| ≤ 3 * t := by
  classical
  have he (a : ℝ) : (host.filter fun e => charge p e = a) ∩ R =
      R.filter (fun e => charge p e = a) := by
    ext e
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨_, hc⟩, hr⟩
      exact ⟨hr, hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨⟨hR hr, hc⟩, hr⟩
  rw [he] at hp hm
  rw [balance_counts, balance_counts]
  rcases abs_le.mp hp with ⟨hp₁, hp₂⟩
  rcases abs_le.mp hm with ⟨hm₁, hm₂⟩
  apply abs_le.mpr
  constructor <;> nlinarith

end PartitionedTriangleAbsorption.F1PhysicalQueriesStage238
