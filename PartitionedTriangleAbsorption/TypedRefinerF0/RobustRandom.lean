/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.PermCount
public import PartitionedTriangleAbsorption.TypedRefinerF0.Estimates
public import PartitionedTriangleAbsorption.TypedRefinerF0.RobustHall

/-! # Existence of bounded-degree robustly matchable bipartite graphs

Six permutations `σ_j` of `6k` points give the plus–`Y` edges (a plus vertex `x` owns the
points `2x, 2x+1`, a `Y` vertex `y` owns `3y, 3y+1, 3y+2`); six further permutations `τ_j`
give the plus–`Z` edges. Counting the bad permutation tuples (`PermCount`) and summing the
union bound (`Estimates`) shows that some tuple satisfies `Good1` and `Good2`, hence the graph
is robustly matchable (`RobustHall`). Plus degrees are at most `24`, minus degrees at most `18`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset

/-- The sample space: two families of six permutations of `6k` points. -/
abbrev Omega (k : ℕ) :=
  (Fin 6 → Equiv.Perm (Fin (6 * k))) × (Fin 6 → Equiv.Perm (Fin (6 * k)))

/-- Points owned (with multiplicity `m`) by a set of vertices. -/
def pts (k m : ℕ) (A : Finset ℕ) : Finset (Fin (6 * k)) := univ.filter fun i => (i : ℕ) / m ∈ A

theorem card_pts (k m : ℕ) (hm : 0 < m) (A : Finset ℕ) (hA : ∀ a ∈ A, m * a + m ≤ 6 * k) :
    (pts k m A).card = m * A.card := by
  have hc : (A ×ˢ range m).card = m * A.card := by
    rw [card_product, card_range, mul_comm]
  rw [← hc]
  symm
  refine card_bij (fun ar h => (⟨m * ar.1 + ar.2, ?_⟩ : Fin (6 * k))) ?_ ?_ ?_
  · obtain ⟨h1, h2⟩ := mem_product.mp h
    have := hA _ h1
    have := mem_range.mp h2
    omega
  · intro ar h
    obtain ⟨h1, h2⟩ := mem_product.mp h
    simp only [pts, mem_filter, mem_univ, true_and]
    rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (mem_range.mp h2), add_zero]
    exact h1
  · intro ar h ar' h' heq
    have heq' : m * ar.1 + ar.2 = m * ar'.1 + ar'.2 := by
      simpa using congrArg Fin.val heq
    have r1 := mem_range.mp (mem_product.mp h).2
    have r2 := mem_range.mp (mem_product.mp h').2
    have e1 : ar.1 = ar'.1 := by
      have := congrArg (· / m) heq'
      simp only [Nat.mul_add_div hm, Nat.div_eq_of_lt r1, Nat.div_eq_of_lt r2] at this
      omega
    have e2 : ar.2 = ar'.2 := by rw [e1] at heq'; omega
    exact Prod.ext e1 e2
  · intro i hi
    simp only [pts, mem_filter, mem_univ, true_and] at hi
    refine ⟨((i : ℕ) / m, (i : ℕ) % m), mem_product.mpr ⟨hi, mem_range.mpr (Nat.mod_lt _ hm)⟩, ?_⟩
    ext
    simp only
    exact Nat.div_add_mod _ _

/-- The random bipartite graph of a sample point. -/
def rgraph {k : ℕ} (ω : Omega k) : Finset (ℕ × (ℕ ⊕ ℕ)) :=
  (univ : Finset (Fin 6 × Fin (6 * k))).image
      (fun ji => ((ji.2 : ℕ) / 2, (Sum.inl (((ω.1 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ))) ∪
    (univ : Finset (Fin 6 × Fin (6 * k))).image
      (fun ji => ((ji.2 : ℕ) / 2, (Sum.inr (((ω.2 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ)))

variable {k : ℕ}

theorem mem_rgraph_inl {ω : Omega k} {x y : ℕ} :
    (x, Sum.inl y) ∈ rgraph ω ↔ ∃ j, ∃ i : Fin (6 * k),
      (i : ℕ) / 2 = x ∧ ((ω.1 j i : Fin (6 * k)) : ℕ) / 3 = y := by
  simp only [rgraph, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq, Prod.exists,
    Sum.inl.injEq, reduceCtorEq, and_false, exists_false, or_false]

theorem mem_rgraph_inr {ω : Omega k} {x y : ℕ} :
    (x, Sum.inr y) ∈ rgraph ω ↔ ∃ j, ∃ i : Fin (6 * k),
      (i : ℕ) / 2 = x ∧ ((ω.2 j i : Fin (6 * k)) : ℕ) / 3 = y := by
  simp only [rgraph, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq, Prod.exists,
    Sum.inr.injEq, reduceCtorEq, and_false, exists_false, false_or]

theorem rgraph_fst {ω : Omega k} {h : ℕ × (ℕ ⊕ ℕ)} (hh : h ∈ rgraph ω) : h.1 < 3 * k := by
  simp only [rgraph, mem_union, mem_image, mem_univ, true_and] at hh
  rcases hh with ⟨⟨j, i⟩, rfl⟩ | ⟨⟨j, i⟩, rfl⟩ <;>
  · have := i.isLt; simp only; omega

theorem rgraph_snd {ω : Omega k} {h : ℕ × (ℕ ⊕ ℕ)} (hh : h ∈ rgraph ω) : h.2 ∈ minusSide k := by
  simp only [rgraph, mem_union, mem_image, mem_univ, true_and] at hh
  rw [minusSide, mem_disjSum]
  rcases hh with ⟨⟨j, i⟩, rfl⟩ | ⟨⟨j, i⟩, rfl⟩
  · have := (ω.1 j i).isLt
    exact Or.inl ⟨_, mem_range.mpr (by omega), rfl⟩
  · have := (ω.2 j i).isLt
    exact Or.inr ⟨_, mem_range.mpr (by omega), rfl⟩

/-! ### Bad events -/

/-- Small plus set `A` whose `Y`-neighbourhood lies in `Q`. -/
noncomputable def E1 (A Q : Finset ℕ) : Finset (Omega k) :=
  (Fintype.piFinset fun _ => permsInto (pts k 2 A) (pts k 3 Q)) ×ˢ univ

/-- Small minus set `B` whose neighbourhood lies in `Q`. -/
noncomputable def E2 (B : Finset (ℕ ⊕ ℕ)) (Q : Finset ℕ) : Finset (Omega k) :=
  (Fintype.piFinset fun _ =>
      univ.filter fun σ : Equiv.Perm (Fin (6 * k)) =>
        ∀ x ∈ pts k 3 B.toLeft, σ.symm x ∈ pts k 2 Q) ×ˢ
    (Fintype.piFinset fun _ =>
      univ.filter fun σ : Equiv.Perm (Fin (6 * k)) => ∀ x ∈ pts k 3 B.toRight, σ.symm x ∈ pts k 2 Q)

variable (k) in
noncomputable def Bad1 : Finset (Omega k) :=
  (Icc 1 k).biUnion fun a => (powersetCard a (range (3 * k))).biUnion fun A =>
    (powersetCard a (range (2 * k))).biUnion fun Q => E1 A Q

variable (k) in
noncomputable def Bad2 : Finset (Omega k) :=
  (Icc 1 (2 * k)).biUnion fun b => (powersetCard b (minusSide k)).biUnion fun B =>
    (powersetCard b (range (3 * k))).biUnion fun Q => E2 B Q

theorem good1_of_not_bad {ω : Omega k} (h : ω ∉ Bad1 k) : Good1 k (rgraph ω) := by
  intro A hA h1 hk
  by_contra hle
  push Not at hle
  have hsub : (nbr (rgraph ω) A).toLeft ⊆ range (2 * k) := by
    intro y hy
    rw [mem_toLeft] at hy
    obtain ⟨x, -, hxy⟩ := mem_nbr.mp hy
    have := rgraph_snd hxy
    simp only [minusSide, mem_disjSum, Sum.inl.injEq, reduceCtorEq, and_false, exists_false,
      or_false] at this
    obtain ⟨a, ha, rfl⟩ := this
    exact ha
  obtain ⟨Q, hNQ, hQ, hQc⟩ := exists_subsuperset_card_eq hsub hle
    (by rw [card_range]; omega)
  apply h
  simp only [Bad1, mem_biUnion, mem_Icc, mem_powersetCard]
  refine ⟨A.card, ⟨h1, hk⟩, A, ⟨hA, rfl⟩, Q, ⟨hQ, hQc⟩, ?_⟩
  simp only [E1, mem_product, Fintype.mem_piFinset, mem_univ, and_true]
  intro j
  rw [mem_permsInto]
  intro i hi
  simp only [pts, mem_filter, mem_univ, true_and] at hi ⊢
  apply hNQ
  rw [mem_toLeft]
  exact mem_nbr.mpr ⟨_, hi, mem_rgraph_inl.mpr ⟨j, i, rfl, rfl⟩⟩

theorem good2_of_not_bad {ω : Omega k} (h : ω ∉ Bad2 k) : Good2 k (rgraph ω) := by
  intro B hB h1 hk
  by_contra hle
  push Not at hle
  have hsub : nbrX (rgraph ω) B ⊆ range (3 * k) := by
    intro x hx
    obtain ⟨y, -, hxy⟩ := mem_nbrX.mp hx
    exact mem_range.mpr (rgraph_fst hxy)
  obtain ⟨Q, hNQ, hQ, hQc⟩ := exists_subsuperset_card_eq hsub hle
    (by rw [card_range]; omega)
  apply h
  simp only [Bad2, mem_biUnion, mem_Icc, mem_powersetCard]
  refine ⟨B.card, ⟨h1, hk⟩, B, ⟨hB, rfl⟩, Q, ⟨hQ, hQc⟩, ?_⟩
  simp only [E2, mem_product, Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
  constructor
  · intro j y hy
    simp only [pts, mem_filter, mem_univ, true_and, mem_toLeft] at hy ⊢
    apply hNQ
    refine mem_nbrX.mpr ⟨_, hy, mem_rgraph_inl.mpr ⟨j, (ω.1 j).symm y, rfl, ?_⟩⟩
    simp
  · intro j y hy
    simp only [pts, mem_filter, mem_univ, true_and, mem_toRight] at hy ⊢
    apply hNQ
    refine mem_nbrX.mpr ⟨_, hy, mem_rgraph_inr.mpr ⟨j, (ω.2 j).symm y, rfl, ?_⟩⟩
    simp

/-! ### Counting -/

theorem card_omega : (Fintype.card (Omega k) : ℝ) = ((6 * k).factorial : ℝ) ^ 12 := by
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_perm, Fintype.card_fin,
    prod_const, card_univ]
  push_cast; ring

theorem card_E1_le {a : ℕ} {A Q : Finset ℕ} (hA : A ⊆ range (3 * k)) (hAc : A.card = a)
    (hQ : Q ⊆ range (2 * k)) (hQc : Q.card = a) :
    ((E1 (k := k) A Q).card : ℝ) ≤
      ((6 * k).factorial : ℝ) ^ 12 * ((a : ℝ) / (2 * k)) ^ (2 * a * 6) := by
  have hpA : (pts k 2 A).card = 2 * a := by
    rw [card_pts k 2 (by norm_num) A (fun x hx => by have := mem_range.mp (hA hx); omega), hAc]
  have hpQ : (pts k 3 Q).card = 3 * a := by
    rw [card_pts k 3 (by norm_num) Q (fun x hx => by have := mem_range.mp (hQ hx); omega), hQc]
  have hc := card_permsInto_le (pts k 2 A) (pts k 3 Q)
  rw [hpA, hpQ, Fintype.card_fin] at hc
  have e : ((3 * a : ℕ) : ℝ) / ((6 * k : ℕ) : ℝ) = (a : ℝ) / (2 * k) := by
    push_cast
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp; ring
  rw [e] at hc
  simp only [E1, card_product, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
    Fintype.card_pi, Fintype.card_perm]
  push_cast
  have h0 : (0 : ℝ) ≤ (permsInto (pts k 2 A) (pts k 3 Q)).card := Nat.cast_nonneg _
  calc ((permsInto (pts k 2 A) (pts k 3 Q)).card : ℝ) ^ 6 * ((6 * k).factorial : ℝ) ^ 6
      ≤ (((6 * k).factorial : ℝ) * ((a : ℝ) / (2 * k)) ^ (2 * a)) ^ 6 *
          ((6 * k).factorial : ℝ) ^ 6 := by
        gcongr
    _ = ((6 * k).factorial : ℝ) ^ 12 * ((a : ℝ) / (2 * k)) ^ (2 * a * 6) := by
        rw [mul_pow, ← pow_mul]; ring

theorem card_E2_le {b : ℕ} {B : Finset (ℕ ⊕ ℕ)} {Q : Finset ℕ} (hB : B ⊆ minusSide k)
    (hBc : B.card = b) (hQ : Q ⊆ range (3 * k)) (hQc : Q.card = b) :
    ((E2 (k := k) B Q).card : ℝ) ≤
      ((6 * k).factorial : ℝ) ^ 12 * ((b : ℝ) / (3 * k)) ^ (3 * b * 6) := by
  have hL : ∀ y ∈ B.toLeft, 3 * y + 3 ≤ 6 * k := by
    intro y hy
    have := hB (mem_toLeft.mp hy)
    simp only [minusSide, mem_disjSum, Sum.inl.injEq, reduceCtorEq, and_false, exists_false,
      or_false] at this
    obtain ⟨a, ha, rfl⟩ := this
    have := mem_range.mp ha; omega
  have hR : ∀ y ∈ B.toRight, 3 * y + 3 ≤ 6 * k := by
    intro y hy
    have := hB (mem_toRight.mp hy)
    simp only [minusSide, mem_disjSum, Sum.inr.injEq, reduceCtorEq, and_false, exists_false,
      false_or] at this
    obtain ⟨a, ha, rfl⟩ := this
    have := mem_range.mp ha; omega
  have hpQ : (pts k 2 Q).card = 2 * b := by
    rw [card_pts k 2 (by norm_num) Q (fun x hx => by have := mem_range.mp (hQ hx); omega), hQc]
  have hpL := card_pts k 3 (by norm_num) _ hL
  have hpR := card_pts k 3 (by norm_num) _ hR
  have hsplit := card_toLeft_add_card_toRight (u := B)
  have e : ((2 * b : ℕ) : ℝ) / ((6 * k : ℕ) : ℝ) = (b : ℝ) / (3 * k) := by
    push_cast
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp; ring
  have c1 := card_permsInto_le (pts k 3 B.toLeft) (pts k 2 Q)
  have c2 := card_permsInto_le (pts k 3 B.toRight) (pts k 2 Q)
  rw [hpQ, hpL, Fintype.card_fin, e] at c1
  rw [hpQ, hpR, Fintype.card_fin, e] at c2
  rw [← card_permsInto_inv] at c1 c2
  simp only [E2, card_product, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  push_cast
  set y : ℝ := (b : ℝ) / (3 * k)
  set F : ℝ := ((6 * k).factorial : ℝ)
  calc ((univ.filter fun σ : Equiv.Perm (Fin (6 * k)) =>
          ∀ x ∈ pts k 3 B.toLeft, σ.symm x ∈ pts k 2 Q).card : ℝ) ^ 6 *
        ((univ.filter fun σ : Equiv.Perm (Fin (6 * k)) =>
          ∀ x ∈ pts k 3 B.toRight, σ.symm x ∈ pts k 2 Q).card : ℝ) ^ 6
      ≤ (F * y ^ (3 * B.toLeft.card)) ^ 6 * (F * y ^ (3 * B.toRight.card)) ^ 6 := by
        gcongr
        · convert c1
        · convert c2
    _ = F ^ 12 * y ^ (3 * (B.toLeft.card + B.toRight.card) * 6) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        rw [show 3 * (B.toLeft.card + B.toRight.card) * 6 =
          3 * B.toLeft.card * 6 + 3 * B.toRight.card * 6 by ring, pow_add]
        ring
    _ = F ^ 12 * y ^ (3 * b * 6) := by rw [hsplit, hBc]

theorem card_bad1_le :
    ((Bad1 k).card : ℝ) ≤ ((6 * k).factorial : ℝ) ^ 12 * (1 / 15) := by
  set F : ℝ := ((6 * k).factorial : ℝ) ^ 12
  have hF : 0 ≤ F := by positivity
  have h1 : ((Bad1 k).card : ℝ) ≤ ∑ a ∈ Icc 1 k, ∑ A ∈ powersetCard a (range (3 * k)),
      ∑ Q ∈ powersetCard a (range (2 * k)), ((E1 (k := k) A Q).card : ℝ) := by
    have : (Bad1 k).card ≤ ∑ a ∈ Icc 1 k, ∑ A ∈ powersetCard a (range (3 * k)),
        ∑ Q ∈ powersetCard a (range (2 * k)), (E1 (k := k) A Q).card := by
      refine card_biUnion_le.trans (sum_le_sum fun a _ => ?_)
      refine card_biUnion_le.trans (sum_le_sum fun A _ => ?_)
      exact card_biUnion_le
    exact_mod_cast this
  refine h1.trans ?_
  calc ∑ a ∈ Icc 1 k, ∑ A ∈ powersetCard a (range (3 * k)),
        ∑ Q ∈ powersetCard a (range (2 * k)), ((E1 (k := k) A Q).card : ℝ)
      ≤ ∑ a ∈ Icc 1 k, F * (((3 * k).choose a : ℝ) * ((2 * k).choose a : ℝ) *
          ((a : ℝ) / (2 * k)) ^ (2 * a * 6)) := by
        refine sum_le_sum fun a _ => ?_
        have : ∑ A ∈ powersetCard a (range (3 * k)), ∑ Q ∈ powersetCard a (range (2 * k)),
            ((E1 (k := k) A Q).card : ℝ) ≤ ∑ A ∈ powersetCard a (range (3 * k)),
              ∑ Q ∈ powersetCard a (range (2 * k)), F * ((a : ℝ) / (2 * k)) ^ (2 * a * 6) := by
          refine sum_le_sum fun A hA => sum_le_sum fun Q hQ => ?_
          obtain ⟨hA1, hA2⟩ := mem_powersetCard.mp hA
          obtain ⟨hQ1, hQ2⟩ := mem_powersetCard.mp hQ
          exact card_E1_le hA1 hA2 hQ1 hQ2
        refine this.trans (le_of_eq ?_)
        simp only [sum_const, card_powersetCard, card_range, nsmul_eq_mul]
        ring
    _ = F * ∑ a ∈ Icc 1 k, ((3 * k).choose a : ℝ) * ((2 * k).choose a : ℝ) *
          ((a : ℝ) / (2 * k)) ^ (2 * a * 6) := by rw [mul_sum]
    _ ≤ F * ∑ a ∈ Icc 1 k, ((1 : ℝ) / 16) ^ a := by
        gcongr with a ha
        obtain ⟨ha1, ha2⟩ := mem_Icc.mp ha
        exact term_one_le k a ha1 ha2
    _ ≤ F * (1 / 15) := by gcongr; exact sum_Icc_pow_le k

theorem card_minusSide : (minusSide k).card = 4 * k := by
  rw [minusSide, card_disjSum, card_range]; ring

theorem card_bad2_le :
    ((Bad2 k).card : ℝ) ≤ ((6 * k).factorial : ℝ) ^ 12 * (1 / 15) := by
  set F : ℝ := ((6 * k).factorial : ℝ) ^ 12
  have hF : 0 ≤ F := by positivity
  have h1 : ((Bad2 k).card : ℝ) ≤ ∑ b ∈ Icc 1 (2 * k), ∑ B ∈ powersetCard b (minusSide k),
      ∑ Q ∈ powersetCard b (range (3 * k)), ((E2 (k := k) B Q).card : ℝ) := by
    have : (Bad2 k).card ≤ ∑ b ∈ Icc 1 (2 * k), ∑ B ∈ powersetCard b (minusSide k),
        ∑ Q ∈ powersetCard b (range (3 * k)), (E2 (k := k) B Q).card := by
      refine card_biUnion_le.trans (sum_le_sum fun b _ => ?_)
      refine card_biUnion_le.trans (sum_le_sum fun B _ => ?_)
      exact card_biUnion_le
    exact_mod_cast this
  refine h1.trans ?_
  calc ∑ b ∈ Icc 1 (2 * k), ∑ B ∈ powersetCard b (minusSide k),
        ∑ Q ∈ powersetCard b (range (3 * k)), ((E2 (k := k) B Q).card : ℝ)
      ≤ ∑ b ∈ Icc 1 (2 * k), F * (((4 * k).choose b : ℝ) * ((3 * k).choose b : ℝ) *
          ((b : ℝ) / (3 * k)) ^ (3 * b * 6)) := by
        refine sum_le_sum fun b _ => ?_
        have : ∑ B ∈ powersetCard b (minusSide k), ∑ Q ∈ powersetCard b (range (3 * k)),
            ((E2 (k := k) B Q).card : ℝ) ≤ ∑ B ∈ powersetCard b (minusSide k),
              ∑ Q ∈ powersetCard b (range (3 * k)), F * ((b : ℝ) / (3 * k)) ^ (3 * b * 6) := by
          refine sum_le_sum fun B hB => sum_le_sum fun Q hQ => ?_
          obtain ⟨hB1, hB2⟩ := mem_powersetCard.mp hB
          obtain ⟨hQ1, hQ2⟩ := mem_powersetCard.mp hQ
          exact card_E2_le hB1 hB2 hQ1 hQ2
        refine this.trans (le_of_eq ?_)
        simp only [sum_const, card_powersetCard, card_range, card_minusSide, nsmul_eq_mul]
        ring
    _ = F * ∑ b ∈ Icc 1 (2 * k), ((4 * k).choose b : ℝ) * ((3 * k).choose b : ℝ) *
          ((b : ℝ) / (3 * k)) ^ (3 * b * 6) := by rw [mul_sum]
    _ ≤ F * ∑ b ∈ Icc 1 (2 * k), ((1 : ℝ) / 16) ^ b := by
        gcongr with b hb
        obtain ⟨hb1, hb2⟩ := mem_Icc.mp hb
        exact term_two_le k b hb1 hb2
    _ ≤ F * (1 / 15) := by gcongr; exact sum_Icc_pow_le (2 * k)

theorem exists_good_omega : ∃ ω : Omega k, ω ∉ Bad1 k ∧ ω ∉ Bad2 k := by
  have h1 := card_bad1_le (k := k)
  have h2 := card_bad2_le (k := k)
  have hF : (0 : ℝ) < ((6 * k).factorial : ℝ) ^ 12 := by positivity
  have hlt : (Bad1 k ∪ Bad2 k).card < (univ : Finset (Omega k)).card := by
    have : ((Bad1 k ∪ Bad2 k).card : ℝ) < ((univ : Finset (Omega k)).card : ℝ) := by
      rw [card_univ, card_omega]
      have := card_union_le (Bad1 k) (Bad2 k)
      have : ((Bad1 k ∪ Bad2 k).card : ℝ) ≤ (Bad1 k).card + (Bad2 k).card := by
        exact_mod_cast this
      linarith
    exact_mod_cast this
  obtain ⟨ω, -, hω⟩ := exists_mem_notMem_of_card_lt_card hlt
  rw [mem_union, not_or] at hω
  exact ⟨ω, hω⟩

/-! ### Degrees -/

theorem card_filter_div_le (n m x : ℕ) (hm : 0 < m) :
    (univ.filter fun i : Fin n => (i : ℕ) / m = x).card ≤ m := by
  have : (univ.filter fun i : Fin n => (i : ℕ) / m = x).card ≤ (range m).card := by
    refine card_le_card_of_injOn (fun i => (i : ℕ) % m) ?_ ?_
    · intro i _; exact mem_coe.mpr (mem_range.mpr (Nat.mod_lt _ hm))
    · intro i hi i' hi' h
      have e1 := (mem_filter.mp (mem_coe.mp hi)).2
      have e2 := (mem_filter.mp (mem_coe.mp hi')).2
      have d1 := Nat.div_add_mod (i : ℕ) m
      have d2 := Nat.div_add_mod (i' : ℕ) m
      simp only at h
      rw [e1, h] at d1
      rw [e2] at d2
      exact Fin.ext (by omega)
  simpa using this

theorem deg_plus_le (ω : Omega k) (x : ℕ) :
    ((rgraph ω).filter fun h => h.1 = x).card ≤ 24 := by
  set S := (univ : Finset (Fin 6 × Fin (6 * k))).filter fun ji => (ji.2 : ℕ) / 2 = x
  have hS : S.card ≤ 12 := by
    have : S = (univ : Finset (Fin 6)) ×ˢ (univ.filter fun i : Fin (6 * k) => (i : ℕ) / 2 = x) := by
      ext ⟨j, i⟩; simp [S]
    rw [this, card_product, card_univ, Fintype.card_fin]
    have := card_filter_div_le (6 * k) 2 x (by norm_num)
    omega
  have hsub : ((rgraph ω).filter fun h => h.1 = x) ⊆
      S.image (fun ji => ((ji.2 : ℕ) / 2, (Sum.inl (((ω.1 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ))) ∪
      S.image (fun ji => ((ji.2 : ℕ) / 2, (Sum.inr (((ω.2 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ))) := by
    intro h hh
    obtain ⟨hh, hx⟩ := mem_filter.mp hh
    simp only [rgraph, mem_union, mem_image, mem_univ, true_and] at hh
    simp only [mem_union, mem_image, S, mem_filter, mem_univ, true_and]
    rcases hh with ⟨ji, rfl⟩ | ⟨ji, rfl⟩
    · exact Or.inl ⟨ji, hx, rfl⟩
    · exact Or.inr ⟨ji, hx, rfl⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have := card_image_le (s := S)
    (f := fun ji => ((ji.2 : ℕ) / 2, (Sum.inl (((ω.1 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ)))
  have := card_image_le (s := S)
    (f := fun ji => ((ji.2 : ℕ) / 2, (Sum.inr (((ω.2 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ)))
  omega

theorem card_perm_fiber_le (σ : Fin 6 → Equiv.Perm (Fin (6 * k))) (y : ℕ) :
    ((univ : Finset (Fin 6 × Fin (6 * k))).filter
      fun ji => ((σ ji.1 ji.2 : Fin (6 * k)) : ℕ) / 3 = y).card ≤ 18 := by
  have : ((univ : Finset (Fin 6 × Fin (6 * k))).filter
      fun ji => ((σ ji.1 ji.2 : Fin (6 * k)) : ℕ) / 3 = y).card ≤
      ((univ : Finset (Fin 6)) ×ˢ (univ.filter fun i : Fin (6 * k) => (i : ℕ) / 3 = y)).card := by
    refine card_le_card_of_injOn (fun ji => (ji.1, σ ji.1 ji.2)) ?_ ?_
    · intro ji hji
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hji
      simp [hji]
    · intro ji _ ji' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h1' := h1
      rcases ji with ⟨j, i⟩
      rcases ji' with ⟨j', i'⟩
      simp only at h1 h2
      subst h1
      exact Prod.ext rfl ((σ j).injective h2)
  refine this.trans ?_
  rw [card_product, card_univ, Fintype.card_fin]
  have := card_filter_div_le (6 * k) 3 y (by norm_num)
  omega

theorem deg_minus_le (ω : Omega k) (y : ℕ ⊕ ℕ) :
    ((rgraph ω).filter fun h => h.2 = y).card ≤ 18 := by
  rcases y with y | y
  · have hsub : ((rgraph ω).filter fun h => h.2 = Sum.inl y) ⊆
        ((univ : Finset (Fin 6 × Fin (6 * k))).filter
          fun ji => ((ω.1 ji.1 ji.2 : Fin (6 * k)) : ℕ) / 3 = y).image
          (fun ji => ((ji.2 : ℕ) / 2, (Sum.inl (((ω.1 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ))) := by
      intro h hh
      obtain ⟨hh, he⟩ := mem_filter.mp hh
      simp only [rgraph, mem_union, mem_image, mem_univ, true_and] at hh
      simp only [mem_image, mem_filter, mem_univ, true_and]
      rcases hh with ⟨ji, rfl⟩ | ⟨ji, rfl⟩
      · simp only [Sum.inl.injEq] at he
        exact ⟨ji, he, rfl⟩
      · simp at he
    exact (card_le_card hsub).trans (card_image_le.trans (card_perm_fiber_le ω.1 y))
  · have hsub : ((rgraph ω).filter fun h => h.2 = Sum.inr y) ⊆
        ((univ : Finset (Fin 6 × Fin (6 * k))).filter
          fun ji => ((ω.2 ji.1 ji.2 : Fin (6 * k)) : ℕ) / 3 = y).image
          (fun ji => ((ji.2 : ℕ) / 2, (Sum.inr (((ω.2 ji.1) ji.2 : ℕ) / 3) : ℕ ⊕ ℕ))) := by
      intro h hh
      obtain ⟨hh, he⟩ := mem_filter.mp hh
      simp only [rgraph, mem_union, mem_image, mem_univ, true_and] at hh
      simp only [mem_image, mem_filter, mem_univ, true_and]
      rcases hh with ⟨ji, rfl⟩ | ⟨ji, rfl⟩
      · simp at he
      · simp only [Sum.inr.injEq] at he
        exact ⟨ji, he, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (card_perm_fiber_le ω.2 y))

/-- **Robustly matchable bipartite graphs of bounded degree exist** for every `k`. -/
theorem exists_rmbg (k : ℕ) : ∃ H : Finset (ℕ × (ℕ ⊕ ℕ)),
    (∀ h ∈ H, h.1 < 3 * k) ∧ (∀ h ∈ H, h.2 ∈ minusSide k) ∧
    (∀ x, (H.filter fun h => h.1 = x).card ≤ 24) ∧
    (∀ y, (H.filter fun h => h.2 = y).card ≤ 18) ∧
    ∀ Z ⊆ range (2 * k), Z.card = k →
      ∃ f : ℕ → ℕ ⊕ ℕ, Set.InjOn f (range (3 * k)) ∧ (∀ x < 3 * k, (x, f x) ∈ H) ∧
        (range (3 * k)).image f = (range (2 * k)).disjSum Z := by
  obtain ⟨ω, h1, h2⟩ := exists_good_omega (k := k)
  refine ⟨rgraph ω, fun h hh => rgraph_fst hh, fun h hh => rgraph_snd hh,
    deg_plus_le ω, deg_minus_le ω, ?_⟩
  intro Z hZs hZ
  exact matching_of_good (fun h hh => rgraph_fst hh) (fun h hh => rgraph_snd hh)
    (good1_of_not_bad h1) (good2_of_not_bad h2) hZs hZ

end PartitionedTriangleAbsorption.TypedRefinerF0
