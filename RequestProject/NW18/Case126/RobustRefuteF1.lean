/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.BalanceLedgerF1

/-!
# Theorem 14.7 for `F₁`: the unconditioned robust weighting statement is false

`F1DamageRobustWeighting c₀ b` (`RobustWeightingF1.lean`) asks for near-unit weightings of the
punctured level for EVERY tolerance `τ`, under `PuncHyp` with arbitrary damage of maximum degree
`c₀ |W|`.  It does not ask for the signed balance that near-unit loads force
(`F1BalanceGateStage228.near_load_requires_balance`).  `not_F1DamageRobustWeighting` (proved)
shows that it fails for every `c₀ > 0` and every cap `b`.

Counterfamily (a variant of the one in the review, with a complete bipartite deletion instead of
matchings): four classes `Fin T`; `G` = all allowed pairs (cliques on the classes, all pairs
between `{0,1}` and `{2,3}`); `H` = `G` minus all edges between the first `k` vertices of class `0`
and the first `k` vertices of class `2`.  With `W = V`, `U = Res = ∅`, `q = 1`, `κ = ε = 0`,
`ξ = 1/(4T)`, `ζ = k/(4T)`, all clauses of `PuncHyp` hold, while
`balance(H) = 4T - k²` and the absolute charge mass is at most `16 T²`.  Taking `T = M m`, `k = m`
with `M ≥ 1/c₀` and `m` large gives the error floor `τ ≥ 1/(64 M²)`.

`H` is not integrally `F₁`-divisible (its balance is not `0`, `balance_eq_zero_of_intDiv`), so
this does NOT challenge the actual divisible vortex level or Nash-Williams 1.8.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.F1BalanceGateStage228 (pairCharge charge balance)

theorem allowedT_F1_symm : ∀ i j : Fin 4, AllowedT F1 i j → AllowedT F1 j i := by decide

/-- The complete allowed host on `Fin 4 × Fin T`. -/
def cexG (T : ℕ) : SimpleGraph (Fin 4 × Fin T) where
  Adj a b := a ≠ b ∧ AllowedT F1 a.1 b.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, allowedT_F1_symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (T : ℕ) : DecidableRel (cexG T).Adj := fun a b => by unfold cexG; infer_instance

/-- The deleted pairs: first `k` vertices of class `0` against first `k` of class `2`. -/
def cexDel (T k : ℕ) (a b : Fin 4 × Fin T) : Prop :=
  ((a.1 = 0 ∧ b.1 = 2) ∨ (a.1 = 2 ∧ b.1 = 0)) ∧ a.2.val < k ∧ b.2.val < k

instance (T k : ℕ) (a b : Fin 4 × Fin T) : Decidable (cexDel T k a b) := by
  unfold cexDel; infer_instance

/-- The damaged host. -/
def cexH (T k : ℕ) : SimpleGraph (Fin 4 × Fin T) where
  Adj a b := (cexG T).Adj a b ∧ ¬ cexDel T k a b
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd =>
    h.2 ⟨hd.1.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩), hd.2.2, hd.2.1⟩⟩⟩
  loopless := ⟨fun a h => (cexG T).loopless.irrefl a h.1⟩

instance (T k : ℕ) : DecidableRel (cexH T k).Adj := fun a b => by unfold cexH; infer_instance

theorem card_val_lt (T k : ℕ) (hk : k ≤ T) :
    (univ.filter fun j : Fin T => j.val < k).card = k := by
  have : (univ.filter fun j : Fin T => j.val < k) =
      (range k).attachFin (fun j hj => by simp at hj; omega) := by
    ext j; simp
  rw [this, card_attachFin, card_range]

theorem allowed_table :
    AllowedT F1 0 0 ∧ ¬ AllowedT F1 0 1 ∧ AllowedT F1 0 2 ∧ AllowedT F1 0 3 ∧
    ¬ AllowedT F1 1 0 ∧ AllowedT F1 1 1 ∧ AllowedT F1 1 2 ∧ AllowedT F1 1 3 ∧
    AllowedT F1 2 0 ∧ AllowedT F1 2 1 ∧ AllowedT F1 2 2 ∧ ¬ AllowedT F1 2 3 ∧
    AllowedT F1 3 0 ∧ AllowedT F1 3 1 ∧ ¬ AllowedT F1 3 2 ∧ AllowedT F1 3 3 := by decide

theorem card_ne_fin (T : ℕ) (i : Fin T) :
    (((univ.filter fun j : Fin T => ¬ i = j).card : ℕ) : ℝ) = T - 1 := by
  have h1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  have : (univ.filter fun j : Fin T => ¬ i = j) = univ.erase i := by
    ext j; simp [eq_comm]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_sub h1]
  simp

theorem card_del_fin (T k : ℕ) (hk : k ≤ T) (i : Fin T) :
    (((univ.filter fun j : Fin T => (i.val < k → k ≤ j.val)).card : ℕ) : ℝ) =
      T - if i.val < k then (k : ℝ) else 0 := by
  by_cases hi : i.val < k
  · have : (univ.filter fun j : Fin T => (i.val < k → k ≤ j.val)) =
        univ \ (univ.filter fun j : Fin T => j.val < k) := by
      ext j; simp [hi]
    rw [this, card_sdiff_of_subset (filter_subset _ _), card_val_lt T k hk, card_univ,
      Fintype.card_fin, Nat.cast_sub hk, if_pos hi]
  · have : (univ.filter fun j : Fin T => (i.val < k → k ≤ j.val)) = univ := by
      ext j; simp [hi]
    rw [this, card_univ, Fintype.card_fin, if_neg hi, sub_zero]

/-- The vertex charge sums of the damaged host. -/
theorem cex_vertex_sum (T k : ℕ) (hk : k ≤ T) (v : Fin 4 × Fin T) :
    (∑ z ∈ univ.filter ((cexH T k).Adj v), (pairCharge v.1 z.1 : ℝ)) =
      2 - if (v.1 = 0 ∨ v.1 = 2) ∧ v.2.val < k then (k : ℝ) else 0 := by
  obtain ⟨c, i⟩ := v
  rw [vertex_charge_fiber Prod.fst (c, i)]
  have hmap : ∀ c' : Fin 4, ((univ.filter ((cexH T k).Adj (c, i))).filter fun z => z.1 = c') =
      (univ.filter fun j : Fin T => (cexH T k).Adj (c, i) (c', j)).map
        ⟨fun j => (c', j), fun a b h => by simpa using h⟩ := by
    intro c'; ext ⟨d, j⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨j, h, rfl⟩
    · rintro ⟨j', h, heq⟩
      change (c', j') = (d, j) at heq
      cases heq
      exact ⟨h, rfl⟩
  simp only [hmap, card_map]
  rw [Fin.sum_univ_four]
  obtain ⟨a00, n01, a02, a03, n10, a11, a12, a13, a20, a21, a22, n23, a30, a31, n32, a33⟩ :=
    allowed_table
  fin_cases c <;>
    simp [cexH, cexG, cexDel, pairCharge, a00, n01, a02, a03, n10, a11, a12, a13, a20, a21, a22,
      n23, a30, a31, n32, a33, card_ne_fin, card_del_fin T k hk] <;> ring

/-- `balance(H) = 4T - k²`. -/
theorem cex_balance (T k : ℕ) (hk : k ≤ T) :
    balance (fun z : Fin 4 × Fin T => z.1) (cexH T k).edgeFinset = 4 * T - (k : ℝ) ^ 2 := by
  have h2 := sum_edges_two (cexH T k) (charge (fun z : Fin 4 × Fin T => z.1))
  have hv : ∀ v : Fin 4 × Fin T,
      (∑ z ∈ univ.filter ((cexH T k).Adj v), charge (fun z : Fin 4 × Fin T => z.1) s(v, z)) =
        2 - if (v.1 = 0 ∨ v.1 = 2) ∧ v.2.val < k then (k : ℝ) else 0 := by
    intro v
    rw [← cex_vertex_sum T k hk v]
    exact sum_congr rfl fun z _ => charge_mk _ v z
  rw [sum_congr rfl (fun v _ => hv v), Fintype.sum_prod_type, Fin.sum_univ_four] at h2
  have hk' : (∑ i : Fin T, if i.val < k then (k : ℝ) else 0) = (k : ℝ) ^ 2 := by
    rw [← sum_filter, sum_const, card_val_lt T k hk, nsmul_eq_mul]; ring
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  simp only [show ((1 : Fin 4) = 2) = False by decide, show ((3 : Fin 4) = 0) = False by decide,
    show ((3 : Fin 4) = 2) = False by decide, false_and, if_false, sum_const_zero,
    show ((1 : Fin 4) = 0) = False by decide, or_self, true_or, or_true, true_and] at h2
  rw [hk'] at h2
  unfold balance
  linarith

/-- The absolute charge mass is at most `(4T)²`. -/
theorem cex_mass (T k : ℕ) :
    ∑ e ∈ (cexH T k).edgeFinset, |charge (fun z : Fin 4 × Fin T => z.1) e| ≤
      16 * (T : ℝ) ^ 2 := by
  have h2 := sum_edges_two (cexH T k) (fun e => |charge (fun z : Fin 4 × Fin T => z.1) e|)
  have hv : ∀ v : Fin 4 × Fin T,
      (∑ z ∈ univ.filter ((cexH T k).Adj v), |charge (fun z : Fin 4 × Fin T => z.1) s(v, z)|) ≤
        2 * (4 * T) := by
    intro v
    have hz : ∀ z ∈ univ.filter ((cexH T k).Adj v),
        |charge (fun z : Fin 4 × Fin T => z.1) s(v, z)| ≤ 2 := by
      intro z _
      rw [charge_mk]
      have : ∀ a b : Fin 4, |(pairCharge a b : ℝ)| ≤ 2 := by
        intro a b; unfold pairCharge; split_ifs <;> norm_num
      exact this _ _
    refine (sum_le_sum hz).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have : ((univ.filter ((cexH T k).Adj v)).card : ℝ) ≤ 4 * T := by
      have := card_le_univ (univ.filter ((cexH T k).Adj v))
      simp only [Fintype.card_prod, Fintype.card_fin] at this
      exact_mod_cast this
    linarith
  have := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin 4 × Fin T))) => hv v)
  rw [← h2, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul] at this
  push_cast at this
  nlinarith

theorem cex_punc_edgeFinset (T k : ℕ) :
    (punc (cexH T k) univ ∅ ∅).edgeFinset = (cexH T k).edgeFinset := by
  ext e
  induction e using Sym2.ind with
  | _ a b => simp [punc_adj]

/-- All clauses of `PuncHyp` hold for the counterfamily. -/
theorem cex_puncHyp (T k : ℕ) (hT : 0 < T) (hk : k ≤ T) :
    PuncHyp (fun z : Fin 4 × Fin T => z.1) (cexG T) (cexH T k) univ ∅ ∅ 0 (1 / (4 * T))
      (k / (4 * T)) 0 1 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hcard : ((univ : Finset (Fin 4 × Fin T)).card : ℝ) = 4 * T := by
    simp [card_univ, Fintype.card_prod]
  have hcls : ∀ j : Fin 4, ((univ.filter fun z : Fin 4 × Fin T => z.1 = j).card : ℝ) = T := by
    intro j
    have : (univ.filter fun z : Fin 4 × Fin T => z.1 = j) = ({j} : Finset (Fin 4)) ×ˢ univ := by
      ext ⟨c, a⟩
      simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true]
    rw [this, card_product]; simp
  refine
    { hUW := empty_subset _
      hW := by rw [card_univ, Fintype.card_prod]; simp; exact hT
      hUh := by rw [hcard]; simp; positivity
      hq := by norm_num
      hq1 := le_rfl
      hκ := le_rfl
      hξ := by positivity
      hζ := by positivity
      hε := le_rfl
      hGF := fun u v h => h.2
      hHG := fun u v h => h.1
      hout := ?_
      hin := ?_
      htyp := ?_
      hdam := ?_
      hR0 := fun _ _ _ _ => notMem_empty _
      hR1 := fun a _ b _ _ _ _ l => by simp
      hR2 := fun a _ b hb => absurd hb (notMem_empty _) }
  · intro j
    rw [sdiff_empty, hcls, tOf, hcard]; simp
  · intro j; simp [uOf]
  · intro v _ j hj
    rw [hcard, show (1 : ℝ) / (4 * T) * (4 * T) = 1 by field_simp]
    have : (univ.filter fun z : Fin 4 × Fin T => z.1 = j ∧ ¬ (cexG T).Adj v z) ⊆ {v} := by
      intro z hz
      obtain ⟨hzj, hz⟩ := (mem_filter.mp hz).2
      rw [mem_singleton]
      by_contra hne
      exact hz ⟨fun h => hne h.symm, hzj ▸ hj⟩
    exact_mod_cast (card_le_card this).trans (card_singleton v).le
  · intro u _
    rw [hcard, show (k : ℝ) / (4 * T) * (4 * T) = k by field_simp]
    have : (univ.filter fun v : Fin 4 × Fin T => (cexG T).Adj u v ∧ ¬ (cexH T k).Adj u v) ⊆
        ({if u.1 = 0 then 2 else 0} : Finset (Fin 4)) ×ˢ
          (univ.filter fun j : Fin T => j.val < k) := by
      intro v hv
      obtain ⟨hG, hH⟩ := (mem_filter.mp hv).2
      have hd : cexDel T k u v := by
        by_contra hd; exact hH ⟨hG, hd⟩
      obtain ⟨hc, -, hv2⟩ := hd
      rw [mem_product, mem_singleton, mem_filter]
      refine ⟨?_, mem_univ _, hv2⟩
      rcases hc with ⟨h0, h2⟩ | ⟨h2, h0⟩
      · rw [if_pos h0, h2]
      · rw [if_neg (by rw [h2]; decide), h0]
    have hc := card_le_card this
    rw [card_product, card_singleton, one_mul, card_val_lt T k hk] at hc
    exact_mod_cast hc

/-- **The unconditioned robust weighting statement is false** for every damage bound `c₀ > 0`
and every weight cap `b` (proved).  The counterfamily is not integrally `F₁`-divisible, so this
refutes only the intermediate interface `F1DamageRobustWeighting`, not the actual level. -/
theorem not_F1DamageRobustWeighting (c₀ b : ℝ) (hc₀ : 0 < c₀) :
    ¬ F1DamageRobustWeighting c₀ b := by
  intro hrob
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 ≤ M ∧ 1 / c₀ ≤ M :=
    ⟨⌈1 / c₀⌉₊ + 1, by omega, by push_cast; linarith [Nat.le_ceil (1 / c₀)]⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.1
  set τ : ℝ := 1 / (64 * (M : ℝ) ^ 2) with hτ
  obtain ⟨σ, hσ, N, hN⟩ := hrob τ (by positivity)
  set m : ℕ := max (max (6 * M) N) ⌈1 / σ⌉₊ + 1 with hm
  have hm6 : 6 * M + 1 ≤ m := by omega
  have hmN : N ≤ m := by omega
  have hmσ : 1 / σ ≤ (m : ℝ) := by
    have : (⌈1 / σ⌉₊ : ℝ) ≤ m := by exact_mod_cast (by omega : ⌈1 / σ⌉₊ ≤ m)
    linarith [Nat.le_ceil (1 / σ)]
  set T : ℕ := M * m with hT
  have hm0 : 0 < m := by omega
  have hT0 : 0 < T := Nat.mul_pos (by omega) hm0
  have hkT : m ≤ T := Nat.le_mul_of_pos_left m (by omega)
  have hTr : (T : ℝ) = M * m := by rw [hT]; push_cast; ring
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hh := cex_puncHyp T m hT0 hkT
  have hcard : ((univ : Finset (Fin 4 × Fin T)).card) = 4 * T := by
    simp [card_univ, Fintype.card_prod]
  obtain ⟨φ, -, hload⟩ := hN (Fin 4 × Fin T) (fun z => z.1) (cexG T) (cexH T m) univ ∅ ∅ 0
    (1 / (4 * T)) (m / (4 * T)) 0 1 (by rw [hcard]; omega) hh
    (by
      rw [zero_add, add_zero, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hσ] at hmσ
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM.1
      have : (m : ℝ) ≤ 4 * T := by rw [hTr]; nlinarith
      nlinarith)
    (by
      rw [hTr, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hc₀] at hM
      nlinarith [hM.2])
  have hbal := F1BalanceGateStage228.graph_near_load_requires_balance (fun z : Fin 4 × Fin T => z.1)
    (punc (cexH T m) univ ∅ ∅) φ τ hload
  rw [cex_punc_edgeFinset, cex_balance T m hkT] at hbal
  have hmass := cex_mass T m
  have hτ0 : 0 ≤ τ := by positivity
  have h1 : |4 * (T : ℝ) - (m : ℝ) ^ 2| ≤ τ * (16 * (T : ℝ) ^ 2) :=
    hbal.trans (mul_le_mul_of_nonneg_left hmass hτ0)
  rw [hTr, hτ] at h1
  have h16 : 1 / (64 * (M : ℝ) ^ 2) * (16 * (M * m) ^ 2) = (m : ℝ) ^ 2 / 4 := by
    field_simp; ring
  rw [h16] at h1
  have hm6' : 6 * (M : ℝ) + 1 ≤ m := by exact_mod_cast hm6
  have := (abs_le.mp h1).1
  nlinarith

end NashWilliams18.SpreadF1
