/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.PeelingLevelF1

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: one physical peeling level on the actual idealized hosts (produced)

This file applies `CrossingCover.F1_peeling_level` to the hosts of `Theorem147F1Statement`
(`IsIntDiv p F1`, `IsIdealizedT F1 ε G p`), discharging every hypothesis from the definition of an
idealized host, with explicit constants: `ε ≤ 1/1000`, `|X| ≤ n/1000`, `n ≥ 10000`, density defect
`γ₀ = ⌊n/1000⌋`.

**Statement.**  For every set `X` of at most `n/1000` vertices, every edge of `G` meeting `X` is
covered by an `F₁`-decomposable `C ⊆ E(G)`, and the edges of `C` with both ends outside `X` form a
graph of maximum degree `≤ |X|`.

**What this is and is not.**  It is a *producer* on the real hosts (no decomposition supplied).
It is ONE level of a cover-down; it does not reduce the leftover to a bounded core (the leftover
lives on `V \ X`, which still has `≥ (1 - 1/1000) n` vertices).  See `NW18_BRANCH_LEDGER.md`
§0quater for the precise remaining obligation.
-/

namespace NashWilliams18.CrossingCover

open Finset PartitionedTriangleAbsorption LinkPairing
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The partners of `c` are `F₁`-allowed with `c`, and so is `c` itself. -/
lemma allowed_partners : ∀ c : Fin 4, AllowedT F1 c c ∧ AllowedT F1 c (partner1 c) ∧
    AllowedT F1 c (partner2 c) := by
  decide

omit [DecidableEq V] in
/-- Class sizes add up to `n`. -/
lemma sum_clsT (p : V → Fin 4) :
    ((clsT p 0).card + (clsT p 1).card + (clsT p 2).card + (clsT p 3).card : ℕ) =
      Fintype.card V := by
  have h := card_eq_sum_card_fiberwise (f := p) (s := (univ : Finset V))
    (t := (univ : Finset (Fin 4))) (fun _ _ => mem_coe.mpr (mem_univ _))
  rw [Fin.sum_univ_four, card_univ] at h
  exact h.symm

/-- Neighbours of `x` of class `j` outside `X`: at least `|V_j| - (non-neighbours) - |X|`. -/
lemma nbrCount_ge (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (x : V) (j : Fin 4) :
    (clsT p j).card ≤ nbrCount p G (univ \ X) x j +
      (univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card + X.card := by
  refine (card_le_card (t := ((univ \ X).filter fun u => G.Adj x u ∧ p u = j) ∪
    (univ.filter fun y => p y = j ∧ ¬ G.Adj x y) ∪ X) ?_).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  intro v hv
  have hpv : p v = j := (mem_filter.mp hv).2
  by_cases hvX : v ∈ X
  · exact mem_union_right _ hvX
  · by_cases hadj : G.Adj x v
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _, hvX⟩, hadj, hpv⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hpv, hadj⟩))

/-- Common neighbours of `x, x'` of class `k` outside `X`. -/
lemma common_ge (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (x x' : V) (k : Fin 4) :
    (clsT p k).card ≤ ((univ \ X).filter fun u => G.Adj x u ∧ G.Adj x' u ∧ p u = k).card +
      (univ.filter fun y => p y = k ∧ ¬ G.Adj x y).card +
      (univ.filter fun y => p y = k ∧ ¬ G.Adj x' y).card + X.card := by
  refine (card_le_card (t := ((univ \ X).filter fun u => G.Adj x u ∧ G.Adj x' u ∧ p u = k) ∪
    (univ.filter fun y => p y = k ∧ ¬ G.Adj x y) ∪
    (univ.filter fun y => p y = k ∧ ¬ G.Adj x' y) ∪ X) ?_).trans ?_
  · intro v hv
    have hpv : p v = k := (mem_filter.mp hv).2
    simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and]
    by_cases hvX : v ∈ X
    · exact Or.inr hvX
    · by_cases h1 : G.Adj x v
      · by_cases h2 : G.Adj x' v
        · exact Or.inl (Or.inl (Or.inl ⟨hvX, h1, h2, hpv⟩))
        · exact Or.inl (Or.inr ⟨hpv, h2⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨hpv, h1⟩))
  · refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact card_union_le _ _

/-- **One physical peeling level on idealized `F₁`-hosts** (produced).  For every `n ≥ 10000`,
every integrally `F₁`-divisible idealized `F₁`-host with `ε ≤ 1/1000` and every vertex set `X`
with `|X| ≤ n/1000`, there is an `F₁`-decomposable `C ⊆ E(G)` containing every edge that meets
`X`, whose edges outside `X` form a graph of maximum degree `≤ |X|`. -/
theorem F1_ideal_peeling_level (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 10000 ≤ Fintype.card V) (ε : ℝ) (hε : ε ≤ 1 / 1000)
    (hint : IsIntDiv p F1 G.edgeFinset) (hid : IsIdealizedT F1 ε G p)
    (X : Finset V) (hX : (X.card : ℝ) ≤ Fintype.card V / 1000) :
    ∃ C ⊆ G.edgeFinset, HasDecomp p F1 C ∧
      (∀ e ∈ G.edgeFinset, e ∉ C → ∀ v ∈ e, v ∉ X) ∧
      ∀ v, ((C.filter fun e => ∀ w ∈ e, w ∉ X).filter fun e => v ∈ e).card ≤ X.card := by
  classical
  set n := Fintype.card V with hndef
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  set γ₀ : ℕ := ⌊(n : ℝ) / 1000⌋₊ with hγdef
  have hγ : (γ₀ : ℝ) ≤ n / 1000 := Nat.floor_le (by positivity)
  set m := X.card with hmdef
  -- non-neighbour bound
  have hmiss : ∀ v j, AllowedT F1 (p v) j →
      ((univ.filter fun y => p y = j ∧ ¬ G.Adj v y).card : ℝ) ≤ ε * n := by
    intro v j hj
    have h1 := hid.2.2 v j hj
    have h2 := card_nonNbr_add_degT G p v j
    have h2' : ((univ.filter fun y => p y = j ∧ ¬ G.Adj v y).card : ℝ) +
        (degT G p v j : ℝ) = ((clsT p j).card : ℝ) := by exact_mod_cast h2
    linarith
  have hcls : ∀ j, (1 - ε) * n / 4 ≤ ((clsT p j).card : ℝ) := fun j => by
    have := hid.1 j; push_cast at this; linarith
  have hsum : ((clsT p 0).card + (clsT p 1).card + (clsT p 2).card + (clsT p 3).card : ℝ) =
      n := by exact_mod_cast sum_clsT p
  have hclsup : ∀ j, ((clsT p j).card : ℝ) ≤ n - 3 * ((1 - ε) * n / 4) := by
    intro j
    have h0 := hcls 0; have h1 := hcls 1; have h2 := hcls 2; have h3 := hcls 3
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  have hεn : ε * n ≤ n / 1000 := by nlinarith
  -- the peeling level
  obtain ⟨C, hCG, hCdec, hCcov, hCdeg⟩ := F1_peeling_level p G hid.2.1 hint X (univ \ X)
    disjoint_sdiff (fun u _ _ => by
      by_cases hu : u ∈ X
      · exact Or.inl hu
      · exact Or.inr (mem_sdiff.mpr ⟨mem_univ _, hu⟩)) γ₀
    (by
      intro x _ x' _ hxx'
      obtain ⟨k, hk⟩ := hid.2.1 x x' hxx'
      refine ⟨k, hk, ?_⟩
      have h1 := hmiss x k (allowedT_of_mem hk)
      have h2 := hmiss x' k (allowedT_of_mem' hk)
      have hc := common_ge p G X x x' k
      have hcR : ((clsT p k).card : ℝ) ≤
          (((univ \ X).filter fun u => G.Adj x u ∧ G.Adj x' u ∧ p u = k).card : ℝ) +
          ((univ.filter fun y => p y = k ∧ ¬ G.Adj x y).card : ℝ) +
          ((univ.filter fun y => p y = k ∧ ¬ G.Adj x' y).card : ℝ) + (m : ℝ) := by
        exact_mod_cast hc
      have := hcls k
      have goal : ((2 * m + 1 : ℕ) : ℝ) ≤
          (((univ \ X).filter fun u => G.Adj x u ∧ G.Adj x' u ∧ p u = k).card : ℝ) := by
        push_cast; nlinarith
      exact_mod_cast goal)
    (by
      intro y _ j hj
      refine le_trans (card_le_card (t := univ.filter fun z => p z = j ∧ ¬ G.Adj y z)
        (fun z hz => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩)) ?_
      apply Nat.le_floor
      exact (hmiss y j hj).trans hεn)
    (by
      intro x _
      obtain ⟨a0, a1, a2⟩ := allowed_partners (p x)
      have lb : ∀ j, AllowedT F1 (p x) j →
          (1 - ε) * n / 4 - ε * n - m ≤ (nbrCount p G (univ \ X) x j : ℝ) := by
        intro j hj
        have h := nbrCount_ge p G X x j
        have hR : ((clsT p j).card : ℝ) ≤ (nbrCount p G (univ \ X) x j : ℝ) +
            ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) + (m : ℝ) := by
          exact_mod_cast h
        have := hmiss x j hj
        have := hcls j
        linarith
      have ub : (nbrCount p G (univ \ X) x (p x) : ℝ) ≤ n - 3 * ((1 - ε) * n / 4) := by
        refine le_trans ?_ (hclsup (p x))
        have hsub : ((univ \ X).filter fun u => G.Adj x u ∧ p u = p x) ⊆ clsT p (p x) :=
          fun u hu => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hu).2.2⟩
        exact_mod_cast card_le_card hsub
      have l0 := lb _ a0
      have l1 := lb _ a1
      have l2 := lb _ a2
      have hm : (m : ℝ) ≤ n / 1000 := hX
      refine ⟨?_, ?_, ?_, ?_⟩
      · have : ((4 * (γ₀ + m) + 1 + m : ℕ) : ℝ) ≤ (nbrCount p G (univ \ X) x (p x) : ℝ) := by
          push_cast; nlinarith
        exact_mod_cast this
      · have : ((6 * (γ₀ + m) + 1 + m : ℕ) : ℝ) ≤
            (nbrCount p G (univ \ X) x (partner1 (p x)) : ℝ) := by
          push_cast; nlinarith
        exact_mod_cast this
      · have : ((6 * (γ₀ + m) + 1 + m : ℕ) : ℝ) ≤
            (nbrCount p G (univ \ X) x (partner2 (p x)) : ℝ) := by
          push_cast; nlinarith
        exact_mod_cast this
      · have : ((nbrCount p G (univ \ X) x (p x) + 8 * (γ₀ + m) + 1 + m : ℕ) : ℝ) ≤
            ((nbrCount p G (univ \ X) x (partner1 (p x)) +
              nbrCount p G (univ \ X) x (partner2 (p x)) : ℕ) : ℝ) := by
          push_cast; nlinarith
        exact_mod_cast this)
  refine ⟨C, hCG, hCdec, fun e he heC v hv => (mem_sdiff.mp (hCcov e he heC v hv)).2, ?_⟩
  intro v
  refine le_trans (card_le_card fun e he => ?_) (hCdeg v)
  obtain ⟨he, hve⟩ := mem_filter.mp he
  obtain ⟨heC, hU⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨heC, fun w hw => mem_sdiff.mpr ⟨mem_univ _, hU w hw⟩⟩,
    hve⟩

end NashWilliams18.CrossingCover
