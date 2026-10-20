/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.Vortex.Conversions
public import RequestProject.NW18.Sampling.MaxCut

@[expose] public section

/-!
# A uniform vortex for branch 12.4, selected in the original graph

`uniform_vortex124` (proved): for `0 < σ ≤ 1/8`, `0 < θ ≤ 1` and a level ratio
`0 < q ≤ 1/32` there are `M, N` (depending only on `σ, θ, q`) such that every graph `G` on
`n ≥ N` vertices with `δ(G) ≥ (3/4 - θ/2) n` that is not `σ`-extremal (the literal `IsExtremal`
of `NW18/Defs.lean`) has a nested chain `V = U₀ ⊇ U₁ ⊇ … ⊇ U_L` with
* `7q/8 |U_i| ≤ |U_{i+1}| ≤ 9q/8 |U_i|`, `|U_i| ≥ M` for `i < L`, `0 < |U_L| < M`;
* for EVERY level: `δ(G[U_i]) ≥ (3/4 - θ)|U_i|` and `G[U_i]` is not `σ/4`-extremal.

The parameters `θ, σ/4` are the SAME at every one of the `O(log n)` levels: the loss is paid
once.  The proof never applies a constant-size sampling lemma at linear size:
* the max-cut half uses `maxcut_sample` ONCE, on the original graph, with a fixed sample length
  `k`, to show that at most `η n^k` of the `k`-tuples have a large cut; the fraction of bad
  `k`-tuples is then inherited level by level by a second-moment (Chebyshev) argument with error
  `O(|W|^{-1/4})`, and converted back by the exact averaging identity `sum_cutQ_tup`;
* the degree and high-degree halves are inherited by Hoeffding with the same error;
* the errors are summed by the potential `K |W|^{-1/4}` (`exists_chain`).

This is a vortex in the ORIGINAL graph.  It does not account for edges used or protected by the
construction (the scale-local damage ledger), which remains to be combined with
`protected_nibble` at each level.
-/

namespace NashWilliams18.Vortex124

open Finset Filter
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma nnb_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (nnb G v univ : ℝ) = Fintype.card V - G.degree v := by
  have h := filter_adj_add_nnb G univ v
  have hdeg : (univ.filter (G.Adj v)).card = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  rw [hdeg, card_univ] at h
  have : (G.degree v : ℝ) + nnb G v univ = Fintype.card V := by exact_mod_cast h
  linarith

omit [DecidableEq V] in
lemma init_deg (G : SimpleGraph V) [DecidableRel G.Adj] {a : ℝ}
    (hδ : (3 / 4 - a) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) :
    ∀ v ∈ (univ : Finset V), (nnb G v univ : ℝ) ≤ (1 / 4 + a) * (univ : Finset V).card := by
  intro v _
  rw [nnb_univ, card_univ]
  have : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast G.minDegree_le_degree v
  linarith

omit [DecidableEq V] in
lemma init_hi (G : SimpleGraph V) [DecidableRel G.Adj] {σ : ℝ}
    (hi : ¬ ((1 - σ) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ))) :
    σ * ((univ : Finset V).card : ℝ) ≤ ((hiSet G univ σ).card : ℝ) := by
  push_neg at hi
  set A := univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)
  have hsub : univ.filter (fun v => ¬ ((G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)) ⊆
      hiSet G univ σ := by
    intro v hv
    rw [mem_filter] at hv
    unfold hiSet
    rw [mem_filter, nnb_univ, card_univ]
    refine ⟨mem_univ _, ?_⟩
    push_neg at hv
    linarith [hv.2]
  have hc := card_le_card hsub
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset V))
    (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)
  rw [card_univ] at hsplit ⊢
  have : (A.card : ℝ) + (univ.filter (fun v => ¬ ((G.degree v : ℝ) ≤
      (3 / 4 + σ) * Fintype.card V))).card = Fintype.card V := by exact_mod_cast hsplit
  have hc' : ((univ.filter (fun v => ¬ ((G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V))).card :
      ℝ) ≤ (hiSet G univ σ).card := by exact_mod_cast hc
  linarith

/-- The bad-tuple predicate: the `k`-sample admits a labelling of doubled cut `≥ θ k²`. -/
def badCut (G : SimpleGraph V) [DecidableRel G.Adj] (θ : ℝ) {k : ℕ} (s : Fin k → V) : Prop :=
  ∃ a : Fin k → Bool, θ * (k : ℝ) ^ 2 ≤ Sampling.cutQ G s a

noncomputable instance (G : SimpleGraph V) [DecidableRel G.Adj] (θ : ℝ) (k : ℕ) :
    DecidablePred (badCut G θ (k := k)) := Classical.decPred _

omit [Fintype V] [DecidableEq V] in
lemma card_filter_badCut (G : SimpleGraph V) [DecidableRel G.Adj] (θ : ℝ) (k : ℕ)
    (S : Finset (Fin k → V)) :
    (S.filter (badCut G θ (k := k))).card =
      (S.filter (fun s => ∃ a : Fin k → Bool, θ * (k : ℝ) ^ 2 ≤ Sampling.cutQ G s a)).card := by
  exact congrArg Finset.card (Finset.filter_congr (fun _ _ => Iff.rfl))

lemma final_ineq {σ ε₁ k : ℝ} (hσ0 : 0 < σ) (hε : ε₁ ≤ σ / 16) (h3 : 3 ≤ σ * (k - 1))
    (hk : 0 < k - 1) :
    ((1 - σ) / 2 + σ / 16 + (σ / 16 + ε₁)) * k < (1 - σ / 4) / 2 * (k - 1) := by
  have hk0 : 0 ≤ k := by linarith
  have h1 : ε₁ * k ≤ σ / 16 * k := mul_le_mul_of_nonneg_right hε hk0
  nlinarith

/-- **Initial tuple statistic** from the max-cut sampling theorem (used ONCE, on `G`). -/
lemma init_tup {η : ℝ} (hη : 0 < η) :
    ∃ m₀ N₀ : ℕ, ∀ k : ℕ, m₀ ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (σ : ℝ), σ ≤ 1 → N₀ ≤ Fintype.card V →
      0 < Fintype.card V →
      (∀ S : Finset V, (cutSize G S : ℝ) < (1 - σ) * (Fintype.card V : ℝ) ^ 2 / 4) →
      (((tup (univ : Finset V) k).filter (fun s => badCut G ((1 - σ) / 2 + η) s)).card : ℝ) ≤
        η * ((univ : Finset V).card : ℝ) ^ k := by
  classical
  obtain ⟨m₀, N₀, hmc⟩ := Sampling.maxcut_sample hη
  refine ⟨m₀, N₀, fun k hk V _ _ G _ σ hσ hN hn hcut => ?_⟩
  haveI : Nonempty V := Fintype.card_pos_iff.mp hn
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn0 : 0 < n := by rw [hn_def]; exact_mod_cast hn
  set K : ℝ := (1 - σ) * n ^ 2 / 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ 1 - σ := by linarith
    positivity
  have hX : ∀ X : V → Bool, (∑ a, ∑ b, if G.Adj a b ∧ X a ≠ X b then (1 : ℝ) else 0) ≤ K := by
    intro X
    have h2 := Sampling.doubled_eq (fun x y => G.Adj x y) (fun x y h => h.symm) X
    set T := univ.filter fun x => X x = true
    have h3 : (∑ x, ∑ y, if G.Adj x y ∧ X x = true ∧ X y = false then (1 : ℝ) else 0) =
        ∑ x, ∑ y, if G.Adj x y ∧ x ∈ T ∧ y ∉ T then (1 : ℝ) else 0 := by
      simp [T]
    have h4 := Sampling.pairs_le_cutSize G T
    have h5 := hcut T
    simp (config := { failIfUnchanged := false }) only at h2
    rw [hK]
    linarith
  have hp := hmc k hk V G K hN hK0 hX
  rw [Sampling.pProb_unif] at hp
  rw [div_le_iff₀ (by positivity), Fintype.card_fin] at hp
  have hKn : (k : ℝ) ^ 2 * (K / n ^ 2) + η * (k : ℝ) ^ 2 = ((1 - σ) / 2 + η) * (k : ℝ) ^ 2 := by
    rw [hK]; field_simp
  have hset : (tup (univ : Finset V) k).filter (fun s => badCut G ((1 - σ) / 2 + η) s) =
      univ.filter (fun ω : Fin k → V => ∃ a : Fin k → Bool,
        (k : ℝ) ^ 2 * (K / (Fintype.card V : ℝ) ^ 2) + η * (k : ℝ) ^ 2 ≤
          Sampling.cutQ G ω a) := by
    ext s
    rw [mem_filter, mem_filter]
    simp only [mem_tup, mem_univ, true_and]
    rw [show (∀ _ : Fin k, True) = True from
      propext ⟨fun _ => trivial, fun _ _ => trivial⟩, true_and]
    change (∃ a : Fin k → Bool,
      ((1 - σ) / 2 + η) * (k : ℝ) ^ 2 ≤ Sampling.cutQ G s a) ↔
      (∃ a : Fin k → Bool,
        (k : ℝ) ^ 2 * (K / (Fintype.card V : ℝ) ^ 2) + η * (k : ℝ) ^ 2 ≤
          Sampling.cutQ G s a)
    rw [← hn_def, hKn]
  rw [hset, card_univ]
  exact hp

omit [Fintype V] [DecidableEq V] in
/-- Degree into a child from a non-neighbour bound. -/
lemma deg_child_of_nnb (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V)
    {c θ : ℝ} (h : (nnb G v U : ℝ) ≤ (1 / 4 + c) * U.card) (hc : c ≤ θ) :
    (3 / 4 - θ) * (U.card : ℝ) ≤ ((U.filter (G.Adj v)).card : ℝ) := by
  have h2 : ((U.filter (G.Adj v)).card : ℝ) + nnb G v U = U.card := by
    exact_mod_cast filter_adj_add_nnb G U v
  have h3 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  nlinarith

/-- **The 12.4 vortex with parent-wide degree control** (proved).  Besides the level properties
of `uniform_vortex124`, every vertex `v` of a level `U i` (not only the vertices of the child)
has at least `(3/4 - θ)|U (i+1)|` neighbours in the child `U (i+1)`.  The per-level sampling
errors are the summable `O(|U|^{-1/4})` terms of the existing proof; the non-extremality case
split uses `¬ (A ∧ B)` exactly. -/
theorem uniform_vortex124_parent (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 8) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (q : ℝ≥0) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1 / 32) (Mlo : ℕ) :
    ∃ M N : ℕ, Mlo ≤ M ∧ 0 < M ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → (3 / 4 - θ / 2) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ¬ IsExtremal σ G →
      ∃ (L : ℕ) (U : ℕ → Finset V), U 0 = univ ∧
        (∀ i < L, U (i + 1) ⊆ U i ∧ M ≤ (U i).card ∧
          7 * q / 8 * ((U i).card : ℝ) ≤ (U (i + 1)).card ∧
          ((U (i + 1)).card : ℝ) ≤ 9 * q / 8 * (U i).card) ∧
        (U L).card < M ∧ 0 < (U L).card ∧
        (∀ i < L, ∀ v ∈ U i,
          (3 / 4 - θ) * ((U (i + 1)).card : ℝ) ≤ (((U (i + 1)).filter (G.Adj v)).card : ℝ)) ∧
        ∀ i ≤ L, (3 / 4 - θ) * ((U i).card : ℝ) ≤ ((G.induce (U i : Set V)).minDegree : ℝ) ∧
          ¬ IsExtremal (σ / 4) (G.induce (U i : Set V)) := by
  classical
  set η : ℝ := σ / 16 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨m₀, N₀, htup⟩ := init_tup hη0
  -- the sample length
  set k : ℕ := max (max m₀ 2) (⌈3 / σ⌉₊ + 2) with hk_def
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk1 : 1 ≤ k := by omega
  have hkm₀ : m₀ ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hkσ : 3 / σ + 2 ≤ (k : ℝ) := by
    have h1 : (⌈3 / σ⌉₊ + 2 : ℕ) ≤ k := le_max_right _ _
    have h2 : 3 / σ ≤ (⌈3 / σ⌉₊ : ℝ) := Nat.le_ceil _
    have : ((⌈3 / σ⌉₊ + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
    push_cast at this
    linarith
  set D : ℝ := 4 * k / q + 4 with hD
  have hD0 : 0 < D := by positivity
  set ε₁ : ℝ := min (θ / 2) (σ / 16) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by positivity)
  obtain ⟨M₀, hM₀⟩ := step_conds k hk1 q hq0
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp
    ((tendsto_sfv.eventually (gt_mem_nhds (show (0 : ℝ) < ε₁ / (2 * D) by positivity))).and
      (eventually_gt_atTop 0))
  -- `M`: large enough for the step conditions, and such that every level has size `≥ M₁`
  set M : ℕ := max (max (max M₀ M₁) (⌈8 * (M₁ : ℝ) / (7 * (q : ℝ))⌉₊)) Mlo + 1 with hM_def
  have hMM₀ : M₀ ≤ M := by omega
  have hMM₁ : M₁ ≤ M := by omega
  have hM0 : 0 < M := by omega
  have hMq : (M₁ : ℝ) ≤ 7 * q / 8 * M := by
    have h1 : 8 * (M₁ : ℝ) / (7 * (q : ℝ)) ≤ (⌈8 * (M₁ : ℝ) / (7 * (q : ℝ))⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈8 * (M₁ : ℝ) / (7 * (q : ℝ))⌉₊ : ℝ) ≤ M := by
      have : ⌈8 * (M₁ : ℝ) / (7 * (q : ℝ))⌉₊ ≤ M := by omega
      exact_mod_cast this
    have h3 : 8 * (M₁ : ℝ) / (7 * (q : ℝ)) ≤ (M : ℝ) := h1.trans h2
    rw [div_le_iff₀ (by positivity)] at h3
    linarith
  have hsfv_small : ∀ m : ℕ, M₁ ≤ m → 2 * D * sfv m ≤ ε₁ := by
    intro m hm
    have := (hM₁ m hm).1
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hKM : 2 * D * sfv M ≤ 1 := by
    have := hsfv_small M hMM₁
    have : ε₁ ≤ 1 := (min_le_right _ _).trans (by linarith)
    linarith
  refine ⟨M, max N₀ M, by omega, hM0, ?_⟩
  intro V _ _ G _ hN hδ hnx
  have hNM : M ≤ Fintype.card V := le_trans (le_max_right _ _) hN
  have hN₀ : N₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hN
  have hn : 0 < Fintype.card V := lt_of_lt_of_le hM0 hNM
  -- every level of a chain started at `univ` has size `≥ M₁`
  have hconv : ∀ (b₀ c₀ ρ₀ : ℝ), 0 ≤ b₀ → b₀ ≤ 1 / 4 → c₀ ≤ 1 → 0 ≤ ρ₀ →
      Inv124 G (badCut G ((1 - σ) / 2 + η) (k := k)) (θ / 2) b₀ c₀ ρ₀ univ 0 →
      ∃ (L : ℕ) (U : ℕ → Finset V), U 0 = univ ∧
        (∀ i < L, U (i + 1) ⊆ U i ∧ M ≤ (U i).card ∧
          7 * q / 8 * ((U i).card : ℝ) ≤ (U (i + 1)).card ∧
          ((U (i + 1)).card : ℝ) ≤ 9 * q / 8 * (U i).card) ∧
        (U L).card < M ∧ 0 < (U L).card ∧
        (∀ i < L, ∀ v ∈ U i,
          (nnb G v (U (i + 1)) : ℝ) ≤ (1 / 4 + (θ / 2 + ε₁)) * (U (i + 1)).card) ∧
        ∀ i ≤ L, M₁ ≤ (U i).card ∧
          Inv124 G (badCut G ((1 - σ) / 2 + η) (k := k)) (θ / 2) b₀ c₀ ρ₀ (U i) ε₁ := by
    intro b₀ c₀ ρ₀ hb₀ hb₁ hc₁ hρ₀ hinit
    have hinit' := Inv124.mono G _ hinit
      (show (0 : ℝ) ≤ 2 * D * sfv (univ : Finset V).card by
        have := sfv_pos (m := (univ : Finset V).card) (by rw [card_univ]; exact hn)
        positivity)
    obtain ⟨L, U, h0, hstep, hlast, hlast0, hall, hpar⟩ := exists_chain G hk1
      (badCut G ((1 - σ) / 2 + η) (k := k)) (by positivity) (by linarith) hb₀ hb₁ hc₁ hρ₀
      hq0 hq1 M (fun m hm => hM₀ m (le_trans hMM₀ hm)) hKM _ univ rfl
      (by rw [card_univ]; exact hn) hinit'
    have hsize : ∀ i ≤ L, M₁ ≤ (U i).card := by
      intro i hi
      rcases Nat.lt_or_ge i L with hiL | hiL
      · exact le_trans hMM₁ (hstep i hiL).2.1
      · obtain rfl : i = L := le_antisymm hi hiL
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; rw [h0, card_univ]; exact le_trans hMM₁ hNM
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          have hj := hstep j (by omega)
          have h1 : (M₁ : ℝ) ≤ (U (j + 1)).card := by
            have hMj : (M : ℝ) ≤ (U j).card := by exact_mod_cast hj.2.1
            have : 7 * q / 8 * (M : ℝ) ≤ 7 * q / 8 * (U j).card :=
              mul_le_mul_of_nonneg_left hMj (by positivity)
            linarith [hj.2.2.1]
          exact_mod_cast h1
    refine ⟨L, U, h0, hstep, hlast, hlast0, fun i hi v hv => ?_, fun i hi => ⟨hsize i hi, ?_⟩⟩
    · have h1 := hpar i hi v hv
      have h2 := hsfv_small _ (hsize (i + 1) (by omega))
      have h3 : (0 : ℝ) ≤ (U (i + 1)).card := Nat.cast_nonneg _
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ h3)
      linarith
    · exact Inv124.mono G _ (hall i hi) (hsfv_small _ (hsize i hi))
  -- the two cases of non-extremality
  have hdeg0 := init_deg G hδ
  unfold IsExtremal at hnx
  rw [not_and_or] at hnx
  rcases hnx with hi | hii
  · -- condition (i) fails: many high-degree vertices
    obtain ⟨L, U, h0, hstep, hlast, hlast0, hpar, hall⟩ := hconv σ σ 1 (by positivity) (by linarith)
      (by linarith) (by norm_num) ⟨by simpa using hdeg0, by simpa using init_hi G hi, by
        have := (card_filter_le (tup (univ : Finset V) k) (badCut G ((1 - σ) / 2 + η))).trans
          (card_tup univ k).le
        have : (((tup (univ : Finset V) k).filter (badCut G ((1 - σ) / 2 + η))).card : ℝ) ≤
            ((univ : Finset V).card : ℝ) ^ k := by exact_mod_cast this
        simpa using this⟩
    refine ⟨L, U, h0, hstep, hlast, hlast0, fun i hi v hv => ?_, fun i hi => ?_⟩
    · have hε₁θ : ε₁ ≤ θ / 2 := min_le_left _ _
      exact deg_child_of_nnb G _ v (hpar i hi v hv) (by linarith)
    obtain ⟨-, hd, hh, -⟩ := hall i hi
    have hU0 : 0 < (U i).card := by
      rcases Nat.lt_or_ge i L with hiL | hiL
      · exact lt_of_lt_of_le hM0 (hstep i hiL).2.1
      · obtain rfl : i = L := le_antisymm hi hiL; exact hlast0
    have hε₁θ : ε₁ ≤ θ / 2 := min_le_left _ _
    have hε₁σ : ε₁ ≤ σ / 16 := min_le_right _ _
    refine ⟨minDegree_induce_ge G (U i) (card_pos.mp hU0) (a := θ / 2 + ε₁) (fun v hv => ?_)
      |>.trans' ?_, ?_⟩
    · have := hd v hv; linarith
    · have : (0 : ℝ) ≤ (U i).card := Nat.cast_nonneg _
      nlinarith
    · intro hext
      exact not_ext_i_of_hiSet G (U i) hU0 (b := σ - ε₁) (c := σ - ε₁) (by linarith)
        (by linarith) hh hext.1
  · -- condition (ii) fails: all cuts are small
    push_neg at hii
    have ht := htup k hkm₀ V G σ (by linarith) hN₀ hn hii
    obtain ⟨L, U, h0, hstep, hlast, hlast0, hpar, hall⟩ := hconv 0 0 η le_rfl (by norm_num)
      (by norm_num) hη0.le ⟨by simpa using hdeg0, by
        simp only [sub_zero, zero_mul]; exact Nat.cast_nonneg _, by simpa using ht⟩
    refine ⟨L, U, h0, hstep, hlast, hlast0, fun i hi v hv => ?_, fun i hi => ?_⟩
    · have hε₁θ : ε₁ ≤ θ / 2 := min_le_left _ _
      exact deg_child_of_nnb G _ v (hpar i hi v hv) (by linarith)
    obtain ⟨-, hd, -, ht'⟩ := hall i hi
    have hU0 : 0 < (U i).card := by
      rcases Nat.lt_or_ge i L with hiL | hiL
      · exact lt_of_lt_of_le hM0 (hstep i hiL).2.1
      · obtain rfl : i = L := le_antisymm hi hiL; exact hlast0
    have hε₁θ : ε₁ ≤ θ / 2 := min_le_left _ _
    have hε₁σ : ε₁ ≤ σ / 16 := min_le_right _ _
    refine ⟨minDegree_induce_ge G (U i) (card_pos.mp hU0) (a := θ / 2 + ε₁) (fun v hv => ?_)
      |>.trans' ?_, ?_⟩
    · have := hd v hv; linarith
    · have : (0 : ℝ) ≤ (U i).card := Nat.cast_nonneg _
      nlinarith
    · intro hext
      have ht'' : (((tup (U i) k).filter (fun s => ∃ a : Fin k → Bool,
          ((1 - σ) / 2 + η) * (k : ℝ) ^ 2 ≤ Sampling.cutQ G s a)).card : ℝ) ≤
          (η + ε₁) * ((U i).card : ℝ) ^ k := by
        rw [← card_filter_badCut]
        exact ht'
      refine not_ext_ii_of_tup G (U i) hU0 hk2 (θ := (1 - σ) / 2 + η) (ρ := η + ε₁)
        (β := σ / 4) (by linarith) ht'' ?_ hext.2
      -- `((1-σ)/2 + 2η + ε₁) k/(k-1) < (1 - σ/4)/2`
      have hk3 : (3 : ℝ) / σ + 1 ≤ k - 1 := by linarith only [hkσ]
      have hkpos : (0 : ℝ) < k - 1 := by
        have : 0 < 3 / σ := by positivity
        linarith only [this, hk3]
      rw [div_lt_iff₀ hkpos]
      have h3σ : 3 ≤ σ * (k - 1) := by
        have := mul_le_mul_of_nonneg_left hk3 hσ0.le
        rw [mul_add, mul_div_cancel₀ _ hσ0.ne'] at this
        linarith only [this, hσ0, mul_one σ]
      have hfin := final_ineq (k := (k : ℝ)) hσ0 hε₁σ h3σ hkpos
      rw [hη]
      linarith only [hfin]

/-- **Uniform vortex for 12.4 in the original graph** (proved; the earlier statement, a
corollary of `uniform_vortex124_parent`). -/
theorem uniform_vortex124 (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 8) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (q : ℝ≥0) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1 / 32) :
    ∃ M N : ℕ, 0 < M ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → (3 / 4 - θ / 2) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ¬ IsExtremal σ G →
      ∃ (L : ℕ) (U : ℕ → Finset V), U 0 = univ ∧
        (∀ i < L, U (i + 1) ⊆ U i ∧ M ≤ (U i).card ∧
          7 * q / 8 * ((U i).card : ℝ) ≤ (U (i + 1)).card ∧
          ((U (i + 1)).card : ℝ) ≤ 9 * q / 8 * (U i).card) ∧
        (U L).card < M ∧ 0 < (U L).card ∧
        ∀ i ≤ L, (3 / 4 - θ) * ((U i).card : ℝ) ≤ ((G.induce (U i : Set V)).minDegree : ℝ) ∧
          ¬ IsExtremal (σ / 4) (G.induce (U i : Set V)) := by
  obtain ⟨M, N, -, hM, h⟩ := uniform_vortex124_parent σ hσ0 hσ1 θ hθ0 hθ1 q hq0 hq1 0
  refine ⟨M, N, hM, fun V _ _ G _ hN hδ hnx => ?_⟩
  obtain ⟨L, U, h0, hstep, hlast, hlast0, -, hall⟩ := h V G hN hδ hnx
  exact ⟨L, U, h0, hstep, hlast, hlast0, hall⟩

end NashWilliams18.Vortex124
