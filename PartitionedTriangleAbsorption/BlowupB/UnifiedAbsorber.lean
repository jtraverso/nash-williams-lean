/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LinearExtras

/-! # BlowupB.UnifiedAbsorber — the terminal absorber for every covered family

**Theorem** (`terminal_absorber_covered`). Let `F` be a family of triangle types which is
linear or satisfies `ThreeStepLinks`. For every `K`, `γ > 0`, `η > 0` there are `N` and `δ > 0`
such that: if `G` lies inside the `F`-blowup of `p` on `n ≥ N` vertices, every vertex misses at
most `d ≤ δ n` allowed neighbours, every class has at least `γ n` vertices, `B` is an edge set of
maximum degree at most `δ n` and `X ⊆ E(G) \ B` has at most `K` edges, then there is
`C ⊆ E(G) \ (B ∪ X)` of maximum degree at most `η n`, decomposable, such that `C ∪ L` decomposes
for every integrally divisible `L ⊆ X`.

The two cases use different constructions: the tree's transformer chain
(`terminal_absorber_nearly`, via `BoundedCoreStage104`) for `ThreeStepLinks`, the windmill
absorbers of `LinearAbsorber` for linear families (`not_threeStepLinks_of_linear`: the two
classes are disjoint).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem DegBounded.mono' {E : Finset (Sym2 V)} {x y : ℝ} (h : DegBounded E x) (hxy : x ≤ y) :
    DegBounded E y := fun v => (h v).trans hxy

/-- The graph `G` with the edges of `B` removed. -/
def delEdges (G : SimpleGraph V) (B : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(u, v) ∉ B
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun v h => G.irrefl h.1⟩

instance instDecRelDelEdges (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) :
    DecidableRel (delEdges G B).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ s(u, v) ∉ B))

theorem delEdges_edgeFinset_sub (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) :
    (delEdges G B).edgeFinset ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact he.1

theorem disjoint_delEdges (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) :
    Disjoint (delEdges G B).edgeFinset B := by
  rw [disjoint_left]
  intro e he heB
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset] at he
    exact he.2 heB

theorem missDeg_delEdges_le {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) (v : V) :
    missDeg p F (delEdges G B) v ≤ missDeg p F G v + (B.filter fun e => v ∈ e).card := by
  unfold missDeg missSet
  calc (univ.filter fun r => v ≠ r ∧ AllowedPair F (p v) (p r) ∧ ¬ (delEdges G B).Adj v r).card
      ≤ ((univ.filter fun r => v ≠ r ∧ AllowedPair F (p v) (p r) ∧ ¬ G.Adj v r) ∪
          (univ.filter fun r => s(v, r) ∈ B)).card := by
        refine card_le_card fun r hr => ?_
        simp only [mem_filter, mem_union, mem_univ, true_and] at hr ⊢
        simp only [delEdges, not_and, not_not] at hr
        by_cases h : G.Adj v r
        · exact Or.inr (hr.2.2 h)
        · exact Or.inl ⟨hr.1, hr.2.1, h⟩
    _ ≤ _ + _ := card_union_le _ _
    _ ≤ _ := by
        refine add_le_add le_rfl (card_le_card_of_injOn (fun r => s(v, r)) ?_ ?_)
        · intro r hr
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hr
          simp only [coe_filter, Set.mem_setOf_eq]
          exact ⟨hr, Sym2.mem_mk_left v r⟩
        · intro a _ b _ h
          exact Sym2.congr_right.mp h

theorem card_filter_mem_le_of_verts {A : Finset (Sym2 V)} {W : Finset V}
    (h : ∀ e ∈ A, ∀ v ∈ e, v ∈ W) (v : V) : (A.filter fun e => v ∈ e).card ≤ W.card := by
  refine (card_le_card ?_).trans (card_image_le (s := W) (f := fun w => s(v, w)))
  intro e he
  obtain ⟨heA, hve⟩ := mem_filter.mp he
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
  exact mem_image.mpr ⟨w, h _ heA w (Sym2.mem_mk_right v w), rfl⟩

end Helpers

/-- **Terminal absorber for linear families or families with three-step links.** -/
theorem terminal_absorber_covered {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hcov : IsLinearFam F ∨ ThreeStepLinks F) (K : ℕ)
    (gamma eta : ℝ) (hg : 0 < gamma) (he : 0 < eta) :
    ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V →
      (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
      (d : ℝ) ≤ δ * Fintype.card V →
      (∀ i, gamma * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
      ∀ B X : Finset (Sym2 V), DegBounded B (δ * Fintype.card V) →
        X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
        ∃ C ⊆ G.edgeFinset, Disjoint C (B ∪ X) ∧ HasDecomp p F C ∧
          DegBounded C (eta * Fintype.card V) ∧
          ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (C ∪ L) := by
  rcases hcov with hL | hF
  · -- linear families: the windmill absorbers, in `G` minus `B`
    set M : ℕ := 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) with hM
    set δ : ℝ := gamma / (8 * (4 * K + 2)) with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨max (⌈4 * (M : ℝ) / gamma⌉₊ + 1) (⌈(2 * K + 4 * K * 2 ^ K : ℝ) / eta⌉₊ + 1), δ,
      hδpos, ?_⟩
    intro V _ _ G _ p d hN hsub hmiss hd hcls B X hB hXG hXB hK
    set n : ℕ := Fintype.card V with hn
    have hn1 : 4 * (M : ℝ) / gamma < n := by
      have := (le_max_left _ _).trans hN
      have h2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast h2)
    have hn2 : (2 * K + 4 * K * 2 ^ K : ℝ) / eta < n := by
      have := (le_max_right _ _).trans hN
      have h2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast h2)
    by_cases ht : 0 < t
    · obtain ⟨O⟩ := exists_orientation F hcard ht
      set d' : ℕ := d + ⌊δ * n⌋₊ with hd'
      have hmiss' : ∀ v, missDeg p F (delEdges G B) v ≤ d' := by
        intro v
        have h1 := missDeg_delEdges_le p F G B v
        have h2 : (B.filter fun e => v ∈ e).card ≤ ⌊δ * n⌋₊ :=
          Nat.le_floor (hB v)
        have := hmiss v
        omega
      have hsub' : ∀ u v, (delEdges G B).Adj u v → AllowedPair F (p u) (p v) := fun u v h => hsub u v h.1
      have hXG' : X ⊆ (delEdges G B).edgeFinset := by
        intro e heX
        have heG := hXG heX
        induction e using Sym2.ind with
        | _ u v =>
          rw [SimpleGraph.mem_edgeFinset] at heG ⊢
          exact ⟨heG, fun h => disjoint_left.mp hXB heX h⟩
      have hclsN : ∀ c, (∅ : Finset V).card + 4 * K * 2 ^ K + 2 * K + 6 * K +
          (4 * K + 2) * (d' + 1) < (univ.filter fun v => p v = c).card := by
        intro c
        have hc := hcls c
        have hfl : (⌊δ * n⌋₊ : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
        have hd'R : ((d' : ℕ) : ℝ) ≤ 2 * (δ * n) := by
          rw [hd']; push_cast; linarith
        have h4 : ((4 * K + 2 : ℕ) : ℝ) * ((d' : ℝ) + 1) ≤ gamma * n / 4 + (4 * K + 2) := by
          have h6 : (0 : ℝ) ≤ ((4 * K + 2 : ℕ) : ℝ) := by positivity
          have h7 := mul_le_mul_of_nonneg_left (show (d' : ℝ) + 1 ≤ 2 * (δ * n) + 1 by linarith) h6
          have h5 : ((4 * K + 2 : ℕ) : ℝ) * (2 * (δ * n) + 1) = gamma * n / 4 + (4 * K + 2) := by
            rw [hδ]; push_cast; field_simp; ring
          linarith
        have hMR : (M : ℝ) * 4 < gamma * n := by
          rw [div_lt_iff₀ hg] at hn1; linarith
        have key : ((∅ : Finset V).card + 4 * K * 2 ^ K + 2 * K + 6 * K +
            (4 * K + 2) * (d' + 1) : ℕ) < (gamma * n : ℝ) := by
          push_cast
          simp only [card_empty, Nat.cast_zero, zero_add]
          have hM' : (M : ℝ) = 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) := by
            rw [hM]; push_cast; ring
          push_cast at h4
          nlinarith
        exact_mod_cast key.trans_le hc
      obtain ⟨A, hAG', hAX, hAdec, hAall, U, hUc, _, hAv⟩ :=
        linear_terminal_absorber hL O hsub' hmiss' X ∅ hXG' hK hclsN
      refine ⟨A, hAG'.trans (delEdges_edgeFinset_sub G B), ?_, hAdec, ?_, hAall⟩
      · rw [disjoint_union_right]
        exact ⟨disjoint_of_subset_left hAG' (disjoint_delEdges G B), hAX⟩
      · intro v
        have h1 := card_filter_mem_le_of_verts (W := vertsOf X ∪ U)
          (fun e he w hw => (hAv e he w hw).elim (mem_union_left _) (mem_union_right _)) v
        have h2 := card_union_le (vertsOf X) U
        have h3 : (vertsOf X).card ≤ 2 * K := card_vertsOf_le.trans (by omega)
        have h4 : ((A.filter fun e => v ∈ e).card : ℝ) ≤ 2 * K + 4 * K * 2 ^ K := by
          exact_mod_cast (h1.trans h2).trans (by omega)
        rw [div_lt_iff₀ he] at hn2
        linarith
    · -- no classes: the host is empty
      have hV : IsEmpty V := ⟨fun v => absurd (p v).2 (by omega)⟩
      refine ⟨∅, empty_subset _, disjoint_empty_left _, hasDecomp_empty', fun v => ?_, ?_⟩
      · simp only [filter_empty, card_empty, Nat.cast_zero]; positivity
      · intro L _ _
        rw [Finset.eq_empty_of_isEmpty L, empty_union]
        exact hasDecomp_empty'
  · -- three-step links: the tree's chain
    obtain ⟨N₁, h₁⟩ := terminal_absorber_nearly F hcard hF K (gamma / 2) eta (by positivity) he
    refine ⟨max N₁ (⌈16 / gamma⌉₊ + 1), gamma / 16, by positivity, ?_⟩
    intro V _ _ G _ p d hN hsub hmiss hd hcls B X hB hXG hXB hK
    have hnN : N₁ ≤ Fintype.card V := (le_max_left _ _).trans hN
    have hn16 : 16 / gamma < Fintype.card V := by
      have := (le_max_right _ _).trans hN
      have h2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast h2)
    have hn16' : 16 < gamma * Fintype.card V := by
      rw [div_lt_iff₀ hg] at hn16; linarith
    refine h₁ G p d hnN hmiss (fun i => ?_) B X (DegBounded.mono' hB ?_) hXG hXB hK
    · have := hcls i
      nlinarith
    · have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      nlinarith

end PartitionedTriangleAbsorption.BlowupB
