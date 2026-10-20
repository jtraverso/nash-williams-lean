/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TeoremaBFamilies
public import PartitionedTriangleAbsorption.BlowupB.KeevashPaddedMain

/-! # BlowupB.Theorem147Bridge — the F₁/F₂ entries of Nash–Williams 1.8 from the Keevash interface

`RequestProject/NW18/Case126/Ideal.lean` (NW return `f7ca1b1f`) defines the idealized hosts
`IsIdealizedT F ε G p`. That project is not compiled in this tree, so its three auxiliary
notions are copied **verbatim** here (`clsNW`, `degNW`, `AllowedNW`, `IsIdealizedNW`); once the
project is integrated, `IsIdealizedT` unfolds to `IsIdealizedNW` and the link is `exact`.

**`theorem147_of_keevash`**: for `F = F₁` or `F = F₂`, `KeevashTypedSpec F` gives the statement
of `Theorem147F1Statement` / `Theorem147F2Statement`:

  ∃ ε > 0, ∃ n₀, every `G` on `n ≥ n₀` vertices with `IsIntDiv p F G.edgeFinset` and
  `IsIdealizedNW F ε G p` has `HasDecomp p F G.edgeFinset`.

Proof: an idealized host is ε-balanced (classes in `[(1 − ε) n/4, (1/4 + 3ε/4) n]`), uses only
allowed pairs and misses at most `4 ε n` allowed neighbours per vertex; apply `teoremaB_F123`
with `ε = min η (δ/4)`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- `V_i` (copy of `NashWilliams18.clsT`). -/
def clsNW (p : V → Fin t) (i : Fin t) : Finset V := univ.filter (fun v => p v = i)

/-- `|N(v) ∩ V_i|` (copy of `NashWilliams18.degT`). -/
def degNW (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (v : V) (i : Fin t) : ℕ :=
  (univ.filter (fun w => G.Adj v w ∧ p w = i)).card

/-- Copy of `NashWilliams18.AllowedT`. -/
def AllowedNW (F : Finset (Multiset (Fin t))) (i j : Fin t) : Prop :=
  ∃ l, ({i, j, l} : Multiset (Fin t)) ∈ F

/-- Copy of `NashWilliams18.IsIdealizedT`. -/
def IsIdealizedNW (F : Finset (Multiset (Fin t))) (ε : ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin t) : Prop :=
  (∀ i, (1 - ε) * Fintype.card V / t ≤ ((clsNW p i).card : ℝ)) ∧
  (∀ u v, G.Adj u v → AllowedNW F (p u) (p v)) ∧
  (∀ v j, AllowedNW F (p v) j → ((clsNW p j).card : ℝ) - ε * Fintype.card V ≤ (degNW G p v j : ℝ))

theorem allowedPair_of_allowedNW {F : Finset (Multiset (Fin t))}
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) {i j : Fin t} (h : AllowedNW F i j) :
    AllowedPair F i j := by
  obtain ⟨l, hl⟩ := h
  refine ⟨_, hl, hcard _ hl, ?_⟩
  simp only [Multiset.insert_eq_cons]
  exact Multiset.cons_le_cons i (Multiset.singleton_le.mpr (by simp))

theorem allowedNW_of_allowedPair {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : AllowedPair F i j) : AllowedNW F i j := by
  obtain ⟨c, hc⟩ := exists_third_cons h
  exact ⟨c, by rw [triRot3]; exact hc⟩

open Classical in
/-- Allowed non-neighbours of a vertex inside one class `V_j`. -/
theorem miss_class_le {F : Finset (Multiset (Fin t))} {ε : ℝ} (hε : 0 ≤ ε)
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin t} (hI : IsIdealizedNW F ε G p)
    (v : V) (j : Fin t) :
    ((univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j).card : ℝ) ≤
      ε * Fintype.card V := by
  by_cases hal : AllowedNW F (p v) j
  · have hdeg := hI.2.2 v j hal
    have hdisj : Disjoint (univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j)
        (univ.filter fun w => G.Adj v w ∧ p w = j) := by
      rw [disjoint_filter]; intro r _ h1 h2; exact h1.2.1 h2.1
    have hu : (univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j) ∪
        (univ.filter fun w => G.Adj v w ∧ p w = j) ⊆ clsNW p j := by
      intro r hr
      rcases mem_union.mp hr with h | h
      · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.1⟩
      · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.2⟩
    have hc := card_le_card hu
    rw [card_union_of_disjoint hdisj] at hc
    have hR : ((univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j).card : ℝ) +
        (degNW G p v j : ℝ) ≤ (clsNW p j).card := by
      unfold degNW; exact_mod_cast hc
    linarith
  · have h0 : (univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j) = ∅ := by
      rw [filter_eq_empty_iff]; intro r _ h; exact hal h.2.2
    rw [h0, card_empty, Nat.cast_zero]
    exact mul_nonneg hε (Nat.cast_nonneg _)

/-- Allowed non-neighbours in an idealized host: at most `t ε n`. -/
theorem missDeg_le_of_idealized {F : Finset (Multiset (Fin t))} {ε : ℝ} (hε : 0 ≤ ε)
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin t} (hI : IsIdealizedNW F ε G p)
    (v : V) : (missDeg p F G v : ℝ) ≤ t * (ε * Fintype.card V) := by
  classical
  have hsub : missSet p F G v ⊆ univ.biUnion fun j : Fin t =>
      (univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j) := by
    intro r hr
    obtain ⟨-, hal, hadj⟩ := (mem_filter.mp hr).2
    exact mem_biUnion.mpr ⟨p r, mem_univ _, mem_filter.mpr ⟨mem_univ _, rfl, hadj,
      allowedNW_of_allowedPair hal⟩⟩
  have h1 : (missDeg p F G v : ℝ) ≤ ∑ j : Fin t,
      ((univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧ AllowedNW F (p v) j).card : ℝ) := by
    unfold missDeg
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  refine h1.trans ?_
  calc ∑ j : Fin t, ((univ.filter fun r => p r = j ∧ ¬ G.Adj v r ∧
        AllowedNW F (p v) j).card : ℝ)
      ≤ ∑ _j : Fin t, ε * Fintype.card V := sum_le_sum fun j _ => miss_class_le hε hI v j
    _ = t * (ε * Fintype.card V) := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sum_clsNW (p : V → Fin t) : ∑ i, ((clsNW p i).card : ℝ) = Fintype.card V := by
  have h := card_eq_sum_card_fiberwise (f := p) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  rw [card_univ] at h
  unfold clsNW
  exact_mod_cast h.symm

/-- **The F₁/F₂ entries of NW 1.8 from `KeevashTypedSpec`.** The conclusion is
`Theorem147F1Statement` / `Theorem147F2Statement` with `IsIdealizedT` unfolded. -/
theorem theorem147_of_keevash {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2)
    (hK : KeevashTypedSpec F) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      IsIntDiv p F G.edgeFinset → IsIdealizedNW F ε G p → HasDecomp p F G.edgeFinset := by
  have hcard : ∀ τ ∈ F, Multiset.card τ = 3 := by
    rcases hF with rfl | rfl
    · unfold F1; decide
    · unfold F2; decide
  obtain ⟨η, hη, N, δ, hδ, hB⟩ := teoremaB_F123 (hF.imp_right Or.inl) hK
  refine ⟨min η (δ / 4), lt_min hη (by linarith), N, ?_⟩
  intro V _ _ p G _ hN hdiv hI
  set ε := min η (δ / 4) with hεdef
  have hε0 : 0 ≤ ε := le_of_lt (lt_min hη (by linarith))
  have hεη : ε ≤ η := min_le_left _ _
  have hεδ : ε ≤ δ / 4 := min_le_right _ _
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hmiss : ∀ v, (missDeg p F G v : ℝ) ≤ 4 * (ε * n) := fun v => by
    have := missDeg_le_of_idealized hε0 hI v
    push_cast at this
    exact this
  refine hB G p ⌊4 * (ε * n)⌋₊ hN
    (fun u v h => allowedPair_of_allowedNW hcard (hI.2.1 u v h))
    (fun v => Nat.le_floor (hmiss v)) ?_ ?_ hdiv
  · calc (⌊4 * (ε * n)⌋₊ : ℝ) ≤ 4 * (ε * n) := Nat.floor_le (by positivity)
      _ ≤ δ * n := by nlinarith
  · have hlow : ∀ i, (1 - ε) * n / 4 ≤ ((clsNW p i).card : ℝ) := fun i => by
      have := hI.1 i; push_cast at this; exact this
    have hsum := sum_clsNW p
    rw [Fin.sum_univ_four] at hsum
    have h0 := hlow 0; have h1 := hlow 1; have h2 := hlow 2; have h3 := hlow 3
    have hεn : 0 ≤ ε * n := mul_nonneg hε0 hn0
    have hηn : ε * n ≤ η * n := mul_le_mul_of_nonneg_right hεη hn0
    intro i
    change (1 / 4 - η) * n ≤ ((clsNW p i).card : ℝ) ∧ ((clsNW p i).card : ℝ) ≤ (1 / 4 + η) * n
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      constructor <;> nlinarith

/-- **The F₁/F₂ entries of NW 1.8 from the padded Keevash interface** (the single open atom). -/
theorem theorem147_of_padded {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2)
    (hK : KeevashPaddedSpec F) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      IsIntDiv p F G.edgeFinset → IsIdealizedNW F ε G p → HasDecomp p F G.edgeFinset := by
  have hcard : ∀ τ ∈ F, Multiset.card τ = 3 := by
    rcases hF with rfl | rfl
    · unfold F1; decide
    · unfold F2; decide
  exact theorem147_of_keevash hF (keevashTypedSpec_of_padded hcard hK)

end PartitionedTriangleAbsorption.BlowupB
