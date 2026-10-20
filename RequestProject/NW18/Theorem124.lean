/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.CloseExtremal
public import RequestProject.NW18.Theorem26Proof
public import RequestProject.NW18.HingeCount

@[expose] public section

/-!
# Theorem 12.4 (the non-extremal case)

Derived, as in §14.2 of the paper, from Theorem 13.16 (explicit hypothesis), Theorem 2.6 and
Lemma 14.4.

The paper says that a graph that is not `β`-extremal is not `β`-close to the three extremal
graphs; that is not literally true with the same `β` (closeness at edit distance `β n²` only
gives about `√β`-extremality), so we apply Lemma 14.4 with `α = min(α₀, β²/8)` and use
`extremal_of_isCloseToExtremal`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma HingefulN.mono {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {α α' : ℝ} {C C' : ℕ} (hα : α' ≤ α)
    (hC : C ≤ C') (h : HingefulN p F G α C) : HingefulN p F G α' C' := by
  intro S S' hS hS' h1
  obtain ⟨i, hi, hcount⟩ := h S S' hS hS' h1
  refine ⟨i, ?_, le_trans ?_ hcount⟩
  · simp only [mem_Icc] at hi ⊢; omega
  · exact mul_le_mul_of_nonneg_right hα (zpow_nonneg (Nat.cast_nonneg _) _)

omit [DecidableEq V] in
lemma AntiEdgeful.mono {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {α α' : ℝ} (hα : α' ≤ α)
    (h : AntiEdgeful p F G α) : AntiEdgeful p F G α' := by
  intro τ hτ i j k hijk u v huv hu hv
  exact le_trans (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _))
    (h τ hτ i j k hijk u v huv hu hv)

lemma copies_K3_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    copies onePart K3fam G = G.cliqueFinset 3 := by
  classical
  ext s
  simp only [copies, mem_filter, mem_powersetCard, subset_univ, true_and,
    SimpleGraph.mem_cliqueFinset_iff, isCopy_K3_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.2, h⟩⟩

/-- `{K₃}`-fractional divisibility of `E(G)` holds for every graph (`t = 1`). -/
lemma isFracDiv_K3 (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsFracDiv onePart K3fam G.edgeFinset := by
  have hF : ∀ (v : V), K3fam.filter (fun τ => onePart v ∈ τ) = K3fam := by
    intro v
    change K3fam.filter (fun τ => (0 : Fin 1) ∈ τ) = K3fam
    decide
  have hE : typeEdgeVec ({0, 0, 0} : Multiset (Fin 1)) 0 0 = 6 := by decide
  have hD : ∀ v : V, typeDegVec ({0, 0, 0} : Multiset (Fin 1)) (onePart v) 0 = 2 := by
    intro v; simp only [onePart]; decide
  refine ⟨⟨fun _ => (G.edgeFinset.card : ℝ) / 3, fun _ => by positivity, ?_⟩, fun v =>
    ⟨fun _ => (G.degree v : ℝ) / 2, fun _ => by positivity, ?_⟩⟩
  · funext i j
    fin_cases i; fin_cases j
    simp only [K3fam, sum_singleton, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Fin.zero_eta, Fin.isValue]
    rw [edgeVec_onePart_of_edgeFinset, hE]
    push_cast; ring
  · funext i
    fin_cases i
    rw [hF]
    simp only [K3fam, sum_singleton, Pi.smul_apply, smul_eq_mul]
    simp only [Fin.zero_eta, Fin.isValue]
    rw [degVec_onePart_of_edgeFinset, hD]
    push_cast; ring

/-- A `C`-regular fractional triangle decomposition is a `C'`-regular `ε`-almost fractional
`{K₃}`-packing for every `C' ≥ C` and `ε ≥ 0`. -/
lemma isRegularAlmostPacking_of_regularFracDecomp {G : SimpleGraph V} [DecidableRel G.Adj]
    {C C' ε : ℝ} {w : Finset V → ℝ} (hC0 : 0 < C) (hC : C ≤ C') (hε : 0 ≤ ε)
    (hn : 0 < Fintype.card V) (hw : IsRegularFracDecomp G C w) :
    IsRegularAlmostPacking onePart K3fam G C' ε w := by
  obtain ⟨⟨-, hsum⟩, hreg⟩ := hw
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  refine ⟨fun s hs => ?_, fun e he => ?_⟩
  · have hs' : s ∈ G.cliqueFinset 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff]; exact (isCopy_K3_iff G s).mp hs
    obtain ⟨h1, h2⟩ := hreg s hs'
    constructor
    · refine le_trans ?_ h1
      gcongr
    · refine le_trans h2 ?_
      gcongr
  · induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      have : ∑ s ∈ copies onePart K3fam G with s(u, v) ∈ triEdges s, w s = 1 := by
        rw [copies_K3_eq, ← hsum u v huv]
        refine sum_congr ?_ fun _ _ => rfl
        ext s
        simp only [mem_filter, mk_mem_triEdges]
        exact ⟨fun ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩,
          fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, huv.ne⟩⟩
      rw [this]; constructor <;> linarith

/-- **Theorem 13.16 for `K₃`, on the hosts of the non-extremal case** (open premise of
branch (1), Theorem 12.4).  This is exactly the instance of Theorem 13.16 that the proof of
Theorem 12.4 uses (`t = 1`, `F = {K₃}`), restricted to the hosts that actually occur there:
`K₃`-divisible graphs with `δ(G) ≥ 3n/4`.  For `t = 1` fractional divisibility holds for every
graph (`isFracDiv_K3`) and integral divisibility is ordinary `K₃`-divisibility
(`isIntDiv_K3_iff`).  It is implied by `Theorem1316Statement`
(`theorem1316K3_of_theorem1316`) but is a strictly more specialised claim.  **Not proved.** -/
def Theorem1316K3Statement : Prop :=
  ∀ α : ℝ, 0 < α → ∀ C : ℕ, 1 ≤ C → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
      3 * Fintype.card V ≤ 4 * G.minDegree →
      (∃ φ, IsRegularAlmostPacking onePart K3fam G C ε φ) →
      AntiEdgeful onePart K3fam G α → HingefulN onePart K3fam G α C →
      NashWilliams.HasTriangleDecomposition G

/-- The global interface `Theorem1316Statement` implies its `K₃` instance. -/
theorem theorem1316K3_of_theorem1316 (h1316 : Theorem1316Statement) :
    Theorem1316K3Statement := by
  intro α hα C hC
  obtain ⟨ε, hε, n₀, h⟩ := h1316 1 K3fam (by simp [K3fam]) α hα C hC
  refine ⟨ε, hε, n₀, fun V _ _ G _ hn hdiv _ hpack hanti hhinge => ?_⟩
  rw [← hasDecomp_K3_iff]
  exact h V onePart G hn (isFracDiv_K3 G) hpack ((isIntDiv_K3_iff G).mpr hdiv) hanti hhinge

/-- **Theorem 12.4.** There is `β₀ > 0` such that for every `β ∈ (0, β₀]` and all large `n`,
every `K₃`-divisible graph on `n` vertices with `δ(G) ≥ 3n/4` that is not `β`-extremal has a
triangle decomposition.  Proved from the `K₃` instance of Theorem 13.16 on these hosts
(hypothesis `h124 : Theorem1316K3Statement`), Theorem 2.6 and Lemma 14.4. -/
theorem theorem_12_4_of_K3 (h124 : Theorem1316K3Statement) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
        NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨σ₀, hσ₀, h26⟩ := theorem_2_6
  obtain ⟨α₀, hα₀, h144⟩ := lemma_14_4
  refine ⟨min σ₀ 1, lt_min hσ₀ one_pos, fun β hβ hββ₀ => ?_⟩
  have hβ1 : β ≤ 1 := hββ₀.trans (min_le_right _ _)
  set α := min α₀ (β ^ 2 / 8) with hαdef
  have hα : 0 < α := lt_min hα₀ (by positivity)
  obtain ⟨c, hc, n₁, hn₁⟩ := h144 α hα (min_le_left _ _)
  obtain ⟨ε, hε, C, hC, n₂, hn₂⟩ := h26 β hβ (hββ₀.trans (min_le_left _ _))
  set C'' : ℕ := max 8 ⌈C⌉₊
  set α' : ℝ := min (1 / 2) c
  have hα' : 0 < α' := lt_min (by norm_num) hc
  obtain ⟨ε', hε', n₃, hn₃⟩ :=
    h124 α' hα' C'' (le_trans (by norm_num) (le_max_left _ _))
  obtain ⟨n₄, hn₄⟩ := extremal_of_isCloseToExtremal hβ
  refine ⟨max (max n₁ n₂) (max n₃ (max n₄ 1)), fun V _ _ G _ hn hdiv hδ hnx => ?_⟩
  have hn₁' : n₁ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₂' : n₂ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₃' : n₃ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₄' : n₄ ≤ Fintype.card V := le_trans (by omega) hn
  have hpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) hn
  -- a `C`-regular fractional decomposition, by Theorem 2.6
  have hδ' : (3 / 4 - ε) * Fintype.card V ≤ G.minDegree := by
    have h1 : (3 : ℝ) * Fintype.card V ≤ 4 * G.minDegree := by exact_mod_cast hδ
    have h2 : 0 ≤ ε * Fintype.card V := by positivity
    nlinarith
  obtain ⟨w, hw⟩ : ∃ w, IsRegularFracDecomp G C w := by
    by_contra hno
    exact hnx (hn₂ V G hn₂' hδ' hno)
  -- not close to the extremal graphs, hence hingeful by Lemma 14.4
  have hnc : ¬ IsCloseToExtremal α G := fun hc =>
    hnx (hn₄ V G hn₄' α (min_le_right _ _)
      ((min_le_right _ _).trans (by nlinarith [hβ, hβ1])) hc)
  have hhinge := hn₁ V G hn₁' hδ hnc
  refine hn₃ V G hn₃' hdiv hδ ⟨w, ?_⟩
    (AntiEdgeful.mono (min_le_left _ _) (antiEdgeful_K3_of_minDegree G hδ))
    (hhinge.mono (min_le_right _ _) (le_max_left _ _))
  refine isRegularAlmostPacking_of_regularFracDecomp (by linarith) ?_ hε'.le hpos hw
  calc C ≤ ⌈C⌉₊ := Nat.le_ceil C
    _ ≤ (C'' : ℝ) := by exact_mod_cast le_max_right _ _


/-- **Theorem 12.4** from the global interface `Theorem1316Statement` (kept for compatibility;
see `theorem_12_4_of_K3` for the version with the specialised premise). -/
theorem theorem_12_4 (h1316 : Theorem1316Statement) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
        NashWilliams.HasTriangleDecomposition G :=
  theorem_12_4_of_K3 (theorem1316K3_of_theorem1316 h1316)

end NashWilliams18
