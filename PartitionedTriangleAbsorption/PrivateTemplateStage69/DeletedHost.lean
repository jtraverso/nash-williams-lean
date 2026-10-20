/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Transport

/-! # Structural F3 absorbers in a four-class host after sparse edge deletion

Let `G₀` be the complete graph between distinct structural classes `cls : V → Fin 4`,
every class of size at least `γ n`, and let `B` be a physical edge ledger of maximum
degree `d`. For every `P ⊆ E(G₀) \ B` with `|P| ≤ m` and **structural** divisibility
`IsIntDiv cls F3 P`, `deleted_host_absorber` produces `A ⊆ E(G₀) \ B`, disjoint from `P`,
with structural `F3` decompositions of both `A` and `A ∪ P` and `|A|, |V(A)| ≤ C(m)`,
where `C(m) = absorberConst 6 * (12 * m) = 2280 m`.

The ingredients are exactly the accepted ones:

* `ClassCertificateLocalStage67.signed_certificate_after_deletion` (weight `≤ 12 m`);
* `ClassHingeDeletionStage69.hingeSupply_after_deletion` (coefficient `γ²/8`, six vertices);
* `ClassHingeDeletionStage69.coarse_antiEdgeful` and
  `SparseReserveGeometry.antiEdgeful_withoutEdges` (coefficient `γ/2` after deletion);
* `SignedAbsorberAPIStage57.absorber_of_budget_api`;
* the promotion `isDecomp_F3_of_proper`: every triangle of `G₀` has three distinct
  structural classes.

No universal common-neighbour query, minimum-degree hypothesis, or embedding oracle is used.
All numerical hypotheses are explicit inequalities in `n, d, γ, m`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplateStage69

open Finset TypedApplicationLinks SignedCertificate SignedHinge SparseReserveGeometry
open ClassCertificate ClassRepresentativesStage65

/-- The explicit size constant of the structural private absorber: `2280 m`. -/
def templateConst (m : ℕ) : ℕ := absorberConst 6 * (12 * m)

theorem templateConst_eq (m : ℕ) : templateConst m = 2280 * m := by
  simp [templateConst, absorberConst, Nat.choose]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleted neighbours of a vertex are counted by the ledger degree. -/
theorem deleted_card_le (G₀ : SimpleGraph V) [DecidableRel G₀.Adj]
    (B : Finset (Sym2 V)) [DecidableRel (withoutEdges G₀ B).Adj] (v : V) :
    (univ.filter fun w => G₀.Adj v w ∧ ¬ (withoutEdges G₀ B).Adj v w).card ≤
      (B.filter fun e => v ∈ e).card := by
  refine card_le_card_of_injOn (fun w => s(v, w)) ?_ ?_
  · intro w hw
    have hw' := (mem_filter.mp (mem_coe.mp hw)).2
    rw [withoutEdges_adj] at hw'
    have hB : s(v, w) ∈ B := by
      by_contra h
      exact hw'.2 ⟨hw'.1, h⟩
    exact mem_coe.mpr (mem_filter.mpr ⟨hB, Sym2.mem_mk_left v w⟩)
  · intro a _ b _ hab
    exact (Sym2.congr_right.mp hab)

theorem withoutEdges_le (G₀ : SimpleGraph V) [DecidableRel G₀.Adj] (B : Finset (Sym2 V)) :
    withoutEdges G₀ B ≤ G₀ := fun a b h => ((withoutEdges_adj G₀ B a b).mp h).1

/-- **Absorbers after sparse deletion in the four-class host.** -/
theorem deleted_host_absorber (m : ℕ) (cls : V → Fin 4) (G₀ : SimpleGraph V)
    [DecidableRel G₀.Adj] (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b)
    (γ d : ℝ) (hd : 0 ≤ d)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (hcert : (2 * m + 3 : ℝ) * d < γ * Fintype.card V)
    (hlarge : 2 ≤ γ * Fintype.card V)
    (hhinge : 56 * d ≤ γ ^ 2 * Fintype.card V)
    (hanti : 4 * d ≤ γ * Fintype.card V)
    (hαM : (absorberBudget 6 (12 * m) : ℝ) < γ / 2 * Fintype.card V)
    (hβM : (2 ^ 21 : ℝ) * absorberBudget 6 (12 * m) < γ ^ 2 / 8 * Fintype.card V)
    (P : Finset (Sym2 V)) (hPG : P ⊆ G₀.edgeFinset) (hPB : Disjoint P B)
    (hm : P.card ≤ m) (hdiv : IsIntDiv cls F3 P) :
    ∃ A : Finset (Sym2 V), A ⊆ G₀.edgeFinset ∧ Disjoint A B ∧ Disjoint A P ∧
      HasDecomp cls F3 A ∧ HasDecomp cls F3 (A ∪ P) ∧
      A.card ≤ templateConst m ∧ (vertSet A).card ≤ templateConst m := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := by
    have hγ : 0 < γ * n := by linarith
    rcases lt_or_ge 0 n with h | h
    · exact h
    · have : n = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [this, mul_zero] at hγ
      exact absurd hγ (lt_irrefl 0)
  have hγ0 : 0 < γ := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hn0.le
    linarith
  let G := withoutEdges G₀ B
  have hsub : G ≤ G₀ := withoutEdges_le G₀ B
  have key : ∀ (_ : Fintype G.edgeSet) (e : Sym2 V), e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
    fun _ _ => SimpleGraph.mem_edgeFinset
  -- the physical edges of `P` survive
  have hPGs : ∀ e ∈ P, e ∈ G.edgeSet := by
    intro e he
    have he0 := SimpleGraph.mem_edgeFinset.mp (hPG he)
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he0 ⊢
      exact (withoutEdges_adj G₀ B a b).mpr ⟨he0, disjoint_left.mp hPB he⟩
  -- deletion degree
  have hdel : ∀ v, ((univ.filter fun w => G₀.Adj v w ∧ ¬ G.Adj v w).card : ℝ) ≤ d := by
    intro v
    exact le_trans (by exact_mod_cast deleted_card_le G₀ B v) (hB v)
  -- signed certificate of weight ≤ 12 m
  have hvP : ((vertSet P).card : ℝ) ≤ 2 * m := by
    have h := card_vertSet_le P
    have : (vertSet P).card ≤ 2 * m := h.trans (by omega)
    exact_mod_cast this
  have hbudget : (((vertSet P).card + 3 : ℕ) : ℝ) * d < γ * n := by
    push_cast
    calc ((vertSet P).card + 3 : ℝ) * d ≤ (2 * m + 3) * d := by nlinarith
      _ < γ * n := hcert
  obtain ⟨ι, hι, t, c, hc, hw, -⟩ :=
    ClassCertificateLocalStage67.signed_certificate_after_deletion cls G₀ G hG₀ hsub d hd
      hdel P (fun e he => (key _ e).mpr (hPGs e he)) hdiv (γ * n) hsize hbudget
  have hK : certWeight c ≤ ((12 * m : ℕ) : ℤ) := by
    refine hw.trans ?_
    push_cast
    have : (P.card : ℤ) ≤ m := by exact_mod_cast hm
    linarith
  -- host hypotheses for the coarse labels
  have hpc : ∀ a b, cls a = cls b → coarse cls a = coarse cls b := fun a b h => by
    simp [coarse, h]
  have hanti0 := ClassHingeDeletionStage69.coarse_antiEdgeful cls G₀ hG₀ γ hsize
  have hanti1 : AntiEdgeful (coarse cls) F0 G (γ / 2) :=
    antiEdgeful_withoutEdges (coarse cls) F0 G₀ B γ (γ / 2) d hanti0 hB (by linarith)
  have hBδ : DegBounded B (d / n * n) := by
    rw [div_mul_cancel₀ d hn0.ne']
    exact hB
  have hδ : d / n ≤ γ ^ 2 / 56 := by
    rw [div_le_iff₀ hn0]
    linarith
  have hsup := ClassHingeDeletionStage69.hingeSupply_after_deletion cls G₀ hG₀ (coarse cls)
    hpc F0 B γ (d / n) hsize hlarge hδ hBδ
  have hparts : ∀ j : Fin 2, ∃ v, coarse cls v = j := by
    have hne : ∀ i, (classSet cls i).Nonempty := by
      intro i
      rw [← card_pos]
      have := hsize i
      have : (0 : ℝ) < (classSet cls i).card := by linarith
      exact_mod_cast this
    intro j
    fin_cases j
    · obtain ⟨v, hv⟩ := hne 0
      exact ⟨v, by simp [coarse, (mem_filter.mp hv).2, MultipartiteBoundaryStage64.classPart]⟩
    · obtain ⟨v, hv⟩ := hne 2
      exact ⟨v, by simp [coarse, (mem_filter.mp hv).2, MultipartiteBoundaryStage64.classPart]⟩
  have hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ vertSet P := fun e he v hv =>
    mem_filter.mpr ⟨mem_univ _, e, he, hv⟩
  have hZ : (vertSet P).card ≤ 3 * (12 * m) := (card_vertSet_le P).trans (by omega)
  have hβ' : (2 ^ Nat.choose (6 + 1) 2 : ℝ) * absorberBudget 6 (12 * m) <
      γ ^ 2 / 8 * n := by
    norm_num [Nat.choose]
    norm_num at hβM
    linarith
  obtain ⟨A, Q, hAG, -, habs, -, -, -, -, hAc, -, hVc, -, -, -⟩ :=
    SignedAbsorberAPIStage57.absorber_of_budget_api (γ / 2) (γ ^ 2 / 8) 6 (12 * m)
      (coarse cls) G hparts hanti1 hsup P t c (vertSet P) hc hK hPZ hZ hαM hβ'
  obtain ⟨hAP, hdA, hdAP⟩ := habs
  -- physical consequences
  have hAG' : ∀ e ∈ A, e ∈ G₀.edgeFinset ∧ e ∉ B := by
    intro e he
    have he' := (key _ e).mp (hAG he)
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he'
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (withoutEdges_adj G₀ B a b).mp he'
  have hprop : ∀ a b, s(a, b) ∈ A ∪ P → cls a ≠ cls b := by
    intro a b hab
    rcases mem_union.mp hab with h | h
    · exact (hG₀ a b).mp (SimpleGraph.mem_edgeFinset.mp (hAG' _ h).1)
    · exact (hG₀ a b).mp (SimpleGraph.mem_edgeFinset.mp (hPG h))
  refine ⟨A, fun e he => (hAG' e he).1, disjoint_left.mpr fun e he => (hAG' e he).2, hAP,
    hasDecomp_F3_of_proper cls hdA fun a b h => hprop a b (mem_union_left _ h),
    hasDecomp_F3_of_proper cls hdAP hprop, hAc, ?_⟩
  refine le_trans (card_le_card ?_) hVc
  intro v hv
  obtain ⟨-, e, he, hve⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨mem_univ _, e, mem_union_left _ he, hve⟩

end PartitionedTriangleAbsorption.PrivateTemplateStage69
