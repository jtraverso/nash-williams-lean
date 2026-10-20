/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Template

/-! # One private absorber placed against a sparse global ledger

`ledger_step`: let `L` be the current physical ledger (source, refiner and all previously
placed private edges) with `deg_L(v) + 2m ≤ D` for all `v` and `4|L| ≤ T γ n`. For a
bounded structural `F3`-divisible piece `P ⊆ E(G₀)`, there is a private absorber `A` with

* `A ⊆ E(G₀)`, `A ∩ L = ∅`, `A ∩ P = ∅`, structural `F3` decompositions of `A` and `A ∪ P`;
* `|A|, |V(A)| ≤ C(m)`;
* `A` has **no edge between two roots of `P`** (root pairs outside `P` are deleted too);
* **load control**: every vertex of `A` is a root of `P` or has ledger degree at most `T`.

Proof: discard the high-load vertices (fewer than `γ n / 2` by double counting), keep the
roots, apply `deleted_host_absorber` in the induced four-class host on the kept vertices
with the ledger `(L \ P) ∪ rootPairs P` of degree `≤ D`, and push the absorber back.
No universal query supply and no minimum-degree hypothesis are used: the only queries
are the class-guarded ones of the four-class host, after the explicit sparse deletion.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplateStage69

open Finset TypedApplicationLinks SignedHinge SparseReserveGeometry PhysicalHingeSupply
open ClassRepresentativesStage65 AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Handshake bound for an arbitrary finite edge set. -/
theorem sum_incidentLoad_le (E : Finset (Sym2 V)) : ∑ v, incidentLoad E v ≤ 2 * E.card := by
  have hswap : ∑ v, incidentLoad E v = ∑ e ∈ E, (univ.filter fun v => v ∈ e).card := by
    simp only [incidentLoad, card_filter]
    exact sum_comm
  rw [hswap]
  calc ∑ e ∈ E, (univ.filter fun v => v ∈ e).card ≤ ∑ _e ∈ E, 2 := by
        refine sum_le_sum fun e _ => ?_
        induction e using Sym2.ind with
        | _ a b =>
          calc (univ.filter fun v => v ∈ s(a, b)).card ≤ ({a, b} : Finset V).card :=
                card_le_card fun v hv => by simpa using hv
            _ ≤ 2 := card_le_two
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Few vertices carry ledger degree above `T`. -/
theorem card_highLoad_le (E : Finset (Sym2 V)) (T : ℝ) :
    ((univ.filter fun v => T < incidentLoad E v).card : ℝ) * T ≤ 2 * E.card := by
  set H := univ.filter fun v => T < (incidentLoad E v : ℝ)
  have h1 : (H.card : ℝ) * T ≤ ∑ v ∈ H, (incidentLoad E v : ℝ) := by
    rw [← nsmul_eq_mul]
    exact card_nsmul_le_sum H _ T fun v hv => (mem_filter.mp hv).2.le
  have h2 : ∑ v ∈ H, (incidentLoad E v : ℝ) ≤ ∑ v, (incidentLoad E v : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  have h3 : ∑ v, (incidentLoad E v : ℝ) ≤ 2 * E.card := by
    exact_mod_cast sum_incidentLoad_le E
  linarith

omit [Fintype V] in
theorem incidentLoad_le_card (E : Finset (Sym2 V)) (v : V) : incidentLoad E v ≤ E.card :=
  card_filter_le _ _

theorem incidentLoad_eq_zero {E : Finset (Sym2 V)} {v : V} (hv : v ∉ vertSet E) :
    incidentLoad E v = 0 := by
  rw [incidentLoad, card_eq_zero, filter_eq_empty_iff]
  intro e he hve
  exact hv (mem_filter.mpr ⟨mem_univ _, e, he, hve⟩)

/-- The pairs of roots of `P` that are not edges of `P`. -/
def rootPairs (P : Finset (Sym2 V)) : Finset (Sym2 V) :=
  ((vertSet P ×ˢ vertSet P).image fun x => s(x.1, x.2)) \ P

theorem incidentLoad_rootPairs_le (P : Finset (Sym2 V)) (v : V) :
    incidentLoad (rootPairs P) v ≤ 2 * P.card := by
  have hsub : (rootPairs P).filter (fun e => v ∈ e) ⊆ (vertSet P).image fun y => s(v, y) := by
    intro e he
    obtain ⟨he, hv⟩ := mem_filter.mp he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp (mem_sdiff.mp he).1
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact mem_image.mpr ⟨b, hb, rfl⟩
    · exact mem_image.mpr ⟨a, ha, Sym2.eq_swap⟩
  exact (card_le_card hsub).trans (card_image_le.trans (card_vertSet_le P))

theorem mem_rootPairs {P : Finset (Sym2 V)} {a b : V} (ha : a ∈ vertSet P)
    (hb : b ∈ vertSet P) (hab : s(a, b) ∉ P) : s(a, b) ∈ rootPairs P :=
  mem_sdiff.mpr ⟨mem_image.mpr ⟨(a, b), mem_product.mpr ⟨ha, hb⟩, rfl⟩, hab⟩

/-- **One private absorber against a sparse ledger, with load control.** -/
theorem ledger_step (m : ℕ) (cls : V → Fin 4) (G₀ : SimpleGraph V) [DecidableRel G₀.Adj]
    (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b) (γ T D : ℝ) (hγ : 0 < γ) (hT : 0 < T)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (hD0 : 0 ≤ D)
    (h1 : (2 * m + 3 : ℝ) * D < γ ^ 2 * Fintype.card V / 4)
    (h2 : 2 ≤ γ ^ 2 * Fintype.card V / 4)
    (h3 : 56 * D ≤ γ ^ 3 * Fintype.card V / 8)
    (h4 : 4 * D ≤ γ ^ 2 * Fintype.card V / 4)
    (h5 : (absorberBudget 6 (12 * m) : ℝ) < γ ^ 2 * Fintype.card V / 8)
    (h6 : (2 ^ 21 : ℝ) * absorberBudget 6 (12 * m) < γ ^ 3 * Fintype.card V / 64)
    (L : Finset (Sym2 V)) (hL : ∀ v, (incidentLoad L v : ℝ) + 2 * m ≤ D)
    (hLc : 4 * (L.card : ℝ) ≤ T * γ * Fintype.card V)
    (P : Finset (Sym2 V)) (hPG : P ⊆ G₀.edgeFinset) (hm : P.card ≤ m)
    (hdiv : IsIntDiv cls F3 P) :
    ∃ A : Finset (Sym2 V), A ⊆ G₀.edgeFinset ∧ Disjoint A L ∧ Disjoint A P ∧
      HasDecomp cls F3 A ∧ HasDecomp cls F3 (A ∪ P) ∧
      A.card ≤ templateConst m ∧ (vertSet A).card ≤ templateConst m ∧
      (∀ a ∈ vertSet P, ∀ b ∈ vertSet P, s(a, b) ∉ A) ∧
      ∀ v ∈ vertSet A, v ∈ vertSet P ∨ (incidentLoad L v : ℝ) ≤ T := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  -- kept vertices
  let Keep : Finset V := univ.filter fun v => (incidentLoad L v : ℝ) ≤ T ∨ v ∈ vertSet P
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ γ * n / 2 := by
    have h := card_highLoad_le L T
    have : (High.card : ℝ) * T ≤ T * (γ * n / 2) := by nlinarith
    nlinarith
  let U := {v : V // v ∈ Keep}
  let valE : U ↪ V := Function.Embedding.subtype _
  let clsU : U → Fin 4 := cls ∘ valE
  let G₀U := fourClassGraph clsU
  -- class sizes survive
  have hclassU : ∀ i, γ * n / 2 ≤ ((classSet clsU i).card : ℝ) := by
    intro i
    have hmap : (classSet clsU i).map valE = classSet cls i ∩ Keep := by
      ext v
      simp only [mem_map, classSet, mem_filter, mem_univ, true_and, mem_inter, clsU,
        Function.comp_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.2⟩
      · rintro ⟨hv, hk⟩
        exact ⟨⟨v, hk⟩, hv, rfl⟩
    have hsplit : classSet cls i ⊆ (classSet cls i ∩ Keep) ∪ High := by
      intro v hv
      by_cases hk : v ∈ Keep
      · exact mem_union_left _ (mem_inter.mpr ⟨hv, hk⟩)
      · refine mem_union_right _ (mem_filter.mpr ⟨mem_univ _, ?_⟩)
        by_contra hle
        exact hk (mem_filter.mpr ⟨mem_univ _, Or.inl (not_lt.mp hle)⟩)
    have hc := (card_le_card hsplit).trans (card_union_le _ _)
    have hcR : ((classSet cls i).card : ℝ) ≤ (classSet cls i ∩ Keep).card + High.card := by
      exact_mod_cast hc
    rw [← hmap, card_map] at hcR
    have := hsize i
    linarith
  have hnU_le : (Fintype.card U : ℝ) ≤ n := by
    have h : Fintype.card U ≤ Fintype.card V := Fintype.card_subtype_le _
    rw [hn]
    exact_mod_cast h
  have hnU_ge : γ * n / 2 ≤ (Fintype.card U : ℝ) := by
    refine (hclassU 0).trans ?_
    exact_mod_cast card_le_univ _
  have hsizeU : ∀ i, γ / 2 * Fintype.card U ≤ ((classSet clsU i).card : ℝ) := by
    intro i
    have := hclassU i
    nlinarith
  -- the pulled-back ledger and piece
  let BU : Finset (Sym2 U) := univ.filter fun e => edgeEmb valE e ∈ (L \ P) ∪ rootPairs P
  let PU : Finset (Sym2 U) := univ.filter fun e => edgeEmb valE e ∈ P
  have hPKeep : ∀ e ∈ P, ∀ v ∈ e, v ∈ Keep := fun e he v hv =>
    mem_filter.mpr ⟨mem_univ _, Or.inr (mem_filter.mpr ⟨mem_univ _, e, he, hv⟩)⟩
  have hPU : PU.map (edgeEmb valE) = P := map_comap_edges Keep P hPKeep
  have hBU : DegBounded BU D := by
    intro x
    have hsub : (BU.filter fun e => x ∈ e).map (edgeEmb valE) ⊆
        (L.filter fun e => valE x ∈ e) ∪ ((rootPairs P).filter fun e => valE x ∈ e) := by
      intro e he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      obtain ⟨he'B, hxe⟩ := mem_filter.mp he'
      have hxe' : valE x ∈ edgeEmb valE e' := by
        simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.mem_map]
        exact ⟨x, hxe, rfl⟩
      rcases mem_union.mp (mem_filter.mp he'B).2 with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨(mem_sdiff.mp h).1, hxe'⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨h, hxe'⟩)
    have h := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_map] at h
    have hZ : (incidentLoad (rootPairs P) (valE x) : ℝ) ≤ 2 * m := by
      have := (incidentLoad_rootPairs_le P (valE x)).trans (Nat.mul_le_mul_left 2 hm)
      exact_mod_cast this
    have hR : ((BU.filter fun e => x ∈ e).card : ℝ) ≤
        incidentLoad L (valE x) + incidentLoad (rootPairs P) (valE x) := by
      exact_mod_cast h
    have := hL (valE x)
    change ((BU.filter fun e => x ∈ e).card : ℝ) ≤ D
    linarith
  have hPUG : PU ⊆ G₀U.edgeFinset := by
    intro e he
    have he' := (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, fourClassGraph_adj]
      have := SimpleGraph.mem_edgeFinset.mp (hPG he')
      exact (hG₀ _ _).mp this
  have hPUB : Disjoint PU BU := by
    refine disjoint_left.mpr fun e he heB => ?_
    have hP := (mem_filter.mp he).2
    rcases mem_union.mp (mem_filter.mp heB).2 with h | h
    · exact (mem_sdiff.mp h).2 hP
    · exact (mem_sdiff.mp h).2 hP
  have hPUm : PU.card ≤ m := by
    rw [← card_map (edgeEmb valE), hPU]
    exact hm
  have hdivU : IsIntDiv clsU F3 PU := by
    apply isIntDiv_comap valE
    rw [hPU]
    exact hdiv
  -- numerical hypotheses in the kept host
  have hU1 : γ ^ 2 * n / 4 ≤ γ / 2 * Fintype.card U := by nlinarith
  have hU2 : γ ^ 3 * n / 8 ≤ (γ / 2) ^ 2 * Fintype.card U := by
    have hγ2 : 0 ≤ (γ / 2) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hnU_ge hγ2
    nlinarith
  have hU3 : γ ^ 2 * n / 8 ≤ γ / 2 / 2 * Fintype.card U := by nlinarith
  have hU4 : γ ^ 3 * n / 64 ≤ (γ / 2) ^ 2 / 8 * Fintype.card U := by nlinarith
  obtain ⟨AU, hAUG, hAUB, hAUP, hdAU, hdAUP, hAUc, hVUc⟩ :=
    deleted_host_absorber m clsU G₀U (fourClassGraph_adj clsU) (γ / 2) D hD0 hsizeU BU hBU
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      PU hPUG hPUB hPUm hdivU
  -- push the absorber back
  refine ⟨AU.map (edgeEmb valE), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    have h := hAUG he'
    induction e' using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, fourClassGraph_adj] at h
      simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.map_mk,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (hG₀ _ _).mpr h
  · refine disjoint_left.mpr fun e he heL => ?_
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    by_cases heP : edgeEmb valE e' ∈ P
    · exact disjoint_left.mp hAUP he' (mem_filter.mpr ⟨mem_univ _, heP⟩)
    · exact disjoint_left.mp hAUB he'
        (mem_filter.mpr ⟨mem_univ _, mem_union_left _ (mem_sdiff.mpr ⟨heL, heP⟩)⟩)
  · rw [← hPU]
    exact (disjoint_map _).mpr hAUP
  · exact hasDecomp_map valE (fun _ => rfl) hdAU
  · rw [← hPU, ← map_union]
    exact hasDecomp_map valE (fun _ => rfl) hdAUP
  · rw [card_map]
    exact hAUc
  · have hsub : vertSet (AU.map (edgeEmb valE)) ⊆ (vertSet AU).map valE := by
      intro v hv
      obtain ⟨-, e, he, hve⟩ := mem_filter.mp hv
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.mem_map] at hve
      obtain ⟨x, hx, rfl⟩ := hve
      exact mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _, e', he', hx⟩)
    exact (card_le_card hsub).trans (by rw [card_map]; exact hVUc)
  · intro a ha b hb hab
    obtain ⟨e', he', hee⟩ := mem_map.mp hab
    by_cases heP : s(a, b) ∈ P
    · exact disjoint_left.mp hAUP he' (mem_filter.mpr ⟨mem_univ _, hee ▸ heP⟩)
    · exact disjoint_left.mp hAUB he' (mem_filter.mpr ⟨mem_univ _,
        mem_union_right _ (hee ▸ mem_rootPairs ha hb heP)⟩)
  · intro v hv
    obtain ⟨-, e, he, hve⟩ := mem_filter.mp hv
    obtain ⟨e', -, rfl⟩ := mem_map.mp he
    simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.mem_map] at hve
    obtain ⟨x, -, rfl⟩ := hve
    rcases (mem_filter.mp x.2).2 with h | h
    · exact Or.inr h
    · exact Or.inl h

end PartitionedTriangleAbsorption.PrivateTemplateStage69
