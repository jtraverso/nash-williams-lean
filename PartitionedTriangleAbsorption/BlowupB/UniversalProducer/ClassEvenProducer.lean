/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ClassEvenRefiner

/-!
# Assembling the per-class heap refiners into a shared even refiner

`evenRefinerProducer_of_commonLinkClasses`: for card-three families with common-link classes,
`EvenRefinerProducer F (Fin t × HeapIdx) 2 42 (4096 t) 2⁻²⁴`.  Combined with the charge layers
(`refinerProducer_of_evenRefinerProducer`) and the existing assembly this gives
`RefinerProducer` and `ProducerTarget` for every card-three family with `ThreeStepLinks` and
common-link classes, without further hypotheses.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.OnePart
open PartitionedTriangleAbsorption.TypedTransformer

variable {t : ℕ}

theorem mem_classIdx {ind : Fin t → Finset HeapIdx} {x : Fin t × HeapIdx} :
    x ∈ univ.biUnion (fun r => (ind r).image (fun j => (r, j))) ↔ x.2 ∈ ind x.1 := by
  constructor
  · intro h
    obtain ⟨r, -, h⟩ := mem_biUnion.mp h
    obtain ⟨j, hj, rfl⟩ := mem_image.mp h
    exact hj
  · intro h
    exact mem_biUnion.mpr ⟨x.1, mem_univ _, mem_image.mpr ⟨x.2, h, rfl⟩⟩

theorem card_classIdx_le (ind : Fin t → Finset HeapIdx) :
    (univ.biUnion (fun r => (ind r).image (fun j => (r, j)))).card ≤ ∑ r, (ind r).card :=
  card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)

theorem sum_classIdx {M : Type*} [AddCommMonoid M] (ind : Fin t → Finset HeapIdx)
    (f : Fin t × HeapIdx → M) :
    ∑ x ∈ univ.biUnion (fun r => (ind r).image (fun j => (r, j))), f x =
      ∑ r, ∑ j ∈ ind r, f (r, j) := by
  rw [sum_biUnion]
  · refine sum_congr rfl fun r _ => ?_
    rw [sum_image]
    intro a _ b _ h
    exact (Prod.ext_iff.mp h).2
  · intro r _ r' _ hrr'
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j', _, h⟩ := mem_image.mp hx'
    exact hrr' (Prod.ext_iff.mp h).1.symm

section Assembly

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem edge_inside_class {F : Finset (Multiset (Fin t))} {p : V → Fin t} {cl : Fin t → Fin t}
    (hcl : IsCommonLinkClassMap F cl) {G : SimpleGraph V} [DecidableRel G.Adj]
    (hact : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) {r : Fin t} {e : Sym2 V}
    (he : e ∈ G.edgeFinset) {v : V} (hve : v ∈ e) (hv : v ∈ classVerts F p cl r) :
    ∀ x ∈ e, x ∈ classVerts F p cl r := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨ha, hb⟩ := mem_classVerts_of_adj hcl (hact a b he)
    have hr : cl (p a) = r := by
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact classVerts_eq_of_mem ha hv
      · exact classVerts_eq_of_mem hb hv
    intro x hx
    rw [← hr]
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact ha
    · exact hb

omit [DecidableEq V] in
theorem class_of_edge {F : Finset (Multiset (Fin t))} {p : V → Fin t} {cl : Fin t → Fin t}
    (hcl : IsCommonLinkClassMap F cl) {G : SimpleGraph V} [DecidableRel G.Adj]
    (hact : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) : ∃ r, ∀ x ∈ e, x ∈ classVerts F p cl r := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨ha, hb⟩ := mem_classVerts_of_adj hcl (hact a b he)
    refine ⟨cl (p a), fun x hx => ?_⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact ha
    · exact hb

omit [DecidableEq V] in
theorem disjoint_of_classes {F : Finset (Multiset (Fin t))} {p : V → Fin t} {cl : Fin t → Fin t}
    {r r' : Fin t} (hrr' : r ≠ r') {E E' : Finset (Sym2 V)}
    (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ classVerts F p cl r)
    (hE' : ∀ e ∈ E', ∀ v ∈ e, v ∈ classVerts F p cl r') : Disjoint E E' := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨v, hv⟩ := exists_mem_sym2 e
  exact hrr' (classVerts_eq_of_mem (hE e he v hv) (hE' e he' v hv))

end Assembly

/-- **The shared even refiner for common-link classes.** -/
theorem evenRefinerProducer_of_commonLinkClasses (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hcl : CommonLinkClasses F) :
    EvenRefinerProducer F (Fin t × HeapIdx) 2 42 (4096 * t) (1 / 2 ^ 24) := by
  classical
  obtain ⟨cl, hclm⟩ := hcl
  intro V _ _ p G _ ω lam rho hω hω1 hact hsup hlam hlamc hrho hrhoc hrn hcn X hXG hXdeg
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have h64 : 64 * lam ≤ ω := by linarith
  have hscale : 2 ^ 24 * rho ≤ lam ^ 2 := by linarith
  have hn2 : 256 ≤ lam * Fintype.card V := by
    have : (1 : ℝ) / 2 ^ 24 * lam * Fintype.card V = lam * Fintype.card V / 2 ^ 24 := by ring
    rw [this, le_div_iff₀ (by norm_num)] at hcn
    linarith
  have hdata := fun r => class_data F p cl hclm r G ω lam rho hsup hlam h64 hrho hscale hrn hn2
    X hXG hXdeg
  choose ind P R hRG hRW hRX hP hrefi hRdeg hcard hload using hdata
  have hLG : ∀ L ⊆ X, L ⊆ G.edgeFinset := fun L hL => hL.trans hXG
  refine ⟨{ lib := univ.biUnion (fun r => (ind r).image (fun j => (r, j)))
            P := fun x => P x.1 x.2
            R0 := univ.biUnion R
            loopP := fun x hx => (hP x.1 x.2 (mem_classIdx.mp hx)).2.1
            evenP := fun x hx => (hP x.1 x.2 (mem_classIdx.mp hx)).2.2.1
            subP := fun x hx => by
              refine (hP x.1 x.2 (mem_classIdx.mp hx)).1.trans ?_
              rw [union_comm]
              exact union_subset_union (subset_biUnion_of_mem R (mem_univ x.1)) subset_rfl
            disjRX := by
              rw [disjoint_biUnion_left]
              exact fun r _ => hRX r
            refines := ?_ }, ?_, ?_, ?_, ?_, ?_⟩
  · -- refinement
    intro L hLX hdiv
    have hloopL : ∀ e ∈ L, ¬ e.IsDiag := fun e he =>
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hLG L hLX he))
    have hevenL := TypedDivisibilityCollapse.even_of_isIntDiv hF3 hloopL hdiv
    set Lr : Fin t → Finset (Sym2 V) :=
      fun r => L.filter (fun e => ∀ v ∈ e, v ∈ classVerts F p cl r) with hLr
    have hLr3 : ∀ r, Even3 (Lr r) := by
      intro r
      refine ⟨?_, ?_⟩
      · have h := three_dvd_card_classEdges p F hF3 (type_closed hF3 hclm r) hdiv
        convert h using 2
        ext e
        simp only [hLr, mem_filter, mem_classVerts]
      · intro v
        by_cases hv : v ∈ classVerts F p cl r
        · have heq : incidentLoad (Lr r) v = incidentLoad L v := by
            unfold incidentLoad
            rw [hLr, filter_filter]
            congr 1
            exact filter_congr fun e he => ⟨fun h => h.2, fun h =>
              ⟨edge_inside_class hclm hact (hLG L hLX he) h hv, h⟩⟩
          rw [heq]; exact hevenL v
        · have heq : incidentLoad (Lr r) v = 0 := by
            unfold incidentLoad
            rw [card_eq_zero, filter_eq_empty_iff]
            intro e he hve
            exact hv ((mem_filter.mp he).2 v hve)
          rw [heq]; exact ⟨0, rfl⟩
    have hs := fun r => hrefi r (Lr r) ((filter_subset _ _).trans hLX)
      (fun e he => (mem_filter.mp he).2) (hLr3 r)
    choose s hs1 hs2 hs3 using hs
    refine ⟨univ.biUnion (fun r => (s r).image (fun j => (r, j))), ?_, ?_, ?_⟩
    · intro x hx
      exact mem_classIdx.mpr (hs1 x.1 (mem_classIdx.mp hx))
    · intro x hx y hy hxy
      have hx' := mem_classIdx.mp hx
      have hy' := mem_classIdx.mp hy
      change Disjoint (P x.1 x.2) (P y.1 y.2)
      by_cases h1 : x.1 = y.1
      · have h2 : x.2 ≠ y.2 := fun h => hxy (Prod.ext h1 h)
        rw [h1] at hx' ⊢
        exact hs2 y.1 hx' hy' h2
      · exact disjoint_of_classes h1 (hP x.1 x.2 (hs1 _ hx')).2.2.2.2
          (hP y.1 y.2 (hs1 _ hy')).2.2.2.2
    · ext e
      simp only [mem_biUnion, mem_image, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨x, ⟨r, j, hj, rfl⟩, he⟩
        have : e ∈ (s r).biUnion (P r) := mem_biUnion.mpr ⟨j, hj, he⟩
        rw [hs3 r, mem_union] at this
        rcases this with h | h
        · exact Or.inl ⟨r, h⟩
        · exact Or.inr (mem_filter.mp h).1
      · rintro (⟨r, he⟩ | he)
        · have : e ∈ (s r).biUnion (P r) := by rw [hs3 r]; exact mem_union_left _ he
          obtain ⟨j, hj, hej⟩ := mem_biUnion.mp this
          exact ⟨(r, j), ⟨r, j, hj, rfl⟩, hej⟩
        · obtain ⟨r, hr⟩ := class_of_edge hclm hact (hLG L hLX he)
          have : e ∈ (s r).biUnion (P r) := by
            rw [hs3 r]; exact mem_union_right _ (mem_filter.mpr ⟨he, hr⟩)
          obtain ⟨j, hj, hej⟩ := mem_biUnion.mp this
          exact ⟨(r, j), ⟨r, j, hj, rfl⟩, hej⟩
  · exact biUnion_subset.mpr fun r _ => hRG r
  · intro x hx
    exact (hP x.1 x.2 (mem_classIdx.mp hx)).2.2.2.1
  · intro v
    change ((incidentLoad (univ.biUnion R) v : ℕ) : ℝ) ≤ _
    have h1 : ((incidentLoad (univ.biUnion R) v : ℕ) : ℝ) ≤ ∑ r, (incidentLoad (R r) v : ℝ) := by
      exact_mod_cast incidentLoad_biUnion_le univ R v
    have h2 : ∑ r, (incidentLoad (R r) v : ℝ) ≤ ∑ _r : Fin t, 4 * lam * Fintype.card V :=
      sum_le_sum fun r _ => hRdeg r v
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (t : ℝ) * (4 * lam * Fintype.card V) ≤ 4096 * t * lam * Fintype.card V := by
      have : (0 : ℝ) ≤ t * lam * Fintype.card V := by positivity
      nlinarith
    linarith
  · have h1 : ((univ.biUnion (fun r => (ind r).image (fun j => (r, j)))).card : ℝ) ≤
        ∑ r, ((ind r).card : ℝ) := by exact_mod_cast card_classIdx_le ind
    have h2 : ∑ r, ((ind r).card : ℝ) ≤ ∑ _r : Fin t, 1224 * rho * (Fintype.card V : ℝ) ^ 2 :=
      sum_le_sum fun r _ => hcard r
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (t : ℝ) * (1224 * rho * (Fintype.card V : ℝ) ^ 2) ≤
        4096 * t * rho * (Fintype.card V : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ t * rho * (Fintype.card V : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  · intro v
    change ((∑ x ∈ univ.biUnion (fun r => (ind r).image (fun j => (r, j))),
      incidentLoad (P x.1 x.2) v : ℕ) : ℝ) ≤ _
    rw [sum_classIdx ind (fun x => incidentLoad (P x.1 x.2) v), Nat.cast_sum]
    have h2 : ∑ r, ((∑ j ∈ ind r, incidentLoad (P r j) v : ℕ) : ℝ) ≤
        ∑ _r : Fin t, 4096 * lam * Fintype.card V := sum_le_sum fun r _ => hload r v
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (t : ℝ) * (4096 * lam * Fintype.card V) = 4096 * t * lam * Fintype.card V := by ring
    linarith

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
