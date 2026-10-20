/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.Stars

@[expose] public section

/-!
# Case (5): bookkeeping for deleting edge sets and for common neighbours

Elementary facts used in the assembly of case (5): degrees, class loads, missing neighbours
and common-neighbour counts after deleting a set of edges; the incidence count of a family of
edge-disjoint triangles; the matching between pairing indices and partner classes; and the
common-neighbour supply for a cross edge of a locally optimal partition (Claim 12.8.9).
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Deleting a set of edges -/

omit [Fintype V] in
lemma incidentLoad_sdiff_add (E P : Finset (Sym2 V)) (hP : P ⊆ E) (v : V) :
    incidentLoad (E \ P) v + incidentLoad P v = incidentLoad E v := by
  unfold incidentLoad
  have h : (E \ P).filter (fun e => v ∈ e) = E.filter (fun e => v ∈ e) \ P.filter (fun e => v ∈ e) := by
    ext x; simp only [mem_filter, mem_sdiff]; tauto
  rw [h]
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ hP)

lemma degree_deleteEdges_add (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Sym2 V))
    (hP : P ⊆ G.edgeFinset) (v : V) :
    (G.deleteEdges (P : Set (Sym2 V))).degree v + incidentLoad P v = G.degree v := by
  classical
  rw [← IndependentStarQuotaStage144.incident_degree, ← IndependentStarQuotaStage144.incident_degree,
    SimpleGraph.edgeFinset_deleteEdges]
  exact incidentLoad_sdiff_add _ _ hP v

omit [DecidableEq V] in
lemma classLoad_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set (Sym2 V))
    [DecidableRel (G.deleteEdges s).Adj] (p : V → Fin 4) (v : V) (j : Fin 4) :
    classLoad p (G.deleteEdges s) v j ≤ classLoad p G v j := by
  unfold classLoad
  apply card_le_card
  intro w hw
  obtain ⟨hw, hp⟩ := mem_filter.mp hw
  refine mem_filter.mpr ⟨?_, hp⟩
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact (SimpleGraph.deleteEdges_adj.mp hw).1

lemma missingOutside_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Sym2 V)) (p : V → Fin 4) (w : V) :
    (missingOutside (G.deleteEdges (P : Set (Sym2 V))) p w).card ≤
      (missingOutside G p w).card + incidentLoad P w := by
  classical
  have hsub : missingOutside (G.deleteEdges (P : Set (Sym2 V))) p w ⊆
      missingOutside G p w ∪ blockedNeighbours P w := by
    intro z hz
    simp only [missingOutside, mem_sdiff, mem_compl, SimpleGraph.mem_neighborFinset,
      SimpleGraph.deleteEdges_adj, not_and, not_not] at hz
    by_cases hG : G.Adj w z
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by simpa using hz.2 hG⟩)
    · exact mem_union_left _ (by
        simp only [missingOutside, mem_sdiff, mem_compl, SimpleGraph.mem_neighborFinset]
        exact ⟨hz.1, hG⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (blockedNeighbours_card_le P w) _))

lemma internalNeighbours_card (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (v : V) : (internalNeighbours G p v).card = classLoad p G v (p v) := by
  rw [← CleanupGeometryStage140.internal_load_eq, internal_inventory]

/-! ### Triangles at a vertex -/

omit [Fintype V] in
lemma incidentLoad_family (D : Finset (Finset V)) (h3 : ∀ t ∈ D, t.card = 3)
    (hdisj : (D : Set (Finset V)).PairwiseDisjoint triEdges) (x : V) :
    incidentLoad (D.biUnion triEdges) x = 2 * (D.filter fun t => x ∈ t).card :=
  covered_incident_card D h3 hdisj x

/-! ### Pairing indices and partner classes -/

lemma exists_partner_eq (c l : Fin 4) (h : l ≠ c) : ∃ i : Fin 3, partner i c = l := by
  fin_cases c <;> fin_cases l <;> first | exact absurd rfl h | decide

lemma partner_injective {i i' : Fin 3} {c : Fin 4} (h : partner i c = partner i' c) :
    i = i' := by
  revert h
  fin_cases i <;> fin_cases i' <;> fin_cases c <;> decide

/-! ### Common neighbours -/

/-- Common neighbours of `a` and `c` in each class add up to all common neighbours. -/
lemma sum_common_class (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (a c : V) :
    ∑ l : Fin 4, (univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card =
      (G.neighborFinset a ∩ G.neighborFinset c).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := p) (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
  refine sum_congr rfl fun l _ => ?_
  congr 1
  ext w
  simp [and_comm]

lemma common_ge (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V) :
    G.degree a + G.degree c ≤ Fintype.card V + (G.neighborFinset a ∩ G.neighborFinset c).card := by
  have h := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset c)
  have hu := card_le_univ (G.neighborFinset a ∪ G.neighborFinset c)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h
  omega

lemma sum_four_split (j k : Fin 4) (h : j ≠ k) (f : Fin 4 → ℝ) :
    ∃ l₁ l₂ : Fin 4, l₁ ≠ j ∧ l₁ ≠ k ∧ l₂ ≠ j ∧ l₂ ≠ k ∧
      ∑ l, f l = f j + f k + f l₁ + f l₂ := by
  rw [Fin.sum_univ_four]
  fin_cases j <;> fin_cases k <;> (try exact absurd rfl h) <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    first
    | exact ⟨2, 3, by decide, by decide, by decide, by decide, by ring⟩
    | exact ⟨1, 3, by decide, by decide, by decide, by decide, by ring⟩
    | exact ⟨1, 2, by decide, by decide, by decide, by decide, by ring⟩
    | exact ⟨0, 3, by decide, by decide, by decide, by decide, by ring⟩
    | exact ⟨0, 2, by decide, by decide, by decide, by decide, by ring⟩
    | exact ⟨0, 1, by decide, by decide, by decide, by decide, by ring⟩

/-- **Supply for a cross edge** (Claim 12.8.9).  In a locally optimal partition of a graph with
`δ(G) ≥ 3n/4`, two vertices in different classes have at least `n/16` common neighbours in one
of the two remaining classes. -/
theorem cross_supply (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v) (a c : V) (hac : p a ≠ p c) :
    ∃ l : Fin 4, l ≠ p a ∧ l ≠ p c ∧ (Fintype.card V : ℝ) / 16 ≤
      (univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card := by
  classical
  set cm : Fin 4 → ℝ := fun l => ((univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card : ℝ)
  have hsum : ∑ l, cm l = ((G.neighborFinset a ∩ G.neighborFinset c).card : ℝ) := by
    simp only [cm]
    exact_mod_cast sum_common_class G p a c
  have hcom : (G.degree a : ℝ) + G.degree c ≤
      Fintype.card V + (G.neighborFinset a ∩ G.neighborFinset c).card := by
    exact_mod_cast common_ge G a c
  have ha : cm (p a) ≤ G.degree a / 4 := by
    have h1 : (univ.filter fun w => p w = p a ∧ G.Adj a w ∧ G.Adj c w).card ≤
        classLoad p G a (p a) := by
      unfold classLoad
      apply card_le_card
      intro w hw
      obtain ⟨-, h1, h2, -⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, h1⟩
    have h2 : (4 * classLoad p G a (p a) : ℝ) ≤ G.degree a := by
      exact_mod_cast four_classLoad_own_le p G hloc a
    have h1' : cm (p a) ≤ classLoad p G a (p a) := by simp only [cm]; exact_mod_cast h1
    linarith
  have hc : cm (p c) ≤ G.degree c / 4 := by
    have h1 : (univ.filter fun w => p w = p c ∧ G.Adj a w ∧ G.Adj c w).card ≤
        classLoad p G c (p c) := by
      unfold classLoad
      apply card_le_card
      intro w hw
      obtain ⟨-, h1, -, h3⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h3, h1⟩
    have h2 : (4 * classLoad p G c (p c) : ℝ) ≤ G.degree c := by
      exact_mod_cast four_classLoad_own_le p G hloc c
    have h1' : cm (p c) ≤ classLoad p G c (p c) := by simp only [cm]; exact_mod_cast h1
    linarith
  obtain ⟨l₁, l₂, h1a, h1c, h2a, h2c, hsplit⟩ := sum_four_split (p a) (p c) hac cm
  have hda := hdeg a
  have hdc := hdeg c
  by_cases h1 : (Fintype.card V : ℝ) / 16 ≤ cm l₁
  · exact ⟨l₁, h1a, h1c, h1⟩
  · refine ⟨l₂, h2a, h2c, ?_⟩
    push_neg at h1
    show (Fintype.card V : ℝ) / 16 ≤ cm l₂
    linarith

/-- Removing the vertices of `S` costs at most `|S|` candidates. -/
lemma common_outside_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (a c : V) (l : Fin 4) :
    ((univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card : ℝ) - S.card ≤
      (univ.filter fun w => w ∉ S ∧ p w = l ∧ G.Adj a w ∧ G.Adj c w).card := by
  classical
  have hsub : (univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w) ⊆
      (univ.filter fun w => w ∉ S ∧ p w = l ∧ G.Adj a w ∧ G.Adj c w) ∪ S := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact mem_union_right _ hwS
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hwS, (mem_filter.mp hw).2⟩)
  have h := (card_le_card hsub).trans (card_union_le _ _)
  have hR : ((univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card : ℝ) ≤
      (univ.filter fun w => w ∉ S ∧ p w = l ∧ G.Adj a w ∧ G.Adj c w).card + S.card := by
    exact_mod_cast h
  linarith

/-- Common neighbours in a class, in the vocabulary of `CleanupSupplyStage140`. -/
lemma candidates_card_eq (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (a c : V)
    (l : Fin 4) :
    (CleanupSupplyStage140.candidates G p a c l).card =
      (univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card := by
  congr 1
  ext w
  simp [CleanupSupplyStage140.candidates, classSet]

/-- Common neighbours after deleting a set of edges. -/
lemma candidates_deleteEdges_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (P : Finset (Sym2 V)) (u v : V) (k : Fin 4) :
    ((CleanupSupplyStage140.candidates G p u v k).card : ℝ) - incidentLoad P u -
        incidentLoad P v ≤
      (RequestPackingStage140.candidates p (G.deleteEdges (P : Set (Sym2 V))) u v k).card := by
  classical
  have hsub : CleanupSupplyStage140.candidates G p u v k ⊆
      RequestPackingStage140.candidates p (G.deleteEdges (P : Set (Sym2 V))) u v k ∪
        (blockedNeighbours P u ∪ blockedNeighbours P v) := by
    intro w hw
    simp only [CleanupSupplyStage140.candidates, classSet, mem_inter, mem_filter, mem_univ,
      true_and, SimpleGraph.mem_neighborFinset] at hw
    obtain ⟨⟨hp, hu⟩, hv⟩ := hw
    by_cases hbu : s(u, w) ∈ P
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hbu⟩))
    by_cases hbv : s(v, w) ∈ P
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hbv⟩))
    refine mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ?_, ?_, hp⟩)
    · exact SimpleGraph.deleteEdges_adj.mpr ⟨hu, by simpa using hbu⟩
    · refine SimpleGraph.deleteEdges_adj.mpr ⟨hv.symm, ?_⟩
      rw [Sym2.eq_swap]; simpa using hbv
  have h := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left ((card_union_le _ _).trans (Nat.add_le_add
      (blockedNeighbours_card_le P u) (blockedNeighbours_card_le P v))) _))
  have hR : ((CleanupSupplyStage140.candidates G p u v k).card : ℝ) ≤
      (RequestPackingStage140.candidates p (G.deleteEdges (P : Set (Sym2 V))) u v k).card +
        (incidentLoad P u + incidentLoad P v) := by
    exact_mod_cast h
  linarith

end NashWilliams18.C128
