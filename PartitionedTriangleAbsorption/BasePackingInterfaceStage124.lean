/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.DenseQuotaPackingStage124
public import PartitionedTriangleAbsorption.ReserveQueryGeometryStage123

/-! # The base packing in the physical reserve interface

Slot multiplicities are not lost when passing to triples. A fixed-root query
loses at most `2*d+2` candidates to a sparse forbidden graph and its endpoints.
Exclusion of the entire final reserve is still performed by Stage123.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQuotaPackingStage124

open Finset AntiEdgeSelection CoverDownStage105
open SelectedCoverDownStage122 ReserveQueryGeometryStage123

variable {V I : Type*} [DecidableEq V]

def triples (s : Finset I) (root a b : I → V) : Finset (V × V × V) :=
  s.image fun i => (root i, a i, b i)

theorem triple_injective (s : Finset I) (root a b : I → V)
    (hd : (s : Set I).PairwiseDisjoint
      (fun i => TypedCorrectionFamily.edges (root i) (a i) (b i))) :
    Set.InjOn (fun i => (root i, a i, b i)) s := by
  intro i hi j hj heq
  by_contra hn
  have hx : root i = root j := congrArg Prod.fst heq
  have ha : a i = a j := congrArg (fun r : V × V × V => r.2.1) heq
  apply disjoint_left.mp (hd hi hj hn)
    (show s(root i, a i) ∈ TypedCorrectionFamily.edges (root i) (a i) (b i) by
      simp [TypedCorrectionFamily.edges])
  simp [TypedCorrectionFamily.edges, hx, ha]

theorem triples_disjoint (s : Finset I) (root a b : I → V)
    (hd : (s : Set I).PairwiseDisjoint
      (fun i => TypedCorrectionFamily.edges (root i) (a i) (b i))) :
    (triples s root a b : Set (V × V × V)).PairwiseDisjoint resTri := by
  intro r hr r' hr' hne
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hr'
  exact hd hi hj (fun h => hne (h ▸ rfl))

theorem triples_card (s : Finset I) (root a b : I → V)
    (hd : (s : Set I).PairwiseDisjoint
      (fun i => TypedCorrectionFamily.edges (root i) (a i) (b i))) :
    (triples s root a b).card = s.card :=
  card_image_of_injOn (triple_injective s root a b hd)

theorem triples_query_card (s : Finset I) (root a b : I → V)
    (hd : (s : Set I).PairwiseDisjoint
      (fun i => TypedCorrectionFamily.edges (root i) (a i) (b i)))
    (P : V × V × V → Prop) [DecidablePred P] :
    ((triples s root a b).filter P).card =
      (s.filter fun i => P (root i, a i, b i)).card := by
  unfold triples
  rw [filter_image]
  exact card_image_of_injOn ((triple_injective s root a b hd).mono (filter_subset _ _))

theorem triples_edges (s : Finset I) (root a b : I → V) :
    resEdges (triples s root a b) = packingEdges s root a b := by
  ext e
  simp [resEdges, triples, packingEdges, resTri, TypedCorrectionFamily.edges]

theorem connectors_disjoint_self (x a b y z : V)
    (hyx : y ≠ x) (hya : y ≠ a) (hyb : y ≠ b)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) :
    Disjoint (connectors y z (x, a, b)) (resTri (x, a, b)) := by
  simp only [connectors, resTri, disjoint_insert_left, disjoint_singleton_left,
    mem_insert, mem_singleton, Sym2.eq_iff]
  tauto

/-- Delete all candidates meeting either endpoint or either forbidden
neighbourhood. The count is simultaneous for the two inner positions. -/
theorem raw_query [Finite V] (p : V → Fin 4) (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (d : ℕ)
    (hF : ∀ v, incidentLoad F v ≤ d)
    (hG : ∀ u v, p u ≠ p v → s(u, v) ∉ F → G.Adj u v)
    (S : Finset (V × V × V))
    (hd : (S : Set (V × V × V)).PairwiseDisjoint resTri)
    (x y z : V) (hyx : y ≠ x) (hzx : z ≠ x)
    (hs : ∀ r ∈ S, r.1 = x ∧ p y ≠ p r.2.1 ∧ p z ≠ p r.2.2) :
    ∃ R ⊆ S, S.card ≤ R.card + 2 * d + 2 ∧
      ∀ r ∈ R, r.1 = x ∧ G.Adj y r.2.1 ∧ G.Adj r.2.2 z ∧
        s(y, r.2.1) ∉ F ∧ s(r.2.2, z) ∉ F ∧
        Disjoint (connectors y z r) (resTri r) := by
  classical
  let _ := Fintype.ofFinite V
  let Z := blockedNeighbours F y ∪ blockedNeighbours F z ∪ {y, z}
  let bad := S.filter fun r => r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)
  have hb : bad.card ≤ Z.card := card_meeting_le hd x Z
  have hzcard : Z.card ≤ 2 * d + 2 := by
    have h1 := card_union_le (blockedNeighbours F y ∪ blockedNeighbours F z)
      ({y, z} : Finset V)
    have h2 := card_union_le (blockedNeighbours F y) (blockedNeighbours F z)
    have h3 := (blockedNeighbours_card_le F y).trans (hF y)
    have h4 := (blockedNeighbours_card_le F z).trans (hF z)
    have h5 : ({y, z} : Finset V).card ≤ 2 := by
      exact (card_insert_le _ _).trans (by simp)
    change Z.card ≤ _ at h1
    omega
  refine ⟨S \ bad, sdiff_subset, ?_, ?_⟩
  · have hc := card_sdiff_add_card_eq_card (filter_subset (fun r =>
        r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)) S)
    change (S \ bad).card + bad.card = S.card at hc
    omega
  · intro r hr
    obtain ⟨hrS, hrbad⟩ := mem_sdiff.mp hr
    obtain ⟨hrx, hpy, hpz⟩ := hs r hrS
    have haZ : r.2.1 ∉ Z := fun h => hrbad (mem_filter.mpr ⟨hrS, hrx, Or.inl h⟩)
    have hbZ : r.2.2 ∉ Z := fun h => hrbad (mem_filter.mpr ⟨hrS, hrx, Or.inr h⟩)
    have hea : s(y, r.2.1) ∉ F := by
      intro h
      exact haZ (mem_union_left _ (mem_union_left _
        (mem_filter.mpr ⟨mem_univ _, h⟩)))
    have heb : s(z, r.2.2) ∉ F := by
      intro h
      exact hbZ (mem_union_left _ (mem_union_right _
        (mem_filter.mpr ⟨mem_univ _, h⟩)))
    have hya : y ≠ r.2.1 := fun h => haZ (mem_union_right _ (by simp [← h]))
    have hyb : y ≠ r.2.2 := fun h => hbZ (mem_union_right _ (by simp [← h]))
    have hza : z ≠ r.2.1 := fun h => haZ (mem_union_right _ (by simp [← h]))
    have hzb : z ≠ r.2.2 := fun h => hbZ (mem_union_right _ (by simp [← h]))
    refine ⟨hrx, hG _ _ hpy hea, (hG _ _ hpz heb).symm, hea, ?_, ?_⟩
    · simpa only [Sym2.eq_swap] using heb
    · exact connectors_disjoint_self r.1 r.2.1 r.2.2 y z
        (by simpa [hrx] using hyx) hya hyb (by simpa [hrx] using hzx) hza hzb

end PartitionedTriangleAbsorption.RootQuotaPackingStage124
