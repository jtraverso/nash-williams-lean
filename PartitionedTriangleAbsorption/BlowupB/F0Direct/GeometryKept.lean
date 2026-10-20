/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.GeometryBounds
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.PrivatePlacement
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.EditStability

@[expose] public section

/-!
# Degree geometry on the kept vertex subtype

Both kinds of deletion are physical.  The host need not be divisible.  The
nonextremal part is transported separately; this file proves all size and
degree estimates without replacing the order of the induced host by the old
order.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply AntiEdgeSelection PhysicalHingeSupply TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def removedNbrs (B : Finset (Sym2 V)) (u : V) : Finset V :=
  univ.filter fun v => s(u,v) ∈ B

theorem removedNbrs_card (B : Finset (Sym2 V)) (u : V) :
    (removedNbrs B u).card ≤ incidentLoad B u := by
  classical
  apply card_le_card_of_injOn (fun v => s(u,v))
  · intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).2, Sym2.mem_mk_left _ _⟩
  · intro v hv w hw he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.2
    · exact he.2.trans he.1

theorem kept_order (Keep : Finset V) :
    (univ \ Keep).card + Fintype.card {v : V // v ∈ Keep} = Fintype.card V := by
  rw [Fintype.card_coe, card_sdiff_of_subset (subset_univ _), card_univ]
  exact Nat.sub_add_cancel (card_le_univ _)

theorem partSet_kept_map (p : V → Fin 2) (Keep : Finset V) (i : Fin 2) :
    (partSet (fun v : {v : V // v ∈ Keep} => p v.val) i).map
      (Function.Embedding.subtype _) = partSet p i ∩ Keep := by
  ext v
  simp only [mem_map, mem_partSet, mem_inter]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,x.2⟩
  · rintro ⟨hp,hk⟩
    exact ⟨⟨v,hk⟩,hp,rfl⟩

theorem partNbrs_kept_map (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Keep : Finset V) (B : Finset (Sym2 V)) (i : Fin 2)
    (x : {v : V // v ∈ Keep}) :
    (partNbrs (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B) i x).map
      (Function.Embedding.subtype _) = (partNbrs p G i x.val ∩ Keep) \ removedNbrs B x.val := by
  classical
  ext v
  simp only [mem_map, mem_partNbrs, mem_sdiff, mem_inter, removedNbrs, mem_filter,
    mem_univ, true_and]
  constructor
  · rintro ⟨y,⟨hp,hg⟩,rfl⟩
    obtain ⟨hg,hb⟩ := (keptGraph_adj G Keep B x y).mp hg
    exact ⟨⟨⟨hp,hg⟩,y.2⟩,hb⟩
  · rintro ⟨⟨⟨hp,hg⟩,hk⟩,hb⟩
    exact ⟨⟨v,hk⟩,⟨hp,(keptGraph_adj G Keep B x ⟨v,hk⟩).mpr ⟨hg,hb⟩⟩,rfl⟩

theorem partSet_kept_loss (p : V → Fin 2) (Keep : Finset V) (i : Fin 2) :
    (partSet p i).card ≤
      (partSet (fun v : {v : V // v ∈ Keep} => p v.val) i).card + (univ \ Keep).card := by
  have hs : partSet p i ⊆ (partSet p i ∩ Keep) ∪ (univ \ Keep) := by
    intro v hv
    by_cases hk : v ∈ Keep
    · exact mem_union_left _ (mem_inter.mpr ⟨hv,hk⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,hk⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  rw [← partSet_kept_map p Keep i, card_map] at hc
  exact hc

theorem partDeg_kept_bounds (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Keep : Finset V) (B : Finset (Sym2 V)) (i : Fin 2)
    (x : {v : V // v ∈ Keep}) :
    partDeg (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B) i x ≤
      partDeg p G i x.val ∧
    partDeg p G i x.val ≤
      partDeg (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B) i x +
      (univ \ Keep).card + incidentLoad B x.val := by
  classical
  have hm := partNbrs_kept_map p G Keep B i x
  have hc : (partNbrs (fun v : {v : V // v ∈ Keep} => p v.val)
      (keptGraph G Keep B) i x).card =
      ((partNbrs p G i x.val ∩ Keep) \ removedNbrs B x.val).card := by
    rw [← hm, card_map]
  constructor
  · change (partNbrs _ _ _ _).card ≤ (partNbrs _ _ _ _).card
    rw [hc]
    exact card_le_card (sdiff_subset.trans inter_subset_left)
  · have hs : partNbrs p G i x.val ⊆
        (((partNbrs p G i x.val ∩ Keep) \ removedNbrs B x.val) ∪ (univ \ Keep)) ∪
          removedNbrs B x.val := by
      intro v hv
      by_cases hb : v ∈ removedNbrs B x.val
      · exact mem_union_right _ hb
      · apply mem_union_left
        by_cases hk : v ∈ Keep
        · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hv,hk⟩,hb⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,hk⟩)
    have h1 := (card_le_card hs).trans (card_union_le _ _)
    have h2 := card_union_le ((partNbrs p G i x.val ∩ Keep) \ removedNbrs B x.val)
      (univ \ Keep)
    have h3 := removedNbrs_card B x.val
    unfold partDeg
    omega

theorem HostHyp.kept_of_nonextreme
    {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {α α' ε η δ : ℝ} (h : HostHyp p G α ε)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hη1 : η ≤ 1)
    (Keep : Finset V) (B : Finset (Sym2 V))
    (hmiss : ((univ \ Keep).card : ℝ) ≤ η * Fintype.card V / 2)
    (hB : DegBounded B (δ * Fintype.card V))
    (hext : ∃ i, Nonextreme (keptGraph G Keep B)
      (partSet (fun v : {v : V // v ∈ Keep} => p v.val) i) α') :
    HostHyp (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B)
      α' (2 * (ε + η + δ)) := by
  classical
  let n : ℝ := Fintype.card V
  let n' : ℝ := Fintype.card {v : V // v ∈ Keep}
  let r : ℝ := (univ \ Keep).card
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hn' : 0 ≤ n' := Nat.cast_nonneg _
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have horder : r + n' = n := by
    dsimp [r,n',n]
    exact_mod_cast kept_order Keep
  have hmiss' : r ≤ η*n/2 := hmiss
  have hn2 : n ≤ 2*n' := by nlinarith [mul_le_mul_of_nonneg_right hη1 hn]
  have hq : 0 ≤ ε+η+δ := by positivity
  have hscale : (ε+η+δ)*n ≤ 2*(ε+η+δ)*n' := by
    nlinarith [mul_le_mul_of_nonneg_left hn2 hq]
  have hepsn : 0 ≤ ε*n := mul_nonneg hε hn
  have hetan : 0 ≤ η*n := mul_nonneg hη hn
  have hdeln : 0 ≤ δ*n := mul_nonneg hδ hn
  refine ⟨?_, ?_, ?_, ?_, hext⟩
  · intro i
    have hs := h.part_size i
    have hl : ((partSet p i).card : ℝ) ≤
        (partSet (fun v : {v : V // v ∈ Keep} => p v.val) i).card + r := by
      dsimp [r]
      exact_mod_cast partSet_kept_loss p Keep i
    change (1-ε)*n/2 ≤ _ at hs
    change (1-2*(ε+η+δ))*n'/2 ≤ _
    nlinarith
  · intro x
    have hl := h.internal_lower x.val
    have hd : (partDeg p G (p x.val) x.val : ℝ) ≤
        partDeg (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B) (p x.val) x +
          r + incidentLoad B x.val := by
      dsimp [r]
      exact_mod_cast (partDeg_kept_bounds p G Keep B (p x.val) x).2
    have hb := hB x.val
    change (1/4-ε)*n ≤ _ at hl
    change (incidentLoad B x.val : ℝ) ≤ δ*n at hb
    change (1/4-2*(ε+η+δ))*n' ≤ _
    nlinarith
  · intro x
    have hu := h.internal_upper x.val
    have hd : (partDeg (fun v : {v : V // v ∈ Keep} => p v.val)
        (keptGraph G Keep B) (p x.val) x : ℝ) ≤ partDeg p G (p x.val) x.val := by
      exact_mod_cast (partDeg_kept_bounds p G Keep B (p x.val) x).1
    change _ ≤ (1/4+ε)*n at hu
    change _ ≤ (1/4+2*(ε+η+δ))*n'
    nlinarith
  · intro x
    have hl := h.cross_lower x.val
    have hd : (partDeg p G (other0 (p x.val)) x.val : ℝ) ≤
        partDeg (fun v : {v : V // v ∈ Keep} => p v.val) (keptGraph G Keep B)
          (other0 (p x.val)) x + r + incidentLoad B x.val := by
      dsimp [r]
      exact_mod_cast (partDeg_kept_bounds p G Keep B (other0 (p x.val)) x).2
    have hb := hB x.val
    change (1/2-ε)*n ≤ _ at hl
    change (incidentLoad B x.val : ℝ) ≤ δ*n at hb
    change (1/2-2*(ε+η+δ))*n' ≤ _
    nlinarith

#print axioms partDeg_kept_bounds
#print axioms HostHyp.kept_of_nonextreme

end PartitionedTriangleAbsorption.BlowupB.F0Direct
