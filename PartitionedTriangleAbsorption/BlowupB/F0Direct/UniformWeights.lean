/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.GeometryDeletion
public import PartitionedTriangleAbsorption.F0RigidBoost
public import PartitionedTriangleAbsorption.IntegerCertificate.Combination

@[expose] public section

/-!
# Uniform physical seed weights

There is one third vertex per physical triangle through a fixed edge.  The
upper and lower counts use the actual crossing adjacency; no complete-cross
replacement occurs in this module.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks TypedNibble TypedLoadNecessity
open TypedLoadFamilies F0RigidBoost

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thirdSet (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset V :=
  univ.filter fun w => G.Adj u w ∧ G.Adj v w ∧ ¬ (p u=p v ∧ p v=p w)

theorem triple_F0_iff (a b c : Fin 2) :
    ({a,b,c}:Multiset (Fin 2)) ∈ F0 ↔ ¬ (a=b ∧ b=c) := by
  revert a b c
  decide

theorem thirdSet_image (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    (thirdSet p G u v).image (fun w => ({u,v,w}:Finset V)) =
      (copies p F0 G).filter (fun S => s(u,v) ∈ triEdges S) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hS
    obtain ⟨huw,hvw,hcol⟩ := (mem_filter.mp hw).2
    apply mem_filter.mpr
    refine ⟨mem_copies_iff.mpr (IntegerCertificate.isCopy_of_adj huv huw hvw hcol),?_⟩
    exact mem_triEdges_mk.mpr ⟨by simp,by simp,huv.ne⟩
  · intro hS
    obtain ⟨hSc,huvS⟩ := mem_filter.mp hS
    have hc := mem_copies_iff.mp hSc
    obtain ⟨hu,hv,_⟩ := mem_triEdges_mk.mp huvS
    have hp : ({u,v}:Finset V) ⊆ S := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl <;> assumption
    have hrem : (S \ {u,v}).card = 1 := by
      rw [card_sdiff_of_subset hp,hc.1.card_eq,card_pair huv.ne]
    obtain ⟨w,hw⟩ := card_eq_one.mp hrem
    have hwrem : w ∈ S \ {u,v} := hw.symm ▸ mem_singleton_self _
    obtain ⟨hwS,hwn⟩ := mem_sdiff.mp hwrem
    have hwu : w ≠ u := by intro he; apply hwn; simp [he]
    have hwv : w ≠ v := by intro he; apply hwn; simp [he]
    have htri : ({u,v,w}:Finset V) = S := by
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert,mem_singleton] at hx
        rcases hx with rfl|rfl|rfl <;> assumption
      · rw [hc.1.card_eq]
        simp [huv.ne,hwu.symm,hwv.symm]
    have hcopy : IsCopy p F0 G {u,v,w} := htri.symm ▸ hc
    have hadj := SimpleGraph.is3Clique_triple_iff.mp hcopy.1
    have hcol := hcopy.2
    rw [map_three p huv.ne hadj.2.1.ne hadj.2.2.ne] at hcol
    refine mem_image.mpr ⟨w,mem_filter.mpr ⟨mem_univ _,hadj.2.1,hadj.2.2,
      (triple_F0_iff _ _ _).mp hcol⟩,htri⟩

theorem count_copies_through_edge (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    ((copies p F0 G).filter (fun S => s(u,v) ∈ triEdges S)).card = (thirdSet p G u v).card := by
  classical
  rw [← thirdSet_image p G huv]
  apply card_image_of_injOn
  intro w hw z hz he
  have hw' := (mem_filter.mp hw).2
  change ({u,v,w}:Finset V)=({u,v,z}:Finset V) at he
  have hm : w ∈ ({u,v,z}:Finset V) := by rw [← he]; simp
  simp only [mem_insert,mem_singleton] at hm
  rcases hm with h|h|h
  · exact False.elim (hw'.1.ne h.symm)
  · exact False.elim (hw'.2.1.ne h.symm)
  · exact h

theorem thirdSet_internal (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (hc : p u=p v) :
    thirdSet p G u v = commonPart p G (other0 (p u)) u v := by
  classical
  ext w
  simp only [thirdSet,mem_filter,mem_univ,true_and,mem_commonPart]
  have hi := other0_ne (p u)
  have he := eq_or_eq_other0 (p u) (p w)
  constructor
  · rintro ⟨hu,hv,hcol⟩
    refine ⟨?_,hu,hv⟩
    rcases he with he|he
    · exact False.elim (hcol ⟨hc,hc.symm.trans he.symm⟩)
    · exact he
  · rintro ⟨hw,hu,hv⟩
    refine ⟨hu,hv,?_⟩
    rintro ⟨_,hv'⟩
    exact hi (hw.symm.trans (hv'.symm.trans hc.symm))

theorem thirdSet_cross (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (hc : p u≠p v) :
    thirdSet p G u v = commonPart p G (p u) u v ∪ commonPart p G (p v) u v := by
  classical
  ext w
  simp only [thirdSet,mem_filter,mem_univ,true_and,mem_union,mem_commonPart]
  have he : p w=p u ∨ p w=p v := by
    have hall : ∀ a b c : Fin 2, a≠b → c=a ∨ c=b := by decide
    exact hall _ _ _ hc
  tauto

theorem HostHyp.thirdSet_bounds {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {α ε : ℝ} (h : HostHyp p G α ε) (he : 0≤ε) (u v : V) :
    (1/2-5*ε)*Fintype.card V ≤ ((thirdSet p G u v).card:ℝ) ∧
      ((thirdSet p G u v).card:ℝ) ≤ (1/2+2*ε)*Fintype.card V := by
  classical
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hen := mul_nonneg he hn
  have hcard : ∀ i, (commonPart p G i u v).card ≤ (partSet p i).card := by
    intro i
    apply card_le_card
    intro w hw
    exact mem_partSet.mpr (mem_commonPart.mp hw).1
  have hbudget : ∀ i, (partDeg p G i u:ℝ)+partDeg p G i v ≤
      (partSet p i).card+(commonPart p G i u v).card := by
    intro i
    exact_mod_cast commonPart_card_budget p G i u v
  by_cases hc : p u=p v
  · rw [thirdSet_internal p G hc]
    have hu := h.cross_lower u
    have hv := h.cross_lower v
    rw [← hc] at hv
    have hp := h.part_upper (other0 (p u))
    have hb := hbudget (other0 (p u))
    have hupper : ((commonPart p G (other0 (p u)) u v).card:ℝ) ≤
        (partSet p (other0 (p u))).card := by exact_mod_cast hcard _
    constructor <;> nlinarith
  · rw [thirdSet_cross p G hc, card_union_of_disjoint]
    · push_cast
      have hU := h.internal_lower u
      have hV := h.internal_lower v
      have hU' := h.cross_to_lower u (p v) hc
      have hV' := h.cross_to_lower v (p u) (Ne.symm hc)
      have hpu := h.part_upper (p u)
      have hpv := h.part_upper (p v)
      have hbU := hbudget (p u)
      have hbV := hbudget (p v)
      have hcu : ((commonPart p G (p u) u v).card:ℝ) ≤ partDeg p G (p u) u := by
        apply Nat.cast_le.mpr
        apply card_le_card
        intro w hw
        have hh := mem_commonPart.mp hw
        exact mem_partNbrs.mpr ⟨hh.1,hh.2.1⟩
      have hcv : ((commonPart p G (p v) u v).card:ℝ) ≤ partDeg p G (p v) v := by
        apply Nat.cast_le.mpr
        apply card_le_card
        intro w hw
        have hh := mem_commonPart.mp hw
        exact mem_partNbrs.mpr ⟨hh.1,hh.2.2⟩
      have hUhi := h.internal_upper u
      have hVhi := h.internal_upper v
      constructor <;> nlinarith
    · apply disjoint_left.mpr
      intro w hu hv
      exact hc ((mem_commonPart.mp hu).1.symm.trans (mem_commonPart.mp hv).1)

noncomputable def seedWeight {V : Type*} [Fintype V] (ε : ℝ) : Finset V → ℝ :=
  fun _ => 2/((1+4*ε)*Fintype.card V)

theorem HostHyp.seed_bounds {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {α ε : ℝ} (h : HostHyp p G α ε) (he : 0≤ε) (he1 : ε≤1/4)
    (hn : 0 < Fintype.card V) :
    (∀ S : Finset V, 1/(Fintype.card V:ℝ) ≤ seedWeight ε S ∧
      seedWeight ε S ≤ 2/Fintype.card V) ∧
    ∀ e ∈ G.edgeFinset, 1-14*ε ≤ edgeLoad p F0 G (seedWeight ε) e ∧
      edgeLoad p F0 G (seedWeight ε) e ≤ 1 := by
  classical
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (0:ℝ) < (1+4*ε)*Fintype.card V := by positivity
  constructor
  · intro S
    unfold seedWeight
    constructor
    · apply (div_le_div_iff₀ hnR hd).mpr
      nlinarith [mul_le_mul_of_nonneg_right he1 hnR.le]
    · apply (div_le_div_iff₀ hd hnR).mpr
      nlinarith [mul_nonneg he hnR.le]
  · intro e heG
    induction e using Sym2.ind with
    | _ u v =>
      have hadj := SimpleGraph.mem_edgeFinset.mp heG
      have hb := h.thirdSet_bounds he u v
      have heq : edgeLoad p F0 G (seedWeight ε) s(u,v) =
          (thirdSet p G u v).card * (2/((1+4*ε)*Fintype.card V)) := by
        simp only [edgeLoad,seedWeight,sum_const,nsmul_eq_mul,count_copies_through_edge p G hadj]
      rw [heq]
      constructor
      · rw [← mul_div_assoc]
        apply (le_div_iff₀ hd).mpr
        nlinarith [mul_nonneg he hnR.le, sq_nonneg ε,
          mul_nonneg (sq_nonneg ε) hnR.le]
      · rw [← mul_div_assoc]
        apply (div_le_iff₀ hd).mpr
        nlinarith

#print axioms count_copies_through_edge
#print axioms HostHyp.thirdSet_bounds
#print axioms HostHyp.seed_bounds

end PartitionedTriangleAbsorption.BlowupB.F0Direct
