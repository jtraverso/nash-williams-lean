/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CopyPushforwardStage74
public import PartitionedTriangleAbsorption.FourClassPhysicalStage73
public import PartitionedTriangleAbsorption.FourMoveWalkStage51
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Four-class tuples as physical copies

The indices are canonically ordered by their class labels. In particular,
permuting the three vertices does not create another indexed copy.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity

variable {V : Type*} [DecidableEq V]

abbrev Class (p : V → Fin 4) (i : Fin 4) := {v : V // p v = i}

abbrev TriIndex (p : V → Fin 4) :=
  (Class p 0 × Class p 1 × Class p 2) ⊕
  ((Class p 0 × Class p 1 × Class p 3) ⊕
  ((Class p 0 × Class p 2 × Class p 3) ⊕
   (Class p 1 × Class p 2 × Class p 3)))

def support (p : V → Fin 4) : TriIndex p → Finset V
  | .inl ⟨a,b,c⟩ => {a.val,b.val,c.val}
  | .inr (.inl ⟨a,b,d⟩) => {a.val,b.val,d.val}
  | .inr (.inr (.inl ⟨a,c,d⟩)) => {a.val,c.val,d.val}
  | .inr (.inr (.inr ⟨b,c,d⟩)) => {b.val,c.val,d.val}

def indexWeight (p : V → Fin 4)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) :
    TriIndex p → ℝ
  | .inl ⟨a,b,c⟩ => w.abc a b c
  | .inr (.inl ⟨a,b,d⟩) => w.abd a b d
  | .inr (.inr (.inl ⟨a,c,d⟩)) => w.acd a c d
  | .inr (.inr (.inr ⟨b,c,d⟩)) => w.bcd b c d

omit [DecidableEq V] in
theorem class_label (p : V → Fin 4) (i : Fin 4) (v : Class p i) :
    p v.val = i := v.property

omit [DecidableEq V] in
theorem class_ne {p : V → Fin 4} {i j : Fin 4} (hij : i ≠ j)
    (u : Class p i) (v : Class p j) : u.val ≠ v.val := by
  intro h
  exact hij (u.property.symm.trans ((congrArg p h).trans v.property))

theorem copy_triple (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (htype : ({i,j,k} : Multiset (Fin 4)) ∈ TypedApplicationLinks.F3)
    (a : Class p i) (b : Class p j) (c : Class p k) :
    IsCopy p TypedApplicationLinks.F3 G {a.val,b.val,c.val} := by
  apply FourMoveWalkStage51.copy_three
  · exact (hG _ _).mpr (by simpa only [class_label] using hij)
  · exact (hG _ _).mpr (by simpa only [class_label] using hik)
  · exact (hG _ _).mpr (by simpa only [class_label] using hjk)
  · simpa only [class_label] using htype

theorem support_copy (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v) (i : TriIndex p) :
    IsCopy p TypedApplicationLinks.F3 G (support p i) := by
  rcases i with ⟨a,b,c⟩ | (⟨a,b,d⟩ | (⟨a,c,d⟩ | ⟨b,c,d⟩))
  all_goals apply copy_triple p G hG <;> decide

theorem eq_of_mem_triple {p : V → Fin 4} {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k)
    (v a : Class p i) (b : Class p j) (c : Class p k)
    (h : v.val ∈ ({a.val,b.val,c.val} : Finset V)) : v = a := by
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h
  · exact Subtype.ext h
  · exact False.elim (class_ne hij v b h)
  · exact False.elim (class_ne hik v c h)

theorem triple_injective {p : V → Fin 4} {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (fun t : Class p i × Class p j × Class p k =>
      ({t.1.val,t.2.1.val,t.2.2.val} : Finset V)) := by
  rintro ⟨a,b,c⟩ ⟨a',b',c'⟩ h
  change ({a.val,b.val,c.val} : Finset V) = {a'.val,b'.val,c'.val} at h
  have ha : a = a' := eq_of_mem_triple hij hik a a' b' c'
    (by rw [← h]; simp)
  have hb : b = b' := eq_of_mem_triple hij.symm hjk b b' a' c'
    (by
      have hp : ({b'.val,a'.val,c'.val} : Finset V) = {a'.val,b'.val,c'.val} :=
        by ext x; simp [or_left_comm]
      rw [hp, ← h]
      simp)
  have hc : c = c' := eq_of_mem_triple hik.symm hjk.symm c c' a' b'
    (by
      have hp : ({c'.val,a'.val,b'.val} : Finset V) = {a'.val,b'.val,c'.val} :=
        by ext x; simp [or_comm, or_left_comm]
      rw [hp, ← h]
      simp)
  subst a'; subst b'; subst c'
  rfl

theorem support_injective (p : V → Fin 4) : Function.Injective (support p) := by
  rintro (⟨a,b,c⟩ | (⟨a,b,d⟩ | (⟨a,c,d⟩ | ⟨b,c,d⟩)))
    (⟨a',b',c'⟩ | (⟨a',b',d'⟩ | (⟨a',c',d'⟩ | ⟨b',c',d'⟩))) h
  · have ht := triple_injective (p := p) (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide)
      (a₁ := ⟨a,b,c⟩) (a₂ := ⟨a',b',c'⟩) h
    cases ht
    rfl
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,1,2} : Finset (Fin 4)) ≠ {0,1,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,1,2} : Finset (Fin 4)) ≠ {0,2,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,1,2} : Finset (Fin 4)) ≠ {1,2,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,1,3} : Finset (Fin 4)) ≠ {0,1,2}) hp)
  · have ht := triple_injective (p := p) (i := 0) (j := 1) (k := 3)
      (by decide) (by decide) (by decide)
      (a₁ := ⟨a,b,d⟩) (a₂ := ⟨a',b',d'⟩) h
    cases ht
    rfl
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,1,3} : Finset (Fin 4)) ≠ {0,2,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,1,3} : Finset (Fin 4)) ≠ {1,2,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,2,3} : Finset (Fin 4)) ≠ {0,1,2}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,2,3} : Finset (Fin 4)) ≠ {0,1,3}) hp)
  · have ht := triple_injective (p := p) (i := 0) (j := 2) (k := 3)
      (by decide) (by decide) (by decide)
      (a₁ := ⟨a,c,d⟩) (a₂ := ⟨a',c',d'⟩) h
    cases ht
    rfl
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({0,2,3} : Finset (Fin 4)) ≠ {1,2,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({1,2,3} : Finset (Fin 4)) ≠ {0,1,2}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({1,2,3} : Finset (Fin 4)) ≠ {0,1,3}) hp)
  · have hp := congrArg (Finset.image p) h
    simp only [support, image_insert, image_singleton, class_label] at hp
    exact False.elim ((by decide : ({1,2,3} : Finset (Fin 4)) ≠ {0,2,3}) hp)
  · have ht := triple_injective (p := p) (i := 1) (j := 2) (k := 3)
      (by decide) (by decide) (by decide)
      (a₁ := ⟨b,c,d⟩) (a₂ := ⟨b',c',d'⟩) h
    cases ht
    rfl

noncomputable def physicalWeights [Fintype V] (p : V → Fin 4)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) : Finset V → ℝ :=
  CopyPushforwardStage74.push (support p) (indexWeight p w)

theorem physicalWeights_bound [Fintype V] (p : V → Fin 4)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (W : ℝ) (hW : 0 ≤ W) (hw : TriangleBound w W) (s : Finset V) :
    |physicalWeights p w s| ≤ W := by
  apply CopyPushforwardStage74.push_bound _ (support_injective p) _ W hW
  rintro (⟨a,b,c⟩ | (⟨a,b,d⟩ | (⟨a,c,d⟩ | ⟨b,c,d⟩)))
  · exact hw.1 a b c
  · exact hw.2.1 a b d
  · exact hw.2.2.1 a c d
  · exact hw.2.2.2 b c d

theorem edge_mem12 {p : V → Fin 4} {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u a : Class p i) (v b : Class p j) (c : Class p k) :
    s(u.val,v.val) ∈ triEdges {a.val,b.val,c.val} ↔ u = a ∧ v = b := by
  rw [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨⟨hu,hv⟩,_⟩
    have hp : ({b.val,a.val,c.val} : Finset V) = {a.val,b.val,c.val} :=
      by ext x; simp [or_left_comm]
    exact ⟨eq_of_mem_triple hij hik u a b c hu,
      eq_of_mem_triple hij.symm hjk v b a c (by rw [hp]; exact hv)⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨by simp,by simp⟩,class_ne hij u v⟩

theorem edge_mem13 {p : V → Fin 4} {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u a : Class p i) (b : Class p j) (v c : Class p k) :
    s(u.val,v.val) ∈ triEdges {a.val,b.val,c.val} ↔ u = a ∧ v = c := by
  have hp : ({a.val,b.val,c.val} : Finset V) = {a.val,c.val,b.val} :=
    by ext x; simp [or_comm]
  rw [hp]
  exact edge_mem12 hik hij hjk.symm u a v c b

theorem edge_mem23 {p : V → Fin 4} {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Class p i) (u b : Class p j) (v c : Class p k) :
    s(u.val,v.val) ∈ triEdges {a.val,b.val,c.val} ↔ u = b ∧ v = c := by
  have hp : ({a.val,b.val,c.val} : Finset V) = {b.val,c.val,a.val} :=
    by ext x; simp [or_comm, or_left_comm]
  rw [hp]
  exact edge_mem12 hjk hij.symm hik.symm u b v c a

theorem edge_absent_left {p : V → Fin 4} {i j k l m : Fin 4}
    (hl : l ≠ i ∧ l ≠ j ∧ l ≠ k)
    (u : Class p l) (v : Class p m)
    (a : Class p i) (b : Class p j) (c : Class p k) :
    s(u.val,v.val) ∉ triEdges {a.val,b.val,c.val} := by
  intro h
  have hu := (mk_mem_sym2_iff.mp (mem_filter.mp h).1).1
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with hu | hu | hu
  · exact class_ne hl.1 u a hu
  · exact class_ne hl.2.1 u b hu
  · exact class_ne hl.2.2 u c hu

theorem edge_absent_right {p : V → Fin 4} {i j k l m : Fin 4}
    (hl : l ≠ i ∧ l ≠ j ∧ l ≠ k)
    (u : Class p m) (v : Class p l)
    (a : Class p i) (b : Class p j) (c : Class p k) :
    s(u.val,v.val) ∉ triEdges {a.val,b.val,c.val} := by
  simpa only [Sym2.eq_swap] using edge_absent_left hl v u a b c

theorem load_ab [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (u : Class p 0) (v : Class p 1) :
    edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p w) s(u.val,v.val) =
      (physicalBoundary w).ab u v := by
  classical
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
    (support p) (support_copy p G hG)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, support, indexWeight]
  simp only [
    edge_mem12 (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    edge_mem12 (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide),
    edge_absent_right (i := 0) (j := 2) (k := 3) (l := 1) (m := 0) (by decide),
    edge_absent_left (i := 1) (j := 2) (k := 3) (l := 0) (m := 1) (by decide), ite_false]
  simp [ite_and, physicalBoundary]

theorem load_ac [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (u : Class p 0) (v : Class p 2) :
    edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p w) s(u.val,v.val) =
      (physicalBoundary w).ac u v := by
  classical
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
    (support p) (support_copy p G hG)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, support, indexWeight]
  simp only [
    edge_mem13 (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    edge_absent_right (i := 0) (j := 1) (k := 3) (l := 2) (m := 0) (by decide),
    edge_mem12 (i := 0) (j := 2) (k := 3) (by decide) (by decide) (by decide),
    edge_absent_left (i := 1) (j := 2) (k := 3) (l := 0) (m := 2) (by decide), ite_false]
  simp [ite_and, physicalBoundary]

theorem load_ad [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (u : Class p 0) (v : Class p 3) :
    edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p w) s(u.val,v.val) =
      (physicalBoundary w).ad u v := by
  classical
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
    (support p) (support_copy p G hG)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, support, indexWeight]
  simp only [
    edge_absent_right (i := 0) (j := 1) (k := 2) (l := 3) (m := 0) (by decide),
    edge_mem13 (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide),
    edge_mem13 (i := 0) (j := 2) (k := 3) (by decide) (by decide) (by decide),
    edge_absent_left (i := 1) (j := 2) (k := 3) (l := 0) (m := 3) (by decide), ite_false]
  simp [ite_and, physicalBoundary]

theorem load_bc [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (u : Class p 1) (v : Class p 2) :
    edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p w) s(u.val,v.val) =
      (physicalBoundary w).bc u v := by
  classical
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
    (support p) (support_copy p G hG)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, support, indexWeight]
  simp only [
    edge_mem23 (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    edge_absent_right (i := 0) (j := 1) (k := 3) (l := 2) (m := 1) (by decide),
    edge_absent_left (i := 0) (j := 2) (k := 3) (l := 1) (m := 2) (by decide),
    edge_mem12 (i := 1) (j := 2) (k := 3) (by decide) (by decide) (by decide), ite_false]
  simp [ite_and, physicalBoundary]

theorem load_bd [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (u : Class p 1) (v : Class p 3) :
    edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p w) s(u.val,v.val) =
      (physicalBoundary w).bd u v := by
  classical
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
    (support p) (support_copy p G hG)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, support, indexWeight]
  simp only [
    edge_absent_right (i := 0) (j := 1) (k := 2) (l := 3) (m := 1) (by decide),
    edge_mem23 (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide),
    edge_absent_left (i := 0) (j := 2) (k := 3) (l := 1) (m := 3) (by decide),
    edge_mem13 (i := 1) (j := 2) (k := 3) (by decide) (by decide) (by decide), ite_false]
  simp [ite_and, physicalBoundary]

theorem load_cd [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (u : Class p 2) (v : Class p 3) :
    edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p w) s(u.val,v.val) =
      (physicalBoundary w).cd u v := by
  classical
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
    (support p) (support_copy p G hG)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, support, indexWeight]
  simp only [
    edge_absent_right (i := 0) (j := 1) (k := 2) (l := 3) (m := 2) (by decide),
    edge_absent_left (i := 0) (j := 1) (k := 3) (l := 2) (m := 3) (by decide),
    edge_mem23 (i := 0) (j := 2) (k := 3) (by decide) (by decide) (by decide),
    edge_mem23 (i := 1) (j := 2) (k := 3) (by decide) (by decide) (by decide), ite_false]
  simp [ite_and, physicalBoundary]

def demandCoordinates (p : V → Fin 4) (d : Sym2 V → ℝ) :
    EdgeData (Class p 0) (Class p 1) (Class p 2) (Class p 3) where
  ab a b := d s(a.val,b.val)
  ac a c := d s(a.val,c.val)
  ad a d' := d s(a.val,d'.val)
  bc b c := d s(b.val,c.val)
  bd b d' := d s(b.val,d'.val)
  cd c d' := d s(c.val,d'.val)

theorem load_eq_of_boundary [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (d : Sym2 V → ℝ) (hw : physicalBoundary w = demandCoordinates p d) :
    ∀ e ∈ G.edgeFinset, edgeLoad p TypedApplicationLinks.F3 G
      (physicalWeights p w) e = d e := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have hne : p u ≠ p v :=
      (hG u v).mp (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he))
    generalize hi : p u = i at hne
    generalize hj : p v = j at hne
    fin_cases i <;> fin_cases j
    · exact False.elim (hne rfl)
    · have hh := load_ab p G hG w ⟨u,hi⟩ ⟨v,hj⟩
      rw [hw] at hh
      simpa only [demandCoordinates] using hh
    · have hh := load_ac p G hG w ⟨u,hi⟩ ⟨v,hj⟩
      rw [hw] at hh
      simpa only [demandCoordinates] using hh
    · have hh := load_ad p G hG w ⟨u,hi⟩ ⟨v,hj⟩
      rw [hw] at hh
      simpa only [demandCoordinates] using hh
    · have hh := load_ab p G hG w ⟨v,hj⟩ ⟨u,hi⟩
      rw [hw] at hh
      simpa only [demandCoordinates, Sym2.eq_swap] using hh
    · exact False.elim (hne rfl)
    · have hh := load_bc p G hG w ⟨u,hi⟩ ⟨v,hj⟩
      rw [hw] at hh
      simpa only [demandCoordinates] using hh
    · have hh := load_bd p G hG w ⟨u,hi⟩ ⟨v,hj⟩
      rw [hw] at hh
      simpa only [demandCoordinates] using hh
    · have hh := load_ac p G hG w ⟨v,hj⟩ ⟨u,hi⟩
      rw [hw] at hh
      simpa only [demandCoordinates, Sym2.eq_swap] using hh
    · have hh := load_bc p G hG w ⟨v,hj⟩ ⟨u,hi⟩
      rw [hw] at hh
      simpa only [demandCoordinates, Sym2.eq_swap] using hh
    · exact False.elim (hne rfl)
    · have hh := load_cd p G hG w ⟨u,hi⟩ ⟨v,hj⟩
      rw [hw] at hh
      simpa only [demandCoordinates] using hh
    · have hh := load_ad p G hG w ⟨v,hj⟩ ⟨u,hi⟩
      rw [hw] at hh
      simpa only [demandCoordinates, Sym2.eq_swap] using hh
    · have hh := load_bd p G hG w ⟨v,hj⟩ ⟨u,hi⟩
      rw [hw] at hh
      simpa only [demandCoordinates, Sym2.eq_swap] using hh
    · have hh := load_cd p G hG w ⟨v,hj⟩ ⟨u,hi⟩
      rw [hw] at hh
      simpa only [demandCoordinates, Sym2.eq_swap] using hh
    · exact False.elim (hne rfl)

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
