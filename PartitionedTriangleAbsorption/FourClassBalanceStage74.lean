/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

/-! # Physical boundary balance, including sparse deleted hosts

Every surviving triangle contributes one edge to each opposite-pair sum.
Masking the tuple weights by the actual copies of a subgraph proves that
restriction preserves the balanced demand space; it is not assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity

theorem triple_swap_tail {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) :
    (∑ a, ∑ c, ∑ b, f a b c) = ∑ a, ∑ b, ∑ c, f a b c := by
  apply sum_congr rfl
  intro a _
  rw [sum_comm]

theorem triple_rotate {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) :
    (∑ b, ∑ c, ∑ a, f a b c) = ∑ a, ∑ b, ∑ c, f a b c := by
  calc
    (∑ b, ∑ c, ∑ a, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := by
      apply sum_congr rfl
      intro b _
      rw [sum_comm]
    _ = ∑ a, ∑ b, ∑ c, f a b c := sum_comm

theorem physical_boundary_balanced {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (w : TriangleData A B C D) : RawBalanced (physicalBoundary w) := by
  simp only [RawBalanced, physicalBoundary, sum_add_distrib]
  rw [triple_rotate w.acd, triple_rotate w.bcd,
    triple_swap_tail w.abc, triple_rotate w.abd, triple_swap_tail w.bcd,
    triple_swap_tail w.abd, triple_swap_tail w.acd, triple_rotate w.abc]
  constructor <;> ring

variable {V : Type*} [DecidableEq V]

open scoped Classical in
noncomputable def masked (p : V → Fin 4) (J : SimpleGraph V)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) :
    TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3) where
  abc a b c := if IsCopy p TypedApplicationLinks.F3 J {a.val,b.val,c.val}
    then w.abc a b c else 0
  abd a b d := if IsCopy p TypedApplicationLinks.F3 J {a.val,b.val,d.val}
    then w.abd a b d else 0
  acd a c d := if IsCopy p TypedApplicationLinks.F3 J {a.val,c.val,d.val}
    then w.acd a c d else 0
  bcd b c d := if IsCopy p TypedApplicationLinks.F3 J {b.val,c.val,d.val}
    then w.bcd b c d else 0

theorem masked_zero (p : V → Fin 4) (J : SimpleGraph V)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (i : TriIndex p) (hi : ¬ IsCopy p TypedApplicationLinks.F3 J (support p i)) :
    indexWeight p (masked p J w) i = 0 := by
  rcases i with ⟨a,b,c⟩ | (⟨a,b,d⟩ | (⟨a,c,d⟩ | ⟨b,c,d⟩))
  all_goals simp only [support] at hi; simp only [indexWeight, masked, ite_eq_right hi]

theorem masked_load_eq [Fintype V] (p : V → Fin 4) (G J : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (e : Sym2 V) :
    edgeLoad p TypedApplicationLinks.F3 J (physicalWeights p (masked p J w)) e =
      edgeLoad p TypedApplicationLinks.F3 G (physicalWeights p (masked p J w)) e := by
  unfold physicalWeights
  rw [CopyPushforwardStage74.load_push_of_zero_outside p TypedApplicationLinks.F3 J
    (support p) _ (masked_zero p J w),
    CopyPushforwardStage74.load_push p TypedApplicationLinks.F3 G
      (support p) (support_copy p G hG)]

theorem masked_coordinates [Fintype V] (p : V → Fin 4) (G J : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) :
    demandCoordinates p (edgeLoad p TypedApplicationLinks.F3 J
      (physicalWeights p (masked p J w))) = physicalBoundary (masked p J w) := by
  change EdgeData.mk _ _ _ _ _ _ = EdgeData.mk _ _ _ _ _ _
  congr 1
  · funext u v
    rw [masked_load_eq p G J hG, load_ab p G hG]
    rfl
  · funext u v
    rw [masked_load_eq p G J hG, load_ac p G hG]
    rfl
  · funext u v
    rw [masked_load_eq p G J hG, load_ad p G hG]
    rfl
  · funext u v
    rw [masked_load_eq p G J hG, load_bc p G hG]
    rfl
  · funext u v
    rw [masked_load_eq p G J hG, load_bd p G hG]
    rfl
  · funext u v
    rw [masked_load_eq p G J hG, load_cd p G hG]
    rfl

theorem masked_load_balanced [Fintype V] (p : V → Fin 4) (G J : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) :
    RawBalanced (demandCoordinates p (edgeLoad p TypedApplicationLinks.F3 J
      (physicalWeights p (masked p J w)))) := by
  rw [masked_coordinates p G J hG]
  exact physical_boundary_balanced _

open scoped Classical in
theorem masked_index (p : V → Fin 4) (J : SimpleGraph V)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (i : TriIndex p) :
    indexWeight p (masked p J w) i =
      if IsCopy p TypedApplicationLinks.F3 J (support p i)
        then indexWeight p w i else 0 := by
  classical
  rcases i with ⟨a,b,c⟩ | (⟨a,b,d⟩ | (⟨a,c,d⟩ | ⟨b,c,d⟩)) <;> rfl

open scoped Classical in
theorem masked_weights [Fintype V] (p : V → Fin 4) (J : SimpleGraph V)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (s : Finset V) :
    physicalWeights p (masked p J w) s =
      if IsCopy p TypedApplicationLinks.F3 J s then physicalWeights p w s else 0 := by
  classical
  unfold physicalWeights CopyPushforwardStage74.push
  simp_rw [masked_index]
  by_cases hs : IsCopy p TypedApplicationLinks.F3 J s
  · simp only [ite_eq_left hs]
    apply sum_congr rfl
    intro i _
    by_cases hi : support p i = s
    · simp [hi,hs]
    · simp [hi]
  · simp only [ite_eq_right hs]
    apply sum_eq_zero
    intro i _
    by_cases hi : support p i = s
    · simp [hi,hs]
    · simp [hi]

theorem masked_load_self [Fintype V] (p : V → Fin 4) (J : SimpleGraph V)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3))
    (e : Sym2 V) :
    edgeLoad p TypedApplicationLinks.F3 J (physicalWeights p (masked p J w)) e =
      edgeLoad p TypedApplicationLinks.F3 J (physicalWeights p w) e := by
  unfold edgeLoad
  apply sum_congr rfl
  intro s hs
  have hc : IsCopy p TypedApplicationLinks.F3 J s :=
    TypedNibble.mem_copies_iff.mp (mem_filter.mp hs).1
  rw [masked_weights, ite_eq_left hc]

theorem physical_load_balanced [Fintype V] (p : V → Fin 4) (G J : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) :
    RawBalanced (demandCoordinates p (edgeLoad p TypedApplicationLinks.F3 J
      (physicalWeights p w))) := by
  have hh := masked_load_balanced p G J hG w
  have heq : edgeLoad p TypedApplicationLinks.F3 J (physicalWeights p (masked p J w)) =
      edgeLoad p TypedApplicationLinks.F3 J (physicalWeights p w) :=
    funext (masked_load_self p J w)
  rw [heq] at hh
  exact hh

theorem residual_balanced [Fintype V] (p : V → Fin 4) (G J : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (d : Sym2 V → ℝ) (hd : RawBalanced (demandCoordinates p d))
    (w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3)) :
    RawBalanced (demandCoordinates p (fun e => d e -
      edgeLoad p TypedApplicationLinks.F3 J (physicalWeights p w) e)) := by
  have hl := physical_load_balanced p G J hG w
  simp only [RawBalanced, demandCoordinates, sum_sub_distrib] at hd hl ⊢
  constructor <;> linarith [hd.1,hd.2,hl.1,hl.2]

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
