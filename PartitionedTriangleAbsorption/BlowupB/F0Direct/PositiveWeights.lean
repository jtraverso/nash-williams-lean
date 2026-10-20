/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.UniformWeights

@[expose] public section

/-!
# Positive exact physical weights from the balanced right inverse

The defect of the uniform seed has zero balance because the original graph
is integrally divisible.  Correcting it once therefore gives exact loads;
there is no limiting argument and no residual-error hypothesis.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks TypedNibble TypedLoadNecessity TypedLoadFamilies F0RigidBoost

variable {V : Type*} [Fintype V] [DecidableEq V]

def ExactWeights (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℝ) : Prop :=
  ∃ φ : Finset V → ℝ,
    (∀ S, IsCopy p F0 G S → 0≤φ S ∧ φ S≤b/Fintype.card V) ∧
    ∀ e ∈ G.edgeFinset, edgeLoad p F0 G φ e=1

theorem gFun_sum_of_isIntDiv (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiv : IsIntDiv p F0 G.edgeFinset) : ∑ e ∈ G.edgeFinset, gFun p e=0 := by
  have hh := annihilator_of_isIntDiv hdiv annihilates_F0
  unfold gFun
  rw [← Int.cast_sum, ← pairFun_edgeVec, hh, Int.cast_zero]

theorem HostHyp.exactWeights_of_inverse
    {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {a ε K : ℝ} (h : HostHyp p G a ε)
    (hε : 0≤ε) (hε1 : ε≤1/4) (hn : 0<Fintype.card V)
    (hsmall : 14*K*ε≤1) (hdiv : IsIntDiv p F0 G.edgeFinset)
    (hinv : HasBoundedBalancedInverse p G K) : ExactWeights p G 4 := by
  classical
  obtain ⟨hw,hl⟩ := h.seed_bounds hε hε1 hn
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  let x : Sym2 V → ℝ := fun e => 1-edgeLoad p F0 G (seedWeight ε) e
  have hx : ∀ e∈G.edgeFinset, |x e|≤14*ε := by
    intro e he
    have hh := hl e he
    dsimp [x]
    rw [abs_le]
    constructor <;> linarith
  have hbal : ∑ e∈G.edgeFinset, gFun p e*x e=0 := by
    have hg := gFun_sum_of_isIntDiv p G hdiv
    have hl := annihilator_load_identity p F0 G (seedWeight ε) annihilates_F0
    change (∑ e∈G.edgeFinset, gFun p e*edgeLoad p F0 G (seedWeight ε) e)=0 at hl
    simp only [x,mul_sub,mul_one,sum_sub_distrib,hg,hl,sub_self]
  obtain ⟨η,hηload,hηbound⟩ := hinv x (14*ε) (by positivity) hx hbal
  refine ⟨fun S=>seedWeight ε S+η S,?_,?_⟩
  · intro S hS
    have hs := hw S
    have hh := hηbound S (mem_copies_iff.mpr hS)
    have hcap : K*(14*ε)/Fintype.card V ≤ 1/(Fintype.card V:ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      nlinarith
    have hη := abs_le.mp (hh.trans hcap)
    have hn0 : (0:ℝ)≤1/(Fintype.card V:ℝ) := by positivity
    dsimp
    simp only [div_eq_mul_inv,one_mul] at hs hη hn0 ⊢
    constructor <;> linarith
  · intro e he
    rw [edgeLoad_add,hηload e he]
    dsimp [x]
    ring

#print axioms gFun_sum_of_isIntDiv
#print axioms HostHyp.exactWeights_of_inverse

end PartitionedTriangleAbsorption.BlowupB.F0Direct
