/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.GeometryDeletion
public import PartitionedTriangleAbsorption.SignedHinge.Main

@[expose] public section

/-!
# Bounded terminals and their use in the private ledger

The signed-certificate consumer is invoked on the actual kept graph.  The
abstract `LocalTerminal` declaration is an intermediate contract, not an
assertion of existence.  Its geometric producer is supplied separately.
-/

universe u

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks SignedHinge SignedCertificate PhysicalHingeSupply
open AntiEdgeSelection

variable {V : Type u} [Fintype V] [DecidableEq V]

def terminalCost (m : ℕ) : ℕ := 310*(126*m)

def LocalTerminal (a e : ℝ) (N m C : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
    ∀ (p : W → Fin 2) (G : SimpleGraph W) [DecidableRel G.Adj],
      HostHyp p G a e →
      ∀ P : Finset (Sym2 W), P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F0 P →
        ∃ A : Finset (Sym2 W), A ⊆ G.edgeFinset ∧ Disjoint A P ∧
          HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ A.card ≤ C

theorem terminal_of_signed_certificate
    (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (m : ℕ) (hparts : ∀ i, ∃ v, p v=i)
    (hanti : AntiEdgeful p F0 G (1/8)) (hhinge : HingeSupply p F0 G β 8)
    (hlarge : (41*(126*m)+1:ℝ) < Fintype.card V/8)
    (hlarge' : (2:ℝ)^36*(41*(126*m)+1) < β*Fintype.card V)
    (P : Finset (Sym2 V)) (hPm : P.card ≤ m)
    {ι : Type*} [Fintype ι] (t : ι → Finset V) (c : ι → ℤ)
    (hcert : IsSignedCert p G P t c) (hweight : certWeight c ≤ 126*P.card) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A P ∧
      HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ A.card ≤ terminalCost m := by
  classical
  have hK : certWeight c ≤ ((126*m:ℕ):ℤ) := by
    have hm : (P.card:ℤ) ≤ m := by exact_mod_cast hPm
    push_cast
    nlinarith
  have hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ vertSet P := by
    intro e he v hv
    exact mem_filter.mpr ⟨mem_univ _,e,he,hv⟩
  have hZ : (vertSet P).card ≤ 3*(126*m) := by
    have := card_vertSet_le P
    omega
  have hαM : (absorberBudget 8 (126*m):ℝ) < (1/8:ℝ)*Fintype.card V := by
    simp only [absorberBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    nlinarith
  have hβM : (2 ^ Nat.choose (8+1) 2:ℝ)*absorberBudget 8 (126*m) < β*Fintype.card V := by
    have hc36 : Nat.choose (8+1) 2 = 36 := by decide
    rw [hc36]
    simp only [absorberBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    nlinarith
  obtain ⟨A,Q,hAG,_,hPA,_,_,_,_,hA,hAP,_,hAc,_⟩ :=
    absorber_of_budget (1/8) β 8 (126*m) p G hparts hanti hhinge P t c
      (vertSet P) hcert hK hPZ hZ hαM hβM
  refine ⟨A,hAG,hPA.symm,hA,hAP,?_⟩
  have hc36 : Nat.choose (8+1) 2 = 36 := by decide
  simpa [absorberConst,terminalCost,hc36] using hAc

theorem keptTerminal_of_local
    {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {a e ε η δ : ℝ} {N m C : ℕ}
    (hlocal : LocalTerminal.{u} a e N m C) (h : HostHyp p G (2*a) ε)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/3)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hη1 : η ≤ 1)
    (hηa : η ≤ a/100) (hδa : δ ≤ a/100)
    (he : 2*(ε+η+δ) ≤ e) (hN : 2*N ≤ Fintype.card V) :
    KeptTerminal p G m C (δ*Fintype.card V) (η*Fintype.card V) := by
  classical
  intro Keep hmiss B hB P hPG hPm hPdiv
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have horder : ((univ \ Keep).card:ℝ)+Fintype.card {v : V // v ∈ Keep} = Fintype.card V := by
    exact_mod_cast kept_order Keep
  have hnR : 2*(N:ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hN' : N ≤ Fintype.card {v : V // v ∈ Keep} := by
    have hmiss' : ((univ \ Keep).card:ℝ) ≤ Fintype.card V/2 := by
      nlinarith [mul_le_mul_of_nonneg_right hη1 hn]
    have : (N:ℝ) ≤ Fintype.card {v : V // v ∈ Keep} := by linarith
    exact_mod_cast this
  have hkept := h.kept ha hε hε1 hη hδ hη1 hηa hδa Keep B hmiss hB
  exact hlocal _ hN' _ _ (hkept.mono le_rfl he) P hPG hPm hPdiv

#print axioms terminal_of_signed_certificate
#print axioms keptTerminal_of_local

end PartitionedTriangleAbsorption.BlowupB.F0Direct
