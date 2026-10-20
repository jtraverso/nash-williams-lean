/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.FiniteTerminal
import PartitionedTriangleAbsorption.BlowupB.F0Direct.PositiveWeights
import PartitionedTriangleAbsorption.BlowupB.F0Direct.UniversalScales
import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveConstruction
import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDownConsumer

/-!
# Exact decomposition from the geometric producers

This module is a consumer with explicit producer arguments.  It fixes the
reserve, the complete refiner library and the absorber before any residue is
selected.  Both physical fractional weightings are produced on the graphs
to which the nibble is applied.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks TypedNibble TypedLoadNecessity AntiEdgeSelection
open StructuralF3General.PrivateFamily PaddedNibble.ReservePacking PaddedNibble.TypedCoverDown

set_option maxHeartbeats 2000000

def WeightProducer (a e : ℝ) (N : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
    ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
      HostHyp p G a e → IsIntDiv p F0 G.edgeFinset → ExactWeights p G 4

theorem reserve_scale_exists (C : ℕ) (hC : 1≤C) (δ η : ℝ) (hd : 0<δ) (hh : 0<η) :
    ∃ κ : ℝ, 0<κ ∧ 134217728*κ≤1 ∧ 524288*(C:ℝ)*κ≤δ ∧
      2097152*(C:ℝ)*κ≤1 ∧ 4194304*κ≤δ*η ∧ κ^2≤δ := by
  have hC0 : (0:ℝ)<C := by exact_mod_cast (show 0<C by omega)
  have hC1 : (1:ℝ)≤C := by exact_mod_cast hC
  let κ : ℝ := min (1/134217728) (min (δ/(524288*C))
    (min (1/(2097152*C)) (δ*η/4194304)))
  have hk : 0<κ := by dsimp [κ]; positivity
  have h1 : κ≤1/134217728 := min_le_left _ _
  have h2 : κ≤δ/(524288*C) := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : κ≤1/(2097152*C) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : κ≤δ*η/4194304 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hb2 : 524288*(C:ℝ)*κ≤δ := by
    have h2' := (le_div_iff₀ (by positivity : (0:ℝ)<524288*C)).mp h2
    nlinarith only [h2']
  have hb3 : 2097152*(C:ℝ)*κ≤1 := by
    have h3' := (le_div_iff₀ (by positivity : (0:ℝ)<2097152*C)).mp h3
    nlinarith only [h3']
  refine ⟨κ,hk,by linarith,hb2,hb3,by linarith,?_⟩
  have hk1 : κ≤1 := by linarith
  have hkc : κ≤(C:ℝ)*κ := by nlinarith only [mul_le_mul_of_nonneg_right hC1 hk.le]
  nlinarith only [hb2,hkc,hk,hk1]

theorem decomposition_from_producers (a e : ℝ) (ha : 0<a) (he : 0<e)
    (N0 C : ℕ) (hC : 1≤C) (hlocal : LocalTerminal.{0} a e N0 214 C)
    (hweights : WeightProducer a e N0) :
    ∃ ε : ℝ, 0<ε ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N≤Fintype.card V →
        ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
          HostHyp p G (2*a) ε → IsIntDiv p F0 G.edgeFinset → HasDecomp p F0 G.edgeFinset := by
  let d : ℝ := min (e/16) (min (a/1000) (1/1000))
  have hd : 0<d := by dsimp [d]; positivity
  have hde : d≤e/16 := min_le_left _ _
  have hda : d≤a/1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : d≤1/1000 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨κ,hk,hk1,hkr,hkc,hkm,hkd⟩ := reserve_scale_exists C hC d d hd hd
  let ρ : ℝ := κ^2
  let σ : ℝ := ρ/2
  let γ : ℝ := σ^2*(1/8)/12
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ≤1 := by dsimp [ρ]; nlinarith only [hk,hk1]
  have hσ : 0<σ := by dsimp [σ]; positivity
  have hσ1 : σ≤1 := by dsimp [σ]; linarith
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hγ1 : γ≤1 := by dsimp [γ]; nlinarith only [hσ,hσ1]
  obtain ⟨Nn,hnibble⟩ := TypedNibble.typed_nibble_packing 4 (1/64)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Nc,hcover⟩ := typed_cover_down_absorption 4 γ (by norm_num) hγ hγ1
  let Nb : ℕ := ⌈(2:ℝ)^27*σ⁻¹^9*(1/8:ℝ)⁻¹^6⌉₊
  let Nk : ℕ := ⌈1/ρ⌉₊
  let Nf : ℕ := ⌈4*(C:ℝ)/d⌉₊
  let N : ℕ := 2*N0+Nn+Nc+Nb+Nk+Nf+1
  refine ⟨d,hd,N,?_⟩
  intro V _ _ hN p G _ hG hdiv
  classical
  have hn : 0<Fintype.card V := by dsimp [N] at hN; omega
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hn0 : N0≤Fintype.card V := by dsimp [N] at hN; omega
  have hn2 : 2*N0≤Fintype.card V := by dsimp [N] at hN; omega
  have hnn : Nn≤Fintype.card V := by dsimp [N] at hN; omega
  have hnc : Nc≤Fintype.card V := by dsimp [N] at hN; omega
  have hnb : Nb≤Fintype.card V := by dsimp [N] at hN; omega
  have hnk : Nk≤Fintype.card V := by dsimp [N] at hN; omega
  have hnf : Nf≤Fintype.card V := by dsimp [N] at hN; omega
  have hnbR : (Nb:ℝ)≤Fintype.card V := by exact_mod_cast hnb
  have hnfR : (Nf:ℝ)≤Fintype.card V := by exact_mod_cast hnf
  have hlarge : (2:ℝ)^27*σ⁻¹^9*(1/8:ℝ)⁻¹^6≤Fintype.card V :=
    (Nat.le_ceil _).trans hnbR
  have hkn : 1≤κ^2*Fintype.card V := by
    have hh : 1/ρ≤(Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnk)
    have hh' := (div_le_iff₀ hρ).mp hh
    change 1≤κ^2*Fintype.card V
    dsimp [ρ] at hh'
    nlinarith only [hh']
  have hfixed : (C:ℝ)≤d*Fintype.card V/4 := by
    have hh : 4*(C:ℝ)/d≤Fintype.card V := (Nat.le_ceil _).trans hnfR
    have hh' := (div_le_iff₀ hd).mp hh
    nlinarith only [hh']
  have hanti : AntiEdgeful p F0 G (1/8) := hG.antiEdgeful (by linarith)
  obtain ⟨φ,hw,hl⟩ := hweights V hn0 p G (hG.mono (by linarith) (by linarith)) hdiv
  obtain ⟨Dp,Q,_,_,hQG,_,hQdec,hleft⟩ := hnibble V hnn 2 p F0 G φ hw hl
  have hleft' : DegBounded (G.edgeFinset \ Q) ((1/8:ℝ)*Fintype.card V/8) := by
    convert hleft using 1 <;> ring
  obtain ⟨X,hXG,hXdec,hXdeg,hXanti⟩ := exists_reserve_of_decomposition p F0 (by norm_num)
    G Q hQG hQdec σ (1/8) hσ hσ1 (by norm_num) (by norm_num) hlarge hanti hleft'
  have hXk : DegBounded X (κ^2*Fintype.card V) := by
    convert hXdeg using 1 <;> dsimp [σ,ρ] <;> ring
  have hterm := keptTerminal_of_local hlocal hG ha.le hd.le (by linarith)
    hd.le hd.le (by linarith) (by linarith) (by linarith) (by linarith) hn2
  have hstep : PrivateStep p F0 G 214 C (d*Fintype.card V/4)
      (d*Fintype.card V) (d*Fintype.card V) :=
    privateStep_of_keptTerminal p G 214 C _ _ _ (by positivity) hterm
  obtain ⟨A,hAG,hAX,hAdec,hAdeg,habs⟩ := universal_from_small_reserve p G C hC κ d d
    hk hk1 hkr hkc hkm hd hd hkn hfixed hanti hstep X hXG hXk
  have hAXdeg : DegBounded (A∪X) ((2*d)*Fintype.card V) := by
    intro v
    have hu := StructuralF3General.PrivateFamily.incidentLoad_union hAX v
    have ha' := hAdeg v
    have hx' := hXk v
    change (incidentLoad A v:ℝ)≤d*Fintype.card V at ha'
    change (incidentLoad X v:ℝ)≤κ^2*Fintype.card V at hx'
    change (incidentLoad (A∪X) v:ℝ)≤(2*d)*Fintype.card V
    have hrhon := mul_le_mul_of_nonneg_right hkd hnR.le
    have huR : (AntiEdgeSelection.incidentLoad (A∪X) v:ℝ) =
        incidentLoad A v+incidentLoad X v := by exact_mod_cast hu
    nlinarith only [huR,ha',hx',hrhon]
  have hmain := hG.delete ha.le (by linarith) (by positivity) (by linarith) (A∪X) hAXdeg
  have hAXdec : HasDecomp p F0 (A∪X) := hAdec.union hXdec hAX
  have hAXG : A∪X⊆G.edgeFinset := union_subset hAG hXG
  have hmaindiv : IsIntDiv p F0 (G.deleteEdges ((A∪X:Finset (Sym2 V)):Set (Sym2 V))).edgeFinset := by
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hAXdec hAXG
  obtain ⟨ψ,hψw,hψl⟩ := hweights V hn0 p (G.deleteEdges ((A∪X:Finset (Sym2 V)):Set (Sym2 V)))
    (hmain.mono le_rfl (by linarith)) hmaindiv
  refine hcover V hnc 2 p F0 G A X ψ hAG hXG hAX hdiv habs hXanti hψw ?_
  intro e heG
  exact hψl e (by simpa only [SimpleGraph.edgeFinset_deleteEdges] using heG)

#print axioms reserve_scale_exists
#print axioms decomposition_from_producers

end PartitionedTriangleAbsorption.BlowupB.F0Direct
