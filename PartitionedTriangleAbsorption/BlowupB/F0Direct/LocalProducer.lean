/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateHost
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostHingeSupply
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.FiniteTerminal

@[expose] public section

/-!
# The geometric producer of bounded terminal absorbers

The only input is `HostHyp`.  In particular this theorem neither assumes a
signed certificate nor a hinge supply.  Both are constructed in the host.
The constants are uniform in the vertex type and in the bounded residue.
-/

universe u

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks SignedHinge SignedCertificate

noncomputable def localTheta (a : ℝ) : ℝ := (min a 1)/100

noncomputable def localEpsilon (a : ℝ) : ℝ := localTheta a/(2:ℝ)^30

theorem localTheta_pos {a : ℝ} (ha : 0<a) : 0<localTheta a := by
  dsimp [localTheta]
  positivity

theorem localTheta_le (a : ℝ) : localTheta a≤1/100 := by
  have hm : min a 1≤1 := min_le_right _ _
  dsimp [localTheta]
  linarith

theorem localTheta_scale (a : ℝ) : 100*localTheta a≤a := by
  have hm : min a 1≤a := min_le_left _ _
  dsimp [localTheta]
  linarith

theorem localEpsilon_pos {a : ℝ} (ha : 0<a) : 0<localEpsilon a := by
  have ht := localTheta_pos ha
  dsimp [localEpsilon]
  positivity

theorem localEpsilon_theta {a : ℝ} (ha : 0<a) :
    100*localEpsilon a≤localTheta a := by
  have ht := localTheta_pos ha
  norm_num [localEpsilon]
  linarith

theorem localEpsilon_le {a : ℝ} (ha : 0<a) : localEpsilon a≤1/100 := by
  have hh := localEpsilon_theta ha
  have ht := localTheta_le a
  linarith

theorem localEpsilon_root (a : ℝ) :
    localEpsilon a*(10*(214:ℝ)+10)≤1/100 := by
  have ht := localTheta_le a
  norm_num [localEpsilon]
  linarith

theorem terminal_producer (a : ℝ) (ha : 0<a) :
    ∃ N : ℕ, LocalTerminal.{u} a (localEpsilon a) N 214 (terminalCost 214) := by
  let θ := localTheta a
  let β := θ/(2:ℝ)^30
  let K : ℝ := 41*(126*214)+1
  let N1 : ℕ := ⌈4096/θ⌉₊
  let N2 : ℕ := ⌈8*K+1⌉₊
  let N3 : ℕ := ⌈((2:ℝ)^36*K+1)/β⌉₊
  let N : ℕ := N1+N2+N3+1
  have ht : 0<θ := localTheta_pos ha
  have hb : 0<β := by dsimp [β]; positivity
  have he := localEpsilon_pos ha
  have he1 := localEpsilon_le ha
  refine ⟨N,?_⟩
  intro V _ _ hn p G _ hG P hPG hPm hPdiv
  classical
  have hn0 : 0<Fintype.card V := by dsimp [N] at hn; omega
  have hn1 : N1≤Fintype.card V := by dsimp [N] at hn; omega
  have hn2 : N2≤Fintype.card V := by dsimp [N] at hn; omega
  have hn3 : N3≤Fintype.card V := by dsimp [N] at hn; omega
  have hn1R : (N1:ℝ)≤Fintype.card V := by exact_mod_cast hn1
  have hn2R : (N2:ℝ)≤Fintype.card V := by exact_mod_cast hn2
  have hn3R : (N3:ℝ)≤Fintype.card V := by exact_mod_cast hn3
  have hscale : 4096≤θ*Fintype.card V := by
    have hh : 4096/θ≤(Fintype.card V:ℝ) := (Nat.le_ceil _).trans hn1R
    have hh' := (div_le_iff₀ ht).mp hh
    nlinarith only [hh']
  have hlarge : (41*(126*214)+1:ℝ)<Fintype.card V/8 := by
    have hh : 8*K+1≤(Fintype.card V:ℝ) := (Nat.le_ceil _).trans hn2R
    dsimp [K] at hh
    linarith only [hh]
  have hlarge' : (2:ℝ)^36*(41*(126*214)+1)<β*Fintype.card V := by
    have hh : ((2:ℝ)^36*K+1)/β≤(Fintype.card V:ℝ) :=
      (Nat.le_ceil _).trans hn3R
    have hh' := (div_le_iff₀ hb).mp hh
    dsimp [K] at hh'
    nlinarith only [hh']
  have hbudget : HostHinges.Budget a (localEpsilon a) θ (Fintype.card V) :=
    ⟨he.le,ht,localTheta_le a,localEpsilon_theta ha,localTheta_scale a,hscale⟩
  obtain ⟨k,t,c,hcert,hweight⟩ := signed_certificate_of_host hG he.le he1 θ ht
    (localTheta_le a) (localEpsilon_theta ha) (localTheta_scale a) hscale 214
    (localEpsilon_root a) P hPG hPm hPdiv
  exact terminal_of_signed_certificate p G β 214
    (hG.part_present (by linarith) hn0) (hG.antiEdgeful (by linarith))
    (hG.hingeSupply hbudget) hlarge hlarge' P hPm t c hcert hweight

#print axioms terminal_producer

end PartitionedTriangleAbsorption.BlowupB.F0Direct
