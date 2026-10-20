/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostTokens
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.OrdinaryHost

/-! # One physical charge layer in the four-class host

`host_layer` combines the generic `token_layer` with the physical token supply `host_tokens`:
the token identities required by the layer are realized by edge-disjoint rectangles of the
complete four-class host avoiding the current remainder and the reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection TypedApplicationLinks TypedRefinerCharge RefinerF0

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem degBounded_union {A B : Finset (Sym2 V)} {a b : ℝ} (hA : DegBounded A a)
    (hB : DegBounded B b) : DegBounded (A ∪ B) (a + b) := by
  intro v
  have h := ModThreeLayer.incidentLoad_union_le A B v
  have h' : ((incidentLoad (A ∪ B) v : ℕ) : ℝ) ≤ (incidentLoad A v : ℝ) + incidentLoad B v := by
    exact_mod_cast h
  have ha := hA v
  have hb := hB v
  change ((incidentLoad (A ∪ B) v : ℕ) : ℝ) ≤ _
  change ((incidentLoad A v : ℕ) : ℝ) ≤ a at ha
  change ((incidentLoad B v : ℕ) : ℝ) ≤ b at hb
  linarith

omit [DecidableEq V] in
theorem crossClass_of_subset_edges {cls : V → Fin 4} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → cls a ≠ cls b) {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) :
    CrossClass cls E := fun a b hab => hG a b (SimpleGraph.mem_edgeFinset.mp (hE hab))

omit [Fintype V] [DecidableEq V] in
/-- A divisible charge of an edge set with unit weights is at most half its size, in units
of four. -/
theorem two_mul_natAbs_div_four_le {t : ℕ} {χ : Fin t → Fin t → ℤ} (hχ : ∀ i j, |χ i j| ≤ 1)
    (p : V → Fin t) (P : Finset (Sym2 V)) (hdvd : (4 : ℤ) ∣ charge χ p P) :
    2 * (charge χ p P / 4).natAbs ≤ P.card := by
  have h := abs_charge_le (χ := χ) (M := 2) p (fun e => abs_pair_pairVec_le hχ p e) P
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [hk, abs_mul] at h
  have : (4 : ℤ) * |k| ≤ 2 * P.card := by simpa using h
  have hk' : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
  omega

/-- **One physical charge layer.** -/
theorem host_layer (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ : ℝ) (hanti : AntiEdgeful cls F3 G γ)
    (hpos : ∀ i, 0 < (classSet cls i).card)
    {κ : Type*} {X : Finset (Sym2 V)} {Q : Finset (Sym2 V) → Prop}
    (E : PredRefiner κ X Q) (hQ0 : Q ∅)
    (d : ℝ) (hd : DegBounded (E.R0 ∪ X) d)
    (χ χ' : Fin 4 → Fin 4 → ℤ)
    (hdvd : ∀ i ∈ E.lib, (4 : ℤ) ∣ charge χ cls (E.P i))
    (kP kM1 kM2 : Fin 4) (hkP : kP ≠ 0) (hkM1 : kM1 ≠ 0) (hkM2 : kM2 ≠ 0)
    (hP : c4charge χ kP = 4) (hM : c4charge χ kM1 + c4charge χ kM2 = -4)
    (hP' : c4charge χ' kP = 0) (hM' : c4charge χ' kM1 + c4charge χ' kM2 = 0)
    (N : ℕ) (hN : 9 * ∑ i ∈ E.lib, (charge χ cls (E.P i) / 4).natAbs ≤ N)
    (q r : ℕ) (hq : 0 < q) (hr : ∀ i, 4 * (2 * N / (classSet cls i).card + 1) ≤ r)
    (hbudget : (4 * N : ℝ) / q + 2 * (d + r + 2 * q) < γ * Fintype.card V) :
    ∃ (S : Finset (Tok κ)) (tokE : Tok κ → Finset (Sym2 V))
      (E' : PredRefiner (JIdx κ) X (fun L => Q L ∧ charge χ cls L = 0)),
      E'.R0 = E.R0 ∪ S.biUnion tokE ∧
      S.biUnion tokE ⊆ G.edgeFinset ∧
      Disjoint (S.biUnion tokE) (E.R0 ∪ X) ∧
      (∀ v, incidentLoad (S.biUnion tokE) v ≤ r + 2 * q) ∧
      (∀ j ∈ E'.lib, charge χ cls (E'.P j) = 0) ∧
      ((∀ i ∈ E.lib, charge χ' cls (E.P i) = 0) → ∀ j ∈ E'.lib, charge χ' cls (E'.P j) = 0) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ 16 ∨
        ∃ i ∈ E.lib, (E'.P j).card ≤ (E.P i).card + 8 * (charge χ cls (E.P i) / 4).natAbs) ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w + 44 * (r + 2 * q)) ∧
      E'.lib.card ≤ E.lib.card + 97 * ∑ i ∈ E.lib, (charge χ cls (E.P i) / 4).natAbs := by
  classical
  let Extra : Finset (Tok κ) → (Tok κ → Finset (Sym2 V)) → Prop := fun S tokE =>
    (∀ τ ∈ S, tokE τ ⊆ G.edgeFinset) ∧ (∀ v, ∑ τ ∈ S, incidentLoad (tokE τ) v ≤ r + 2 * q)
  have hsupply : ∀ S : Finset (Tok κ),
      S.card ≤ 9 * ∑ i ∈ E.lib, (charge χ cls (E.P i) / 4).natAbs →
      ∃ tokE, TokReal χ χ' cls 4 8 (E.R0 ∪ X) S tokE ∧ Extra S tokE := by
    intro S hS
    have hSN : S.card ≤ N := hS.trans hN
    have hr' : ∀ i, 4 * (2 * S.card / (classSet cls i).card + 1) ≤ r := by
      intro i
      refine le_trans ?_ (hr i)
      exact Nat.mul_le_mul_left 4 (Nat.add_le_add_right
        (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hSN)) 1)
    have hb' : (4 * S.card : ℝ) / q + 2 * (d + r + 2 * q) < γ * Fintype.card V := by
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have : (4 * S.card : ℝ) / q ≤ (4 * N : ℝ) / q := by
        apply div_le_div_of_nonneg_right _ hqR.le
        have : (S.card : ℝ) ≤ N := by exact_mod_cast hSN
        linarith
      linarith
    obtain ⟨tokE, hreal, hsub, hload⟩ := host_tokens cls G γ hanti hpos (E.R0 ∪ X) d hd S
      kP kM1 kM2 hkP hkM1 hkM2 χ χ' hP hM hP' hM' q r hq hr' hb'
    exact ⟨tokE, hreal, hsub, hload⟩
  obtain ⟨S, tokE, E', hreal, ⟨hsubG, hloadS⟩, -, hR', hchg, hchg', hcard, hload, hlib⟩ :=
    token_layer E hQ0 χ χ' cls 4 (by norm_num) hdvd 8 Extra hsupply
  refine ⟨S, tokE, E', hR', ?_, hreal.avoid_biUnion le_rfl, ?_, hchg, hchg', ?_, ?_, hlib⟩
  · intro e he
    obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp he
    exact hsubG τ hτ he
  · intro v
    rw [← incidentLoad_biUnion_eq S tokE hreal.disj v]
    exact hloadS v
  · intro j hj
    rcases hcard j hj with h | h
    · left; simpa using h
    · right; exact h
  · intro w
    refine (hload w).trans (Nat.add_le_add_left ?_ _)
    exact Nat.mul_le_mul_left 44 (hloadS w)

end PartitionedTriangleAbsorption.StructuralF3General
