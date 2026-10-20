/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.GroupLayer
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostLayer

@[expose] public section

/-!
# Iterating cyclic layers along a finite list of generators

Let `l = [g₁, …, g_r]` be a finite list in an abelian group `A`.  Write
`H_k = ⟨g_{k+1}, …, g_r⟩`.  If every library piece has value in `H_0`, then `r` successive
applications of `group_layer` (layer `k` kills the `g_k`-coordinate of `H_{k-1}/H_k`,
which is cyclic, free or torsion) produce a refiner all of whose pieces have value `0`.

All constants (piece size `m'`, library factor `Lc`, token factor `Tc`) are chosen from
the list, the size bound `szMax` of the token templates, the input piece size `m` and a
host-independent finite description `Vals` of the possible values of bounded edge sets —
BEFORE any host, reserve or leftover.  The physical tokens are requested from a supply
hypothesis `TokSupply` for every generator; the supply is proved separately for the
physical host.  The library index type after `r` layers is `LIdx r κ`, a fixed type.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0

/-- The library index type after `n` layers. -/
def LIdx : ℕ → Type → Type
  | 0, κ => κ
  | n + 1, κ => LIdx n (JIdx (κ ⊕ ℕ))

/-- Decidable equality of the iterated index type. -/
def LIdx.decEq : (n : ℕ) → (κ : Type) → [DecidableEq κ] → DecidableEq (LIdx n κ)
  | 0, _, h => h
  | n + 1, κ, _ => LIdx.decEq n (JIdx (κ ⊕ ℕ))

instance (n : ℕ) (κ : Type) [DecidableEq κ] : DecidableEq (LIdx n κ) := LIdx.decEq n κ

theorem exists_coef_of_mem_closure_insert {A : Type*} [AddCommGroup A] (g : A) (S : Set A)
    (x : A) (hx : x ∈ AddSubgroup.closure (insert g S)) :
    ∃ a : ℤ, x - a • g ∈ AddSubgroup.closure S := by
  let H : AddSubgroup A :=
    { carrier := {x | ∃ a : ℤ, x - a • g ∈ AddSubgroup.closure S}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        have := (AddSubgroup.closure S).add_mem ha hb
        rw [add_zsmul]
        convert this using 1; abel
      zero_mem' := ⟨0, by simp [(AddSubgroup.closure S).zero_mem]⟩
      neg_mem' := by
        rintro x ⟨a, ha⟩
        refine ⟨-a, ?_⟩
        have := (AddSubgroup.closure S).neg_mem ha
        convert this using 1; rw [neg_zsmul]; abel }
  have hle : AddSubgroup.closure (insert g S) ≤ H := by
    rw [AddSubgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact ⟨1, by simp [(AddSubgroup.closure S).zero_mem]⟩
    · exact ⟨0, by simpa using AddSubgroup.subset_closure hy⟩
  exact hle hx

variable {W : Type} [DecidableEq W]

/-- Weakening the leftover predicate of a predicate refiner. -/
def weakenRefiner {κ : Type*} {X0 : Finset (Sym2 W)} {Q Q' : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q) (h : ∀ L, Q' L → Q L) : PredRefiner κ X0 Q' where
  lib := E.lib
  P := E.P
  R0 := E.R0
  loopP := E.loopP
  evenP := E.evenP
  subP := E.subP
  disjRX := E.disjRX
  refines := fun L hL hQ => E.refines L hL (h L hQ)

/-- Physical token supply for one generator `g`: for every token identity set of size at most
`Ncap` and every forbidden edge set of maximum degree at most `dB`, there are pairwise
edge-disjoint, loopless, even tokens of size at most `sz`, avoiding the forbidden set, with
values `±g`, inside `Gedges`, of total vertex incidence at most `Δ`. -/
def TokSupply {A : Type*} [AddCommGroup A] (val : Sym2 W → A) (g : A) (sz : ℕ)
    (Gedges : Finset (Sym2 W)) (Ncap : ℕ) (dB : ℝ) (Δ : ℕ) : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (S : Finset (Tok κ)) (B : Finset (Sym2 W)),
    S.card ≤ Ncap → DegBounded B dB →
    ∃ tokE : Tok κ → Finset (Sym2 W), TokRealV val g sz B S tokE ∧
      (∀ τ ∈ S, tokE τ ⊆ Gedges) ∧ ∀ v, ∑ τ ∈ S, incidentLoad (tokE τ) v ≤ Δ

theorem incidentLoad_sdiff_union_le (X Y Z : Finset (Sym2 W)) (v : W) :
    incidentLoad (Z \ X) v ≤ incidentLoad (Z \ Y) v + incidentLoad (Y \ X) v := by
  have h : Z \ X ⊆ (Z \ Y) ∪ (Y \ X) := by
    intro e he
    rcases mem_sdiff.mp he with ⟨hz, hx⟩
    by_cases hy : e ∈ Y
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hy, hx⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hz, hy⟩)
  exact (ModThreeLayer.incidentLoad_mono h v).trans (ModThreeLayer.incidentLoad_union_le _ _ v)

/-- **Iterated cyclic layers.** -/
theorem iterate_layers {A : Type} [AddCommGroup A] (Vals : ℕ → Finset A) :
    ∀ (l : List A) (szMax m : ℕ), ∃ m' Lc Tc : ℕ, 1 ≤ Lc ∧
      ∀ (W : Type) [DecidableEq W] (val : Sym2 W → A),
      (∀ (E : Finset (Sym2 W)) (k : ℕ), E.card ≤ k → edgeVal val E ∈ Vals k) →
      ∀ (X0 : Finset (Sym2 W)) (Q Q' : Finset (Sym2 W) → Prop), (∀ L, Q' L → Q L) → Q' ∅ →
      (∀ L ⊆ X0, Q' L → edgeVal val L = 0) →
      ∀ (Gedges : Finset (Sym2 W)) (Ncap Δ : ℕ) (dB : ℝ) (sz : A → ℕ),
      (∀ g ∈ l, sz g ≤ szMax) → (∀ g ∈ l, TokSupply val g (sz g) Gedges Ncap dB Δ) →
      ∀ (κ : Type) [DecidableEq κ] (E : PredRefiner κ X0 Q),
      (∀ i ∈ E.lib, edgeVal val (E.P i) ∈ AddSubgroup.closure {x | x ∈ l}) →
      (∀ i ∈ E.lib, (E.P i).card ≤ m) →
      Tc * E.lib.card ≤ Ncap →
      ∀ d0 : ℝ, DegBounded (E.R0 ∪ X0) d0 → d0 + l.length * Δ ≤ dB →
      ∃ E' : PredRefiner (LIdx l.length κ) X0 Q',
        (∀ j ∈ E'.lib, edgeVal val (E'.P j) = 0) ∧
        (∀ j ∈ E'.lib, (E'.P j).card ≤ m') ∧
        E'.lib.card ≤ Lc * E.lib.card ∧
        E.R0 ⊆ E'.R0 ∧ E'.R0 \ E.R0 ⊆ Gedges ∧
        (∀ v, incidentLoad (E'.R0 \ E.R0) v ≤ l.length * Δ) ∧
        ∀ v, ∑ j ∈ E'.lib, incidentLoad (E'.P j) v ≤
          Lc * (∑ i ∈ E.lib, incidentLoad (E.P i) v + Δ) := by
  intro l
  induction l with
  | nil =>
    intro szMax m
    refine ⟨m, 1, 0, le_rfl, ?_⟩
    intro W _ val _ X0 Q Q' hQ' _ _ Gedges Ncap Δ dB sz _ _ κ _ E hE hEm _ d0 _ _
    refine ⟨weakenRefiner E hQ', ?_, hEm,
      by change E.lib.card ≤ 1 * E.lib.card; omega, subset_rfl, ?_, ?_, ?_⟩
    · intro j hj
      have h := hE j hj
      simp only [List.not_mem_nil, Set.setOf_false, AddSubgroup.closure_empty,
        AddSubgroup.mem_bot] at h
      exact h
    · simp [weakenRefiner]
    · intro v; simp [weakenRefiner, incidentLoad]
    · intro v
      change ∑ j ∈ E.lib, incidentLoad (E.P j) v ≤ 1 * (∑ i ∈ E.lib, incidentLoad (E.P i) v + Δ)
      omega
  | cons g l ih =>
    intro szMax m
    classical
    have hgen : ∀ x ∈ AddSubgroup.closure {x | x ∈ g :: l},
        ∃ a : ℤ, x - a • g ∈ AddSubgroup.closure {x | x ∈ l} := by
      intro x hx
      have hset : {x | x ∈ g :: l} = insert g {x | x ∈ l} := by
        ext y; simp
      rw [hset] at hx
      exact exists_coef_of_mem_closure_insert g _ x hx
    obtain ⟨d, hd, coef, hcoef, hnn⟩ := exists_cyclic_coef _ _ g hgen
    obtain ⟨Ab, hAb⟩ : ∃ Ab, Ab = d + (Vals m).sup (fun x => (coef x).natAbs) := ⟨_, rfl⟩
    obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = m + szMax * Ab + 2 * szMax := ⟨_, rfl⟩
    obtain ⟨L1, hL1⟩ : ∃ L1, L1 = 1 + 98 * (Ab * (Ab + 1)) := ⟨_, rfl⟩
    obtain ⟨m', Lc', Tc', hLc', hrest⟩ := ih szMax m₁
    refine ⟨m', 45 * L1 * Lc', 9 * (Ab * (Ab + 1)) + Tc' * L1, ?_, ?_⟩
    · have : 1 ≤ L1 := by omega
      nlinarith
    intro W _ val hVals X0 Q Q' hQ' hQ0 hval Gedges Ncap Δ dB sz hsz hsup κ _ E hE hEm hN
      d0 hd0 hdB
    have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    have hlen : ((g :: l).length : ℝ) = l.length + 1 := by simp
    have hdB' : d0 ≤ dB := by
      rw [hlen] at hdB
      have : (0 : ℝ) ≤ (l.length + 1) * Δ := by positivity
      linarith
    let Extra : Finset (Tok (κ ⊕ ℕ)) → (Tok (κ ⊕ ℕ) → Finset (Sym2 W)) → Prop :=
      fun S tokE => (∀ τ ∈ S, tokE τ ⊆ Gedges) ∧ ∀ v, ∑ τ ∈ S, incidentLoad (tokE τ) v ≤ Δ
    have hcE : ∀ i ∈ E.lib, edgeVal val (E.P i) - coef (edgeVal val (E.P i)) • g ∈
        AddSubgroup.closure {x | x ∈ l} := fun i hi => hcoef _ (hE i hi)
    have hnnE : 0 < d → ∀ i ∈ E.lib, 0 ≤ coef (edgeVal val (E.P i)) :=
      fun h i _ => (hnn h _).1
    have hAbE : ∀ i ∈ E.lib, (coef (edgeVal val (E.P i))).natAbs ≤ Ab := by
      intro i hi
      have hmem := hVals (E.P i) m (hEm i hi)
      have : (coef (edgeVal val (E.P i))).natAbs ≤ (Vals m).sup (fun x => (coef x).natAbs) :=
        Finset.le_sup (f := fun x => (coef x).natAbs) hmem
      rw [hAb]; omega
    have hdAb : d ≤ Ab := by rw [hAb]; omega
    have hsupE : ∀ S : Finset (Tok (κ ⊕ ℕ)), S.card ≤ 9 * (Ab * (Ab + 1) * E.lib.card) →
        ∃ tokE, TokRealV val g (sz g) (E.R0 ∪ X0) S tokE ∧ Extra S tokE := by
      intro S hS
      have hS' : S.card ≤ Ncap := by
        refine hS.trans (le_trans ?_ hN)
        calc 9 * (Ab * (Ab + 1) * E.lib.card) = 9 * (Ab * (Ab + 1)) * E.lib.card := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      obtain ⟨tokE, h1, h2, h3⟩ := hsup g List.mem_cons_self (κ ⊕ ℕ) S (E.R0 ∪ X0) hS'
        (fun v => (hd0 v).trans hdB')
      exact ⟨tokE, h1, h2, h3⟩
    obtain ⟨S, tokE, E₁, hreal, ⟨hTG, hTload⟩, -, hR₁, hval₁, hcard₁, hload₁, hlib₁⟩ :=
      group_layer E hQ' hQ0 val hval (AddSubgroup.closure {x | x ∈ l}) g d hd
        (fun i => coef (edgeVal val (E.P i))) hcE hnnE Ab hAbE hdAb (sz g) Extra hsupE
    rw [← hL1] at hlib₁
    set TE := S.biUnion tokE with hTE
    have hTdeg : ∀ v, incidentLoad TE v ≤ Δ := fun v =>
      (incidentLoad_biUnion_le S tokE v).trans (hTload v)
    have hszg : sz g ≤ szMax := hsz g List.mem_cons_self
    have hm₁E : ∀ j ∈ E₁.lib, (E₁.P j).card ≤ m₁ := by
      intro j hj
      have h1 : sz g * Ab ≤ szMax * Ab := Nat.mul_le_mul_right _ hszg
      rcases hcard₁ j hj with h | h | ⟨i, hi, h⟩
      · rw [hm₁]; omega
      · rw [hm₁]; omega
      · have := hEm i hi
        rw [hm₁]; omega
    have hN₁ : Tc' * E₁.lib.card ≤ Ncap := by
      refine le_trans ?_ hN
      calc Tc' * E₁.lib.card ≤ Tc' * (E.lib.card * L1) := Nat.mul_le_mul_left _ hlib₁
        _ = (Tc' * L1) * E.lib.card := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    have hd₁ : DegBounded (E₁.R0 ∪ X0) (d0 + Δ) := by
      have h := degBounded_union hd0 (fun v => (by exact_mod_cast hTdeg v :
        ((TE.filter fun e => v ∈ e).card : ℝ) ≤ Δ))
      rw [hR₁]
      have heq : E.R0 ∪ TE ∪ X0 = (E.R0 ∪ X0) ∪ TE := by
        ext e; simp only [mem_union]; tauto
      rw [heq]; exact h
    have hdB₁ : d0 + Δ + l.length * Δ ≤ dB := by
      rw [hlen] at hdB; linarith
    obtain ⟨E', hv', hm', hlib', hsub', hG', hload', hlibload'⟩ :=
      hrest W val hVals X0 Q' Q' (fun _ h => h) hQ0 hval Gedges Ncap Δ dB sz
        (fun g' hg' => hsz g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hsup g' (List.mem_cons_of_mem _ hg'))
        (JIdx (κ ⊕ ℕ)) E₁ hval₁ hm₁E hN₁ (d0 + Δ) hd₁ hdB₁
    have hR0sub : E.R0 ⊆ E₁.R0 := by rw [hR₁]; exact subset_union_left
    have hdiff₁ : E₁.R0 \ E.R0 ⊆ TE := by
      rw [hR₁]; intro e he
      rcases mem_sdiff.mp he with ⟨h1, h2⟩
      rcases mem_union.mp h1 with h | h
      · exact absurd h h2
      · exact h
    refine ⟨E', hv', hm', ?_, hR0sub.trans hsub', ?_, ?_, ?_⟩
    · calc E'.lib.card ≤ Lc' * E₁.lib.card := hlib'
        _ ≤ Lc' * (E.lib.card * L1) := Nat.mul_le_mul_left _ hlib₁
        _ = (L1 * Lc') * E.lib.card := by ring
        _ ≤ (45 * L1 * Lc') * E.lib.card := by
            apply Nat.mul_le_mul_right
            rw [mul_assoc 45]
            exact Nat.le_mul_of_pos_left _ (by norm_num)
    · intro e he
      rcases mem_sdiff.mp he with ⟨h1, h2⟩
      by_cases h3 : e ∈ E₁.R0
      · obtain ⟨τ, hτ, he'⟩ := mem_biUnion.mp (hdiff₁ (mem_sdiff.mpr ⟨h3, h2⟩))
        exact hTG τ hτ he'
      · exact hG' (mem_sdiff.mpr ⟨h1, h3⟩)
    · intro v
      have h1 := incidentLoad_sdiff_union_le E.R0 E₁.R0 E'.R0 v
      have h2 := ModThreeLayer.incidentLoad_mono hdiff₁ v
      have h3 := hload' v
      have h4 := hTdeg v
      simp only [List.length_cons, add_mul, one_mul]
      omega
    · intro v
      have h1 := hlibload' v
      have h2 := hload₁ v
      have h3 : ∑ τ ∈ S, incidentLoad (tokE τ) v ≤ Δ := hTload v
      calc ∑ j ∈ E'.lib, incidentLoad (E'.P j) v
          ≤ Lc' * (∑ j ∈ E₁.lib, incidentLoad (E₁.P j) v + Δ) := h1
        _ ≤ Lc' * (∑ i ∈ E.lib, incidentLoad (E.P i) v + 44 * Δ + Δ) := by
            apply Nat.mul_le_mul_left; omega
        _ ≤ Lc' * (45 * (∑ i ∈ E.lib, incidentLoad (E.P i) v + Δ)) := by
            apply Nat.mul_le_mul_left; omega
        _ ≤ (Lc' * 45) * L1 * (∑ i ∈ E.lib, incidentLoad (E.P i) v + Δ) := by
            have : 1 ≤ L1 := by omega
            rw [← mul_assoc]
            exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ this)
        _ = 45 * L1 * Lc' * (∑ i ∈ E.lib, incidentLoad (E.P i) v + Δ) := by ring

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
