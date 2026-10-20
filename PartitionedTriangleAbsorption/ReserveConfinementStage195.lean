/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveRetirementStage194
public import PartitionedTriangleAbsorption.TypedLinkCoefficients
public import PartitionedTriangleAbsorption.TypedCoverDownConsumer

/-! # Physical confinement with a charged packing retirement

A reserve and its quantitative budget are still explicit inputs. The packing
need not avoid it in advance: retirement constructs that disjointness.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveConfinementStage195

open Finset ReserveRetirementStage194 TypedLinkCoefficients

variable {V : Type} [DecidableEq V]

noncomputable def outsideCharge (D : Finset (Finset V)) (X : Finset (Sym2 V))
    (v : V) : ℕ := by
  classical
  exact (((touching D X).biUnion triEdges \ X).filter fun e => v ∈ e).card

theorem outside_charge_zero_of_whole_triangles {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D B : Finset (Finset V)) (hD : IsDecomp p F Q D) (hBD : B ⊆ D) (v : V) :
    outsideCharge D (B.biUnion triEdges) v = 0 := by
  classical
  have hsub : (touching D (B.biUnion triEdges)).biUnion triEdges ⊆ B.biUnion triEdges := by
    intro e he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    obtain ⟨hsD, ht⟩ := mem_filter.mp hs
    obtain ⟨f, hfs, hfB⟩ := not_disjoint_iff.mp ht
    obtain ⟨b, hb, hfb⟩ := mem_biUnion.mp hfB
    have hsb : s = b := by
      by_contra hne
      exact disjoint_left.mp (hD.2.1 hsD (hBD hb) hne) hfs hfb
    exact mem_biUnion.mpr ⟨b, hb, hsb ▸ hes⟩
  simp only [outsideCharge, sdiff_eq_empty_iff_subset.mpr hsub, filter_empty, card_empty]

theorem natural_links_after_subpacking {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E Q Q' : Finset (Sym2 V))
    (D D' : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (hD' : IsDecomp p F Q' D') (hsub : D' ⊆ D) (hQE : Q ⊆ E) (hQ'E : Q' ⊆ E)
    (hlinks : ∀ v, Realizable F (p v) (degVec p (E \ Q) v)) :
    ∀ v, Realizable F (p v) (degVec p (E \ Q') v) := by
  classical
  intro v
  obtain ⟨a, ha⟩ := hlinks v
  let c : Multiset (Fin t) → ℕ := fun τ =>
    a τ + (D.filter fun s => v ∈ s ∧ triType p s = τ).card
  have hc : degVec p E v = ∑ τ ∈ F with p v ∈ τ,
      (c τ : ℤ) • typeDegVec τ (p v) := by
    have h := degVec_union p (disjoint_sdiff : Disjoint Q (E \ Q)) v
    rw [union_sdiff_of_subset hQE, hD.degVec_eq v, ha, ← sum_add_distrib] at h
    rw [h]
    apply sum_congr rfl
    intro τ _
    dsimp [c]
    rw [add_smul]
    exact add_comm _ _
  refine ⟨fun τ => c τ - (D'.filter fun s => v ∈ s ∧ triType p s = τ).card, ?_⟩
  have h := degVec_union p (disjoint_sdiff : Disjoint Q' (E \ Q')) v
  rw [union_sdiff_of_subset hQ'E, hc, hD'.degVec_eq v] at h
  rw [eq_sub_of_add_eq' h.symm, ← sum_sub_distrib]
  apply sum_congr rfl
  intro τ _
  have hcount : (D'.filter fun s => v ∈ s ∧ triType p s = τ).card ≤ c τ := by
    have hb := card_le_card (filter_subset_filter (fun s => v ∈ s ∧ triType p s = τ) hsub)
    dsimp [c]
    omega
  rw [Nat.cast_sub hcount, sub_smul]

theorem confine_with_charged_reserve [Fintype V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q X : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F Q D) (hQE : Q ⊆ G.edgeFinset) (hX : X ⊆ G.edgeFinset)
    (hI : IsIntDiv p F G.edgeFinset)
    (hpos : ∃ a : Multiset (Fin t) → ℕ,
      edgeVec p (G.edgeFinset \ Q) = ∑ τ ∈ F, (a τ : ℤ) • typeEdgeVec τ)
    (α : ℝ) [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
    (hres : AntiEdgeful p F (ReserveCoverDown.reserveGraph X) α)
    (htype : ∀ a b : V, G.Adj a b →
      ∃ k : Fin t, ({p a, p b, k} : Multiset (Fin t)) ∈ F)
    (r q : ℕ) (hq : 0 < q)
    (hcharge : ∀ v, (((G.edgeFinset \ Q) \ X).filter fun e => v ∈ e).card +
      outsideCharge D X v ≤ r)
    (hbudget : (((r * Fintype.card V) / 2 : ℕ) : ℝ) / q +
      2 * ((r : ℝ) + 2 * q) < α * Fintype.card V) :
    ∃ EQ, EQ ⊆ G.edgeFinset ∧ HasDecomp p F EQ ∧
      G.edgeFinset \ EQ ⊆ X ∧ IsIntDiv p F (G.edgeFinset \ EQ) := by
  classical
  obtain ⟨D', Q', hD'eq, hQ'eq, hsub, hQ', hD', hdis, _, _, _⟩ :=
    retire_reserve p F G.edgeFinset Q X D hD hQE hI hpos
  let L := (G.edgeFinset \ Q') \ X
  have hLE : L ⊆ G.edgeFinset := sdiff_subset.trans sdiff_subset
  have hLX : Disjoint L X := disjoint_left.mpr fun e he heX =>
    (mem_sdiff.mp he).2 heX
  have hdiag : ∀ e ∈ L, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (by simpa using hLE he)
  have hdegreeNat : ∀ v, (L.filter fun e => v ∈ e).card ≤ r := by
    intro v
    have hcover : L ⊆ ((G.edgeFinset \ Q) \ X) ∪
        ((touching D X).biUnion triEdges \ X) := by
      intro e he
      have heX := (mem_sdiff.mp he).2
      have heE := (mem_sdiff.mp (mem_sdiff.mp he).1).1
      by_cases heQ : e ∈ Q
      · obtain ⟨s, hs, hes⟩ := mem_biUnion.mp (hD.2.2.symm ▸ heQ)
        have hst : s ∈ touching D X := by
          by_contra hst
          have hs' : s ∈ D' := by rw [hD'eq]; exact mem_sdiff.mpr ⟨hs, hst⟩
          have heQ' : e ∈ Q' := by rw [hQ'eq]; exact mem_biUnion.mpr ⟨s, hs', hes⟩
          exact (mem_sdiff.mp (mem_sdiff.mp he).1).2 heQ'
        exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨s, hst, hes⟩, heX⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨heE, heQ⟩, heX⟩)
    calc
      _ ≤ ((((G.edgeFinset \ Q) \ X) ∪
          ((touching D X).biUnion triEdges \ X)).filter fun e => v ∈ e).card :=
        card_le_card (filter_subset_filter _ hcover)
      _ ≤ (((G.edgeFinset \ Q) \ X).filter fun e => v ∈ e).card + outsideCharge D X v := by
        rw [filter_union]
        exact card_union_le _ _
      _ ≤ r := hcharge v
  have hdegree : DegBounded L r := by
    intro v
    exact_mod_cast hdegreeNat v
  have hcard : L.card ≤ (r * Fintype.card V) / 2 := by
    have hh := TypedCoverDown.sum_degrees_eq_two_mul_card L hdiag
    have hs : (∑ v : V, (L.filter fun e => v ∈ e).card) ≤
        r * Fintype.card V := by
      calc
        _ ≤ ∑ _v : V, r := sum_le_sum fun v _ => hdegreeNat v
        _ = _ := by simp [Nat.mul_comm]
    rw [hh] at hs
    omega
  obtain ⟨P, hPX, _, _, hLP, _⟩ := ReserveCoverDown.exists_reserve_cover
    p F X L α hres hLX hdiag
    (fun a b he => htype a b (G.mem_edgeFinset.mp (hLE he)))
    ((r * Fintype.card V) / 2) r q hq hcard hdegree hbudget
  have hQLP : Disjoint Q' (L ∪ P) := by
    rw [disjoint_union_right]
    refine ⟨disjoint_left.mpr (fun e heQ heL =>
      (mem_sdiff.mp (mem_sdiff.mp heL).1).2 heQ), hdis.mono_right hPX⟩
  let EQ := Q' ∪ (L ∪ P)
  have hEQ : EQ ⊆ G.edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hQE (hQ' he)
    · rcases mem_union.mp he with he | he
      · exact hLE he
      · exact hX (hPX he)
  have hdec : HasDecomp p F EQ := (show HasDecomp p F Q' from ⟨D', hD'⟩).union hLP hQLP
  refine ⟨EQ, hEQ, hdec, ?_, isIntDiv_sdiff_of_hasDecomp hI hdec hEQ⟩
  intro e he
  by_contra heX
  have heQ : e ∉ Q' := fun heQ =>
    (mem_sdiff.mp he).2 (mem_union_left _ heQ)
  have heL : e ∈ L := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp he).1, heQ⟩, heX⟩
  exact (mem_sdiff.mp he).2 (mem_union_right _ (mem_union_left _ heL))


end PartitionedTriangleAbsorption.ReserveConfinementStage195
