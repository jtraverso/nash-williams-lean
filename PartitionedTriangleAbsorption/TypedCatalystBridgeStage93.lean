/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystProducerStage89
public import PartitionedTriangleAbsorption.EdgeTypeMatchingStage91

/-! # Integrating the completed catalyst return with type-preserving deployment

The return's producer is strengthened only at its deployment call: Stage90
retains the selected labels and hence the edge-type vector. All catalyst
selection, framing, insertion and separation proofs are reused unchanged.
No terminal triangle decomposition or private absorber is claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

open Finset AntiEdgeSelection TypedTransformer PhysicalMovesStage86
  CatalystSelectionStage89 CatalystFramingStage89 CatalystInsertionStage89

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Actual deployment and catalyst selection, retaining the type vector. -/
theorem deploy_reserve_frame (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hb : (Z.card : ℝ) + 52 * X.card + 4 * (d + U.card) < a) :
    ∃ (Y L : Finset (Sym2 V)) (m : ℕ) (co cs ct : V → V), m ≤ X.card ∧
      (∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) ∧
      Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = X.card ∧ edgeVec p Y = edgeVec p X ∧
      (∀ u v, s(u, v) ∈ Y → ∃ k, Link F (p u) (p v) k) ∧
      U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      Catalysts p F G B L (Z ∪ active Y) (active Y) co cs ct ∧
      (active Y).card = Y.card ∧
      HasDecomp p F (catUnion (active Y) co cs ct) ∧
      catUnion (active Y) co cs ct ⊆ G.edgeFinset ∧
      Disjoint (catUnion (active Y) co cs ct) (B ∪ L) ∧
      (catUnion (active Y) co cs ct).card ≤ 3 * Y.card ∧
      PhysicalMoves p F G.edgeFinset B (U ∪ catUnion (active Y) co cs ct)
        (X ∪ catUnion (active Y) co cs ct) (Y ∪ catUnion (active Y) co cs ct) m ∧
      (∀ W k, PhysicalMoves p F G.edgeFinset B (L ∪ catUnion (active Y) co cs ct)
          (Y ∪ catUnion (active Y) co cs ct) W k →
        PhysicalMoves p F G.edgeFinset B (U ∪ catUnion (active Y) co cs ct)
          (X ∪ catUnion (active Y) co cs ct) W (m + k)) := by
  have hb37 : (Z.card : ℝ) + 37 * X.card + 4 * (d + U.card) < a := by
    have : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    linarith
  obtain ⟨Y, m, hm, ht, hdeg, hYG, hYB, hYc, hYvec⟩ :=
    TypedDeploymentStage90.deploy p F hF G a d hs B U X Z hB hd hXU hXG hXB hZ hact
      heven hb37
  obtain ⟨L, hUL, hYL, hLc, hcont⟩ := padded_ledger ht hXU
  have hactY := links_of_trace ht hact
  have hZY : ∀ e ∈ Y, ∀ v ∈ e, v ∈ Z ∪ active Y := fun e he v hv =>
    mem_union.mpr (Or.inr (mem_active_of_mem hdeg he hv))
  have hZc : ((Z ∪ active Y).card : ℝ) ≤ Z.card + (active Y).card := by
    exact_mod_cast card_union_le _ _
  have hloop : ∀ e ∈ Y, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hYG he))
  have hAc := active_card hloop hdeg
  have hLc' : (L.card : ℝ) ≤ U.card + 9 * X.card := by
    have : L.card ≤ U.card + 9 * X.card :=
      hLc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 9 hm) _)
    exact_mod_cast this
  have hYc' : (Y.card : ℝ) = X.card := by exact_mod_cast hYc
  have hAc' : ((active Y).card : ℝ) = X.card := by rw [hAc]; exact hYc'
  obtain ⟨co, cs, ct, hc, -, -, hdec, hDG, hDBL, hDc⟩ :=
    select_catalysts p F G a d hs B L Y (Z ∪ active Y) hB hd hYG hdeg hactY hZY
      (by rw [hYc']; linarith)
  have hDL : Disjoint (catUnion (active Y) co cs ct) L :=
    hDBL.mono_right subset_union_right
  refine ⟨Y, L, m, co, cs, ct, hm, hdeg, hYG, hYB, hYc, hYvec, hactY, hUL, hYL,
    hLc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 9 hm) _), hc, hAc, hdec, hDG, hDBL,
    hDc, ?_, fun W k hW => hcont _ hDL W k hW⟩
  simpa using hcont _ hDL _ 0 (.stop _ _)

/-- Deployment and actual insertion, retaining the original type inventory. -/
theorem catalyst_producer {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hb : (Z.card : ℝ) + 176 * X.card + 4 * (d + U.card) < a) :
    ∃ (S : Data V) (L : Finset (Sym2 V)) (m : ℕ) (cz cz' : V → V)
      (U₂ : Finset (Sym2 V)) (Z₂ : Finset V),
      -- deployment
      m ≤ X.card ∧ (∀ v, incidentLoad S.Y v = 0 ∨ incidentLoad S.Y v = 2) ∧
      S.Y ⊆ G.edgeFinset ∧ Disjoint S.Y B ∧ S.Y.card = X.card ∧ edgeVec p S.Y = edgeVec p X ∧
      S.A = active S.Y ∧ S.A.card = S.Y.card ∧
      U ⊆ L ∧ S.Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      -- catalyst selection
      Catalysts p F G B L (Z ∪ S.A) S.A S.co S.cs S.ct ∧
      HasDecomp p F S.cats ∧ S.cats ⊆ G.edgeFinset ∧ Disjoint S.cats (B ∪ L) ∧
      S.cats.card ≤ 3 * S.Y.card ∧
      -- insertion frame and final invariant
      Frame p F G B S (Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct) ∧
      Inv p F G B S (Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct) cz cz' S.A U₂ Z₂ ∧
      U₂.card ≤ (L ∪ S.cats).card + 27 * S.A.card ∧
      -- the actual trace, deployment followed by insertion
      PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats)
        (S.config cz cz' S.A) (m + 3 * S.A.card) ∧
      (∀ W k, PhysicalMoves p F G.edgeFinset B U₂ (S.config cz cz' S.A) W k →
        PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) W
          (m + (3 * S.A.card + k))) ∧
      -- the final configuration is 2-regular
      (∀ v, incidentLoad (S.config cz cz' S.A) v = 0 ∨
        incidentLoad (S.config cz cz' S.A) v = 2) := by
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  obtain ⟨Y, L, m, co, cs, ct, hm, hdeg, hYG, hYB, hYc, hYvec, hactY, hUL, hYL, hLc, hc, hAc,
      hdec, hDG, hDBL, hDc, -, hcont⟩ :=
    deploy_reserve_frame G a d hF hs B U X Z hB hd hXU hXG hXB hZ hact heven
      (by linarith)
  have hstar : ∀ y ∈ active Y, ∃ ab : V × V, ab.1 ≠ ab.2 ∧
      Y.filter (fun e => y ∈ e) = {s(y, ab.1), s(y, ab.2)} := by
    intro y hy
    obtain ⟨a, b, hab, h⟩ := exists_star hy
    exact ⟨(a, b), hab, h⟩
  choose! nmp hnmp using hstar
  set S : Data V := ⟨Y, active Y, fun y => (nmp y).1, fun y => (nmp y).2, co, cs, ct⟩ with hS
  have fr : Frame p F G B S (Z ∪ active Y ∪ catVertsAll (active Y) co cs ct) :=
    frame_of_selection (nm := fun y => (nmp y).1) (np := fun y => (nmp y).2)
      (fun y hy => hnmp y hy) hdeg hYG hYB hactY hc
  set Z₀ := Z ∪ active Y ∪ catVertsAll (active Y) co cs ct with hZ₀
  have hZ₀c : (Z₀.card : ℝ) ≤ Z.card + 4 * X.card := by
    have h1 : Z₀.card ≤ (Z ∪ active Y).card + (catVertsAll (active Y) co cs ct).card :=
      card_union_le _ _
    have h2 : (Z ∪ active Y).card ≤ Z.card + (active Y).card := card_union_le _ _
    have h3 := catVertsAll_card_le (active Y) co cs ct
    have : Z₀.card ≤ Z.card + 4 * X.card := by omega
    exact_mod_cast this
  have hU₀c : ((L ∪ S.cats).card : ℝ) ≤ U.card + 12 * X.card := by
    have h1 : (L ∪ S.cats).card ≤ L.card + S.cats.card := card_union_le _ _
    have h2 : S.cats.card ≤ 3 * Y.card := hDc
    have : (L ∪ S.cats).card ≤ U.card + 12 * X.card := by omega
    exact_mod_cast this
  have hAc' : (S.A.card : ℝ) = X.card := by
    change ((active Y).card : ℝ) = X.card
    rw [hAc]; exact_mod_cast hYc
  obtain ⟨cz, cz', U₂, Z₂, inv, hU₂, -, htr, hcont₂⟩ :=
    insert_catalysts a d hF hs hB hd fr (L ∪ S.cats)
      (union_subset_union hYL (Subset.refl _)) (by rw [hAc']; linarith)
  refine ⟨S, L, m, cz, cz', U₂, Z₂, hm, hdeg, hYG, hYB, hYc, hYvec, rfl, hAc, hUL, hYL, hLc, hc,
    hdec, hDG, hDBL, hDc, fr, inv, hU₂, hcont _ _ htr, fun W k h => hcont _ _ (hcont₂ W k h),
    final_two_regular fr inv.carriers⟩


/-- Original token positions preserve their unordered endpoint-label type.
This follows from the actual insertion invariant, including carrier labels. -/
theorem original_token_type {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}
    {U : Finset (Sym2 V)} {Z : Finset V}
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z) (e : Sym2 V) :
    Sym2.map p (S.curY cz cz' S.A e) = Sym2.map p e := by
  have hrep (u : V) (e : Sym2 V) : p (S.rep cz cz' S.A u e) = p u := by
    unfold Data.rep
    by_cases hu : u ∈ S.A
    · simp only [ite_eq_left hu]
      split_ifs
      · exact (inv.carrier_label u hu).1
      · exact (inv.carrier_label u hu).2
    · simp [hu]
  induction e using Sym2.ind with
  | _ u v =>
    change s(p (S.rep cz cz' S.A u s(u,v)), p (S.rep cz cz' S.A v s(u,v))) = s(p u,p v)
    rw [hrep, hrep]

end PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

