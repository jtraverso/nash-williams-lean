/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0PrivateHost
public import PartitionedTriangleAbsorption.DivisiblePrivateAbsorberStage101

/-! # Private typed absorbers on the actual unsaturated, unoccupied host

Source vertices are retained even when saturated. All other saturated vertices
and all occupied edges except source edges are removed before construction.
The returned absorber is constructed, not supplied as a certificate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedPrivateHostStage208

open Finset SignedHinge SparseReserveGeometry AntiEdgeSelection TypedTransformer
  TypedEmbeddingSelection PairMoveSelectionStage85 PairMoveAssemblyStage85

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem compatible_supply_deleted_induced (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G J : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel J.Adj] (K : Finset V) (a d a' : ℝ)
    (hd : 0 ≤ d) (hs : CompatibleSupply p F G a)
    (hdel : ∀ v, ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤ d)
    (hbudget : a' + (univ \ K).card + 4 * d ≤ a) :
    CompatibleSupply (fun w : K => p w.val) F (J.induce (↑K : Set V)) a' := by
  classical
  intro S hS i hi
  let R := S.image Subtype.val
  let C := typedNeighbours p G R i
  let Q := typedNeighbours (fun w : K => p w.val) (J.induce (↑K : Set V)) S i
  let bad := fun u => univ.filter fun w => G.Adj u w ∧ ¬ J.Adj u w
  have hR : R.card ≤ 4 := card_image_le.trans hS
  have hc : Compatible p F R i := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    exact hi x hx
  have hcover : C ⊆ (Q.image Subtype.val ∪ (univ \ K)) ∪ R.biUnion bad := by
    intro w hw
    obtain ⟨hp, hroot⟩ := (mem_filter.mp hw).2
    by_cases hwK : w ∈ K
    · by_cases hall : ∀ u ∈ R, J.Adj u w
      · exact mem_union_left _ (mem_union_left _ (mem_image.mpr
          ⟨⟨w, hwK⟩, mem_filter.mpr ⟨mem_univ _, hp,
            fun x hx => hall x.val (mem_image.mpr ⟨x, hx, rfl⟩)⟩, rfl⟩))
      · push Not at hall
        obtain ⟨u, hu, huw⟩ := hall
        exact mem_union_right _ (mem_biUnion.mpr
          ⟨u, hu, mem_filter.mpr ⟨mem_univ _, hroot u hu, huw⟩⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _, hwK⟩))
  have hcount : (C.card : ℝ) ≤ Q.card + (univ \ K).card +
      ∑ u ∈ R, ((bad u).card : ℝ) := by
    have h := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add (card_union_le _ _) card_biUnion_le))
    rw [card_image_of_injective _ Subtype.val_injective] at h
    exact_mod_cast h
  have hbad : (∑ u ∈ R, ((bad u).card : ℝ)) ≤ 4 * d := by
    calc
      _ ≤ ∑ _u ∈ R, d := sum_le_sum fun u _ => hdel u
      _ = (R.card : ℝ) * d := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hR) hd
  have hsource : a ≤ (C.card : ℝ) := hs R hR i hc
  change a' ≤ (Q.card : ℝ)
  linarith only [hsource, hcount, hbad, hbudget]

theorem exists_private_avoiding (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F)
    (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ b N : ℕ, 0 < b ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
      (P B : Finset (Sym2 V)) (Z : Finset V) (d : ℝ),
      N ≤ Fintype.card V → 0 ≤ d →
      CompatibleSupply p F G (β * Fintype.card V) → DegBounded B d →
      (Z.card : ℝ) + 4 * d ≤ β * Fintype.card V / 2 →
      P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A B ∧
        HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧
        A.card ≤ b ∧ (vertSet A).card ≤ b ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∉ vertSet P → v ∉ Z := by
  obtain ⟨q, hprod⟩ := PrivateAbsorberStage101.private_absorber_from_divisible F hcard hF m
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (388 * m + 1164 * q + 1 : ℝ) / β)
  refine ⟨max 1 (2 * (93 * m + 282 * q)), N, by omega, ?_⟩
  intro V _ _ p G _ P B Z d hn hd hs hB hbudget hPG hm hdiv
  classical
  let K := univ \ (Z \ vertSet P)
  let f : K ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let J := withoutEdges G (B \ P)
  let JK := J.induce (↑K : Set V)
  have hkeep : ∀ e ∈ P, ∀ v ∈ e, v ∈ K := by
    intro e he v hv
    have hvP : v ∈ vertSet P := SignedHinge.mem_vertSet.mpr ⟨e, he, hv⟩
    simp [K, hvP]
  have hback : (F0PrivateHost.source K P).map (PhysicalHingeSupply.edgeEmb f) = P :=
    F0PrivateHost.source_map K P hkeep
  have hexclude : univ \ K ⊆ Z := by
    intro v hv
    have hvK := (mem_sdiff.mp hv).2
    by_contra hvZ
    exact hvK (by simp [K, hvZ])
  have hdel : ∀ v,
      ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤ d := by
    intro v
    have h := PrivateTemplateStage69.deleted_card_le G (B \ P) v
    have hm' : ((B \ P).filter (fun e => v ∈ e)).card ≤
        (B.filter (fun e => v ∈ e)).card :=
      card_le_card (filter_subset_filter (fun e => v ∈ e) sdiff_subset)
    have h' : ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤
        incidentLoad B v := by exact_mod_cast h.trans hm'
    exact h'.trans (hB v)
  have hJK : CompatibleSupply (fun w : K => p w.val) F JK
      (β * Fintype.card V / 2) :=
    compatible_supply_deleted_induced p F G J K _ d _ hd hs hdel
      (by have h : ((univ \ K).card : ℝ) ≤ Z.card :=
            by exact_mod_cast card_le_card hexclude
          linarith only [h, hbudget])
  have hPK : F0PrivateHost.source K P ⊆ JK.edgeFinset := by
    intro e he
    have horig : Sym2.map Subtype.val e ∈ P := (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ a b =>
      have hGorig := G.mem_edgeFinset.mp (hPG horig)
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change J.Adj a.val b.val
      exact (withoutEdges_adj G (B \ P) a.val b.val).mpr
        ⟨hGorig, fun h => (mem_sdiff.mp h).2 horig⟩
  have hdivK : IsIntDiv (fun w : K => p w.val) F (F0PrivateHost.source K P) := by
    apply PrivateTemplateStage69.isIntDiv_comap f
    rw [hback]
    exact hdiv
  have hcardK : (F0PrivateHost.source K P).card ≤ m := by
    have hc := congrArg Finset.card hback
    rw [card_map] at hc
    exact hc.trans_le hm
  have hNn : (N : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hscale : 388 * (m : ℝ) + 1164 * q < β * Fintype.card V / 2 := by
    have h := (div_lt_iff₀ hβ).mp (hN.trans_le hNn)
    linarith only [h]
  obtain ⟨Ak, habs, -, hc, hAk⟩ := hprod JK (fun w => p w.val)
    (β * Fintype.card V / 2) 0 hJK ∅ (F0PrivateHost.source K P)
    (vertSet (F0PrivateHost.source K P)) (by simp [DegBounded]) le_rfl
    hPK (by simp) (fun e he v hv => SignedHinge.mem_vertSet.mpr ⟨e, he, hv⟩)
    hcardK hdivK (by
      have hz := SignedHinge.card_vertSet_le (F0PrivateHost.source K P)
      have hz' : ((vertSet (F0PrivateHost.source K P)).card : ℝ) ≤ 2 * m :=
        by exact_mod_cast hz.trans (Nat.mul_le_mul_left 2 hcardK)
      have hp' : ((F0PrivateHost.source K P).card : ℝ) ≤ m := by exact_mod_cast hcardK
      linarith only [hz', hp', hscale])
  let A := Ak.map (PhysicalHingeSupply.edgeEmb f)
  have hAP : Disjoint A P := by
    rw [← hback]
    exact (disjoint_map _).mpr habs.1
  have hAJ : ∀ e ∈ A, e ∈ J.edgeSet := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    have h := SimpleGraph.mem_edgeFinset.mp (hAk he')
    induction e' using Sym2.ind with
    | _ a b =>
      change J.Adj a.val b.val
      exact h
  have hhost : ∀ e ∈ A, e ∈ G.edgeSet ∧ e ∉ B := by
    intro e he
    have h := hAJ e he
    have hnP := disjoint_left.mp hAP he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at h ⊢
      obtain ⟨hGedge, hfree⟩ := (withoutEdges_adj G (B \ P) a b).mp h
      exact ⟨hGedge, fun hBedge => hfree (mem_sdiff.mpr ⟨hBedge, hnP⟩)⟩
  have hAc : A.card ≤ 93 * m + 282 * q := by simpa only [A, card_map] using hc
  refine ⟨A, fun e he => G.mem_edgeFinset.mpr ((hhost e he).1),
    disjoint_left.mpr (fun e he => (hhost e he).2),
    PhysicalHingeSupply.hasDecomp_map f (pV := p) (fun _ => rfl) habs.2.1,
    ?_, by omega, ?_, ?_⟩
  · have h := PhysicalHingeSupply.hasDecomp_map f (pV := p) (fun _ => rfl) habs.2.2
    rw [map_union, hback] at h
    exact h
  · exact (SignedHinge.card_vertSet_le A).trans (by omega)
  · intro e he v hv hvP hvZ
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    obtain ⟨w, -, hw⟩ := Sym2.mem_map.mp hv
    have hwK : v ∈ K := hw ▸ w.property
    exact (mem_sdiff.mp hwK).2 (mem_sdiff.mpr ⟨hvZ, hvP⟩)


end PartitionedTriangleAbsorption.TypedPrivateHostStage208
