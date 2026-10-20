/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.DivisiblePrivateAbsorberStage101
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # A physical private family fixed before residual selection

All absorbers are produced by Stage101. Their edge sets avoid the whole piece
support J and are mutually disjoint. The size budget is global; this does not
claim a sparse refiner or a degree-efficient family for a quadratic library.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateFamilyStage102

open Finset TypedTransformer PairMoveAssemblyStage85 PairMoveSelectionStage85
  AntiEdgeSelection

variable {t : ℕ} {I V : Type*} [DecidableEq I] [DecidableEq V] [Fintype V]
  {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- The actual produced family, including its physical union bound. -/
structure Family (s : Finset I) (P : I → Finset (Sym2 V))
    (B J E : Finset (Sym2 V)) (C : ℕ) (A : I → Finset (Sym2 V)) : Prop where
  absorbs : ∀ i ∈ s, Absorbs (p := p) (F := F) (A i) (P i)
  avoids : ∀ i ∈ s, Disjoint (A i) (B ∪ J)
  size : ∀ i ∈ s, (A i).card ≤ C
  physical : ∀ i ∈ s, A i ⊆ E
  disjoint : (s : Set I).PairwiseDisjoint A
  total : (s.biUnion A).card ≤ s.card * C

/-- Uniform bounded-divisibility coefficient choice followed by a real family
induction. Only the piece library is supplied, not its private absorbers. -/
theorem exists_private_family (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F) (K : ℕ) :
    ∃ q : ℕ, ∀ {I V : Type} [DecidableEq I] [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
      (a d : ℝ) (_hs : CompatibleSupply p F G a)
      (s : Finset I) (P : I → Finset (Sym2 V)) (B J : Finset (Sym2 V))
      (_hB : DegBounded B d) (_hd : 0 ≤ d),
      (∀ i ∈ s, P i ⊆ J ∧ P i ⊆ G.edgeFinset ∧ Disjoint (P i) B ∧
        (P i).card ≤ K ∧ IsIntDiv p F (P i)) →
      388 * (K : ℝ) + 1164 * q +
        4 * (d + J.card + s.card * (93 * K + 282 * q)) < a →
      ∃ A, Family (p := p) (F := F) s P B J G.edgeFinset (93 * K + 282 * q) A := by
  obtain ⟨q, prod⟩ := PrivateAbsorberStage101.private_absorber_from_divisible F hcard hF K
  refine ⟨q, fun {I V} _ _ _ G _ p a d hs s P B J hB hd hp hb => ?_⟩
  classical
  let C := 93 * K + 282 * q
  have build : ∀ z : Finset I, z ⊆ s →
      ∃ A, Family (p := p) (F := F) z P B J G.edgeFinset C A := by
    intro z
    induction z using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ => ∅, ?_⟩
      constructor <;> simp
    | @insert i z hi ih =>
      intro hzs
      have hz : z ⊆ s := fun j hj => hzs (mem_insert_of_mem hj)
      have his : i ∈ s := hzs (mem_insert_self _ _)
      obtain ⟨A, fam⟩ := ih hz
      obtain ⟨hPJ, hPG, hPB, hPK, hdiv⟩ := hp i his
      let D := z.biUnion A
      let B' := B ∪ (J \ P i) ∪ D
      have hDBJ : Disjoint D (B ∪ J) := by
        rw [disjoint_biUnion_left]
        exact fam.avoids
      have hPD : Disjoint (P i) D :=
        ((disjoint_union_right.mp hDBJ).2.mono_right hPJ).symm
      have hPB' : Disjoint (P i) B' :=
        disjoint_union_right.mpr ⟨disjoint_union_right.mpr
          ⟨hPB, by
            rw [disjoint_left]
            exact fun e he he' => (mem_sdiff.mp he').2 he⟩, hPD⟩
      have hB' : DegBounded B' (d + (J \ P i).card + D.card) :=
        blocked_union_degree (B ∪ (J \ P i)) D _
          (blocked_union_degree B (J \ P i) d hB)
      have hDc : D.card ≤ s.card * C :=
        fam.total.trans (Nat.mul_le_mul_right C (card_le_card hz))
      have hJc : (J \ P i).card ≤ J.card := card_le_card sdiff_subset
      have hZc : (vertSet (P i)).card ≤ 2 * K :=
        (SignedHinge.card_vertSet_le (P i)).trans (Nat.mul_le_mul_left 2 hPK)
      have hDr : (D.card : ℝ) ≤ s.card * C := by exact_mod_cast hDc
      have hJr : ((J \ P i).card : ℝ) ≤ J.card := by exact_mod_cast hJc
      have hZr : ((vertSet (P i)).card : ℝ) ≤ 2 * K := by exact_mod_cast hZc
      have hPr : ((P i).card : ℝ) ≤ K := by exact_mod_cast hPK
      have hCr : (C : ℝ) = 93 * K + 282 * q := by simp [C]
      obtain ⟨Ai, habs, havoid, hsize, hphys⟩ :=
        prod G p a (d + (J \ P i).card + D.card) hs B' (P i) (vertSet (P i))
          hB' (by positivity) hPG hPB'
          (fun e he v hv => SignedHinge.mem_vertSet.mpr ⟨e, he, hv⟩) hPK hdiv
          (by rw [hCr] at hDr; linarith)
      have hAiD : Disjoint Ai D := (disjoint_union_right.mp havoid).2
      have hAiB : Disjoint Ai B :=
        (disjoint_union_right.mp (disjoint_union_right.mp havoid).1).1
      have hAiJ : Disjoint Ai J := by
        rw [disjoint_left]
        intro e he hj
        by_cases hpi : e ∈ P i
        · exact (disjoint_left.mp habs.1) he hpi
        · exact (disjoint_left.mp
            (disjoint_union_right.mp (disjoint_union_right.mp havoid).1).2)
            he (mem_sdiff.mpr ⟨hj, hpi⟩)
      let A' := Function.update A i Ai
      have hkeep : ∀ j ∈ z, A' j = A j := fun j hj =>
        Function.update_of_ne (ne_of_mem_of_not_mem hj hi) Ai A
      have hnew : A' i = Ai := Function.update_self _ _ _
      have hcross : ∀ j ∈ z, Disjoint Ai (A j) := by
        intro j hj
        exact hAiD.mono_right (fun e he => mem_biUnion.mpr ⟨j, hj, he⟩)
      have hsz : ∀ j ∈ insert i z, (A' j).card ≤ C := by
        intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa only [hnew] using hsize
        · simpa only [hkeep j hj] using fam.size j hj
      refine ⟨A', ?_⟩
      constructor
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa only [hnew] using habs
        · simpa only [hkeep j hj] using fam.absorbs j hj
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa only [hnew] using disjoint_union_right.mpr ⟨hAiB, hAiJ⟩
        · simpa only [hkeep j hj] using fam.avoids j hj
      · exact hsz
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa only [hnew] using hphys
        · simpa only [hkeep j hj] using fam.physical j hj
      · intro j hj k hk hjk
        change Disjoint (A' j) (A' k)
        by_cases hji : j = i
        · subst j
          have hkz := (mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hnew, hkeep k hkz] using hcross k hkz
        · have hjz := (mem_insert.mp hj).resolve_left hji
          by_cases hki : k = i
          · subst k
            simpa only [hnew, hkeep j hjz] using (hcross j hjz).symm
          · have hkz := (mem_insert.mp hk).resolve_left hki
            simpa only [Function.onFun, hkeep j hjz, hkeep k hkz]
              using fam.disjoint hjz hkz hjk
      · exact (card_biUnion_le).trans (by simpa using sum_le_sum hsz)
  exact build s (Subset.refl _)

end PartitionedTriangleAbsorption.PrivateFamilyStage102
