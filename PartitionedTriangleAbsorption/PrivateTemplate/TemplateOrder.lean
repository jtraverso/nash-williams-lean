/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.TemplateCounts

/-!
# A concrete rooted order of the template, of degeneracy four

The rank of a vertex is `0` for roots and `tagIdx t * m + j + 1` for the auxiliary `(j, t)`
(the centre gets index `1`).  The tag order is

`q < centre < j1 < j2 < j3 < p1 < q1 < p2a < p2b < q2a < q2b < tp·0 < tq·0 < tp·1 < tq·1
 < tp·2 < tq·2`,

i.e. `Q, J`, then first and second subdivision vertices, then the transformer auxiliaries,
all `u`'s before all `v`'s before all `w`'s.  Every auxiliary has at most four template
neighbours of smaller rank (all roots included).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

/-- Position of a tag in the order. -/
def tagIdx : Tag → ℕ
  | .q => 0
  | .j1 => 2
  | .j2 => 3
  | .j3 => 4
  | .p1 => 5
  | .q1 => 6
  | .p2a => 7
  | .p2b => 8
  | .q2a => 9
  | .q2b => 10
  | .tp k c => 11 + 8 * c.val + k.val
  | .tq k c => 15 + 8 * c.val + k.val

theorem tagIdx_injective : Function.Injective tagIdx := by
  intro t t' h
  cases t <;> cases t' <;> simp [tagIdx] at h ⊢ <;> omega

variable {Rt : Type*} {m : ℕ}

/-- The rank of a template vertex: roots first, then auxiliaries by tag, then position. -/
def rank : TV Rt m → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inr _) => m + 1
  | Sum.inr (Sum.inl (j, t)) => tagIdx t * m + j.val + 1

theorem rank_aux (j : Fin m) (t : Tag) : rank (aux j t : TV Rt m) = tagIdx t * m + j.val + 1 :=
  rfl

theorem rank_aux_lt {t t' : Tag} (h : tagIdx t < tagIdx t') (j j' : Fin m) :
    rank (aux j t : TV Rt m) < rank (aux j' t' : TV Rt m) := by
  rw [rank_aux, rank_aux]
  have hj := j.isLt
  have : (tagIdx t + 1) * m ≤ tagIdx t' * m := Nat.mul_le_mul_right _ h
  nlinarith

theorem rank_centre_lt {t : Tag} (h : 1 < tagIdx t) (hm : 0 < m) (j : Fin m) :
    rank (centre hm : TV Rt m) < rank (aux j t : TV Rt m) := by
  change m + 1 < tagIdx t * m + j.val + 1
  have : 2 * m ≤ tagIdx t * m := Nat.mul_le_mul_right _ h
  omega

/-- The rank is injective on auxiliaries. -/
theorem rank_injective_aux : Function.Injective fun u : AuxV m => rank (Sum.inr u : TV Rt m) := by
  rintro (⟨j, t⟩ | ⟨⟨⟩, h⟩) (⟨j', t'⟩ | ⟨⟨⟩, h'⟩) he
  · simp only [rank] at he
    have hj := j.isLt
    have hj' := j'.isLt
    have h1 : tagIdx t = tagIdx t' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have : (tagIdx t + 1) * m ≤ tagIdx t' * m := Nat.mul_le_mul_right _ hlt
        nlinarith
      · have : (tagIdx t' + 1) * m ≤ tagIdx t * m := Nat.mul_le_mul_right _ hlt
        nlinarith
    have h2 : j.val = j'.val := by rw [h1] at he; omega
    rw [tagIdx_injective h1, Fin.ext h2]
  · simp only [rank] at he
    have hj := j.isLt
    exfalso
    rcases Nat.lt_or_ge (tagIdx t) 2 with ht | ht
    · cases t <;> simp [tagIdx] at ht he <;> omega
    · have : 2 * m ≤ tagIdx t * m := Nat.mul_le_mul_right _ ht
      omega
  · simp only [rank] at he
    have hj := j'.isLt
    exfalso
    rcases Nat.lt_or_ge (tagIdx t') 2 with ht | ht
    · cases t' <;> simp [tagIdx] at ht he <;> omega
    · have : 2 * m ≤ tagIdx t' * m := Nat.mul_le_mul_right _ ht
      omega
  · rfl

variable [DecidableEq Rt]

theorem blowPerm_symm_apply (σ : Equiv.Perm (Fin m)) (j : Fin m) (k : Fin 4) :
    (blowPerm σ).symm (j, k) = if k = 0 then (σ.symm j, 3) else (j, k - 1) := by
  rw [Equiv.symm_apply_eq]
  fin_cases k <;> simp

variable (σt : Equiv.Perm (Fin m)) (xr : Fin m → Rt) (h3 : 3 ∣ m)

/-- The template neighbours of an auxiliary which may precede it. -/
noncomputable def lowerNbrs : AuxV m → Finset (TV Rt m)
  | Sum.inr _ => ∅
  | Sum.inl (j, .q) => {qv (triPerm h3 j), qv ((triPerm h3).symm j)}
  | Sum.inl (j, .j1) => {centre j.pos}
  | Sum.inl (j, .j2) => {aux j .j1}
  | Sum.inl (j, .j3) => {aux j .j2, centre j.pos}
  | Sum.inl (j, .p1) => {Sum.inl (xr j), Sum.inl (xr (σt j))}
  | Sum.inl (j, .q1) => {qv j, qv (triPerm h3 j)}
  | Sum.inl (j, .p2a) => {Sum.inl (xr j), aux j .p1}
  | Sum.inl (j, .p2b) => {aux j .p1, Sum.inl (xr (σt j))}
  | Sum.inl (j, .q2a) => {qv j, aux j .q1}
  | Sum.inl (j, .q2b) => {aux j .q1, qv (triPerm h3 j)}
  | Sum.inl (j, .tp k 0) => {xP xr (j, k), petalV (j, k), xP xr ((blowPerm σt).symm (j, k)),
      petalV ((blowPerm σt).symm (j, k))}
  | Sum.inl (j, .tp k 1) => {xP xr (j, k), petalV (j, k), aux j (.tp k 0)}
  | Sum.inl (j, .tp k 2) => {xP xr (j, k), petalV (j, k), aux j (.tp k 1),
      auxP (blowPerm σt (j, k), 0)}
  | Sum.inl (j, .tq k 0) => {xQ (j, k), petalV (j, k), xQ ((blowPerm (triPerm h3)).symm (j, k)),
      petalV ((blowPerm (triPerm h3)).symm (j, k))}
  | Sum.inl (j, .tq k 1) => {xQ (j, k), petalV (j, k), aux j (.tq k 0)}
  | Sum.inl (j, .tq k 2) => {xQ (j, k), petalV (j, k), aux j (.tq k 1),
      auxQ (blowPerm (triPerm h3) (j, k), 0)}

theorem card_le_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
    (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))

theorem card_le_three {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))

theorem card_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 :=
  (card_insert_le _ _).trans (by simp)

theorem card_lowerNbrs (u : AuxV m) : (lowerNbrs σt xr h3 u).card ≤ 4 := by
  rcases u with ⟨j, t⟩ | c
  · cases t with
    | tp k c =>
      fin_cases c
      · exact card_le_four _ _ _ _
      · exact (card_le_three _ _ _).trans (by norm_num)
      · exact card_le_four _ _ _ _
    | tq k c =>
      fin_cases c
      · exact card_le_four _ _ _ _
      · exact (card_le_three _ _ _).trans (by norm_num)
      · exact card_le_four _ _ _ _
    | j1 => simp [lowerNbrs]
    | j2 => simp [lowerNbrs]
    | _ => exact (card_le_two _ _).trans (by norm_num)
  · simp [lowerNbrs]

/-- The ordering property to be checked edge by edge. -/
def OrderedEdges (X : Finset (Sym2 (TV Rt m))) : Prop :=
  ∀ e ∈ X, ∀ (u : AuxV m) (w : TV Rt m), e = s(Sum.inr u, w) →
    w ∈ lowerNbrs σt xr h3 u ∨ rank (Sum.inr u : TV Rt m) < rank w

theorem OrderedEdges.union {X Y : Finset (Sym2 (TV Rt m))} (hX : OrderedEdges σt xr h3 X)
    (hY : OrderedEdges σt xr h3 Y) : OrderedEdges σt xr h3 (X ∪ Y) := by
  intro e he
  rcases mem_union.mp he with he | he
  exacts [hX e he, hY e he]

set_option hygiene false in
/-- Close one oriented edge `s(A, B) = s(inr u, w)`. -/
local macro "oclose" : tactic => `(tactic|
  (rcases Sym2.eq_iff.mp hh with ⟨hu, rfl⟩ | ⟨rfl, hu⟩ <;>
   rcases u with ⟨j', t'⟩ | ⟨⟨⟩, hc⟩ <;>
   (try simp (config := {decide := true}) only [xP, xQ, pathV, petalV, auxP, auxQ,
     blowPerm_apply, Fin.isValue,
     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
     Fin.reduceAdd, reduceIte, Fin.reduceEq, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq,
     Prod.mk.injEq, Tag.tp.injEq, Tag.tq.injEq, and_true, true_and] at hu) <;>
   (try obtain ⟨rfl, rfl⟩ := hu) <;>
   first
   | (left
      simp [lowerNbrs, xP, xQ, pathV, petalV, auxP, auxQ, blowPerm_symm_apply]
      done)
   | (right
      (try simp (config := {decide := true}) only [xP, xQ, pathV, petalV, auxP, auxQ,
        blowPerm_apply, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Fin.reduceAdd, reduceIte, Fin.reduceEq])
      first
      | exact rank_aux_lt (by decide) _ _
      | exact rank_centre_lt (by decide) _ _)))

theorem orderedEdges_P1 : OrderedEdges σt xr h3 (edgesP1 σt xr) := by
  intro e he u w hh
  rcases mem_union.mp he with he | he <;> obtain ⟨j, rfl⟩ := mem_posEdges.mp he <;> oclose

theorem orderedEdges_P2 : OrderedEdges σt xr h3 (edgesP2 σt xr) := by
  intro e he u w hh
  rw [edgesP2, xP, mem_srcEdges_pathV] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> oclose

theorem orderedEdges_J : OrderedEdges σt xr h3 (edgesJ σt) := by
  intro e he u w hh
  rw [edgesJ, mem_srcEdges_petalV] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> oclose

theorem orderedEdges_Q2 : OrderedEdges σt xr h3 (edgesQ2 h3) := by
  intro e he u w hh
  rw [edgesQ2, xQ, mem_srcEdges_pathV] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> oclose

theorem orderedEdges_Q1 : OrderedEdges σt xr h3 (edgesQ1 h3) := by
  intro e he u w hh
  rcases mem_union.mp he with he | he <;> obtain ⟨j, rfl⟩ := mem_posEdges.mp he <;> oclose

theorem orderedEdges_Q : OrderedEdges σt xr h3 (edgesQ h3) := by
  intro e he u w hh
  obtain ⟨j, rfl⟩ := mem_posEdges.mp he
  oclose

theorem orderedEdges_TP : OrderedEdges σt xr h3 (edgesTP σt xr) := by
  intro e he u w hh
  simp only [edgesTP, transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨⟨j, k⟩, he⟩ := he
  simp only [transAt, mem_insert, mem_singleton] at he
  fin_cases k <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> oclose

theorem orderedEdges_TQ : OrderedEdges σt xr h3 (edgesTQ h3) := by
  intro e he u w hh
  simp only [edgesTQ, transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨⟨j, k⟩, he⟩ := he
  simp only [transAt, mem_insert, mem_singleton] at he
  fin_cases k <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> oclose

theorem orderedEdges_template : OrderedEdges σt xr h3 (template σt xr h3) := by
  intro e he
  simp only [template, mem_union] at he
  rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he
  exacts [orderedEdges_P1 σt xr h3 e he, orderedEdges_P2 σt xr h3 e he,
    orderedEdges_TP σt xr h3 e he, orderedEdges_J σt xr h3 e he,
    orderedEdges_TQ σt xr h3 e he, orderedEdges_Q2 σt xr h3 e he,
    orderedEdges_Q1 σt xr h3 e he, orderedEdges_Q σt xr h3 e he]

/-- Every template neighbour of an auxiliary which precedes it lies in `lowerNbrs`. -/
theorem mem_lowerNbrs_of_lt (u : AuxV m) (w : TV Rt m) (hw : s(Sum.inr u, w) ∈ template σt xr h3)
    (hr : rank w < rank (Sum.inr u : TV Rt m)) : w ∈ lowerNbrs σt xr h3 u := by
  rcases orderedEdges_template σt xr h3 _ hw u w rfl with h | h
  · exact h
  · omega

open Classical in
/-- **Rooted degeneracy four.** Every auxiliary has at most four template neighbours of
smaller rank; all roots have rank `0`, so they are counted. -/
theorem card_preceding_le_four [Fintype Rt] (u : AuxV m) :
    (univ.filter fun w : TV Rt m =>
      s(Sum.inr u, w) ∈ template σt xr h3 ∧ rank w < rank (Sum.inr u : TV Rt m)).card ≤ 4 := by
  refine (card_le_card fun w hw => ?_).trans (card_lowerNbrs σt xr h3 u)
  rw [mem_filter] at hw
  exact mem_lowerNbrs_of_lt σt xr h3 u w hw.2.1 hw.2.2

omit [DecidableEq Rt] in
theorem rank_root (r : Rt) : rank (Sum.inl r : TV Rt m) = 0 := rfl

omit [DecidableEq Rt] in
theorem rank_aux_pos (u : AuxV m) : 0 < rank (Sum.inr u : TV Rt m) := by
  rcases u with ⟨j, t⟩ | c <;> simp [rank]

end PartitionedTriangleAbsorption.PrivateTemplate
