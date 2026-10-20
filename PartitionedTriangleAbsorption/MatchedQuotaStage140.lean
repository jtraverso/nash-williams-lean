/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeF0
public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.RootQuotaPackingStage124

/-! # Exact quotas for cleaning the three pairings of four classes

The quotas are produced from physical edge counts, even degrees, divisibility
by three and the three nonnegative-surplus inequalities. This file does not
assume a cleanup packing exists.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.MatchedQuotaStage140

open Finset AntiEdgeSelection TypedRefinerCharge

variable {V : Type*}

def side (i : Fin 3) (j : Fin 4) : Fin 2 :=
  if i = 0 then (if j = 0 ∨ j = 1 then 0 else 1)
  else if i = 1 then (if j = 0 ∨ j = 2 then 0 else 1)
  else (if j = 0 ∨ j = 3 then 0 else 1)

def partner (i : Fin 3) (j : Fin 4) : Fin 4 :=
  if i = 0 then ![1, 0, 3, 2] j
  else if i = 1 then ![2, 3, 0, 1] j
  else ![3, 2, 1, 0] j

theorem partner_ne (i : Fin 3) (j : Fin 4) : partner i j ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

theorem side_partner (i : Fin 3) (j : Fin 4) : side i (partner i j) = side i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem side_partner_ne (i k : Fin 3) (h : i ≠ k) (j : Fin 4) :
    side i (partner k j) ≠ side i j := by
  fin_cases i <;> fin_cases k <;> fin_cases j <;> first | contradiction | decide

def cuts (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) : Finset (Sym2 V) :=
  E.filter fun e => ¬ (e.map (side i ∘ p)).IsDiag

def internal (p : V → Fin 4) (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e => (e.map p).IsDiag

theorem cut_charge (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) :
    charge chi0 (side i ∘ p) E = 6 * ((cuts p E i).card : ℤ) - 4 * E.card := by
  have hedge : ∀ e : Sym2 V,
      pair chi0 (pairVec (side i ∘ p) e) =
        6 * (if ¬ (e.map (side i ∘ p)).IsDiag then (1 : ℤ) else 0) - 4 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      rw [TypedRefinerF0.edge_charge]
      by_cases h : side i (p a) = side i (p b) <;> simp [Function.comp_apply, h]
  rw [charge_eq_sum]
  simp_rw [hedge]
  simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  have hc : (∑ e ∈ E, if ¬ (e.map (side i ∘ p)).IsDiag then (1 : ℤ) else 0) =
      ((cuts p E i).card : ℤ) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, cuts]
  rw [hc]
  ring

theorem cuts_even [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v, Even (incidentLoad E v))
    (i : Fin 3) : Even (cuts p E i).card := by
  obtain ⟨k, hk⟩ := TypedRefinerF0.four_dvd_charge (side i ∘ p) hloop heven
  rw [cut_charge] at hk
  have hz : Even (((cuts p E i).card : ℕ) : ℤ) := by
    refine ⟨k + E.card - (cuts p E i).card, ?_⟩
    omega
  exact (Int.even_coe_nat _).mp hz

/-- Every finite inventory can be allocated to prescribed natural-number quotas. -/
theorem exists_assignment {I : Type*} [Fintype I] (q : Fin 3 → ℕ)
    (hq : (∑ i, q i) = Fintype.card I) :
    ∃ f : I → Fin 3, ∀ i, Fintype.card {x : I // f x = i} = q i := by
  classical
  have hcard : Fintype.card I = Fintype.card (Σ i : Fin 3, Fin (q i)) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hq.symm
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun x => (e x).1, fun i => ?_⟩
  have he := Fintype.card_congr
    (e.subtypeEquiv (p := fun x => (e x).1 = i)
      (q := fun x => x.1 = i) (fun _ => Iff.rfl))
  rw [he]
  let g : {x : (Σ j : Fin 3, Fin (q j)) // x.1 = i} ≃ Fin (q i) :=
    { toFun := fun x => by
        obtain ⟨⟨j, a⟩, h⟩ := x
        change j = i at h
        subst j
        exact a
      invFun := fun a => ⟨⟨i, a⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨j, a⟩, h⟩
        change j = i at h
        subst j
        rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr g).trans (Fintype.card_fin (q i))

theorem cut_indicator_sum (p : V → Fin 4) (e : Sym2 V) :
    (∑ i : Fin 3, if ¬ (e.map (side i ∘ p)).IsDiag then (1 : ℕ) else 0) =
      if (e.map p).IsDiag then 0 else 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, Function.comp_apply]
    generalize p a = x
    generalize p b = y
    fin_cases x <;> fin_cases y <;> decide

theorem cuts_sum (p : V → Fin 4) (E : Finset (Sym2 V)) :
    ∑ i : Fin 3, (cuts p E i).card = 2 * (E.card - (internal p E).card) := by
  calc
    ∑ i : Fin 3, (cuts p E i).card =
        ∑ i : Fin 3, ∑ e ∈ E, if ¬ (e.map (side i ∘ p)).IsDiag then 1 else 0 := by
          apply sum_congr rfl
          intro i _
          rw [← sum_filter]
          simp [cuts]
    _ = ∑ e ∈ E, ∑ i : Fin 3,
        if ¬ (e.map (side i ∘ p)).IsDiag then 1 else 0 := sum_comm
    _ = ∑ e ∈ E, if (e.map p).IsDiag then 0 else 2 := by
          exact sum_congr rfl fun e _ => cut_indicator_sum p e
    _ = 2 * (E.card - (internal p E).card) := by
          simp only [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul]
          have hc : (E.filter fun e => ¬ (e.map p).IsDiag).card =
              E.card - (internal p E).card := by
            have h := card_filter_add_card_filter_not (s := E) (fun e => (e.map p).IsDiag)
            unfold internal
            omega
          rw [hc]
          omega

theorem exists_quotas [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : OnePart.Even3 E)
    (hsurplus : ∀ i : Fin 3, 3 * (cuts p E i).card ≤ 2 * E.card) :
    ∃ q : Fin 3 → ℕ,
      (∀ i, 6 * q i + 3 * (cuts p E i).card = 2 * E.card) ∧
      (∑ i, q i) = (internal p E).card := by
  obtain ⟨k, hk⟩ := hdiv.1
  have hc : ∀ i : Fin 3, ∃ d : ℕ, (cuts p E i).card = 2 * d := by
    intro i
    obtain ⟨d, hd⟩ := cuts_even p E hloop hdiv.2 i
    exact ⟨d, by omega⟩
  choose d hd using hc
  have hdk : ∀ i, d i ≤ k := by
    intro i
    have h := hsurplus i
    rw [hd i, hk] at h
    omega
  refine ⟨fun i => k - d i, ?_, ?_⟩
  · intro i
    dsimp only
    have := hdk i
    rw [hd i, hk]
    omega
  · have hcSum := cuts_sum p E
    have hsub : (internal p E).card ≤ E.card := card_le_card (filter_subset _ _)
    rw [Fin.sum_univ_three] at hcSum ⊢
    simp only [hd] at hcSum
    have h0 := hdk 0
    have h1 := hdk 1
    have h2 := hdk 2
    rw [hk] at hcSum hsub
    omega

/-- The quota assignment uses the actual internal edges as its inventory. -/
theorem exists_internal_assignment [DecidableEq V] (p : V → Fin 4)
    (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hdiv : OnePart.Even3 E)
    (hsurplus : ∀ i : Fin 3, 3 * (cuts p E i).card ≤ 2 * E.card) :
    ∃ f : (internal p E) → Fin 3, ∀ i,
      6 * Fintype.card {e : (internal p E) // f e = i} +
        3 * (cuts p E i).card = 2 * E.card := by
  obtain ⟨q, hq, hsum⟩ := exists_quotas p E hloop hdiv hsurplus
  obtain ⟨f, hf⟩ := exists_assignment (I := internal p E) q (by simpa using hsum)
  exact ⟨f, fun i => by rw [hf i]; exact hq i⟩

noncomputable def edgeLeft (E : Finset (Sym2 V)) (e : E) : V := e.val.out.1

noncomputable def edgeRight (E : Finset (Sym2 V)) (e : E) : V := e.val.out.2

theorem edge_rebuild (E : Finset (Sym2 V)) (e : E) :
    s(edgeLeft E e, edgeRight E e) = e.val := by
  exact Quot.out_eq e.val

theorem edge_ne (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag) (e : E) :
    edgeLeft E e ≠ edgeRight E e := by
  intro h
  apply hloop e.val e.property
  rw [← edge_rebuild E e, h]
  simp

theorem internal_endpoints_same (p : V → Fin 4) (E : Finset (Sym2 V))
    (e : internal p E) :
    p (edgeLeft (internal p E) e) = p (edgeRight (internal p E) e) := by
  have h := (mem_filter.mp e.property).2
  rw [← edge_rebuild (internal p E) e, Sym2.map_mk, Sym2.mk_isDiag_iff] at h
  exact h

theorem oriented_injective (E : Finset (Sym2 V)) :
    Function.Injective (fun e : E => s(edgeLeft E e, edgeRight E e)) := by
  intro e f h
  simpa only [edge_rebuild, Subtype.val_inj] using h

/-- Orienting the actual loopless edge inventory counts each incident request
exactly once, irrespective of the arbitrary orientation chosen. -/
theorem rootLoad_edges [DecidableEq V] (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (x : V) :
    rootLoad univ (edgeLeft E) (edgeRight E) x = incidentLoad E x := by
  classical
  let S := (univ : Finset E).filter fun e => edgeLeft E e = x
  let T := (univ : Finset E).filter fun e => edgeRight E e = x
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    intro e heS heT
    have hl := (mem_filter.mp heS).2
    have hr := (mem_filter.mp heT).2
    apply hloop e.val e.property
    rw [← edge_rebuild E e, hl, hr]
    simp
  have hc : (S ∪ T).card = (E.filter fun e => x ∈ e).card := by
    apply card_bij (fun e _ => e.val)
    · intro e he
      refine mem_filter.mpr ⟨e.property, ?_⟩
      rcases mem_union.mp he with he | he
      · have h := (mem_filter.mp he).2
        rw [← h]
        exact Sym2.out_fst_mem e.val
      · have h := (mem_filter.mp he).2
        rw [← h]
        exact Sym2.out_snd_mem e.val
    · intro a _ b _ h
      exact Subtype.ext h
    · intro e he
      obtain ⟨heE, hxe⟩ := mem_filter.mp he
      let a : E := ⟨e, heE⟩
      refine ⟨a, ?_, rfl⟩
      have heq := edge_rebuild E a
      change s(edgeLeft E a, edgeRight E a) = e at heq
      rw [← heq, Sym2.mem_iff] at hxe
      rcases hxe with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h.symm⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h.symm⟩)
  change S.card + T.card = _
  rw [← card_union_of_disjoint hdis, hc]
  rfl

theorem cuts_matched_triangle [DecidableEq V] (p : V → Fin 4)
    (a b w : V) (hab : a ≠ b) (hp : p a = p b) (k i : Fin 3)
    (hw : p w = partner k (p a)) :
    (cuts p (TypedCorrectionFamily.edges a b w) i).card = if k = i then 0 else 2 := by
  have hsame : side i (p a) = side i (p b) := congrArg (side i) hp
  by_cases h : k = i
  · subst k
    have hs : side i (p w) = side i (p a) := by rw [hw, side_partner]
    simp [cuts, TypedCorrectionFamily.edges, Sym2.map_mk, Function.comp_apply,
      hsame, hs]
  · have hs : side i (p w) ≠ side i (p a) := by
      rw [hw]
      exact side_partner_ne i k (Ne.symm h) (p a)
    have hs' : side i (p w) ≠ side i (p b) := by rwa [← hsame]
    have heq : cuts p (TypedCorrectionFamily.edges a b w) i = pathEdges a b w := by
      simp [cuts, TypedCorrectionFamily.edges, pathEdges, Sym2.map_mk,
        filter_insert, filter_singleton, Function.comp_apply, hsame,
        Ne.symm hs']
    rw [heq, pathEdges_card _ _ _ hab, ite_eq_right h]

theorem cuts_packing [DecidableEq V] {I : Type*}
    (p : V → Fin 4) (s : Finset I) (u v w : I → V) (a : I → Fin 3)
    (hne : ∀ j ∈ s, u j ≠ v j) (hp : ∀ j ∈ s, p (u j) = p (v j))
    (hw : ∀ j ∈ s, p (w j) = partner (a j) (p (u j)))
    (hdis : (s : Set I).PairwiseDisjoint
      (fun j => TypedCorrectionFamily.edges (u j) (v j) (w j))) (i : Fin 3) :
    (cuts p (RootQuotaPackingStage124.packingEdges s u v w) i).card =
      2 * (s.card - (s.filter fun j => a j = i).card) := by
  classical
  unfold cuts RootQuotaPackingStage124.packingEdges
  rw [filter_biUnion, card_biUnion]
  · calc
      _ = ∑ j ∈ s, if a j = i then 0 else 2 := by
        exact sum_congr rfl fun j hj => cuts_matched_triangle p (u j) (v j) (w j)
          (hne j hj) (hp j hj) (a j) i (hw j hj)
      _ = 2 * (s.card - (s.filter fun j => a j = i).card) := by
        simp only [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul]
        have hc := card_filter_add_card_filter_not (s := s) (fun j => a j = i)
        omega
  · intro j hj k hk hjk
    exact (hdis hj hk hjk).mono (filter_subset _ _) (filter_subset _ _)

theorem residual_cuts_equal [DecidableEq V] (p : V → Fin 4)
    (E Q : Finset (Sym2 V)) (hQE : Q ⊆ E) (r : ℕ) (q : Fin 3 → ℕ)
    (hq : ∀ i, 6 * q i + 3 * (cuts p E i).card = 2 * E.card)
    (hqle : ∀ i, q i ≤ r)
    (hQ : ∀ i, (cuts p Q i).card = 2 * (r - q i)) (i j : Fin 3) :
    (cuts p (E \ Q) i).card = (cuts p (E \ Q) j).card := by
  have hc (k : Fin 3) : (cuts p (E \ Q) k).card + (cuts p Q k).card =
      (cuts p E k).card := by
    have heq : cuts p (E \ Q) k = cuts p E k \ cuts p Q k := by
      ext e
      simp only [cuts, mem_filter, mem_sdiff]
      tauto
    rw [heq]
    exact card_sdiff_add_card_eq_card (filter_subset_filter _ hQE)
  have hi := hc i
  have hj := hc j
  rw [hQ i] at hi
  rw [hQ j] at hj
  have hqi := hq i
  have hqj := hq j
  have hqile := hqle i
  have hqjle := hqle j
  omega

end PartitionedTriangleAbsorption.MatchedQuotaStage140
