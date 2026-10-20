/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedCorrectionFamily

/-! # Rooted triangle requests with repeated roots and a common inner quota

The supply hypothesis is local to a prescribed inner set. Each slot requests
one triangle; unlike the single-root correction API, roots may repeat. The
proof constructs actual edge-disjoint triangles, not fractional requests.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQuotaPackingStage124

open Finset AntiEdgeSelection
open TypedCorrectionFamily (edges edges_incident_le)

variable {V I : Type*} [DecidableEq V]

def packingEdges (s : Finset I) (root a b : I → V) : Finset (Sym2 V) :=
  s.biUnion fun i => edges (root i) (a i) (b i)

def innerLoad (s : Finset I) (a b : I → V) (x : V) : ℕ :=
  auxiliaryLoad s a x + auxiliaryLoad s b x

theorem packing_incident_le (s : Finset I) (root a b : I → V) (x : V) :
    incidentLoad (packingEdges s root a b) x ≤
      2 * (auxiliaryLoad s root x + innerLoad s a b x) := by
  unfold incidentLoad packingEdges
  rw [filter_biUnion]
  refine card_biUnion_le.trans ((sum_le_sum fun i _ =>
    edges_incident_le (root i) (a i) (b i) x).trans_eq ?_)
  simp [innerLoad, auxiliaryLoad, mul_add, sum_add_distrib, ← sum_filter,
    Nat.mul_comm, Nat.add_assoc]

theorem inner_sum [Fintype V] (s : Finset I) (a b : I → V) :
    ∑ x, innerLoad s a b x = 2 * s.card := by
  simp [innerLoad, sum_add_distrib, auxiliaryLoad_sum, two_mul]

theorem inner_insert [DecidableEq I] (s : Finset I) (i : I) (hi : i ∉ s)
    (a b : I → V) (a' b' x : V) :
    innerLoad (insert i s) (Function.update a i a') (Function.update b i b') x =
      innerLoad s a b x + (if a' = x then 1 else 0) +
        (if b' = x then 1 else 0) := by
  simp only [innerLoad, auxiliaryLoad_insert_update s i hi]
  omega

theorem used_incident_le (s : Finset I) (root a b : I → V)
    (B : Finset (Sym2 V)) (d k q : ℕ)
    (hB : ∀ x, incidentLoad B x ≤ d)
    (hr : ∀ x, auxiliaryLoad s root x ≤ k)
    (ha : ∀ x, innerLoad s a b x ≤ q) (x : V) :
    incidentLoad (B ∪ packingEdges s root a b) x ≤ d + 2 * (k + q) := by
  have hc := packing_incident_le s root a b x
  have hu : incidentLoad (B ∪ packingEdges s root a b) x ≤
      incidentLoad B x + incidentLoad (packingEdges s root a b) x := by
    unfold incidentLoad
    rw [filter_union]
    exact card_union_le _ _
  have := hB x
  have := hr x
  have := ha x
  omega

/-- The local selection step consumes two used-edge budgets and a saturation
budget. All candidates are already physically valid and correctly typed. -/
theorem select_unsaturated [Fintype V] (S : Finset V)
    (used : Finset (Sym2 V)) (u v : V) (load : V → ℕ) (q d n b : ℕ)
    (hS : b ≤ S.card) (hu : incidentLoad used u ≤ d)
    (hv : incidentLoad used v ≤ d) (hsum : ∑ x, load x ≤ 2 * n)
    (hbudget : 2 * n + 2 * d * q < b * q) :
    ∃ w ∈ S, load w < q ∧ s(u, w) ∉ used ∧ s(v, w) ∉ used := by
  let Z := univ.filter fun w => q ≤ load w
  let A := S \ (Z ∪ blockedNeighbours used u ∪ blockedNeighbours used v)
  have hs : q * Z.card ≤ 2 * n := (saturated_card_budget load q).trans hsum
  have hc := available_card_budget S Z used u v
  have hne : A.Nonempty := by
    by_contra h
    have hz : A.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
    change S.card ≤ A.card + Z.card + _ + _ at hc
    rw [hz] at hc
    have hbc : b ≤ Z.card + 2 * d := by omega
    have hm := Nat.mul_le_mul_right q hbc
    nlinarith
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hwS, hwN⟩ := mem_sdiff.mp hw
  have hwZ : w ∉ Z := fun h => hwN (mem_union_left _ (mem_union_left _ h))
  have heu : w ∉ blockedNeighbours used u :=
    fun h => hwN (mem_union_left _ (mem_union_right _ h))
  have hev : w ∉ blockedNeighbours used v := fun h => hwN (mem_union_right _ h)
  refine ⟨w, hwS, ?_, ?_, ?_⟩
  · simpa only [Z, mem_filter, mem_univ, true_and, not_le] using hwZ
  · simpa [blockedNeighbours] using heu
  · simpa [blockedNeighbours] using hev

def common [Fintype V] {t : ℕ} (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (W : Finset V) (u v : V) (c : Fin t) : Finset V :=
  W.filter fun w => p w = c ∧ G.Adj u w ∧ G.Adj w v

/-- Construct one physical triangle per slot, allowing repeated roots. The
two inner endpoints belong to `W`, avoid `B`, and share the same quota `q`.
The explicit local supply is not a conclusion about a general dense host. -/
theorem exists_packing [Fintype V] {t : ℕ} (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (B : Finset (Sym2 V)) (d k q b : ℕ) (hB : ∀ x, incidentLoad B x ≤ d)
    (root anchor : I → V) (left right : I → Fin t) (s : Finset I)
    (hanchor : ∀ i ∈ s, anchor i ∈ W ∧ p (anchor i) = right i)
    (hroot : ∀ x, auxiliaryLoad s root x ≤ k)
    (hsupply : ∀ i ∈ s, ∀ v ∈ W,
      (p v = right i → b ≤ (common p G W (root i) v (left i)).card) ∧
      (p v = left i → b ≤ (common p G W (root i) v (right i)).card))
    (hbudget : 2 * s.card + 2 * (d + 2 * (k + q)) * q < b * q) :
    ∃ a b' : I → V,
      (∀ i ∈ s, a i ∈ W ∧ b' i ∈ W ∧
        G.Adj (root i) (a i) ∧ G.Adj (root i) (b' i) ∧ G.Adj (a i) (b' i) ∧
        p (a i) = left i ∧ p (b' i) = right i ∧
        Disjoint (edges (root i) (a i) (b' i)) B) ∧
      (s : Set I).PairwiseDisjoint (fun i => edges (root i) (a i) (b' i)) ∧
      ∀ x, innerLoad s a b' x ≤ q := by
  classical
  revert hanchor hroot hsupply hbudget
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _ _
      exact ⟨root, root, by simp, by simp [Set.PairwiseDisjoint, Set.Pairwise],
        by simp [innerLoad, auxiliaryLoad]⟩
  | @insert i s hi ih =>
      intro hanchor hroot hsupply hbudget
      have hsub : s ⊆ insert i s := subset_insert _ _
      have hr : ∀ x, auxiliaryLoad s root x ≤ k := by
        intro x
        apply (card_le_card (filter_subset_filter _ hsub)).trans (hroot x)
      have hb : 2 * s.card + 2 * (d + 2 * (k + q)) * q < b * q := by
        have := card_le_card hsub
        omega
      obtain ⟨a, c, hac, hd, hquota⟩ := ih
        (fun j hj => hanchor j (hsub hj)) hr
        (fun j hj => hsupply j (hsub hj)) hb
      let used := B ∪ packingEdges s root a c
      have hused := used_incident_le s root a c B d k q hB hr hquota
      have hsum : ∑ x, innerLoad s a c x ≤ 2 * s.card := (inner_sum s a c).le
      have hi' : i ∈ insert i s := mem_insert_self _ _
      obtain ⟨a', haS, hqa, hea, _⟩ := select_unsaturated
        (common p G W (root i) (anchor i) (left i)) used (root i) (anchor i)
        (innerLoad s a c) q (d + 2 * (k + q)) s.card b
        ((hsupply i hi' (anchor i) (hanchor i hi').1).1 (hanchor i hi').2)
        (hused _) (hused _) hsum hb
      obtain ⟨haW, hpa, hua, _⟩ := mem_filter.mp haS
      obtain ⟨c', hcS, hqc, hec, heac⟩ := select_unsaturated
        (common p G W (root i) a' (right i)) used (root i) a'
        (innerLoad s a c) q (d + 2 * (k + q)) s.card b
        ((hsupply i hi' a' haW).2 hpa) (hused _) (hused _) hsum hb
      obtain ⟨hcW, hpc, huc, hca⟩ := mem_filter.mp hcS
      have hnew : Disjoint (edges (root i) a' c') used := by
        apply disjoint_left.mpr
        intro e he heUsed
        rcases mem_insert.mp he with he | he
        · exact hea (he ▸ heUsed)
        · rcases mem_insert.mp he with he | he
          · exact hec (he ▸ heUsed)
          · exact heac ((mem_singleton.mp he) ▸ heUsed)
      let anew := Function.update a i a'
      let cnew := Function.update c i c'
      have holda : ∀ j ∈ s, anew j = a j := by
        intro j hj
        exact Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj)) a' a
      have holdc : ∀ j ∈ s, cnew j = c j := by
        intro j hj
        exact Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj)) c' c
      have hai : anew i = a' := Function.update_self _ _ _
      have hci : cnew i = c' := Function.update_self _ _ _
      refine ⟨anew, cnew, ?_, ?_, ?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · rw [hai, hci]
          exact ⟨haW, hcW, hua, huc, hca.symm, hpa, hpc,
            hnew.mono_right subset_union_left⟩
        · rw [holda j hj, holdc j hj]
          exact hac j hj
      · intro j hj l hl hjl
        change Disjoint (edges (root j) (anew j) (cnew j))
          (edges (root l) (anew l) (cnew l))
        by_cases hji : j = i
        · subst j
          have hls : l ∈ s := (mem_insert.mp hl).resolve_left hjl.symm
          rw [hai, hci, holda l hls, holdc l hls]
          exact hnew.mono_right (fun e he =>
            mem_union_right _ (mem_biUnion.mpr ⟨l, hls, he⟩))
        · have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hji
          by_cases hli : l = i
          · subst l
            rw [hai, hci, holda j hjs, holdc j hjs]
            have hjsub : edges (root j) (a j) (c j) ⊆ used := by
              intro e he
              exact mem_union_right _ (mem_biUnion.mpr ⟨j, hjs, he⟩)
            exact (hnew.mono_right hjsub).symm
          · have hls : l ∈ s := (mem_insert.mp hl).resolve_left hli
            rw [holda j hjs, holdc j hjs, holda l hls, holdc l hls]
            exact hd hjs hls hjl
      · intro x
        rw [inner_insert s i hi]
        have hn : a' ≠ c' := hca.ne.symm
        by_cases hax : a' = x
        · subst x
          simp only [ite_true, ite_eq_right hn.symm, Nat.add_zero]
          omega
        · by_cases hcx : c' = x
          · subst x
            simp only [ite_eq_right hax, ite_true, Nat.add_zero]
            omega
          · simp only [ite_eq_right hax, ite_eq_right hcx, Nat.add_zero]
            exact hquota x

end PartitionedTriangleAbsorption.RootQuotaPackingStage124
