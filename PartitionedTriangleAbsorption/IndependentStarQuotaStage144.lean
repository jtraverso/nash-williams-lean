/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CutSurplusStage140
public import PartitionedTriangleAbsorption.StarCutsStage143

/-! # Forced star quotas paid by flipping independent roots

This argument applies to the graph that still satisfies the minimum-degree
threshold. It does not assume that exceptional pre-cleaning preserves it.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IndependentStarQuotaStage144

open Finset MatchedQuotaStage140

variable {V : Type*} [DecidableEq V]

noncomputable def sameLoad {K : Type*} [DecidableEq K]
    (b : V → K) (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter fun e : Sym2 V => v ∈ e ∧ (e.map b).IsDiag).card

noncomputable def crossLoad (b : V → Fin 2) (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter fun e : Sym2 V => v ∈ e ∧ ¬ (e.map b).IsDiag).card

noncomputable def flip (b : V → Fin 2) (P : Finset V) (v : V) : Fin 2 :=
  if v ∈ P then 1 - b v else b v

noncomputable def cutSet (b : V → Fin 2) (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e => ¬ (e.map b).IsDiag

theorem sum_endpoints (P : Finset V) (a b : V) (hab : a ≠ b) (c : ℤ) :
    (∑ v ∈ P, if v ∈ s(a, b) then c else 0) =
      (if a ∈ P then c else 0) + (if b ∈ P then c else 0) := by
  classical
  have h (v : V) : (if v ∈ s(a, b) then c else 0) =
      (if v = a then c else 0) + (if v = b then c else 0) := by
    by_cases ha : v = a <;> by_cases hb : v = b <;> simp_all [Sym2.mem_iff]
  simp_rw [h]
  rw [sum_add_distrib]
  simp

theorem flip_edge (b : V → Fin 2) (P : Finset V) (a c : V)
    (hP : ¬ (a ∈ P ∧ c ∈ P)) :
    (if ¬ ((s(a, c)).map (flip b P)).IsDiag then (1 : ℤ) else 0) -
        (if ¬ ((s(a, c)).map b).IsDiag then 1 else 0) =
      (if a ∈ P then (if b a = b c then 1 else -1) else 0) +
        (if c ∈ P then (if b a = b c then 1 else -1) else 0) := by
  classical
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
  unfold flip
  by_cases ha : a ∈ P <;> by_cases hc : c ∈ P
  · exact False.elim (hP ⟨ha, hc⟩)
  all_goals
    simp only [ha, hc, ite_true, ite_false]
    generalize b a = x
    generalize b c = y
    fin_cases x <;> fin_cases y <;> decide

theorem flip_cut_identity (b : V → Fin 2) (E : Finset (Sym2 V)) (P : Finset V)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hP : ∀ a ∈ P, ∀ c ∈ P, s(a, c) ∉ E) :
    ((cutSet (flip b P) E).card : ℤ) - (cutSet b E).card =
      ∑ v ∈ P, ((sameLoad b E v : ℤ) - crossLoad b E v) := by
  classical
  have hcount (d : V → Fin 2) : ((cutSet d E).card : ℤ) =
      ∑ e ∈ E, if ¬ (e.map d).IsDiag then 1 else 0 := by
    rw [← sum_filter]
    simp [cutSet]
  have hload (v : V) : ((sameLoad b E v : ℤ) - crossLoad b E v) =
      ∑ e ∈ E, if v ∈ e then (if (e.map b).IsDiag then 1 else -1) else 0 := by
    have hs : (sameLoad b E v : ℤ) =
        ∑ e ∈ E, if v ∈ e ∧ (e.map b).IsDiag then 1 else 0 := by
      rw [← sum_filter]
      simp [sameLoad]
    have hc : (crossLoad b E v : ℤ) =
        ∑ e ∈ E, if v ∈ e ∧ ¬ (e.map b).IsDiag then 1 else 0 := by
      rw [← sum_filter]
      simp [crossLoad]
    rw [hs, hc, ← sum_sub_distrib]
    apply sum_congr rfl
    intro e _
    split_ifs <;> simp_all
  simp_rw [hcount, hload]
  rw [← sum_sub_distrib, sum_comm]
  apply sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ a c =>
    have hne : a ≠ c := by simpa using hloop s(a, c) he
    have hp : ¬ (a ∈ P ∧ c ∈ P) := fun h => hP a h.1 c h.2 he
    rw [flip_edge b P a c hp]
    simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
    exact (sum_endpoints P a c hne (if b a = b c then 1 else -1)).symm

theorem forced_column_bound [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (h : V → ℕ) (i : Fin 3) (q : ℕ)
    (hdegree : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v)
    (hS : ∀ a ∈ S, ∀ c ∈ S, ¬ G.Adj a c)
    (hrow : ∀ v ∈ S, sameLoad (side i ∘ p) G.edgeFinset v +
      crossLoad (side i ∘ p) G.edgeFinset v = 2 * h v)
    (hq : 6 * q + 3 * (cuts p G.edgeFinset i).card = 2 * G.edgeFinset.card) :
    (∑ v ∈ S, (sameLoad (side i ∘ p) G.edgeFinset v - h v)) ≤ q := by
  classical
  let b := side i ∘ p
  let P := S.filter fun v => h v < sameLoad b G.edgeFinset v
  have hpS : P ⊆ S := filter_subset _ _
  have hflip := flip_cut_identity b G.edgeFinset P
    (fun e he => G.not_isDiag_of_mem_edgeFinset he)
    (fun a ha c hc he => hS a (hpS ha) c (hpS hc) (by simpa using he))
  let p' : V → Fin 4 := fun v => if flip b P v = 0 then 0 else 2
  have hside : side 0 ∘ p' = flip b P := by
    funext v
    have hv := (flip b P v).isLt
    simp only [Function.comp_apply, p', side]
    split_ifs <;> simp_all
    omega
  have hbound := CutSurplusStage140.surplus_of_degree p' G hdegree 0
  have hcut' : cuts p' G.edgeFinset 0 = cutSet (flip b P) G.edgeFinset := by
    simp only [cuts, cutSet, hside]
  rw [hcut'] at hbound
  have hsum : (∑ v ∈ P, ((sameLoad b G.edgeFinset v : ℤ) - crossLoad b G.edgeFinset v)) =
      2 * (∑ v ∈ S, (sameLoad b G.edgeFinset v - h v) : ℕ) := by
    rw [sum_filter]
    simp only [Nat.cast_sum]
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    have hr := hrow v hv
    change sameLoad b G.edgeFinset v + crossLoad b G.edgeFinset v = 2 * h v at hr
    by_cases hp : h v < sameLoad b G.edgeFinset v
    · have he : sameLoad b G.edgeFinset v - h v + h v = sameLoad b G.edgeFinset v :=
        Nat.sub_add_cancel (by omega)
      simp only [hp, ite_true]
      exact_mod_cast (show (sameLoad b G.edgeFinset v : ℤ) - crossLoad b G.edgeFinset v =
        2 * (sameLoad b G.edgeFinset v - h v : ℕ) by omega)
    · simp only [hp, ite_false]
      have hz : sameLoad b G.edgeFinset v - h v = 0 := Nat.sub_eq_zero_of_le (by omega)
      simp [hz]
  rw [hsum] at hflip
  have hqz : (6 : ℤ) * q + 3 * (cutSet b G.edgeFinset).card = 2 * G.edgeFinset.card := by
    exact_mod_cast hq
  have hbz : (3 : ℤ) * (cutSet (flip b P) G.edgeFinset).card ≤ 2 * G.edgeFinset.card := by
    exact_mod_cast hbound
  have : ((∑ v ∈ S, (sameLoad b G.edgeFinset v - h v) : ℕ) : ℤ) ≤ q := by omega
  exact_mod_cast this

theorem load_partition (b : V → Fin 2) (E : Finset (Sym2 V)) (v : V) :
    sameLoad b E v + crossLoad b E v = AntiEdgeSelection.incidentLoad E v := by
  classical
  have he : (E.filter fun e : Sym2 V => v ∈ e).filter (fun e => (e.map b).IsDiag) =
      E.filter (fun e : Sym2 V => v ∈ e ∧ (e.map b).IsDiag) := by
    ext e
    simp [and_assoc]
  have hn : (E.filter fun e : Sym2 V => v ∈ e).filter (fun e => ¬ (e.map b).IsDiag) =
      E.filter (fun e : Sym2 V => v ∈ e ∧ ¬ (e.map b).IsDiag) := by
    ext e
    simp [and_assoc]
  simpa only [he, hn, sameLoad, crossLoad, AntiEdgeSelection.incidentLoad] using
    card_filter_add_card_filter_not (s := E.filter fun e : Sym2 V => v ∈ e)
      (fun e => (e.map b).IsDiag)

theorem incident_degree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    AntiEdgeSelection.incidentLoad G.edgeFinset v = G.degree v := by
  classical
  have he : G.edgeFinset.filter (fun e : Sym2 V => v ∈ e) = G.incidenceFinset v := by
    ext e
    simp [SimpleGraph.incidenceSet]
  rw [AntiEdgeSelection.incidentLoad, he, G.card_incidenceFinset_eq_degree]

theorem independent_incident_bound (E : Finset (Sym2 V)) (S : Finset V)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hS : ∀ a ∈ S, ∀ c ∈ S, s(a, c) ∉ E) :
    (∑ v ∈ S, AntiEdgeSelection.incidentLoad E v) ≤ E.card := by
  classical
  have hload (v : V) : AntiEdgeSelection.incidentLoad E v =
      ∑ e ∈ E, if v ∈ e then 1 else 0 := by
    rw [← sum_filter]
    simp [AntiEdgeSelection.incidentLoad]
  simp_rw [hload]
  rw [sum_comm]
  calc
    _ ≤ ∑ e ∈ E, 1 := by
      apply sum_le_sum
      intro e he
      induction e using Sym2.ind with
      | _ a c =>
        have hne : a ≠ c := by simpa using hloop s(a, c) he
        have hp : ¬ (a ∈ S ∧ c ∈ S) := fun h => hS a h.1 c h.2 he
        have hz := sum_endpoints S a c hne 1
        have hc : (∑ v ∈ S, if v ∈ s(a, c) then (1 : ℤ) else 0) ≤ 1 := by
          rw [hz]
          split_ifs <;> simp_all
        exact_mod_cast hc
    _ = E.card := by simp

theorem exists_graph_star_counts [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (h a : V → ℕ)
    (b : V → Fin 3 → ℕ) (q : Fin 3 → ℕ)
    (hdegree : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v)
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hhalf : ∀ v ∈ S, G.degree v = 2 * h v)
    (ha : ∀ v ∈ S, a v = AntiEdgeSelection.incidentLoad (internal p G.edgeFinset) v)
    (hsame : ∀ v ∈ S, ∀ i, a v + b v i = sameLoad (side i ∘ p) G.edgeFinset v)
    (hrow : ∀ v ∈ S, a v + ∑ i, b v i = 2 * h v)
    (hcap : ∀ v ∈ S, a v ≤ h v ∧ ∀ i, b v i ≤ h v)
    (hq : ∀ i, 6 * q i + 3 * (cuts p G.edgeFinset i).card = 2 * G.edgeFinset.card)
    (hqsum : (∑ i, q i) = (internal p G.edgeFinset).card) :
    ∃ x : S → Fin 3 → ℕ,
      (∀ v : S, ∑ i, x v i = a v) ∧
      (∀ (v : S) i, a v + b v i - h v ≤ x v i ∧ x v i ≤ b v i) ∧
      (∀ i, ∑ v, x v i ≤ q i) := by
  classical
  apply StarCutsStage143.exists_star_counts (fun v : S => a v) (fun v : S => h v)
    (fun v : S => b v) q
    (fun v => hrow v v.property) (fun v => (hcap v v.property).1)
    (fun v => (hcap v v.property).2)
  · intro i
    have hf := forced_column_bound p G S h i (q i) hdegree hS
      (fun v hv => (load_partition (side i ∘ p) G.edgeFinset v).trans
        ((incident_degree G v).trans (hhalf v hv))) (hq i)
    rw [← sum_attach] at hf
    rw [univ_eq_attach]
    simpa only [hsame _ (Subtype.mem _) i] using hf
  · have ht := independent_incident_bound (internal p G.edgeFinset) S
      (fun e he => G.not_isDiag_of_mem_edgeFinset (mem_filter.mp he).1)
      (fun u hu v hv he => hS u hu v hv (by simpa using (mem_filter.mp he).1))
    rw [← sum_attach] at ht
    rw [univ_eq_attach]
    simpa only [← ha _ (Subtype.mem _), ← hqsum] using ht

end PartitionedTriangleAbsorption.IndependentStarQuotaStage144
