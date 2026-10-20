/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeFamily
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # A sparse physical family of rooted typed triangles

Each requested vertex is used as a root once. The other two vertices share one
quota counter. Two anti-edge queries create a triangle avoiding all old edges.
The anchor in the first query is not an edge resource of the final triangle.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedCorrectionFamily

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

def edges (u a b : V) : Finset (Sym2 V) := {s(u, a), s(u, b), s(a, b)}

def unionEdges (s : Finset V) (a b : V → V) : Finset (Sym2 V) :=
  s.biUnion fun u => edges u (a u) (b u)

def auxLoad (s : Finset V) (a b : V → V) (x : V) : ℕ :=
  auxiliaryLoad s a x + auxiliaryLoad s b x

theorem edges_incident_le (u a b x : V) :
    incidentLoad (edges u a b) x ≤
      2 * ((if u = x then 1 else 0) + (if a = x then 1 else 0) +
        (if b = x then 1 else 0)) := by
  have he : edges u a b = ({s(u, a)} ∪ {s(u, b)}) ∪ {s(a, b)} := by
    simp [edges]
  unfold incidentLoad
  rw [he, filter_union, filter_union]
  have hc := (card_union_le
    ((({s(u, a)} : Finset (Sym2 V)).filter (fun e => x ∈ e)) ∪
      (({s(u, b)} : Finset (Sym2 V)).filter (fun e => x ∈ e)))
    (({s(a, b)} : Finset (Sym2 V)).filter (fun e => x ∈ e))).trans
    (Nat.add_le_add_right (card_union_le _ _) _)
  by_cases hu : u = x <;> by_cases ha : a = x <;> by_cases hb : b = x <;>
    simp [filter_singleton, Sym2.mem_iff, hu, ha, hb, eq_comm] at hc ⊢
  all_goals omega

theorem union_incident_le (s : Finset V) (a b : V → V) (x : V) :
    incidentLoad (unionEdges s a b) x ≤ 2 * (1 + auxLoad s a b x) := by
  have hc : (s.filter (fun u => u = x)).card ≤ 1 := by
    exact (card_le_card (by intro u hu; simpa using (mem_filter.mp hu).2 :
      s.filter (fun u => u = x) ⊆ {x})).trans (by simp)
  unfold incidentLoad unionEdges
  rw [filter_biUnion]
  refine card_biUnion_le.trans ((sum_le_sum fun u _ =>
    edges_incident_le u (a u) (b u) x).trans ?_)
  simp only [mul_add, sum_add_distrib, ← mul_sum]
  simp only [← sum_filter, sum_const, smul_eq_mul, mul_one]
  change 2 * (s.filter (fun u => u = x)).card +
    2 * auxiliaryLoad s a x + 2 * auxiliaryLoad s b x ≤ _
  unfold auxLoad
  omega

theorem union_degree_bound (s : Finset V) (a b : V → V)
    (B : Finset (Sym2 V)) (d : ℝ) (q : ℕ) (hB : DegBounded B d)
    (haux : ∀ x, auxLoad s a b x ≤ q) :
    DegBounded (B ∪ unionEdges s a b) (d + 2 * (q + 1)) := by
  intro x
  have hc : incidentLoad (B ∪ unionEdges s a b) x ≤
      incidentLoad B x + 2 * (q + 1) := by
    unfold incidentLoad at ⊢
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add_left
      ((union_incident_le s a b x).trans (by have := haux x; omega)) _)
  have hr : (incidentLoad (B ∪ unionEdges s a b) x : ℝ) ≤
      incidentLoad B x + 2 * ((q : ℝ) + 1) := by exact_mod_cast hc
  have hb : (incidentLoad B x : ℝ) ≤ d := hB x
  change (incidentLoad (B ∪ unionEdges s a b) x : ℝ) ≤ _
  linarith

theorem aux_sum [Fintype V] (s : Finset V) (a b : V → V) :
    ∑ x, auxLoad s a b x = 2 * s.card := by
  simp [auxLoad, sum_add_distrib, auxiliaryLoad_sum, two_mul]

theorem aux_insert (s : Finset V) (u : V) (hu : u ∉ s)
    (a b : V → V) (a' b' x : V) :
    auxLoad (insert u s) (Function.update a u a') (Function.update b u b') x =
      auxLoad s a b x + (if a' = x then 1 else 0) + (if b' = x then 1 else 0) := by
  simp only [auxLoad, auxiliaryLoad_insert_update s u hu]
  omega

/-- A physical triangle per requested root, with a shared auxiliary quota.
The strict budget is independent of the order in which roots are processed. -/
theorem exists_family [Fintype V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α d : ℝ) (hanti : AntiEdgeful p F G α)
    (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (anchor : V → V) (central branch : V → Fin t) (s : Finset V)
    (hanchor : ∀ u ∈ s, u ≠ anchor u ∧ p (anchor u) = branch u)
    (htype : ∀ u ∈ s, ({p u, central u, branch u} : Multiset (Fin t)) ∈ F)
    (q : ℕ) (hq : 0 < q)
    (hbudget : 2 * (s.card : ℝ) / q + 2 * (d + 2 * (q + 1)) <
      α * Fintype.card V) :
    ∃ a b : V → V,
      (∀ u ∈ s, G.Adj u (a u) ∧ G.Adj u (b u) ∧ G.Adj (a u) (b u) ∧
        p (a u) = central u ∧ p (b u) = branch u ∧
        Disjoint (edges u (a u) (b u)) B) ∧
      (s : Set V).PairwiseDisjoint (fun u => edges u (a u) (b u)) ∧
      ∀ x, auxLoad s a b x ≤ q := by
  classical
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  revert hanchor htype hbudget
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      exact ⟨id, id, by simp, by simp [Set.PairwiseDisjoint, Set.Pairwise],
        by simp [auxLoad, auxiliaryLoad]⟩
  | @insert u s hu ih =>
      intro hanchor htype hbudget
      have hsub : s ⊆ insert u s := subset_insert _ _
      have hbudgetS : 2 * (s.card : ℝ) / q + 2 * (d + 2 * (q + 1)) <
          α * Fintype.card V := by
        have hc : (s.card : ℝ) ≤ (insert u s).card := by
          exact_mod_cast card_le_card hsub
        have hd := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)) hqr.le
        linarith
      obtain ⟨a, b, hab, hdis, haux⟩ := ih
        (fun i hi => hanchor i (hsub hi)) (fun i hi => htype i (hsub hi)) hbudgetS
      let used := B ∪ unionEdges s a b
      let load := auxLoad s a b
      have hused : DegBounded used (d + 2 * (q + 1)) :=
        union_degree_bound s a b B d q hB haux
      have hb : ((∑ x, load x : ℕ) : ℝ) / q + 2 * (d + 2 * (q + 1)) <
          α * Fintype.card V := by
        simp only [load, aux_sum, Nat.cast_mul, Nat.cast_ofNat]
        exact hbudgetS
      have ht : ({p u, p (anchor u), central u} : Multiset (Fin t)) ∈ F := by
        rw [(hanchor u (mem_insert_self _ _)).2]
        have hswap : ({p u, branch u, central u} : Multiset (Fin t)) =
            {p u, central u, branch u} := by
          simp only [Multiset.insert_eq_cons]
          congr 1
          exact Multiset.cons_swap _ _ _
        rw [hswap]
        exact htype u (mem_insert_self _ _)
      obtain ⟨a', hua, _, hpa, hqa, hea, _⟩ :=
        exists_unsaturated p F G α (d + 2 * (q + 1)) hanti
          (p u) (p (anchor u)) (central u) ht u (anchor u)
          (hanchor u (mem_insert_self _ _)).1 rfl rfl used hused load q hq hb
      obtain ⟨b', hub, hab', hpb, hqb, heb, heab⟩ :=
        exists_unsaturated p F G α (d + 2 * (q + 1)) hanti
          (p u) (central u) (branch u) (htype u (mem_insert_self _ _))
          u a' hua.ne rfl hpa used hused load q hq hb
      have hnew : Disjoint (edges u a' b') used := by
        apply disjoint_left.mpr
        intro e he heUsed
        rcases mem_insert.mp he with he | he
        · exact hea (he ▸ heUsed)
        · rcases mem_insert.mp he with he | he
          · exact heb (he ▸ heUsed)
          · exact heab ((mem_singleton.mp he) ▸ heUsed)
      let anew := Function.update a u a'
      let bnew := Function.update b u b'
      have holda : ∀ i ∈ s, anew i = a i := by
        intro i hi
        exact Function.update_of_ne (show i ≠ u from fun h => hu (h ▸ hi)) a' a
      have holdb : ∀ i ∈ s, bnew i = b i := by
        intro i hi
        exact Function.update_of_ne (show i ≠ u from fun h => hu (h ▸ hi)) b' b
      have hau : anew u = a' := Function.update_self _ _ _
      have hbu : bnew u = b' := Function.update_self _ _ _
      refine ⟨anew, bnew, ?_, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hau, hbu]
          exact ⟨hua, hub, hab'.symm, hpa, hpb, hnew.mono_right subset_union_left⟩
        · rw [holda i hi, holdb i hi]
          exact hab i hi
      · intro i hi j hj hij
        change Disjoint (edges i (anew i) (bnew i)) (edges j (anew j) (bnew j))
        by_cases hiu : i = u
        · subst i
          have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hij.symm
          rw [hau, hbu, holda j hjs, holdb j hjs]
          exact hnew.mono_right (fun e he =>
            mem_union_right _ (mem_biUnion.mpr ⟨j, hjs, he⟩))
        · have his : i ∈ s := (mem_insert.mp hi).resolve_left hiu
          by_cases hju : j = u
          · subst j
            rw [hau, hbu, holda i his, holdb i his]
            have hsubi : edges i (a i) (b i) ⊆ used := by
              intro e he
              exact mem_union_right _ (mem_biUnion.mpr ⟨i, his, he⟩)
            exact (hnew.mono_right hsubi).symm
          · have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hju
            rw [holda i his, holdb i his, holda j hjs, holdb j hjs]
            exact hdis his hjs hij
      · intro x
        rw [aux_insert s u hu]
        have hn : a' ≠ b' := hab'.ne.symm
        have ha : auxLoad s a b a' < q := hqa
        have hb : auxLoad s a b b' < q := hqb
        by_cases hax : a' = x
        · subst x
          simp only [ite_true, ite_eq_right hn.symm, Nat.add_zero]
          omega
        · by_cases hbx : b' = x
          · subst x
            simp only [ite_eq_right hax, ite_true, Nat.add_zero]
            omega
          · simp only [ite_eq_right hax, ite_eq_right hbx, Nat.add_zero]
            exact haux x

end PartitionedTriangleAbsorption.TypedCorrectionFamily
