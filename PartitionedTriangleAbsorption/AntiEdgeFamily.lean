/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeSelection

/-! # Compatible typed anti-edge families with bounded auxiliary congestion

Root demand and auxiliary load are counted separately. A family may reuse an
auxiliary vertex up to its quota, but never reuse a physical edge. This is not
yet a refiner or a universal absorber: the input is a given finite request family.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.AntiEdgeSelection

open Finset

variable {V I : Type*} [DecidableEq V]

def pathEdges (u v w : V) : Finset (Sym2 V) := {s(u, w), s(v, w)}

def familyEdges (s : Finset I) (u v f : I → V) : Finset (Sym2 V) :=
  s.biUnion fun i => pathEdges (u i) (v i) (f i)

def rootLoad (s : Finset I) (u v : I → V) (x : V) : ℕ :=
  (s.filter (fun i => u i = x)).card + (s.filter (fun i => v i = x)).card

def auxiliaryLoad (s : Finset I) (f : I → V) (x : V) : ℕ :=
  (s.filter (fun i => f i = x)).card

theorem pathEdges_card (u v w : V) (huv : u ≠ v) : (pathEdges u v w).card = 2 := by
  have hne : s(u, w) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨hu, _⟩ | ⟨huw, hwv⟩
    · exact huv hu
    · exact huv (huw.trans hwv)
  simp [pathEdges, hne]

theorem familyEdges_card (s : Finset I) (u v f : I → V)
    (hneq : ∀ i ∈ s, u i ≠ v i)
    (hdis : (s : Set I).PairwiseDisjoint (fun i => pathEdges (u i) (v i) (f i))) :
    (familyEdges s u v f).card = 2 * s.card := by
  unfold familyEdges
  rw [card_biUnion hdis]
  calc
    ∑ i ∈ s, (pathEdges (u i) (v i) (f i)).card = ∑ _i ∈ s, 2 :=
      sum_congr rfl fun i hi => pathEdges_card (u i) (v i) (f i) (hneq i hi)
    _ = 2 * s.card := by simp [Nat.mul_comm]

/-- A concrete budget allocation; with linear quota it permits quadratic demand. -/
theorem quadratic_family_budget (a d z m r q : ℝ) (hq : 0 < q)
    (hz : z ≤ a / 8) (hd : d ≤ a / 16) (hr : r ≤ a / 16)
    (hquota : q ≤ a / 32) (hm : m ≤ a * q / 4) :
    z + m / q + 2 * (d + r + 2 * q) < a := by
  have hquot : m / q ≤ a / 4 := (div_le_iff₀ hq).mpr (by nlinarith)
  linarith

theorem path_incident_card_le (u v w x : V) :
    ((pathEdges u v w).filter (fun e => x ∈ e)).card ≤
      (if u = x then 1 else 0) + (if v = x then 1 else 0) +
        2 * (if w = x then 1 else 0) := by
  have heq : pathEdges u v w = {s(u, w)} ∪ {s(v, w)} := by simp [pathEdges]
  rw [heq, filter_union]
  have hc := card_union_le (({s(u, w)} : Finset (Sym2 V)).filter (fun e => x ∈ e))
    (({s(v, w)} : Finset (Sym2 V)).filter (fun e => x ∈ e))
  by_cases hu : u = x <;> by_cases hv : v = x <;> by_cases hw : w = x <;>
    simp [filter_singleton, Sym2.mem_iff, hu, hv, hw, eq_comm] at hc ⊢
  all_goals omega

theorem family_incident_card_le (s : Finset I) (u v f : I → V) (x : V) :
    incidentLoad (familyEdges s u v f) x ≤ rootLoad s u v x + 2 * auxiliaryLoad s f x := by
  unfold incidentLoad familyEdges
  rw [filter_biUnion]
  refine card_biUnion_le.trans ((sum_le_sum fun i _ =>
    path_incident_card_le (u i) (v i) (f i) x).trans_eq ?_)
  simp [rootLoad, auxiliaryLoad, sum_add_distrib, ← sum_filter, Nat.mul_comm]

theorem auxiliaryLoad_sum [Fintype V] (s : Finset I) (f : I → V) :
    ∑ x, auxiliaryLoad s f x = s.card := by
  simpa only [auxiliaryLoad] using
    (card_eq_sum_card_fiberwise (s := s) (t := univ) (f := f)
      (fun i _ => mem_univ (f i))).symm

theorem rootLoad_mono {s s' : Finset I} (h : s ⊆ s') (u v : I → V) (x : V) :
    rootLoad s u v x ≤ rootLoad s' u v x := by
  apply Nat.add_le_add <;> apply card_le_card <;>
    exact fun i hi => mem_filter.mpr ⟨h (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩

theorem auxiliaryLoad_insert_update [DecidableEq I] (s : Finset I) (a : I) (ha : a ∉ s)
    (f : I → V) (w x : V) :
    auxiliaryLoad (insert a s) (Function.update f a w) x =
      auxiliaryLoad s f x + if w = x then 1 else 0 := by
  have htail : s.filter (fun i => Function.update f a w i = x) =
      s.filter (fun i => f i = x) := by
    apply filter_congr
    intro i hi
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    simp [Function.update_of_ne hia]
  unfold auxiliaryLoad
  rw [filter_insert, htail]
  by_cases hw : w = x <;> simp [hw, ha, Nat.add_comm]

theorem family_degree_bound (s : Finset I) (u v f : I → V)
    (B : Finset (Sym2 V)) (d : ℝ) (r q : ℕ) (hB : DegBounded B d)
    (hroot : ∀ x, rootLoad s u v x ≤ r) (haux : ∀ x, auxiliaryLoad s f x ≤ q) :
    DegBounded (B ∪ familyEdges s u v f) (d + r + 2 * q) := by
  intro x
  have hcard : ((B ∪ familyEdges s u v f).filter (fun e => x ∈ e)).card ≤
      incidentLoad B x + (r + 2 * q) := by
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add_left
      ((family_incident_card_le s u v f x).trans
        (Nat.add_le_add (hroot x) (Nat.mul_le_mul_left 2 (haux x)))) _)
  have hreal : (((B ∪ familyEdges s u v f).filter (fun e => x ∈ e)).card : ℝ) ≤
      (incidentLoad B x : ℝ) + ((r : ℝ) + 2 * q) := by exact_mod_cast hcard
  have hBx : (incidentLoad B x : ℝ) ≤ d := hB x
  linarith

/-- Realize all finite typed requests with edge-disjoint anti-edges and bounded
auxiliary reuse. The budget can accommodate quadratically many requests when
the root demand and the auxiliary quota are linear in the host order. -/
theorem exists_compatible_family [Fintype V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α d : ℝ) (hanti : AntiEdgeful p F G α)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (Z : Finset V)
    (u v : I → V) (k : I → Fin t) (s : Finset I)
    (hneq : ∀ i ∈ s, u i ≠ v i)
    (htype : ∀ i ∈ s, ({p (u i), p (v i), k i} : Multiset (Fin t)) ∈ F)
    (r q : ℕ) (hq : 0 < q) (hroot : ∀ x, rootLoad s u v x ≤ r)
    (hbudget : (Z.card : ℝ) + (s.card : ℝ) / q +
      2 * (d + r + 2 * q) < α * (Fintype.card V : ℝ)) :
    ∃ f : I → V,
      (∀ i ∈ s, G.Adj (u i) (f i) ∧ G.Adj (f i) (v i) ∧ p (f i) = k i ∧
        f i ∉ Z ∧ s(u i, f i) ∉ B ∧ s(v i, f i) ∉ B) ∧
      (s : Set I).PairwiseDisjoint (fun i => pathEdges (u i) (v i) (f i)) ∧
      ∀ x, auxiliaryLoad s f x ≤ q := by
  classical
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  revert hneq htype hroot hbudget
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _ _
      exact ⟨u, by simp, by simp [Set.PairwiseDisjoint, Set.Pairwise],
        by simp [auxiliaryLoad]⟩
  | @insert a s ha ih =>
      intro hneq htype hroot hbudget
      have hsub : s ⊆ insert a s := subset_insert _ _
      have hrootS : ∀ x, rootLoad s u v x ≤ r :=
        fun x => (rootLoad_mono hsub u v x).trans (hroot x)
      have hbudgetS : (Z.card : ℝ) + (s.card : ℝ) / q +
          2 * (d + r + 2 * q) < α * (Fintype.card V : ℝ) := by
        have hc : (s.card : ℝ) ≤ (insert a s).card := by
          exact_mod_cast card_le_card hsub
        have hd := div_le_div_of_nonneg_right hc hqReal.le
        linarith
      obtain ⟨f, hf, hdis, haux⟩ := ih
        (fun i hi => hneq i (hsub hi)) (fun i hi => htype i (hsub hi)) hrootS hbudgetS
      let used := B ∪ familyEdges s u v f
      let saturated := univ.filter (fun x => q ≤ auxiliaryLoad s f x)
      have hsaturation : (saturated.card : ℝ) ≤ (s.card : ℝ) / q := by
        have hs := saturated_card_budget (auxiliaryLoad s f) q
        rw [auxiliaryLoad_sum] at hs
        have hsReal : (q : ℝ) * saturated.card ≤ (s.card : ℝ) := by exact_mod_cast hs
        exact (le_div_iff₀ hqReal).mpr (by simpa only [mul_comm] using hsReal)
      have hzcard : ((Z ∪ saturated).card : ℝ) ≤ (Z.card : ℝ) + (s.card : ℝ) / q := by
        have hz : ((Z ∪ saturated).card : ℝ) ≤ (Z.card : ℝ) + saturated.card := by
          exact_mod_cast card_union_le Z saturated
        linarith
      obtain ⟨w, huw, hwv, hwtype, hwZ, heU, heV⟩ :=
        exists_avoiding_of_degree_bound p F G α (d + r + 2 * q) hanti
          (p (u a)) (p (v a)) (k a) (htype a (mem_insert_self _ _))
          (u a) (v a) (hneq a (mem_insert_self _ _)) rfl rfl used (Z ∪ saturated)
          (family_degree_bound s u v f B d r q hB hrootS haux) (by linarith)
      have hwQuota : auxiliaryLoad s f w < q := by
        have hn : w ∉ saturated := fun h => hwZ (mem_union_right _ h)
        simpa only [saturated, mem_filter, mem_univ, true_and, not_le] using hn
      have hwNotZ : w ∉ Z := fun h => hwZ (mem_union_left _ h)
      have heUB : s(u a, w) ∉ B := fun h => heU (mem_union_left _ h)
      have heVB : s(v a, w) ∉ B := fun h => heV (mem_union_left _ h)
      have hnewdis : Disjoint (pathEdges (u a) (v a) w) (familyEdges s u v f) := by
        apply disjoint_left.mpr
        intro e he heOld
        rcases mem_insert.mp he with he | he
        · exact heU (mem_union_right _ (he ▸ heOld))
        · have heq := mem_singleton.mp he
          exact heV (mem_union_right _ (heq ▸ heOld))
      let f' := Function.update f a w
      have hold : ∀ i ∈ s, f' i = f i := by
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        exact Function.update_of_ne hia w f
      refine ⟨f', ?_, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · simpa only [f', Function.update_self] using
            And.intro huw (And.intro hwv (And.intro hwtype
              (And.intro hwNotZ (And.intro heUB heVB))))
        · rw [hold i hi]
          exact hf i hi
      · intro i hi j hj hij
        change Disjoint (pathEdges (u i) (v i) (f' i)) (pathEdges (u j) (v j) (f' j))
        by_cases hia : i = a
        · subst i
          have hja : j ≠ a := Ne.symm hij
          have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hja
          rw [show f' a = w from Function.update_self a w f, hold j hjs]
          exact hnewdis.mono_right
            (subset_biUnion_of_mem (fun b => pathEdges (u b) (v b) (f b)) hjs)
        · have his : i ∈ s := (mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            rw [hold i his, show f' a = w from Function.update_self a w f]
            exact (hnewdis.mono_right
              (subset_biUnion_of_mem (fun b => pathEdges (u b) (v b) (f b)) his)).symm
          · have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hja
            rw [hold i his, hold j hjs]
            exact hdis his hjs hij
      · intro x
        rw [show f' = Function.update f a w from rfl, auxiliaryLoad_insert_update s a ha]
        split_ifs with hx
        · subst x
          exact Nat.succ_le_of_lt hwQuota
        · simpa only [Nat.add_zero] using haux x

end PartitionedTriangleAbsorption.AntiEdgeSelection
