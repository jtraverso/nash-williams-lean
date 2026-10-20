/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.RoutedPath

/-!
# The weighted physical routing theorem

`weighted_routing`: every edge `e = s(x, y)` of a (virtual) reserve `R` that admits a label walk
of length between `2` and `Lb` is replaced, ONCE and for all, by a simple physical path of the
host `G` from `x` to `y` with at most `Lb` edges.  The paths are pairwise edge-disjoint, avoid
the sparse reserve `X`, have the parity of their pair `e`, and the accumulated weighted
auxiliary incidence `∑_e w(e) · aux_e(v)` (an interior use on the path of `e` counts `2 w(e)`)
is at most `6 K λ n` at every vertex.

The proof is the finite induction over `R`.  Before each route, vertices with auxiliary load
`≥ 4 K λ n` are forbidden as interior vertices; the heavy set is small by the total weight
bound, the used edges plus `X` have degree at most `(7 K λ + 2 ρ) n` (using `w ≥ 1`), and the
one-step choice `weighted_routing_vertex` provides each next vertex.  Inside a single path all
its vertices and the far endpoint stay forbidden, so its own edges are automatically new.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption AntiEdgeSelection StructuralF3General
open UniversalRefiner

variable {V : Type} [Fintype V] [DecidableEq V] {t : ℕ}

omit [Fintype V] in
/-- Degree of the used edges, from the incidence identity and the weighted ledger. -/
theorem routed_degree_le (R T : Finset (Sym2 V)) (hTR : T ⊆ R) (w : Sym2 V → ℕ)
    (hw1 : ∀ e ∈ R, 1 ≤ w e) (f : Sym2 V → Finset (Sym2 V)) (aux : Sym2 V → V → ℕ)
    (hinc : ∀ e ∈ T, ∀ v, incidentLoad (f e) v = (if v ∈ e then 1 else 0) + aux e v)
    (v : V) :
    incidentLoad (T.biUnion f) v ≤
      (∑ e ∈ R.filter (fun e => v ∈ e), w e) + ∑ e ∈ T, w e * aux e v := by
  refine (StructuralF3General.incidentLoad_biUnion_le T f v).trans ?_
  rw [sum_congr rfl fun e he => hinc e he v, sum_add_distrib]
  refine Nat.add_le_add ?_ ?_
  · rw [sum_filter]
    calc ∑ e ∈ T, (if v ∈ e then 1 else 0) ≤ ∑ e ∈ T, (if v ∈ e then w e else 0) :=
          sum_le_sum fun e he => by split_ifs <;> simp [hw1 e (hTR he)]
      _ ≤ ∑ e ∈ R, (if v ∈ e then w e else 0) :=
          sum_le_sum_of_subset_of_nonneg hTR (fun _ _ _ => Nat.zero_le _)
  · exact sum_le_sum fun e he => Nat.le_mul_of_pos_left _ (hw1 e (hTR he))

omit [DecidableEq V] in
/-- Total weighted auxiliary mass. -/
theorem routed_total_le (R T : Finset (Sym2 V)) (hTR : T ⊆ R) (w : Sym2 V → ℕ)
    (aux : Sym2 V → V → ℕ) (Lb : ℕ) (haux : ∀ e ∈ T, ∑ v, aux e v ≤ 2 * Lb) :
    ∑ v, ∑ e ∈ T, w e * aux e v ≤ 2 * Lb * ∑ e ∈ R, w e := by
  rw [sum_comm]
  calc ∑ e ∈ T, ∑ v, w e * aux e v = ∑ e ∈ T, w e * ∑ v, aux e v := by
        simp only [mul_sum]
    _ ≤ ∑ e ∈ T, w e * (2 * Lb) := sum_le_sum fun e he => Nat.mul_le_mul_left _ (haux e he)
    _ ≤ ∑ e ∈ R, w e * (2 * Lb) :=
        sum_le_sum_of_subset_of_nonneg hTR (fun _ _ _ => Nat.zero_le _)
    _ = 2 * Lb * ∑ e ∈ R, w e := by rw [← sum_mul, mul_comm]

/-- **Weighted physical routing.** -/
theorem weighted_routing (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (hsymm : ∀ i j, Allowed i j → Allowed j i)
    (K lam rho omega : ℝ) (Lb : ℕ) (hK : 1 ≤ K) (hlam : 0 < lam) (hrho : 0 ≤ rho)
    (hn : 0 < Fintype.card V)
    (hsmall : 64 * K * lam ≤ omega) (hratio : 128 * (Lb : ℝ) * rho ≤ omega * lam)
    (hrholam : rho ≤ lam) (horder : 4 * ((Lb : ℝ) + 1) ≤ omega * Fintype.card V)
    (hs : GuardedSupply p G Allowed 2 (omega * Fintype.card V))
    (X : Finset (Sym2 V)) (hX : DegBounded X (2 * rho * Fintype.card V))
    (R : Finset (Sym2 V)) (w : Sym2 V → ℕ) (hw1 : ∀ e ∈ R, 1 ≤ w e)
    (hwv : ∀ v, ((∑ e ∈ R.filter (fun e => v ∈ e), w e : ℕ) : ℝ) ≤ K * lam * Fintype.card V)
    (hwtot : ((∑ e ∈ R, w e : ℕ) : ℝ) ≤ 42 * K * rho * (Fintype.card V : ℝ) ^ 2)
    (hwalk : ∀ e ∈ R, ∃ x y, e = s(x, y) ∧ x ≠ y ∧ ∃ (m : ℕ) (lab : ℕ → Fin t), 2 ≤ m ∧
      m ≤ Lb ∧ lab 0 = p x ∧ lab m = p y ∧ ∀ k < m, Allowed (lab k) (lab (k + 1))) :
    ∃ (f : Sym2 V → Finset (Sym2 V)) (aux : Sym2 V → V → ℕ),
      (∀ e ∈ R, f e ⊆ G.edgeFinset ∧ (f e).card ≤ Lb ∧ Disjoint (f e) X ∧
        (∀ v, incidentLoad (f e) v = (if v ∈ e then 1 else 0) + aux e v) ∧
        ∀ v, (incidentLoad (f e) v : ZMod 2) = symInd e v) ∧
      (R : Set (Sym2 V)).PairwiseDisjoint f ∧
      ∀ v, ((∑ e ∈ R, w e * aux e v : ℕ) : ℝ) ≤ 6 * K * lam * Fintype.card V := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hKl : 0 ≤ K * lam * n := by
    have : 0 < K := by linarith
    positivity
  -- the generalized statement, by induction over subsets of `R`
  suffices H : ∀ T : Finset (Sym2 V), T ⊆ R →
      ∃ (f : Sym2 V → Finset (Sym2 V)) (aux : Sym2 V → V → ℕ),
        (∀ e ∈ T, f e ⊆ G.edgeFinset ∧ (f e).card ≤ Lb ∧ Disjoint (f e) X ∧
          (∀ v, incidentLoad (f e) v = (if v ∈ e then 1 else 0) + aux e v) ∧
          (∀ v, (incidentLoad (f e) v : ZMod 2) = symInd e v) ∧
          ∑ v, aux e v ≤ 2 * Lb) ∧
        (T : Set (Sym2 V)).PairwiseDisjoint f ∧
        ∀ v, ((∑ e ∈ T, w e * aux e v : ℕ) : ℝ) ≤ 6 * K * lam * n by
    obtain ⟨f, aux, h1, h2, h3⟩ := H R subset_rfl
    exact ⟨f, aux, fun e he => ⟨(h1 e he).1, (h1 e he).2.1, (h1 e he).2.2.1,
      (h1 e he).2.2.2.1, (h1 e he).2.2.2.2.1⟩, h2, h3⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun _ => ∅, fun _ _ => 0, by simp, by simp, fun v => ?_⟩
    simp only [sum_empty, Nat.cast_zero]
    nlinarith
  | insert e T heT ih =>
    intro hTR
    have hTR' : T ⊆ R := (subset_insert e T).trans hTR
    have heR : e ∈ R := hTR (mem_insert_self e T)
    obtain ⟨f, aux, hfT, hdisjT, hloadT⟩ := ih hTR'
    -- the current auxiliary load and forbidden edges
    set load : V → ℝ := fun v => ((∑ e' ∈ T, w e' * aux e' v : ℕ) : ℝ) with hload
    set B : Finset (Sym2 V) := T.biUnion f ∪ X with hB
    have hBdeg : DegBounded B ((7 * K * lam + 2 * rho) * n) := by
      have h1 : DegBounded (T.biUnion f) (7 * K * lam * n) := by
        intro v
        change ((incidentLoad (T.biUnion f) v : ℕ) : ℝ) ≤ _
        have h := routed_degree_le R T hTR' w hw1 f aux (fun e he => (hfT e he).2.2.2.1) v
        have h' : ((incidentLoad (T.biUnion f) v : ℕ) : ℝ) ≤
            ((∑ e ∈ R.filter (fun e => v ∈ e), w e : ℕ) : ℝ) +
              ((∑ e ∈ T, w e * aux e v : ℕ) : ℝ) := by exact_mod_cast h
        have := hwv v
        have := hloadT v
        linarith
      have h2 := StructuralF3General.degBounded_union h1 hX
      intro v
      have := h2 v
      linarith
    have htotal : ∑ v, load v ≤ 84 * (Lb : ℝ) * K * rho * n ^ 2 := by
      have h := routed_total_le R T hTR' w aux Lb (fun e he => (hfT e he).2.2.2.2.2)
      have h' : ((∑ v, ∑ e ∈ T, w e * aux e v : ℕ) : ℝ) ≤ 2 * Lb * ((∑ e ∈ R, w e : ℕ) : ℝ) := by
        exact_mod_cast h
      have hcast : ∑ v, load v = ((∑ v, ∑ e ∈ T, w e * aux e v : ℕ) : ℝ) := by
        simp only [hload, Nat.cast_sum]
      rw [hcast]
      have hL0 : (0 : ℝ) ≤ 2 * Lb := by positivity
      have := mul_le_mul_of_nonneg_left hwtot hL0
      nlinarith
    have hload0 : ∀ v, 0 ≤ load v := fun v => Nat.cast_nonneg _
    -- the one-step chooser
    have hstep : ∀ S Z : Finset V, S.card ≤ 2 → Z.card ≤ Lb + 1 → ∀ i : Fin t,
        (∀ u ∈ S, Allowed (p u) i) →
        ∃ w', p w' = i ∧ (∀ u ∈ S, G.Adj u w') ∧ w' ∉ Z ∧ load w' < 4 * K * lam * n ∧
          ∀ u ∈ S, s(u, w') ∉ B := by
      intro S Z hS hZ i hi
      exact weighted_routing_vertex p G Allowed K Lb lam rho omega hK (Nat.cast_nonneg _) hlam
        hrho hn hsmall hratio hrholam horder hs load hload0 htotal B hBdeg S Z hS
        (by exact_mod_cast hZ) i hi
    -- route `e`
    obtain ⟨x, y, rfl, hxy, m, lab, hm2, hmL, hlab0, hlabm, hlab⟩ := hwalk _ heR
    obtain ⟨l, hlen, hlast, hnd, hch, hfresh, hnB⟩ :=
      exists_path_along_walk p G Allowed hsymm B (fun v => load v < 4 * K * lam * n) Lb hstep
        lab m hlab y hlabm.symm m hm2 0 (zero_add m) x hlab0.symm hxy {x, y}
        (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _))
        (by rw [card_pair hxy]; omega)
    have hl : l ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    -- the weight of `e` is at most `K λ n`
    have hwe : (w s(x, y) : ℝ) ≤ K * lam * n := by
      refine le_trans ?_ (hwv x)
      exact_mod_cast single_le_sum (f := w) (fun _ _ => Nat.zero_le _)
        (mem_filter.mpr ⟨heR, Sym2.mem_mk_left x y⟩)
    refine ⟨Function.update f s(x, y) (pathEdgesFrom x l),
      Function.update aux s(x, y) (pathAux x l), ?_, ?_, ?_⟩
    · intro e' he'
      rcases mem_insert.mp he' with rfl | he'T
      · simp only [Function.update_self]
        refine ⟨pathEdgesFrom_subset_edgeFinset G hch, (card_pathEdgesFrom_le x l).trans
          (hlen ▸ hmL), ?_, ?_, ?_, ?_⟩
        · rw [disjoint_left]
          intro a ha haX
          exact hnB a ha (mem_union_right _ haX)
        · intro v
          rw [incidentLoad_pathEdgesFrom hnd hl v, hlast]
        · intro v
          rw [pathEdgesFrom_parity hnd hl v, hlast]
        · exact (sum_pathAux_le x l).trans (by rw [hlen]; omega)
      · have hne : e' ≠ s(x, y) := fun h => heT (h ▸ he'T)
        simp only [Function.update_of_ne hne]
        exact hfT e' he'T
    · intro a ha b hb hab
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
      have hnew : ∀ c ∈ T, Disjoint (pathEdgesFrom x l) (f c) := by
        intro c hc
        rw [disjoint_left]
        intro z hz hzc
        exact hnB z hz (mem_union_left _ (mem_biUnion.mpr ⟨c, hc, hzc⟩))
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · have hne : b ≠ s(x, y) := fun h => heT (h ▸ hb)
        change Disjoint (Function.update f _ _ _) (Function.update f _ _ _)
        rw [Function.update_self, Function.update_of_ne hne]
        exact hnew b hb
      · have hne : a ≠ s(x, y) := fun h => heT (h ▸ ha)
        change Disjoint (Function.update f _ _ _) (Function.update f _ _ _)
        rw [Function.update_self, Function.update_of_ne hne]
        exact (hnew a ha).symm
      · have hne1 : a ≠ s(x, y) := fun h => heT (h ▸ ha)
        have hne2 : b ≠ s(x, y) := fun h => heT (h ▸ hb)
        change Disjoint (Function.update f _ _ _) (Function.update f _ _ _)
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hdisjT ha hb hab
    · intro v
      rw [sum_insert heT, Function.update_self]
      have hrest : ∑ e' ∈ T, w e' * Function.update aux s(x, y) (pathAux x l) e' v =
          ∑ e' ∈ T, w e' * aux e' v := by
        refine sum_congr rfl fun e' he' => ?_
        have hne : e' ≠ s(x, y) := fun h => heT (h ▸ he')
        rw [Function.update_of_ne hne]
      rw [hrest]
      have hT := hloadT v
      push_cast at hT ⊢
      by_cases hint : v ≠ x ∧ v ≠ l.getLastD x ∧ v ∈ l
      · have haux : pathAux x l v = 2 := by unfold pathAux; rw [if_pos hint]
        have hvy : v ≠ y := hlast ▸ hint.2.1
        have hgood : load v < 4 * K * lam * n := (hfresh v hint.2.2 hvy).2
        simp only [hload] at hgood
        push_cast at hgood
        rw [haux]
        push_cast
        nlinarith
      · have haux : pathAux x l v = 0 := by unfold pathAux; rw [if_neg hint]
        rw [haux]
        push_cast
        linarith

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
