/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.WeightedRoutingChoice
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.SubdivisionLoad

/-!
# Simple physical paths along a label walk

`pathEdgesFrom a l` is the edge set of the vertex sequence `a :: l`.  For a simple sequence
(`(a :: l).Nodup`) its incidence is exactly one at the two (distinct) ends, two at an interior
vertex and zero elsewhere (`incidentLoad_pathEdgesFrom`), so it has the parity of the single
pair `s(a, last)`.

`exists_path_along_walk` is the inner induction of the weighted routing: given a label walk
`lab 0, …, lab m` of length `m ≥ 2` with allowed consecutive labels and a one-step chooser
(supplied by `weighted_routing_vertex`), it builds a simple path from `x` to `y` with exactly
`m` edges whose labels follow the walk, whose interior vertices avoid a forbidden set and
satisfy a goodness predicate, and none of whose edges lies in a fixed forbidden edge set `B`.
Only the last interior vertex has two adjacency constraints.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption AntiEdgeSelection StructuralF3General
open UniversalRefiner

variable {V : Type*} [DecidableEq V]

/-- Edge set of the vertex sequence `a :: l`. -/
def pathEdgesFrom : V → List V → Finset (Sym2 V)
  | _, [] => ∅
  | a, b :: l => insert s(a, b) (pathEdgesFrom b l)

/-- Interior auxiliary incidence (`2` at an interior vertex) of the path `a :: l`. -/
def pathAux (a : V) (l : List V) (v : V) : ℕ :=
  if v ≠ a ∧ v ≠ l.getLastD a ∧ v ∈ l then 2 else 0

@[simp] theorem pathEdgesFrom_nil (a : V) : pathEdgesFrom a [] = ∅ := rfl

@[simp] theorem pathEdgesFrom_cons (a b : V) (l : List V) :
    pathEdgesFrom a (b :: l) = insert s(a, b) (pathEdgesFrom b l) := rfl

theorem mem_of_mem_pathEdgesFrom {a : V} {l : List V} {e : Sym2 V}
    (he : e ∈ pathEdgesFrom a l) : ∀ v ∈ e, v ∈ a :: l := by
  induction l generalizing a with
  | nil => simp at he
  | cons b l ih =>
    rw [pathEdgesFrom_cons, mem_insert] at he
    rcases he with rfl | he
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
    · intro v hv
      exact List.mem_cons_of_mem _ (ih he v hv)

theorem card_pathEdgesFrom_le (a : V) (l : List V) : (pathEdgesFrom a l).card ≤ l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [pathEdgesFrom_cons]
    exact (card_insert_le _ _).trans (by simpa using ih b)

theorem incidentLoad_insert_of_notMem {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ E) (u : V) :
    incidentLoad (insert e E) u = incidentLoad E u + (if u ∈ e then 1 else 0) := by
  unfold incidentLoad
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => he (mem_filter.mp h').1)]
  · simp

/-- Exact incidence identity for a simple vertex sequence. -/
theorem incidentLoad_pathEdgesFrom_add {a : V} {l : List V} (hnd : (a :: l).Nodup) (u : V) :
    incidentLoad (pathEdgesFrom a l) u + (if u = a then 1 else 0) +
      (if u = l.getLastD a then 1 else 0) = if u ∈ a :: l then 2 else 0 := by
  induction l generalizing a with
  | nil =>
    simp only [pathEdgesFrom_nil, List.getLastD_nil, List.mem_singleton]
    unfold incidentLoad
    split_ifs <;> simp_all
  | cons b l ih =>
    have hnd' : (b :: l).Nodup := (List.nodup_cons.mp hnd).2
    have ha : a ∉ b :: l := (List.nodup_cons.mp hnd).1
    have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
    have hnot : s(a, b) ∉ pathEdgesFrom b l := fun h =>
      ha (mem_of_mem_pathEdgesFrom h a (Sym2.mem_mk_left a b))
    have ih' := ih hnd'
    rw [pathEdgesFrom_cons, incidentLoad_insert_of_notMem hnot, List.getLastD_cons]
    have hs : (u ∈ s(a, b)) ↔ (u = a ∨ u = b) := Sym2.mem_iff
    rw [if_congr hs rfl rfl]
    have hlast : l.getLastD b ∈ b :: l := List.getLastD_mem_cons
    have hmem : (u ∈ a :: b :: l) ↔ (u = a ∨ u ∈ b :: l) := List.mem_cons
    rw [if_congr hmem rfl rfl]
    by_cases hua : u = a
    · subst hua
      have h2 : ¬ u = l.getLastD b := fun h => ha (h ▸ hlast)
      have h1 : ¬ u ∈ b :: l := ha
      have h3 : ¬ u = b := hab
      simp only [h1, h2, h3, if_false] at ih'
      simp only [h2, h3, if_false, true_or, if_true]
      omega
    · simp only [hua, false_or, if_false, add_zero]
      exact ih'

omit [DecidableEq V] in
theorem getLastD_ne_of_nodup {a : V} {l : List V} (hnd : (a :: l).Nodup) (hl : l ≠ []) :
    l.getLastD a ≠ a := by
  intro h
  have hmem : l.getLastD a ∈ l := by
    rw [List.getLastD_eq_getLast?]
    cases hl' : l.getLast? with
    | none => simp_all
    | some x => simpa using List.mem_of_getLast? hl'
  exact (List.nodup_cons.mp hnd).1 (h ▸ hmem)

/-- Incidence of a simple path: endpoints plus the interior auxiliary incidence. -/
theorem incidentLoad_pathEdgesFrom {a : V} {l : List V} (hnd : (a :: l).Nodup) (hl : l ≠ [])
    (u : V) :
    incidentLoad (pathEdgesFrom a l) u =
      (if u ∈ s(a, l.getLastD a) then 1 else 0) + pathAux a l u := by
  have h := incidentLoad_pathEdgesFrom_add hnd u
  have hne := getLastD_ne_of_nodup hnd hl
  have hlast : l.getLastD a ∈ l := by
    rw [List.getLastD_eq_getLast?]
    cases hl' : l.getLast? with
    | none => simp_all
    | some x => simpa using List.mem_of_getLast? hl'
  unfold pathAux
  generalize l.getLastD a = b at h hne hlast ⊢
  have hs : (u ∈ s(a, b)) ↔ (u = a ∨ u = b) := Sym2.mem_iff
  rw [if_congr hs rfl rfl]
  have hm : (u ∈ a :: l) ↔ (u = a ∨ u ∈ l) := List.mem_cons
  rw [if_congr hm rfl rfl] at h
  by_cases hua : u = a
  · have hub : ¬ u = b := fun h' => hne (h'.symm.trans hua)
    simp only [eq_true hua, eq_false hub, ne_eq, not_true, not_false_eq_true, true_or,
      false_and, if_true, if_false] at h ⊢
    omega
  · by_cases hub : u = b
    · have hul : u ∈ l := hub ▸ hlast
      simp only [eq_false hua, eq_true hub, eq_true hul, ne_eq, not_true, not_false_eq_true,
        or_true, false_and, and_false, if_true, if_false] at h ⊢
      omega
    · by_cases hul : u ∈ l
      · simp only [eq_false hua, eq_false hub, eq_true hul, ne_eq, not_false_eq_true,
          or_true, or_false, true_and, if_true, if_false] at h ⊢
        omega
      · simp only [eq_false hua, eq_false hub, eq_false hul, ne_eq, not_false_eq_true,
          or_false, and_false, if_false] at h ⊢
        omega

/-- The parity of a simple path is that of the pair of its ends. -/
theorem pathEdgesFrom_parity {a : V} {l : List V} (hnd : (a :: l).Nodup) (hl : l ≠ [])
    (u : V) : (incidentLoad (pathEdgesFrom a l) u : ZMod 2) = symInd s(a, l.getLastD a) u := by
  rw [incidentLoad_pathEdgesFrom hnd hl u, symInd]
  unfold pathAux
  push_cast
  split_ifs <;> rfl

theorem pathAux_le (a : V) (l : List V) (u : V) : pathAux a l u ≤ 2 := by
  unfold pathAux; split_ifs <;> omega

theorem sum_pathAux_le [Fintype V] (a : V) (l : List V) :
    ∑ u, pathAux a l u ≤ 2 * l.length := by
  calc ∑ u, pathAux a l u ≤ ∑ u, (if u ∈ l.toFinset then 2 else 0) := by
        refine sum_le_sum fun u _ => ?_
        unfold pathAux
        split_ifs with h1 h2 <;> simp_all
    _ = 2 * l.toFinset.card := by
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
        congr 2
        ext u; simp
    _ ≤ 2 * l.length := Nat.mul_le_mul_left _ (List.toFinset_card_le l)

theorem pathEdgesFrom_subset_edgeFinset (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {a : V} {l : List V} (hc : List.IsChain G.Adj (a :: l)) :
    pathEdgesFrom a l ⊆ G.edgeFinset := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [List.isChain_cons_cons] at hc
    rw [pathEdgesFrom_cons]
    refine insert_subset ?_ (ih hc.2)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hc.1

/-- **Inner induction: one simple path along a label walk.** -/
theorem exists_path_along_walk {t : ℕ} (p : V → Fin t) (G : SimpleGraph V)
    (Allowed : Fin t → Fin t → Prop) (hsymm : ∀ i j, Allowed i j → Allowed j i)
    (B : Finset (Sym2 V)) (good : V → Prop) (Lb : ℕ)
    (hstep : ∀ S Z : Finset V, S.card ≤ 2 → Z.card ≤ Lb + 1 → ∀ i : Fin t,
      (∀ u ∈ S, Allowed (p u) i) →
      ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧ good w ∧ ∀ u ∈ S, s(u, w) ∉ B)
    (lab : ℕ → Fin t) (m : ℕ) (hlab : ∀ k < m, Allowed (lab k) (lab (k + 1)))
    (y : V) (hy : p y = lab m) :
    ∀ r, 2 ≤ r → ∀ k, k + r = m → ∀ u : V, p u = lab k → u ≠ y → ∀ Z : Finset V,
      u ∈ Z → y ∈ Z → Z.card + r ≤ Lb + 3 →
      ∃ l : List V, l.length = r ∧ l.getLastD u = y ∧ (u :: l).Nodup ∧
        List.IsChain G.Adj (u :: l) ∧ (∀ w ∈ l, w ≠ y → w ∉ Z ∧ good w) ∧
        ∀ e ∈ pathEdgesFrom u l, e ∉ B := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro k hk u hu huy Z huZ hyZ hZ
    obtain ⟨w, hw, hadj, hwZ, hgood, hB⟩ := hstep {u, y} Z card_le_two (by omega) (lab (k + 1))
      (by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · rw [hu]; exact hlab k (by omega)
        · rw [mem_singleton.mp hv, hy, ← hk]
          exact hsymm _ _ (hlab (k + 1) (by omega)))
    have hwu : w ≠ u := fun h => hwZ (h ▸ huZ)
    have hwy : w ≠ y := fun h => hwZ (h ▸ hyZ)
    refine ⟨[w, y], rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      exact ⟨fun h => h.elim (fun h => hwu h.symm) (fun h => huy h), hwy⟩
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hadj u (by simp), (hadj y (by simp)).symm⟩
    · intro v hv hvy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨hwZ, hgood⟩
      · exact absurd rfl hvy
    · intro e he
      simp only [pathEdgesFrom_cons, pathEdgesFrom_nil, insert_empty, mem_insert,
        mem_singleton] at he
      rcases he with rfl | rfl
      · exact hB u (by simp)
      · rw [Sym2.eq_swap]; exact hB y (by simp)
  | succ r hr ih =>
    intro k hk u hu huy Z huZ hyZ hZ
    obtain ⟨w, hw, hadj, hwZ, hgood, hB⟩ := hstep {u} Z (by simp) (by omega) (lab (k + 1))
      (by
        intro v hv
        rw [mem_singleton.mp hv, hu]; exact hlab k (by omega))
    have hwu : w ≠ u := fun h => hwZ (h ▸ huZ)
    have hwy : w ≠ y := fun h => hwZ (h ▸ hyZ)
    obtain ⟨l, hlen, hlast, hnd, hch, hfresh, hnB⟩ := ih (k + 1) (by omega) w hw hwy (insert w Z)
      (mem_insert_self _ _) (mem_insert_of_mem hyZ)
      (by have := card_insert_le w Z; omega)
    refine ⟨w :: l, by simp [hlen], by rw [List.getLastD_cons]; exact hlast, ?_, ?_, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, hnd⟩
      intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hwu h.symm
      · by_cases h' : u = y
        · exact huy h'
        · exact (hfresh u h h').1 (mem_insert_of_mem huZ)
    · rw [List.isChain_cons_cons]
      exact ⟨hadj u (by simp), hch⟩
    · intro v hv hvy
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨hwZ, hgood⟩
      · obtain ⟨h1, h2⟩ := hfresh v hv hvy
        exact ⟨fun h => h1 (mem_insert_of_mem h), h2⟩
    · intro e he
      rw [pathEdgesFrom_cons, mem_insert] at he
      rcases he with rfl | he
      · exact hB u (by simp)
      · exact hnB e he

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
