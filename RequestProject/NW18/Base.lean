/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import RequestProject.NashWilliamsBasic

@[expose] public section

/-!
# Base of the Theorem 1.8 development: partitioned-triangle definitions and `K₃` sanity facts

This file is the common base of `RequestProject/NW18`.  It imports the partitioned-triangle
definitions (`edgeVec`, `IsIntDiv`, `HasDecomp`, `IsCopy`, `IsHinge`, … from
`PartitionedTriangleAbsorption.ReturnedBasic`, and the bookkeeping of
`PartitionedTriangleAbsorption.ReturnedDivisibility`) from the ported local route
(`Stage133Port`), so that the Theorem 1.8 development can import the route's modules
(Stages 134–146, `CommonClassSupply`, `PhysicalStarMatching`).  Those two modules are verbatim
ports of `RequestProject/PartitionedTriangleAbsorption/Basic.lean` and `Divisibility.lean`
(identical declaration names and bodies), which cannot be imported together with the originals
(Lean rejects duplicate declarations), so the NW18 development now uses the ported copies.

Below are the facts of `RequestProject/PartitionedTriangleAbsorption/Sanity.lean`, restated
verbatim in the namespace `NashWilliams18` (same statements and proofs):

* `hasDecomp_edgeFinset_iff`: an `F`-decomposition of `E(G)` (edge sets of typed triangles
  partitioning `E(G)`) is the same as a family of `F`-copies of `G` such that every edge of `G`
  lies in exactly one of them — the paper's Definition 13.2.
* The unpartitioned case `t = 1`, `F = {K₃}`:
  `hasDecomp_K3_iff` (decompositions are triangle decompositions),
  `isIntDiv_K3_iff` (integral `{K₃}`-divisibility is `K₃`-divisibility: `3 ∣ e(G)` and all
  degrees even), and `antiEdgeful_K3_of_minDegree` (`δ(G) ≥ 3n/4` gives `1/2`-anti-edgefulness,
  the first step of the proof of Theorem 12.4).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [Fintype V] in
lemma mk_mem_triEdges {s : Finset V} {x y : V} :
    s(x, y) ∈ triEdges s ↔ x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  simp [triEdges, and_assoc]

omit [Fintype V] in
lemma triEdges_subset_of_isNClique {G : SimpleGraph V} {s : Finset V} (h : G.IsNClique 3 s)
    [DecidableRel G.Adj] [Fintype G.edgeSet] : triEdges s ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := mk_mem_triEdges.mp he
    simpa using h.1 hx hy hxy

omit [Fintype V] in
lemma isNClique_of_triEdges_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {s : Finset V} (hs : s.card = 3) (h : triEdges s ⊆ G.edgeFinset) :
    G.IsNClique 3 s := by
  refine ⟨fun x hx y hy hxy => ?_, hs⟩
  simpa using h (mk_mem_triEdges.mpr ⟨hx, hy, hxy⟩)

/-- An `F`-decomposition of `E(G)` is exactly a family of `F`-copies of `G` such that every
edge of `G` lies in exactly one member (Definition 13.2). -/
theorem hasDecomp_edgeFinset_iff (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDecomp p F G.edgeFinset ↔ ∃ D : Finset (Finset V), (∀ s ∈ D, IsCopy p F G s) ∧
      ∀ e ∈ G.edgeFinset, ∃! s, s ∈ D ∧ e ∈ triEdges s := by
  constructor
  · rintro ⟨D, hT, hdisj, hU⟩
    have hsub : ∀ s ∈ D, triEdges s ⊆ G.edgeFinset := fun s hs =>
      hU ▸ subset_biUnion_of_mem triEdges hs
    refine ⟨D, fun s hs => ⟨isNClique_of_triEdges_subset (hT s hs).1 (hsub s hs),
      (hT s hs).2⟩, fun e he => ?_⟩
    rw [← hU, mem_biUnion] at he
    obtain ⟨s, hs, hes⟩ := he
    refine ⟨s, ⟨hs, hes⟩, fun s' ⟨hs', hes'⟩ => ?_⟩
    by_contra hne
    exact disjoint_left.mp (hdisj hs' hs hne) hes' hes
  · rintro ⟨D, hC, huniq⟩
    refine ⟨D, fun s hs => ⟨(hC s hs).1.2, (hC s hs).2⟩, fun s hs s' hs' hne => ?_, ?_⟩
    · refine disjoint_left.mpr fun e he he' => hne ?_
      have heG := triEdges_subset_of_isNClique (hC s hs).1 he
      exact (huniq e heG).unique ⟨hs, he⟩ ⟨hs', he'⟩
    · ext e
      simp only [mem_biUnion]
      constructor
      · rintro ⟨s, hs, he⟩; exact triEdges_subset_of_isNClique (hC s hs).1 he
      · intro he; obtain ⟨s, ⟨hs, hes⟩, -⟩ := huniq e he; exact ⟨s, hs, hes⟩

/-! ### The unpartitioned case `t = 1`, `F = {K₃}` -/

/-- The single-part partition. -/
def onePart : V → Fin 1 := fun _ => 0

/-- The family `{K₃} = {T₀₀₀}` for `t = 1`. -/
def K3fam : Finset (Multiset (Fin 1)) := {{0, 0, 0}}

omit [Fintype V] [DecidableEq V] in
lemma map_onePart {s : Finset V} (hs : s.card = 3) :
    s.val.map onePart = ({0, 0, 0} : Multiset (Fin 1)) := by
  have : s.val.map onePart = Multiset.replicate 3 0 := by
    rw [Multiset.eq_replicate]
    exact ⟨by simpa using hs, fun b _ => Subsingleton.elim _ _⟩
  rw [this]; rfl

omit [Fintype V] [DecidableEq V] in
lemma isCopy_K3_iff (G : SimpleGraph V) (s : Finset V) :
    IsCopy onePart K3fam G s ↔ G.IsNClique 3 s := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [map_onePart h.2]; simp [K3fam]

/-- For `t = 1` and `F = {K₃}`, `F`-decompositions of `E(G)` are triangle decompositions. -/
theorem hasDecomp_K3_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDecomp onePart K3fam G.edgeFinset ↔ NashWilliams.HasTriangleDecomposition G := by
  rw [hasDecomp_edgeFinset_iff]
  simp only [isCopy_K3_iff]
  constructor
  · rintro ⟨D, hC, hu⟩
    refine ⟨D, hC, fun u v huv => ?_⟩
    have he : s(u, v) ∈ G.edgeFinset := by simpa using huv
    obtain ⟨s, ⟨hs, hes⟩, hu'⟩ := hu _ he
    rw [mk_mem_triEdges] at hes
    refine ⟨s, ⟨hs, hes.1, hes.2.1⟩, fun s' ⟨hs', hu1, hv1⟩ => hu' s' ⟨hs', ?_⟩⟩
    exact mk_mem_triEdges.mpr ⟨hu1, hv1, huv.ne⟩
  · rintro ⟨D, hC, hu⟩
    refine ⟨D, hC, fun e he => ?_⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      obtain ⟨s, ⟨hs, hus, hvs⟩, hu'⟩ := hu u v huv
      refine ⟨s, ⟨hs, mk_mem_triEdges.mpr ⟨hus, hvs, huv.ne⟩⟩, fun s' ⟨hs', he'⟩ => ?_⟩
      obtain ⟨h1, h2, -⟩ := mk_mem_triEdges.mp he'
      exact hu' s' ⟨hs', h1, h2⟩

omit [DecidableEq V] in
lemma edgeVec_onePart_of_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeVec onePart G.edgeFinset 0 0 = 2 * G.edgeFinset.card := by
  rw [edgeVec, Finset.sum_apply, Finset.sum_apply, card_eq_sum_ones, Nat.cast_sum,
    mul_sum]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ u v => simp [pairVec, onePart]

lemma degVec_onePart_of_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degVec onePart G.edgeFinset v 0 = G.degree v := by
  have hdeg : (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
    rw [← G.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]
  rw [← hdeg, degVec, Finset.sum_apply, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := (by simpa using he : G.Adj a b).ne
    by_cases ha : a = v
    · subst ha; simp [degContrib, onePart, hab.symm]
    · by_cases hb : b = v
      · subst hb; simp [degContrib, onePart, ha]
      · simp [degContrib, ha, hb, Ne.symm ha, Ne.symm hb]

/-- For `t = 1` and `F = {K₃}`, integral `F`-divisibility of `E(G)` is the usual
`K₃`-divisibility: `3 ∣ e(G)` and every degree is even. -/
theorem isIntDiv_K3_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsIntDiv onePart K3fam G.edgeFinset ↔ NashWilliams.IsTriangleDivisible G := by
  have hF : ∀ (v : V), ({{0, 0, 0}} : Finset (Multiset (Fin 1))).filter
      (fun τ => onePart v ∈ τ) = {{0, 0, 0}} := by
    intro v
    apply Finset.filter_eq_self.mpr
    intro τ hτ
    have hτ' := Finset.mem_singleton.mp hτ
    subst τ
    exact Multiset.mem_cons_self _ _
  have hE : typeEdgeVec ({0, 0, 0} : Multiset (Fin 1)) 0 0 = 6 := by decide
  have hD : ∀ v : V, typeDegVec ({0, 0, 0} : Multiset (Fin 1)) (onePart v) 0 = 2 := by
    intro v; simp only [onePart]; decide
  have funext2 : ∀ f g : Fin 1 → Fin 1 → ℤ, f = g ↔ f 0 0 = g 0 0 := fun f g =>
    ⟨fun h => by rw [h], fun h => by funext i j; fin_cases i; fin_cases j; exact h⟩
  have funext1 : ∀ f g : Fin 1 → ℤ, f = g ↔ f 0 = g 0 := fun f g =>
    ⟨fun h => by rw [h], fun h => by funext i; fin_cases i; exact h⟩
  simp only [IsIntDiv, hF, K3fam, sum_singleton, funext2, funext1, Pi.smul_apply,
    smul_eq_mul, hE, hD, edgeVec_onePart_of_edgeFinset, degVec_onePart_of_edgeFinset,
    NashWilliams.IsTriangleDivisible]
  constructor
  · rintro ⟨⟨c, hc⟩, hv⟩
    refine ⟨?_, fun v => ?_⟩
    · have : (3 : ℤ) ∣ G.edgeFinset.card := ⟨c _, by linarith⟩
      exact_mod_cast this
    · obtain ⟨c, hc⟩ := hv v
      have : Even (G.degree v : ℤ) := ⟨c _, by linarith⟩
      exact_mod_cast this
  · rintro ⟨⟨k, hk⟩, hv⟩
    refine ⟨⟨fun _ => k, by rw [hk]; push_cast; ring⟩, fun v => ?_⟩
    obtain ⟨m, hm⟩ := hv v
    exact ⟨fun _ => m, by rw [hm]; push_cast; ring⟩

/-- For `t = 1` and `F = {K₃}`: `δ(G) ≥ 3n/4` implies that `G` is `1/2`-`{K₃}`-anti-edgeful
(every two distinct vertices have at least `n/2` common neighbours). -/
theorem antiEdgeful_K3_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    AntiEdgeful onePart K3fam G (1 / 2) := by
  intro τ _ i j k _ u v _ _ _
  have hk : ∀ w : V, onePart w = k := fun w => Subsingleton.elim _ _
  simp only [hk, and_true]
  have hu := G.minDegree_le_degree u
  have hv := G.minDegree_le_degree v
  have key : G.degree u + G.degree v ≤
      Fintype.card V + (univ.filter (fun w => G.Adj u w ∧ G.Adj w v)).card := by
    rw [← G.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
    have h1 := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    have h2 : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
      card_le_univ _
    have h3 : G.neighborFinset u ∩ G.neighborFinset v =
        univ.filter (fun w => G.Adj u w ∧ G.Adj w v) := by
      ext w; simp [G.adj_comm w v]
    rw [h3] at h1
    omega
  have : (1 / 2 : ℝ) * Fintype.card V ≤
      ((univ.filter (fun w => G.Adj u w ∧ G.Adj w v)).card : ℕ) := by
    have h : 2 * Fintype.card V ≤ 4 * (univ.filter (fun w => G.Adj u w ∧ G.Adj w v)).card := by
      omega
    have h' : (2 * Fintype.card V : ℝ) ≤ 4 * (univ.filter (fun w => G.Adj u w ∧ G.Adj w v)).card := by
      exact_mod_cast h
    linarith
  exact this

end NashWilliams18
