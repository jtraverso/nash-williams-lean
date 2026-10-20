/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Defs
public import PartitionedTriangleAbsorption.GeometricStarMarginStage146
public import PartitionedTriangleAbsorption.PhysicalStarMatching

@[expose] public section

/-!
# Sequential assembly of the exceptional stars (independent exceptional set)

Stage146 (`GeometricStarMarginStage146.exists_allocated_neighbour_pairings`) produces graph
quotas `q`, an integer allocation `x` and, **for a fixed forbidden relation `B`** of maximum
degree `≤ |S|`, a local physical pairing of the neighbourhood of each exceptional centre
avoiding `B`.  It does not select the pairings of different centres simultaneously.

Here the pairings are chosen **sequentially**: the forbidden relation is updated, after each
centre, with the base edges `w f(w)` already used.  Each pairing is an involution, so it
uses at most one base edge at every vertex; hence after processing any set `T` of centres the
updated relation has maximum degree `≤ |T| ≤ |S|`, which is exactly the hypothesis of the
Stage146 constructor.  The result (`exists_simultaneous_star_pairings`) gives pairings of all
exceptional centres at once, with the same quotas and allocation, whose base edges are pairwise
distinct across centres.

The hypotheses are those of Stage146; in particular the exceptional set must be independent
**in the same graph** `G` (with `δ(G) ≥ 3n/4`).  The pre-clean of edges inside a
non-independent exceptional set is not addressed here.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open StarPairProfileStage145 NeighbourStarAdapterStage146 ExceptionalGeometryStage141

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Simultaneous exceptional star pairings** (sequential assembly of Stage146).
Under the hypotheses of `GeometricStarMarginStage146.exists_allocated_neighbour_pairings`
(but with no forbidden relation), there are graph quotas `q`, an allocation `x`, and for every
exceptional centre `v` a fixed-point-free involution `g v` of the actual neighbours of `v`
pairing each neighbour with an adjacent neighbour in a different class and realising the
prescribed class-pair counts, such that the base edges `w (g v w)` of distinct centres are
distinct. -/
theorem exists_simultaneous_star_pairings (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hn : 128 ≤ Fintype.card V)
    (hrho : 0 ≤ rho) (htau : 0 < tau)
    (htsmall : tau ≤ 1 / 1024) (hrsmall : rho ≤ tau / 1024)
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hdiv : OnePart.Even3 G.edgeFinset)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (hS : ∀ u ∈ exceptional G p tau, ∀ w ∈ exceptional G p tau, ¬ G.Adj u w) :
    ∃ q : Fin 3 → ℕ, ∃ x : exceptional G p tau → Fin 3 → ℕ,
      (∀ i, 6 * q i + 3 * (cuts p G.edgeFinset i).card = 2 * G.edgeFinset.card) ∧
      (∑ i, q i) = (internal p G.edgeFinset).card ∧
      (∀ v : exceptional G p tau, ∑ i, x v i = classLoad p G v (p v)) ∧
      (∀ (v : exceptional G p tau) i,
        classLoad p G v (p v) + classLoad p G v (partner i (p v)) -
          G.degree v / 2 ≤ x v i ∧ x v i ≤ classLoad p G v (partner i (p v))) ∧
      (∀ i, ∑ v, x v i ≤ q i) ∧
      ∃ g : (v : exceptional G p tau) → (Neighbours G v ≃ Neighbours G v),
        (∀ v, Function.Involutive (g v) ∧ (∀ w : Neighbours G v, p (g v w) ≠ p w) ∧
          (∀ w : Neighbours G v, G.Adj w (g v w)) ∧
          ∀ j k, (univ.filter fun w : Neighbours G v =>
            localLabel p v w = j ∧ localLabel p v (g v w) = k).card =
              pairDemand (classLoad p G v (p v)) (G.degree v / 2)
                (fun i => classLoad p G v (partner i (p v))) (x v) j k) ∧
        ∀ v v' : exceptional G p tau, v ≠ v' →
          ∀ (w : Neighbours G v) (w' : Neighbours G v'),
            s(w.1, (g v w).1) ≠ s(w'.1, (g v' w').1) := by
  classical
  set S := exceptional G p tau with hSdef
  have hnpos : 0 < Fintype.card V := by omega
  have hr64 : rho ≤ 1 / 64 := by linarith
  have hd (v : V) : 3 * Fintype.card V ≤ 4 * G.degree v := by
    have hh : (3 : ℝ) * Fintype.card V ≤ 4 * G.degree v := by linarith [hdegree v]
    exact_mod_cast hh
  have hc (j : Fin 4) :
      8 * (univ.filter fun w => p w = j).card ≤ 3 * Fintype.card V :=
    class_budget_of_average p G rho hrho hr64 hnpos hdegree herr j
  obtain ⟨q, x, hq, hsum, hrow, hx, hcol⟩ :=
    exists_allocation_of_graph p G S hd hdiv hS hc
  refine ⟨q, x, hq, hsum, hrow, hx, hcol, ?_⟩
  have heven (v : V) : G.degree v = 2 * (G.degree v / 2) := by
    obtain ⟨d, h⟩ := hdiv.2 v
    rw [IndependentStarQuotaStage144.incident_degree G v] at h
    omega
  have ha (v : V) : classLoad p G v (p v) ≤ G.degree v / 2 := by
    have h1 := hc (p v)
    have h2 := hd v
    have h3 := classLoad_le_class_card p G v (p v)
    omega
  -- the local properties of a pairing at the centre `v`
  let Good : (v : S) → (Neighbours G v ≃ Neighbours G v) → Prop := fun v f =>
    Function.Involutive f ∧ (∀ w : Neighbours G v, p (f w) ≠ p w) ∧
      (∀ w : Neighbours G v, G.Adj w (f w)) ∧
      ∀ j k, (univ.filter fun w : Neighbours G v =>
        localLabel p v w = j ∧ localLabel p v (f w) = k).card =
          pairDemand (classLoad p G v (p v)) (G.degree v / 2)
            (fun i => classLoad p G v (partner i (p v))) (x v) j k
  suffices H : ∀ T : Finset S, ∃ g : (v : S) → (Neighbours G v ≃ Neighbours G v),
      (∀ v ∈ T, Good v (g v)) ∧
      ∀ v ∈ T, ∀ v' ∈ T, v ≠ v' → ∀ (w : Neighbours G v) (w' : Neighbours G v'),
        s(w.1, (g v w).1) ≠ s(w'.1, (g v' w').1) by
    obtain ⟨g, hg, hdisj⟩ := H univ
    exact ⟨g, fun v => hg v (mem_univ v), fun v v' hvv' => hdisj v (mem_univ v) v' (mem_univ v') hvv'⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨fun v => Equiv.refl _, by simp, by simp⟩
  | @insert v₀ T hv₀ ih =>
    obtain ⟨g, hg, hdisj⟩ := ih
    -- the base edges already used by the centres of `T`
    let B : V → V → Prop := fun a b =>
      ∃ v ∈ T, ∃ w : Neighbours G v, s(w.1, (g v w).1) = s(a, b)
    have hBsymm : ∀ a b, B a b → B b a := by
      rintro a b ⟨v, hv, w, hw⟩
      exact ⟨v, hv, w, hw.trans Sym2.eq_swap⟩
    have hused : ∀ a, (univ.filter fun z => B a z).card ≤ S.card := by
      intro a
      let h : S → V := fun v =>
        if ha : a ∈ G.neighborFinset v then (g v ⟨a, ha⟩).1 else a
      have hsub : (univ.filter fun z => B a z) ⊆ T.image h := by
        intro z hz
        obtain ⟨v, hv, w, hw⟩ := (mem_filter.mp hz).2
        refine mem_image.mpr ⟨v, hv, ?_⟩
        rcases Sym2.eq_iff.mp hw with ⟨hwa, hgz⟩ | ⟨hwz, hga⟩
        · have ha : a ∈ G.neighborFinset v := hwa ▸ w.2
          have hw' : w = ⟨a, ha⟩ := Subtype.ext hwa
          simp only [h, dif_pos ha, ← hw', hgz]
        · have ha : a ∈ G.neighborFinset v := hga ▸ (g v w).2
          have hw' : g v w = ⟨a, ha⟩ := Subtype.ext hga
          have hinv : g v ⟨a, ha⟩ = w := by
            rw [← hw']; exact (hg v hv).1 w
          simp only [h, dif_pos ha, hinv, hwz]
      calc (univ.filter fun z => B a z).card ≤ (T.image h).card := card_le_card hsub
        _ ≤ T.card := card_image_le
        _ ≤ (univ : Finset S).card := card_le_univ T
        _ = S.card := by rw [card_univ, Fintype.card_coe]
    obtain ⟨f, hfinv, hfp, hfadj, hfcount⟩ :=
      GeometricStarMarginStage146.exists_geometric_star_pairing G p rho tau hn hrho htau
        htsmall hrsmall hdegree herr hS B hBsymm hused v₀ (x v₀) (heven v₀) (ha v₀)
        (hrow v₀) (hx v₀)
    have hne : ∀ v ∈ T, v ≠ v₀ := fun v hv h => hv₀ (h ▸ hv)
    refine ⟨Function.update g v₀ f, ?_, ?_⟩
    · intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · rw [Function.update_self]
        exact ⟨hfinv, hfp, fun w => (hfadj w).1, hfcount⟩
      · rw [Function.update_of_ne (hne v hv)]
        exact hg v hv
    · intro v hv v' hv' hvv' w w'
      rcases mem_insert.mp hv with h1 | hvT <;> rcases mem_insert.mp hv' with h2 | hv'T
      · exact absurd (h1.trans h2.symm) hvv'
      · subst h1
        rw [Function.update_self, Function.update_of_ne (hne v' hv'T)]
        intro h
        exact (hfadj w).2 ⟨v', hv'T, w', h.symm⟩
      · subst h2
        rw [Function.update_self, Function.update_of_ne (hne v hvT)]
        intro h
        exact (hfadj w').2 ⟨v, hvT, w, h⟩
      · rw [Function.update_of_ne (hne v hvT), Function.update_of_ne (hne v' hv'T)]
        exact hdisj v hvT v' hv'T hvv' w w'

/-! ### From pairings to physical triangles -/

omit [Fintype V] in
lemma star_tri_eq_of_mem {v a b : V} (π : V → V) (hinv : π (π a) = a) (hb : b = a ∨ b = π a)
    (hinvb : π (π b) = b) : ({v, a, π a} : Finset V) = {v, b, π b} := by
  rcases hb with rfl | rfl
  · rfl
  · rw [hinv]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto

/-- The family of star triangles `{v, a, π v a}` (`v ∈ S`, `a` a neighbour of `v`). -/
def starFamily (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (π : V → V → V) :
    Finset (Finset V) :=
  S.biUnion (fun v => (G.neighborFinset v).image (fun a => ({v, a, π v a} : Finset V)))

/-- **Physical star packing from pairings** (explicit family).  Let `S` be an independent set
of `G` and, for every `v ∈ S`, let `π v` be an involution of the neighbourhood of `v` pairing
each neighbour `a` with an adjacent neighbour `π v a`, such that the base edges `a (π v a)` of
distinct centres are distinct.  Then the triangles `{v, a, π v a}` (the family `starFamily`) are
edge-disjoint triangles of `G` covering every edge at `S`, each containing exactly one vertex of
`S`, and every vertex outside `S` lies in at most `|S|` of them. -/
theorem starFamily_spec (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w) (π : V → V → V)
    (hπN : ∀ v ∈ S, ∀ a, G.Adj v a → G.Adj v (π v a))
    (hπinv : ∀ v ∈ S, ∀ a, G.Adj v a → π v (π v a) = a)
    (hπadj : ∀ v ∈ S, ∀ a, G.Adj v a → G.Adj a (π v a))
    (hdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → ∀ a b, G.Adj v a → G.Adj v' b →
      s(a, π v a) ≠ s(b, π v' b)) :
    let Q := starFamily G S π
    (∀ t ∈ Q, G.IsNClique 3 t) ∧ (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ v ∈ S, ∀ w, G.Adj v w → s(v, w) ∈ Q.biUnion triEdges) ∧
      (∀ t ∈ Q, (t.filter (· ∈ S)).card = 1) ∧
      (∀ x, x ∉ S → (Q.filter (fun t => x ∈ t)).card ≤ S.card) := by
  classical
  let tri : V → V → Finset V := fun v a => {v, a, π v a}
  intro Q
  have hQ : ∀ t, t ∈ Q ↔ ∃ v ∈ S, ∃ a, G.Adj v a ∧ tri v a = t := by
    intro t
    simp [Q, starFamily, tri, mem_biUnion, mem_image]
  have hnotS : ∀ v ∈ S, ∀ a, G.Adj v a → a ∉ S := fun v hv a ha haS => hS v hv a haS ha
  -- the vertices of a star triangle
  have hmemS : ∀ v ∈ S, ∀ a, G.Adj v a → ∀ z ∈ tri v a, z ∈ S → z = v := by
    intro v hv a ha z hz hzS
    simp only [tri, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rfl
    · exact absurd hzS (hnotS v hv _ ha)
    · exact absurd hzS (hnotS v hv _ (hπN v hv a ha))
  have hmemN : ∀ v ∈ S, ∀ a, G.Adj v a → ∀ z ∈ tri v a, z ≠ v → z = a ∨ z = π v a := by
    intro v hv a ha z hz hzv
    simp only [tri, mem_insert, mem_singleton] at hz
    rcases hz with rfl | h | h
    · exact absurd rfl hzv
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨v, hv, a, ha, rfl⟩ := (hQ t).mp ht
    exact (SimpleGraph.is3Clique_triple_iff).mpr ⟨ha, hπN v hv a ha, hπadj v hv a ha⟩
  · intro t ht t' ht' hne
    obtain ⟨v, hv, a, ha, rfl⟩ := (hQ t).mp ht
    obtain ⟨v', hv', b, hb, rfl⟩ := (hQ t').mp ht'
    refine Finset.disjoint_left.mpr fun e he he' => hne ?_
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx, hy, hxy⟩ := mk_mem_triEdges.mp he
      obtain ⟨hx', hy', -⟩ := mk_mem_triEdges.mp he'
      have hinva := hπinv v hv a ha
      have hinvb := hπinv v' hv' b hb
      -- a vertex of `S` on the common edge forces the same centre
      have key : ∀ z w, z ∈ tri v a → w ∈ tri v a → z ∈ tri v' b → w ∈ tri v' b →
          z ∈ S → z ≠ w → tri v a = tri v' b := by
        intro z w hz hw hz' hw' hzS hzw
        have h1 := hmemS v hv a ha z hz hzS
        have h2 := hmemS v' hv' b hb z hz' hzS
        subst h1
        subst h2
        have hwz : w ≠ z := fun h => hzw h.symm
        have hwa := hmemN z hv a ha w hw hwz
        have hwb := hmemN z hv' b hb w hw' hwz
        have hwN : G.Adj z w := by
          rcases hwa with rfl | rfl
          · exact ha
          · exact hπN z hv a ha
        have hinvw := hπinv z hv w hwN
        have e1 := star_tri_eq_of_mem (v := z) (π z) hinva hwa hinvw
        have e2 := star_tri_eq_of_mem (v := z) (π z) hinvb hwb hinvw
        exact e1.trans e2.symm
      by_cases hxS : x ∈ S
      · exact key x y hx hy hx' hy' hxS hxy
      by_cases hyS : y ∈ S
      · exact key y x hy hx hy' hx' hyS (Ne.symm hxy)
      have hxv : x ≠ v := fun h => hxS (h ▸ hv)
      have hyv : y ≠ v := fun h => hyS (h ▸ hv)
      have hxv' : x ≠ v' := fun h => hxS (h ▸ hv')
      have hyv' : y ≠ v' := fun h => hyS (h ▸ hv')
      have hxa := hmemN v hv a ha x hx hxv
      have hya := hmemN v hv a ha y hy hyv
      have hxb := hmemN v' hv' b hb x hx' hxv'
      have hyb := hmemN v' hv' b hb y hy' hyv'
      have hea : s(x, y) = s(a, π v a) := by
        rcases hxa with rfl | rfl <;> rcases hya with rfl | rfl
        · exact absurd rfl hxy
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hxy
      have heb : s(x, y) = s(b, π v' b) := by
        rcases hxb with rfl | rfl <;> rcases hyb with rfl | rfl
        · exact absurd rfl hxy
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hxy
      by_cases hvv : v = v'
      · subst hvv
        have hxN : G.Adj v x := by
          rcases hxa with rfl | rfl
          · exact ha
          · exact hπN v hv a ha
        have hinvx := hπinv v hv x hxN
        exact (star_tri_eq_of_mem (v := v) (π v) hinva hxa hinvx).trans
          (star_tri_eq_of_mem (v := v) (π v) hinvb hxb hinvx).symm
      · exact absurd (hea.symm.trans heb) (hdisj v hv v' hv' hvv a b ha hb)
  · intro v hv w hw
    refine mem_biUnion.mpr ⟨tri v w, (hQ _).mpr ⟨v, hv, w, hw, rfl⟩, ?_⟩
    exact mk_mem_triEdges.mpr ⟨by simp [tri], by simp [tri], hw.ne⟩
  · intro t ht
    obtain ⟨v, hv, a, ha, rfl⟩ := (hQ t).mp ht
    rw [card_eq_one]
    refine ⟨v, ?_⟩
    ext z
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hz, hzS⟩
      exact hmemS v hv a ha z hz hzS
    · rintro rfl
      exact ⟨by simp [tri], hv⟩
  · intro x hxS
    have hsub : Q.filter (fun t => x ∈ t) ⊆ S.image (fun v => tri v x) := by
      intro t ht
      obtain ⟨htQ, hxt⟩ := mem_filter.mp ht
      obtain ⟨v, hv, a, ha, rfl⟩ := (hQ t).mp htQ
      refine mem_image.mpr ⟨v, hv, ?_⟩
      have hxv : x ≠ v := fun h => hxS (h ▸ hv)
      have hxa := hmemN v hv a ha x hxt hxv
      have hxN : G.Adj v x := by
        rcases hxa with rfl | rfl
        · exact ha
        · exact hπN v hv a ha
      exact (star_tri_eq_of_mem (v := v) (π v) (hπinv v hv a ha) hxa (hπinv v hv x hxN)).symm
    exact (card_le_card hsub).trans card_image_le

/-- **Physical star packing from pairings.**  Existential form of `starFamily_spec`. -/
theorem star_triangles_of_pairings (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w) (π : V → V → V)
    (hπN : ∀ v ∈ S, ∀ a, G.Adj v a → G.Adj v (π v a))
    (hπinv : ∀ v ∈ S, ∀ a, G.Adj v a → π v (π v a) = a)
    (hπadj : ∀ v ∈ S, ∀ a, G.Adj v a → G.Adj a (π v a))
    (hdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → ∀ a b, G.Adj v a → G.Adj v' b →
      s(a, π v a) ≠ s(b, π v' b)) :
    ∃ Q : Finset (Finset V),
      (∀ t ∈ Q, G.IsNClique 3 t) ∧ (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ v ∈ S, ∀ w, G.Adj v w → s(v, w) ∈ Q.biUnion triEdges) ∧
      (∀ t ∈ Q, (t.filter (· ∈ S)).card = 1) ∧
      (∀ x, x ∉ S → (Q.filter (fun t => x ∈ t)).card ≤ S.card) :=
  ⟨starFamily G S π, starFamily_spec G S hS π hπN hπinv hπadj hdisj⟩

/-- **Exceptional star packing** (independent exceptional set).  Under the hypotheses of
Stage146 (`n ≥ 128`, `0 < τ ≤ 1/1024`, `0 ≤ ρ ≤ τ/1024`, `δ(G) ≥ 3n/4`, ordinary triangle
divisibility, at most `ρ n²` internal edges, and exceptional set `S` independent in the same
graph `G`), there is a family `Q` of edge-disjoint triangles of `G` covering every edge at `S`,
each containing exactly one vertex of `S`, and with every vertex outside `S` in at most `|S|`
triangles of `Q`.  The quota bookkeeping of the residual is *not* part of this statement. -/
theorem exists_exceptional_star_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hn : 128 ≤ Fintype.card V)
    (hrho : 0 ≤ rho) (htau : 0 < tau)
    (htsmall : tau ≤ 1 / 1024) (hrsmall : rho ≤ tau / 1024)
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hdiv : OnePart.Even3 G.edgeFinset)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (hS : ∀ u ∈ exceptional G p tau, ∀ w ∈ exceptional G p tau, ¬ G.Adj u w) :
    ∃ Q : Finset (Finset V),
      (∀ t ∈ Q, G.IsNClique 3 t) ∧ (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ v ∈ exceptional G p tau, ∀ w, G.Adj v w → s(v, w) ∈ Q.biUnion triEdges) ∧
      (∀ t ∈ Q, (t.filter (· ∈ exceptional G p tau)).card = 1) ∧
      (∀ x, x ∉ exceptional G p tau →
        (Q.filter (fun t => x ∈ t)).card ≤ (exceptional G p tau).card) := by
  classical
  have hP := exists_simultaneous_star_pairings G p rho tau hn
    hrho htau htsmall hrsmall hdegree hdiv herr hS
  set S := exceptional G p tau
  obtain ⟨q, x, -, -, -, -, -, g, hg, hgd⟩ := hP
  let π : V → V → V := fun v a =>
    if hv : v ∈ S then
      if ha : a ∈ G.neighborFinset v then (g ⟨v, hv⟩ ⟨a, ha⟩).1 else a
    else a
  have hπ : ∀ v (hv : v ∈ S) a (ha : G.Adj v a),
      π v a = (g ⟨v, hv⟩ ⟨a, (G.mem_neighborFinset v a).mpr ha⟩).1 := by
    intro v hv a ha
    simp only [π, dif_pos hv, dif_pos ((G.mem_neighborFinset v a).mpr ha)]
  have hmemN : ∀ v (hv : v ∈ S) (w : Neighbours G v), G.Adj v (g ⟨v, hv⟩ w).1 :=
    fun v hv w => (G.mem_neighborFinset _ _).mp (g ⟨v, hv⟩ w).2
  apply star_triangles_of_pairings G S hS π
  · intro v hv a ha
    rw [hπ v hv a ha]
    exact hmemN v hv _
  · intro v hv a ha
    rw [hπ v hv a ha, hπ v hv _ (hmemN v hv _)]
    have := (hg ⟨v, hv⟩).1 ⟨a, (G.mem_neighborFinset v a).mpr ha⟩
    simp only [Subtype.coe_eta]
    rw [this]
  · intro v hv a ha
    rw [hπ v hv a ha]
    exact (hg ⟨v, hv⟩).2.2.1 ⟨a, (G.mem_neighborFinset v a).mpr ha⟩
  · intro v hv v' hv' hvv a b ha hb
    rw [hπ v hv a ha, hπ v' hv' b hb]
    exact hgd ⟨v, hv⟩ ⟨v', hv'⟩ (fun h => hvv (congrArg Subtype.val h))
      ⟨a, (G.mem_neighborFinset v a).mpr ha⟩ ⟨b, (G.mem_neighborFinset v' b).mpr hb⟩

/-- **Single dense star** (contribution `PhysicalStarMatching`, restated with the edge-cover
convention of this development).  If the neighbourhood of `z` is split into two disjoint blocks
`X`, `Y` of the same size `k`, each vertex having at most `r` non-neighbours in the other block,
and `2r ≤ k`, then there are `k` edge-disjoint triangles of `G` through `z` covering every edge
at `z`.  This is a statement about one star only. -/
theorem single_star_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) (X Y : Finset V) (r : ℕ)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = G.neighborFinset z)
    (hcard : X.card = Y.card) (hsize : 2 * r ≤ Y.card)
    (hleft : ∀ x ∈ X, (Y.filter fun y => ¬ G.Adj x y).card ≤ r)
    (hright : ∀ y ∈ Y, (X.filter fun x => ¬ G.Adj x y).card ≤ r) :
    ∃ D : Finset (Finset V),
      (∀ t ∈ D, G.IsNClique 3 t ∧ z ∈ t) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
      D.card = X.card ∧ ∀ w, G.Adj z w → s(z, w) ∈ D.biUnion triEdges := by
  obtain ⟨f, D, hD, htri, hdis, hcount, hroot⟩ :=
    PhysicalStarMatching.exists_dense_star_packing G z X Y r hXY hcover hcard hsize hleft hright
  refine ⟨D, fun t ht => ⟨htri t ht, ?_⟩, hdis, hcount, fun w hw => ?_⟩
  · rw [hD] at ht
    obtain ⟨a, -, rfl⟩ := mem_image.mp ht
    simp
  · obtain ⟨t, ⟨htD, hzt, hwt⟩, -⟩ := hroot w hw
    exact mem_biUnion.mpr ⟨t, htD, mk_mem_triEdges.mpr ⟨hzt, hwt, hw.ne⟩⟩

end NashWilliams18
