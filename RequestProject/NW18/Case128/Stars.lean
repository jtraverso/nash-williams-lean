/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.Preclean

@[expose] public section

/-!
# Case (5): the exceptional stars with prescribed matched counts

After the pre-clean, the exceptional set `S` is independent.  For every `v ∈ S` an allocation
`x v i` prescribes how many internal neighbours of `v` are paired with neighbours in the `i`-th
partner class.  The local pairings of `NeighbourStarAdapterStage146` are chosen one centre at a
time, each avoiding the base edges already used, and the triangles `{v, w, π v w}` form an
edge-disjoint family covering every edge at `S`.  The number of its triangles lying on one side
of the `i`-th bipartition (the `i`-matched triangles) is at most `Σ_v x v i`.

This replaces the use of Theorem 15.19 (Claim 15.19.1) together with Claim 12.8.11: the edges
`O₄` are covered inside the stars themselves, with the prescribed colour counts.
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open StarPairProfileStage145 NeighbourStarAdapterStage146 ClassRepresentativesStage65
open CleanupSupplyStage140

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Exceptional stars with prescribed matched counts.** -/
theorem exists_star_family (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w)
    (x : S → Fin 3 → ℕ) (L D : ℕ)
    (heven : ∀ v ∈ S, G.degree v = 2 * (G.degree v / 2))
    (ha : ∀ v ∈ S, classLoad p G v (p v) ≤ G.degree v / 2)
    (hrow : ∀ v : S, ∑ i, x v i = classLoad p G v (p v))
    (hx : ∀ (v : S) i,
      classLoad p G v (p v) + classLoad p G v (partner i (p v)) - G.degree v / 2 ≤ x v i ∧
        x v i ≤ classLoad p G v (partner i (p v)))
    (hclasses : ∀ j, (classSet p j).card ≤ L)
    (hmissing : ∀ v ∈ S, ∀ w, G.Adj v w → (missingOutside G p w).card ≤ D)
    (hmargin : ∀ v ∈ S, 2 * L + 4 * (D + S.card) + 2 < G.degree v) :
    ∃ Q : Finset (Finset V),
      (∀ t ∈ Q, G.IsNClique 3 t) ∧ (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ v ∈ S, ∀ w, G.Adj v w → s(v, w) ∈ Q.biUnion triEdges) ∧
      (∀ y, y ∉ S → (Q.filter (fun t => y ∈ t)).card ≤ S.card) ∧
      (∀ i, (Q.filter (SameSide p i)).card ≤ ∑ v, x v i) := by
  classical
  -- the local properties of a pairing at the centre `v`
  let Good : (v : S) → (Neighbours G v ≃ Neighbours G v) → Prop := fun v f =>
    Function.Involutive f ∧ (∀ w : Neighbours G v, p (f w) ≠ p w) ∧
      (∀ w : Neighbours G v, G.Adj w (f w)) ∧
      ∀ j k, (univ.filter fun w : Neighbours G v =>
        localLabel p v w = j ∧ localLabel p v (f w) = k).card =
          pairDemand (classLoad p G v (p v)) (G.degree v / 2)
            (fun i => classLoad p G v (partner i (p v))) (x v) j k
  have H : ∀ T : Finset S, ∃ g : (v : S) → (Neighbours G v ≃ Neighbours G v),
      (∀ v ∈ T, Good v (g v)) ∧
      ∀ v ∈ T, ∀ v' ∈ T, v ≠ v' → ∀ (w : Neighbours G v) (w' : Neighbours G v'),
        s(w.1, (g v w).1) ≠ s(w'.1, (g v' w').1) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨fun v => Equiv.refl _, by simp, by simp⟩
    | @insert v₀ T hv₀ ih =>
      obtain ⟨g, hg, hdisj⟩ := ih
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
        exists_neighbour_star_pairing G p v₀ (x v₀) B hBsymm L D S.card
          (heven v₀ v₀.2) (ha v₀ v₀.2) (hrow v₀) (hx v₀) hclasses
          (fun w => hmissing v₀ v₀.2 w.1 ((G.mem_neighborFinset _ _).mp w.2)) hused
          (hmargin v₀ v₀.2)
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
  obtain ⟨g, hg', hgd'⟩ := H univ
  have hg : ∀ v, Good v (g v) := fun v => hg' v (mem_univ v)
  have hgd : ∀ v v' : S, v ≠ v' → ∀ (w : Neighbours G v) (w' : Neighbours G v'),
      s(w.1, (g v w).1) ≠ s(w'.1, (g v' w').1) :=
    fun v v' hvv' => hgd' v (mem_univ v) v' (mem_univ v') hvv'
  -- the pairing maps
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
  have hπN : ∀ v ∈ S, ∀ a, G.Adj v a → G.Adj v (π v a) := by
    intro v hv a ha
    rw [hπ v hv a ha]
    exact hmemN v hv _
  have hπinv : ∀ v ∈ S, ∀ a, G.Adj v a → π v (π v a) = a := by
    intro v hv a ha
    rw [hπ v hv a ha, hπ v hv _ (hmemN v hv _)]
    have := (hg ⟨v, hv⟩).1 ⟨a, (G.mem_neighborFinset v a).mpr ha⟩
    simp only [Subtype.coe_eta]
    rw [this]
  have hπadj : ∀ v ∈ S, ∀ a, G.Adj v a → G.Adj a (π v a) := by
    intro v hv a ha
    rw [hπ v hv a ha]
    exact (hg ⟨v, hv⟩).2.2.1 ⟨a, (G.mem_neighborFinset v a).mpr ha⟩
  have hπp : ∀ v ∈ S, ∀ a, G.Adj v a → p (π v a) ≠ p a := by
    intro v hv a ha
    rw [hπ v hv a ha]
    exact (hg ⟨v, hv⟩).2.1 ⟨a, (G.mem_neighborFinset v a).mpr ha⟩
  have hπdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → ∀ a b, G.Adj v a → G.Adj v' b →
      s(a, π v a) ≠ s(b, π v' b) := by
    intro v hv v' hv' hvv a b ha hb
    rw [hπ v hv a ha, hπ v' hv' b hb]
    exact hgd ⟨v, hv⟩ ⟨v', hv'⟩ (fun h => hvv (congrArg Subtype.val h))
      ⟨a, (G.mem_neighborFinset v a).mpr ha⟩ ⟨b, (G.mem_neighborFinset v' b).mpr hb⟩
  obtain ⟨hcl, hdis, hcov, -, hload⟩ := starFamily_spec G S hS π hπN hπinv hπadj hπdisj
  refine ⟨starFamily G S π, hcl, hdis, hcov, hload, fun i => ?_⟩
  -- counting the matched triangles
  let M : (v : S) → Finset (Neighbours G v) := fun v =>
    univ.filter fun w => localLabel p v w = 0 ∧ localLabel p v (g v w) = i.succ
  have hMcard : ∀ v : S, (M v).card = x v i := by
    intro v
    have h := (hg v).2.2.2 0 i.succ
    rw [h]
    have hd := own_class_demands (classLoad p G v (p v)) (G.degree v / 2)
      (fun i => classLoad p G v (partner i (p v))) (x v)
    fin_cases i
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2
  have hsub : (starFamily G S π).filter (SameSide p i) ⊆
      (univ : Finset S).biUnion (fun v =>
        (M v).image (fun w => ({v.1, w.1, π v w.1} : Finset V))) := by
    intro t ht
    obtain ⟨htQ, hside⟩ := mem_filter.mp ht
    simp only [starFamily, mem_biUnion, mem_image] at htQ
    obtain ⟨v, hv, a, ha, rfl⟩ := htQ
    have haN : G.Adj v a := (G.mem_neighborFinset _ _).mp ha
    rw [sameSide_three_iff] at hside
    obtain ⟨h1, h2⟩ := hside
    have h1' := (same_labels i (p v) (p a)).mp h1.symm
    have h2' := (same_labels i (p v) (p (π v a))).mp h2.symm
    have hne := hπp v hv a haN
    refine mem_biUnion.mpr ⟨⟨v, hv⟩, mem_univ _, ?_⟩
    rcases h1' with h1' | h1'
    · -- `a` is the internal neighbour
      have h2'' : p (π v a) = partner i (p v) := by
        rcases h2' with h2' | h2'
        · exact absurd (h2'.trans h1'.symm) hne
        · exact h2'
      refine mem_image.mpr ⟨⟨a, ha⟩, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩
      · rw [localLabel_eq, rootLabels_zero]; exact h1'
      · rw [localLabel_eq, rootLabels_succ]
        rw [← hπ v hv a haN]; exact h2''
      · rfl
    · -- `π v a` is the internal neighbour
      have h2'' : p (π v a) = p v := by
        rcases h2' with h2' | h2'
        · exact h2'
        · exact absurd (h2'.trans h1'.symm) hne
      let b : Neighbours G v := ⟨π v a, (G.mem_neighborFinset _ _).mpr (hπN v hv a haN)⟩
      have hgb : (g ⟨v, hv⟩ b).1 = a := by
        rw [← hπ v hv _ (hπN v hv a haN)]
        exact hπinv v hv a haN
      refine mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩
      · rw [localLabel_eq, rootLabels_zero]; exact h2''
      · rw [localLabel_eq, rootLabels_succ, hgb]; exact h1'
      · change ({v, π v a, π v (π v a)} : Finset V) = {v, a, π v a}
        rw [hπinv v hv a haN]
        ext z
        simp only [mem_insert, mem_singleton]
        tauto
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  apply sum_le_sum
  intro v _
  exact card_image_le.trans (hMcard v).le

end NashWilliams18.C128
