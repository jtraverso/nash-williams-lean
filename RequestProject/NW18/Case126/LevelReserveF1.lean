/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.VortexSupplyF1
import RequestProject.NW18.Case126.BalanceLedgerF1
import PartitionedTriangleAbsorption.F1PhysicalQueriesStage238

/-!
# One sampled cross reserve with all the statistics of a protected `F₁` level

`level_reserve_exists` samples ONE reserve `R` on the actual boundary graph
`bdEdges H W U` (the edges of `H` between `W \ U` and `U`) by the Stage 238 joint test
(`exists_graph_tests`, at most `30|W|²+2` simultaneous queries).  From that single outcome it
derives:

* every field of `CrossResGood p H W U R ρ (3ε)` (the reserve statistics used by the exact
  weights, the balance ledger, the margins, the overlaps and the apex supply);
* the reserve degree `Δ(R) ≤ (ρ + ε)|W|`;
* the sampled BAD-SET bound used for the density defect of the cross neighbourhoods: for all
  `x, v ∈ W` and every class `c`, the reserved neighbours `z` of `x` in `U_c` with `z ∈ U'` or
  `zv ∉ E(H)` are at most `ρ(|U'| + |{z ∈ U_c : zv ∉ E(H)}|) + ε|W|`.

The threshold `N` depends only on `ε`.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.F1PhysicalQueriesStage238 (queryIndices queryVertices
  exists_graph_tests uniform_threshold sampled_bad_upper unreserved_pair_error)
open scoped NNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Membership in the boundary graph. -/
theorem mem_bdEdges_mk (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V) (a b : V) :
    s(a, b) ∈ bdEdges H W U ↔
      H.Adj a b ∧ ((a ∈ W ∧ a ∉ U ∧ b ∈ U) ∨ (b ∈ W ∧ b ∉ U ∧ a ∈ U)) := by
  simp only [bdEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_sdiff]
  constructor
  · rintro ⟨hab, x, ⟨hxW, hxU⟩, z, hz, he⟩
    refine ⟨hab, ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hxW, hxU, hz⟩
    · exact Or.inr ⟨hxW, hxU, hz⟩
  · rintro ⟨hab, (⟨haW, haU, hb⟩ | ⟨hbW, hbU, ha⟩)⟩
    · exact ⟨hab, a, ⟨haW, haU⟩, b, hb, rfl⟩
    · exact ⟨hab, b, ⟨hbW, hbU⟩, a, ha, Sym2.eq_swap⟩

theorem bdEdges_support (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V) (hUW : U ⊆ W) :
    ∀ e ∈ bdEdges H W U, ∀ v ∈ e, v ∈ W := by
  intro e he v hv
  obtain ⟨-, x, hx, z, hz, rfl⟩ := mem_filter.mp he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact (mem_sdiff.mp hx).1
  · exact hUW hz

set_option maxHeartbeats 1600000 in
/-- **The single sampled reserve of a protected level** (producer, proved). -/
theorem level_reserve_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (H : SimpleGraph V) [DecidableRel H.Adj] (W U U' : Finset V) (ρ : ℝ),
      U ⊆ W → 0 ≤ ρ → ρ ≤ 1 → N ≤ W.card →
      ∃ R : Finset (Sym2 V), R ⊆ bdEdges H W U ∧ CrossResGood p H W U R ρ (3 * ε) ∧
        (∀ x, ((R.filter fun e => x ∈ e).card : ℝ) ≤ (ρ + ε) * W.card) ∧
        (∀ x ∈ W, ∀ v ∈ W, ∀ c : Fin 4,
          ((U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(x, z) ∈ R).card : ℝ) ≤
            ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ H.Adj v z).card) + ε * W.card) := by
  obtain ⟨N, hN0, hN⟩ := uniform_threshold ε hε
  refine ⟨N, hN0, ?_⟩
  intro V _ _ p H _ W U U' ρ hUW hρ0 hρ1 hNW
  set host := bdEdges H W U with hhost
  have hW : 0 < W.card := lt_of_lt_of_le hN0 hNW
  have hsize : (host.card : ℝ) ≤ (W.card : ℝ) ^ 2 := by
    exact_mod_cast F1GraphReserveStage234.supported_card_le W host
      (bdEdges_support H W U hUW)
  obtain ⟨R, hRh, hq, -⟩ := exists_graph_tests H p W U U' hUW host (filter_subset _ _) hsize
    (fun _ => ∅) (fun _ => empty_subset _) ⟨ρ, hρ0⟩ (by exact_mod_cast hρ1) ε hε hW
    (hN W.card hNW)
  set n : ℝ := (W.card : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hW
  have hεn : 0 ≤ ε * n := by positivity
  have hmemh : ∀ a b, s(a, b) ∈ host ↔
      H.Adj a b ∧ ((a ∈ W ∧ a ∉ U ∧ b ∈ U) ∨ (b ∈ W ∧ b ∉ U ∧ a ∈ U)) :=
    mem_bdEdges_mk H W U
  have hRm : ∀ a b, s(a, b) ∈ R → s(a, b) ∈ host := fun a b h => hRh h
  have hidx : ∀ (m : Fin 6) (x v : V) (o : Option (Fin 4)), x ∈ W → v ∈ W →
      (m = 3 → x ≠ v) → (m, x, v, o) ∈ queryIndices W := by
    intro m x v o hx hv hm
    simp only [queryIndices, mem_filter, mem_product, mem_univ, and_true, true_and]
    exact ⟨⟨hx, hv⟩, hm⟩
  -- generic shape of one query
  have hQ : ∀ (m : Fin 6) (x v : V) (o : Option (Fin 4)), x ∈ W → v ∈ W → (m = 3 → x ≠ v) →
      |(((queryVertices H p W U U' host (m, x, v, o)).filter fun z => s(x, z) ∈ R ∧
          (m = 3 → s(v, z) ∈ R)).card : ℝ) -
        ρ ^ (if m = 3 then 2 else 1) * (queryVertices H p W U U' host (m, x, v, o)).card| <
        ε * n := fun m x v o hx hv hm => hq _ (hidx m x v o hx hv hm)
  -- mode 1 : child targets
  have hmode1 : ∀ x ∈ W, x ∉ U → ∀ c : Fin 4,
      |((U.filter fun z => p z = c ∧ H.Adj x z ∧ s(x, z) ∈ R).card : ℝ) -
        ρ * (U.filter fun z => p z = c ∧ H.Adj x z).card| < ε * n := by
    intro x hx hxU c
    have h := hQ 1 x x (some c) hx hx (fun h => absurd h (by decide))
    have hY : queryVertices H p W U U' host (1, x, x, some c) =
        U.filter fun z => p z = c ∧ H.Adj x z := by
      ext z
      simp [queryVertices, hmemh]
      aesop
    have hF : (queryVertices H p W U U' host (1, x, x, some c)).filter
        (fun z => s(x, z) ∈ R ∧ ((1 : Fin 6) = 3 → s(x, z) ∈ R)) =
        U.filter fun z => p z = c ∧ H.Adj x z ∧ s(x, z) ∈ R := by
      rw [hY]; ext z; simp only [mem_filter]
      constructor
      · rintro ⟨⟨hz, hc, ha⟩, hr, -⟩; exact ⟨hz, hc, ha, hr⟩
      · rintro ⟨hz, hc, ha, hr⟩; exact ⟨⟨hz, hc, ha⟩, hr, fun _ => hr⟩
    rw [hF, hY] at h
    simpa using h
  -- mode 0 : full degree
  have hmode0 : ∀ x ∈ W,
      |(((W.filter fun z => s(x, z) ∈ host).filter fun z => s(x, z) ∈ R).card : ℝ) -
        ρ * (W.filter fun z => s(x, z) ∈ host).card| < ε * n := by
    intro x hx
    have h := hQ 0 x x none hx hx (fun h => absurd h (by decide))
    have hY : queryVertices H p W U U' host (0, x, x, none) = W.filter fun z => s(x, z) ∈ host := by
      ext z; simp [queryVertices]
    have hF : (queryVertices H p W U U' host (0, x, x, none)).filter
        (fun z => s(x, z) ∈ R ∧ ((0 : Fin 6) = 3 → s(x, z) ∈ R)) =
        (W.filter fun z => s(x, z) ∈ host).filter fun z => s(x, z) ∈ R := by
      rw [hY]; ext z; simp
    rw [hF, hY] at h
    simpa using h
  -- mode 3 : both reserved
  have hmode3 : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → a ∉ U → b ∉ U → ∀ l : Fin 4,
      |((U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R ∧ s(b, z) ∈ R).card
          : ℝ) - ρ ^ 2 * (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| < ε * n := by
    intro a ha b hb hab haU hbU l
    have h := hQ 3 a b (some l) ha hb (fun _ => hab)
    have hY : queryVertices H p W U U' host (3, a, b, some l) =
        U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z := by
      ext z
      simp [queryVertices, hmemh]
      aesop
    have hF : (queryVertices H p W U U' host (3, a, b, some l)).filter
        (fun z => s(a, z) ∈ R ∧ ((3 : Fin 6) = 3 → s(b, z) ∈ R)) =
        U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R ∧ s(b, z) ∈ R := by
      rw [hY]; ext z; simp only [mem_filter]
      constructor
      · rintro ⟨⟨hz, hc, h1, h2⟩, hr, hr'⟩; exact ⟨hz, hc, h1, h2, hr, by simpa using hr'⟩
      · rintro ⟨hz, hc, h1, h2, hr, hr'⟩; exact ⟨⟨hz, hc, h1, h2⟩, hr, fun _ => hr'⟩
    rw [hF, hY] at h
    simpa using h
  -- mode 5 : one reserved edge of a common neighbourhood
  have hmode5 : ∀ a ∈ W, ∀ b ∈ W, a ∉ U → b ∉ U → ∀ l : Fin 4,
      |((U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R).card : ℝ) -
        ρ * (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| < ε * n := by
    intro a ha b hb haU hbU l
    have h := hQ 5 a b (some l) ha hb (fun h => absurd h (by decide))
    have hY : queryVertices H p W U U' host (5, a, b, some l) =
        U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z := by
      ext z
      simp only [queryVertices, mem_filter, hmemh, Fin.reduceEq, if_false, if_true,
        false_implies, true_implies, and_true, true_and, reduceCtorEq, false_or, Option.some.injEq]
      constructor
      · rintro ⟨hz, hc, ⟨h1, -⟩, ⟨h2, -⟩⟩
        exact ⟨hz, hc.symm, h1, h2⟩
      · rintro ⟨hz, hc, h1, h2⟩
        exact ⟨hz, hc.symm, ⟨h1, Or.inl ⟨ha, haU, hz⟩⟩, ⟨h2, Or.inl ⟨hb, hbU, hz⟩⟩⟩
    have hF : (queryVertices H p W U U' host (5, a, b, some l)).filter
        (fun z => s(a, z) ∈ R ∧ ((5 : Fin 6) = 3 → s(b, z) ∈ R)) =
        U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R := by
      rw [hY]; ext z; simp only [mem_filter]
      constructor
      · rintro ⟨⟨hz, hc, h1, h2⟩, hr, -⟩; exact ⟨hz, hc, h1, h2, hr⟩
      · rintro ⟨hz, hc, h1, h2, hr⟩; exact ⟨⟨hz, hc, h1, h2⟩, hr, by simp⟩
    rw [hF, hY] at h
    simpa using h
  -- mode 4 : outer common neighbours of a root and a child vertex
  have hmode4 : ∀ a ∈ W, ∀ b ∈ U, a ∉ U → ∀ l : Fin 4,
      |((((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).filter
          fun z => s(b, z) ∈ R).card : ℝ) -
        ρ * ((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| < ε * n := by
    intro a ha b hb haU l
    have h := hQ 4 b a (some l) (hUW hb) ha (fun h => absurd h (by decide))
    have hY : queryVertices H p W U U' host (4, b, a, some l) =
        (W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z := by
      ext z
      simp only [queryVertices, mem_filter, hmemh, Fin.reduceEq, if_false, if_true,
        false_implies, true_implies, and_true, true_and, reduceCtorEq, false_or, Option.some.injEq,
        mem_sdiff]
      constructor
      · rintro ⟨hz, hc, ⟨h1, h1'⟩, h2⟩
        refine ⟨hz, hc.symm, h2, h1⟩
      · rintro ⟨hz, hc, h1, h2⟩
        exact ⟨hz, hc.symm, ⟨h2, Or.inr ⟨hz.1, hz.2, hb⟩⟩, h1⟩
    have hF : (queryVertices H p W U U' host (4, b, a, some l)).filter
        (fun z => s(b, z) ∈ R ∧ ((4 : Fin 6) = 3 → s(a, z) ∈ R)) =
        ((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).filter
          fun z => s(b, z) ∈ R := by
      rw [hY]; ext z; simp
    rw [hF, hY] at h
    simpa using h
  refine ⟨R, hRh, ?_, ?_, ?_⟩
  · refine
      { sub := fun e he => (mem_filter.mp (hRh he)).1
        cross := fun e he => by
          obtain ⟨-, x, hx, z, hz, rfl⟩ := mem_filter.mp (hRh he)
          exact ⟨x, hx, z, hz, rfl⟩
        out := fun x z hx hz hR => by
          have := (hmemh x z).mp (hRm x z hR)
          rcases this.2 with h | h
          · exact hz h.2.2
          · exact hx h.2.2
        r1 := ?_
        r2 := ?_
        r3 := ?_
        r4 := ?_
        r5 := ?_ }
    · intro a ha b hb hab haU hbU l
      set Y := U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z with hYdef
      set A := univ.filter fun z => s(a, z) ∈ R
      set B := univ.filter fun z => s(b, z) ∈ R
      have hYA : Y ∩ A = U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R := by
        ext z; simp [Y, A, and_assoc]
      have hYB : Y ∩ B = U.filter fun z => p z = l ∧ H.Adj b z ∧ H.Adj a z ∧ s(b, z) ∈ R := by
        ext z; simp only [Y, B, mem_inter, mem_filter, mem_univ, true_and]; tauto
      have hYAB : Y ∩ A ∩ B =
          U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R ∧ s(b, z) ∈ R := by
        ext z; simp [Y, A, B, and_assoc]
      have hYc : Y \ (A ∪ B) = U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧
          s(a, z) ∉ R ∧ s(b, z) ∉ R := by
        ext z; simp [Y, A, B, and_assoc]
      have hYb : Y = U.filter fun z => p z = l ∧ H.Adj b z ∧ H.Adj a z := by
        ext z; simp only [Y, mem_filter]; tauto
      have h1 := hmode5 a ha b hb haU hbU l
      have h2 := hmode5 b hb a ha hbU haU l
      have h3 := hmode3 a ha b hb hab haU hbU l
      rw [← hYA] at h1
      rw [← hYB, ← hYb] at h2
      rw [← hYAB] at h3
      have := unreserved_pair_error Y A B ρ (ε * n) (ε * n) (ε * n) h1.le h2.le h3.le
      rw [hYc] at this
      linarith
    · intro a ha b hb haU l
      have h := hmode4 a ha b hb haU l
      set Y := (W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z
      have hsplit := card_filter_add_card_filter_not (s := Y) (fun z => s(b, z) ∈ R)
      have hT : (Y.filter fun z => ¬ s(b, z) ∈ R) =
          (W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(b, z) ∉ R := by
        ext z; simp [Y, and_assoc]
      rw [← hT]
      have hs : ((Y.filter fun z => s(b, z) ∈ R).card : ℝ) +
          (Y.filter fun z => ¬ s(b, z) ∈ R).card = Y.card := by exact_mod_cast hsplit
      rw [abs_le]
      constructor <;> nlinarith [abs_lt.mp h]
    · intro a ha b hb hab haU hbU l
      have h := hmode3 a ha b hb hab haU hbU l
      linarith [h.le]
    · intro x hx hxU c
      have h := hmode1 x hx hxU c
      refine h.le.trans ?_
      rw [hn]
      have : 0 ≤ ε * (W.card : ℝ) := by positivity
      linarith
    · intro v hv
      have hvW := hUW hv
      have h := hmode0 v hvW
      have hY : (W.filter fun z => s(v, z) ∈ host) = (W \ U).filter fun z => H.Adj v z := by
        ext z
        simp only [mem_filter, hmemh, mem_sdiff]
        constructor
        · rintro ⟨hz, hadj, h | h⟩
          · exact absurd hv h.2.1
          · exact ⟨⟨hz, h.2.1⟩, hadj⟩
        · rintro ⟨⟨hz, hzU⟩, hadj⟩; exact ⟨hz, hadj, Or.inr ⟨hz, hzU, hv⟩⟩
      have hF : ((W.filter fun z => s(v, z) ∈ host).filter fun z => s(v, z) ∈ R) =
          (W \ U).filter fun z => H.Adj v z ∧ s(v, z) ∈ R := by
        rw [hY]; ext z; simp [and_assoc]
      rw [hF, hY] at h
      linarith [h.le]
  · intro x
    by_cases hx : x ∈ W
    · have h := hmode0 x hx
      have hdeg : (R.filter fun e => x ∈ e).card =
          ((W.filter fun z => s(x, z) ∈ host).filter fun z => s(x, z) ∈ R).card := by
        have hd := deg_eq_card_nbrs R x
        unfold SpreadGen.deg at hd
        rw [hd]
        congr 1
        ext z
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro hz
          exact ⟨⟨bdEdges_support H W U hUW _ (hRh hz) z (Sym2.mem_mk_right _ _), hRh hz⟩, hz⟩
        · intro hz; exact hz.2
      have hY : ((W.filter fun z => s(x, z) ∈ host).card : ℝ) ≤ n := by
        rw [hn]; exact_mod_cast card_filter_le _ _
      rw [hdeg]
      have := (abs_lt.mp h).2
      nlinarith
    · have he : R.filter (fun e => x ∈ e) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro e he hxe
        exact hx (bdEdges_support H W U hUW e (hRh he) x hxe)
      rw [he, card_empty, Nat.cast_zero]
      have : 0 ≤ ρ + ε := by linarith
      positivity
  · intro x hx v hv c
    have h := (hQ 2 x v (some c) hx hv (fun h => absurd h (by decide))).le
    have hF : (queryVertices H p W U U' host (2, x, v, some c)).filter
        (fun z => s(x, z) ∈ R ∧ ((2 : Fin 6) = 3 → s(v, z) ∈ R)) =
        (queryVertices H p W U U' host (2, x, v, some c)).filter (fun z => s(x, z) ∈ R) := by
      ext z; simp
    rw [hF] at h
    exact sampled_bad_upper H p W U U' host R hRh x v c ρ (ε * n) hρ0 (by simpa using h)

end NashWilliams18.SpreadF1
