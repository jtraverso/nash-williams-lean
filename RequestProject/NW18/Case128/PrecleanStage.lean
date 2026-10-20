/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case128.GraphOps

/-!
# Case (5): the pre-clean stage with prescribed target classes

For an edge `ac` inside the exceptional set `S`:

* if `a` and `c` lie in different classes (an edge of `O₁`), the third vertex is taken in one
  of the two remaining classes, so the triangle is a copy of `F₃` and consumes no quota
  (Claim 12.8.9);
* if `a` and `c` lie in the same class (an edge of `O₂`), the third vertex is taken in a partner
  class whose pairing index belongs to a prescribed set `C` of "large" indices; Claim 12.8.5
  (`CommonClassSupply`) provides two admissible classes, and `C` misses at most one index
  (Claim 12.8.8(ii)).

Consequently every pre-clean triangle lying on one side of the `i`-th bipartition has `i ∈ C`.
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The pre-clean stage.** -/
theorem stage_preclean (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (C : Fin 3 → Prop) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 1920)
    (hn : 0 < Fintype.card V)
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j)
    (hmin : (3 / 4 : ℝ) * Fintype.card V ≤ G.minDegree)
    (hsize : ∀ j, ((classSet p j).card : ℝ) ≤ (1 / 4 + 8 * ρ) * Fintype.card V)
    (hC : S.Nonempty → ∃ ℓ₀ : Fin 3, ∀ i, i ≠ ℓ₀ → C i)
    (hsmall : 8 * ((S.card : ℝ) + 1) + S.card ≤ Fintype.card V / 20) :
    ∃ D : Finset (Finset V),
      (∀ t ∈ D, G.IsNClique 3 t) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ a ∈ S, ∀ c ∈ S, G.Adj a c → s(a, c) ∈ D.biUnion triEdges) ∧
      DegBounded (D.biUnion triEdges) (4 * S.card + 2) ∧
      (∀ x ∈ S, (D.filter fun t => x ∈ t).card ≤ S.card) ∧
      (∀ t ∈ D, ∀ i, SameSide p i t → C i) ∧
      (∀ t ∈ D, ∃ x ∈ S, x ∈ t) := by
  classical
  have hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v :=
    fun v => hmin.trans (by exact_mod_cast G.minDegree_le_degree v)
  set m := (univ.filter fun w : V => w ∉ S) with hm
  -- the admissibility predicate for a target class
  let P : V → V → Fin 4 → Prop := fun a c l =>
    l ≠ p a ∧ l ≠ p c ∧ (p a = p c → ∃ i, C i ∧ l = partner i (p a)) ∧
      8 * (S.card + 1) ≤
        (univ.filter fun w => w ∉ S ∧ p w = l ∧ G.Adj a w ∧ G.Adj c w).card
  have hPsymm : ∀ a c l, P a c l → P c a l := by
    rintro a c l ⟨h1, h2, h3, h4⟩
    refine ⟨h2, h1, fun h => ?_, ?_⟩
    · obtain ⟨i, hi, hl⟩ := h3 h.symm
      exact ⟨i, hi, h ▸ hl⟩
    · convert h4 using 2
      ext w
      simp only [mem_filter, mem_univ, true_and]
      tauto
  -- turning a real supply bound into the natural-number one
  have hsupply_of : ∀ a c l, (Fintype.card V : ℝ) / 20 ≤
      (univ.filter fun w => p w = l ∧ G.Adj a w ∧ G.Adj c w).card →
      8 * (S.card + 1) ≤
        (univ.filter fun w => w ∉ S ∧ p w = l ∧ G.Adj a w ∧ G.Adj c w).card := by
    intro a c l h
    have h' := common_outside_ge G p S a c l
    have : (8 * (S.card + 1) : ℝ) ≤
        (univ.filter fun w => w ∉ S ∧ p w = l ∧ G.Adj a w ∧ G.Adj c w).card := by
      linarith
    exact_mod_cast this
  have hPex : ∀ a ∈ S, ∀ c ∈ S, G.Adj a c → ∃ l, P a c l := by
    intro a ha c hc hac
    by_cases hpc : p a = p c
    · obtain ⟨ℓ₀, hℓ₀⟩ := hC ⟨a, ha⟩
      have hint : ∀ w, ((internalNeighbours G p w).card : ℝ) ≤
          G.degree w / 4 + 8 * ρ * Fintype.card V := by
        intro w
        rw [internalNeighbours_card]
        have h := four_classLoad_own_le p G hloc w
        have h' : (4 * classLoad p G w (p w) : ℝ) ≤ G.degree w := by exact_mod_cast h
        have : (0 : ℝ) ≤ 8 * ρ * Fintype.card V := by positivity
        linarith
      obtain ⟨j, k, hjk, hj, hk, hjc, hkc⟩ :=
        CommonClassSupply.exists_two_destination_classes G p a c (8 * ρ) hn (by linarith)
          hsize hmin hpc (hint a) (hint c)
      rw [candidates_card_eq] at hjc hkc
      obtain ⟨ij, hij⟩ := exists_partner_eq (p a) j hj
      obtain ⟨ik, hik⟩ := exists_partner_eq (p a) k hk
      have hne : ij ≠ ik := fun h => hjk (by rw [← hij, ← hik, h])
      by_cases hij0 : ij = ℓ₀
      · have hik0 : ik ≠ ℓ₀ := fun h => hne (hij0.trans h.symm)
        refine ⟨k, hk, hpc ▸ hk, fun _ => ⟨ik, hℓ₀ ik hik0, hik.symm⟩, hsupply_of a c k hkc⟩
      · refine ⟨j, hj, hpc ▸ hj, fun _ => ⟨ij, hℓ₀ ij hij0, hij.symm⟩, hsupply_of a c j hjc⟩
    · obtain ⟨l, hla, hlc, hl⟩ := cross_supply G p hloc hdeg a c hpc
      refine ⟨l, hla, hlc, fun h => absurd h hpc, hsupply_of a c l ?_⟩
      have : (Fintype.card V : ℝ) / 20 ≤ Fintype.card V / 16 := by
        have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
        linarith
      linarith
  -- the target classes
  let Good : Sym2 V → Fin 4 → Prop := fun e l =>
    ∀ a c, e = s(a, c) → a ∈ S → c ∈ S → G.Adj a c → P a c l
  let tgt : Sym2 V → Fin 4 := fun e => if h : ∃ l, Good e l then h.choose else 0
  have htgt : ∀ a ∈ S, ∀ c ∈ S, G.Adj a c → P a c (tgt s(a, c)) := by
    intro a ha c hc hac
    obtain ⟨l, hl⟩ := hPex a ha c hc hac
    have hex : ∃ l, Good s(a, c) l := by
      refine ⟨l, fun a' c' he _ _ _ => ?_⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hl
      · exact hPsymm _ _ _ hl
    have := hex.choose_spec
    simp only [tgt, dif_pos hex]
    exact this a c rfl ha hc hac
  obtain ⟨D, hcl, hdis, hstr, hcov, hdeg', hloadS⟩ := exists_typed_preclean G p S tgt
    (fun a ha c hc hac => (htgt a ha c hc hac).2.2.2)
  refine ⟨D, hcl, hdis, hcov, hdeg', hloadS, ?_, ?_⟩
  · intro t ht i hside
    obtain ⟨a, c, w, rfl, ha, hc, -, hpw⟩ := hstr t ht
    have hcl' := hcl _ ht
    rw [SimpleGraph.is3Clique_triple_iff] at hcl'
    obtain ⟨hla, hlc, hsame, -⟩ := htgt a ha c hc hcl'.1
    rw [sameSide_three_iff] at hside
    obtain ⟨h1, h2⟩ := hside
    have h1' := (same_labels i (p a) (p c)).mp h1.symm
    have h2' := (same_labels i (p a) (p w)).mp h2.symm
    rw [hpw] at h2'
    by_cases hpc : p a = p c
    · obtain ⟨i', hi', hl⟩ := hsame hpc
      rcases h2' with h2' | h2'
      · exact absurd h2' hla
      · rw [hl] at h2'
        exact (partner_injective h2') ▸ hi'
    · rcases h1' with h1' | h1'
      · exact absurd h1'.symm hpc
      · rcases h2' with h2' | h2'
        · exact absurd h2' hla
        · exact absurd (h2'.trans h1'.symm) hlc
  · intro t ht
    obtain ⟨a, c, w, rfl, ha, -, -, -⟩ := hstr t ht
    exact ⟨a, ha, by simp⟩

end NashWilliams18.C128
