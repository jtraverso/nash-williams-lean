/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Localization
public import PartitionedTriangleAbsorption.CloneSupply.InternalDegree

/-! # A fresh destination `Q` with prescribed type counts (no common `A`)

Internal-degree supply gives a fresh internal edge `uv` of the doubled part `i`, and
anti-edgefulness gives a fresh centre `w` of the opposite part. Iterating, any prescribed
numbers `n₀, n₁` of vertex-disjoint F0 triangles of types `001` and `011` avoiding a set `W`
exist as soon as `|W| + 3 (n₀ + n₁) < α n` (`exists_fresh_packing`).

For a certified source `P`, choosing `n₀ = e₀₀(P)` and `n₁ = e₁₁(P)` gives a destination `Q`
outside `Z` with the same three part-pair counts as `P` (`exists_fresh_destination`).
This constructs `Q` only; it does **not** construct the common `A`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks CloneSupply

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The F0 type whose doubled part is `i`. -/
def typeOf (i : Fin 2) : Multiset (Fin 2) := if i = 0 then {0, 0, 1} else {0, 1, 1}

theorem typeOf_mem (i : Fin 2) : typeOf i ∈ F0 := by
  unfold typeOf; split_ifs <;> decide

omit [DecidableEq V] in
/-- **One fresh triangle.** If `|W| < α n` there is an F0 copy of type `typeOf i` avoiding `W`. -/
theorem exists_fresh_triangle (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hanti : AntiEdgeful p F0 G α) (hparts : ∀ j : Fin 2, ∃ v, p v = j)
    (i : Fin 2) (W : Finset V) (hW : (W.card : ℝ) < α * Fintype.card V) :
    ∃ s : Finset V, IsCopy p F0 G s ∧ s.val.map p = typeOf i ∧ Disjoint s W := by
  classical
  obtain ⟨j, hji⟩ := exists_other i
  obtain ⟨x, hx⟩ := hparts i
  have hdx := internal_degree_of_parts p G α hanti hparts i x hx
  obtain ⟨u, hu, huW⟩ := exists_mem_notMem_of_card_lt_card
    (s := W) (t := partNbrs p G i x) (by exact_mod_cast hW.trans_le hdx)
  have hpu : p u = i := (mem_partNbrs.mp hu).1
  have hdu := internal_degree_of_parts p G α hanti hparts i u hpu
  obtain ⟨v, hv, hvW⟩ := exists_mem_notMem_of_card_lt_card
    (s := W) (t := partNbrs p G i u) (by exact_mod_cast hW.trans_le hdu)
  obtain ⟨hpv, huv⟩ := mem_partNbrs.mp hv
  have hq := hanti {i, i, j} (iij_mem_F0 i j hji.symm) i i j rfl u v huv.ne hpu hpv
  obtain ⟨w, hw, hwW⟩ := exists_mem_notMem_of_card_lt_card
    (s := W) (t := univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ p w = j)
    (by exact_mod_cast hW.trans_le hq)
  simp only [mem_filter, mem_univ, true_and] at hw
  obtain ⟨huw, hwv, hpw⟩ := hw
  have hab : u ≠ v := huv.ne
  have hac : u ≠ w := huw.ne
  have hbc : v ≠ w := hwv.ne.symm
  refine ⟨{u, v, w}, ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hwv.symm⟩, ?_⟩, ?_, ?_⟩
  · rw [map_three p hab hac hbc, hpu, hpv, hpw]
    exact iij_mem_F0 i j hji.symm
  · rw [map_three p hab hac hbc, hpu, hpv, hpw]
    unfold typeOf
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hji | decide
  · simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨huW, hvW, hwW⟩

/-- Invariant of a fresh packing: F0 copies of `G`, avoiding `W`, pairwise vertex-disjoint. -/
def PackInv (p : V → Fin 2) (G : SimpleGraph V) (W : Finset V) (D : Finset (Finset V)) : Prop :=
  (∀ s ∈ D, IsCopy p F0 G s ∧ Disjoint s W) ∧ (D : Set (Finset V)).PairwiseDisjoint id

/-- Number of members of `D` of part-type `τ`. -/
def typeCount (p : V → Fin 2) (D : Finset (Finset V)) (τ : Multiset (Fin 2)) : ℕ :=
  (D.filter fun s => s.val.map p = τ).card

omit [Fintype V] in
theorem card_biUnion_id_le {p : V → Fin 2} {G : SimpleGraph V} {W : Finset V}
    {D : Finset (Finset V)} (h : PackInv p G W D) : (D.biUnion id).card ≤ 3 * D.card := by
  refine (card_biUnion_le).trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum fun s hs => (h.1 s hs).1.1.card_eq.le

omit [DecidableEq V] in
/-- **Extension step**, iterated `k` times with a fixed type. -/
theorem extend_packing (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hanti : AntiEdgeful p F0 G α) (hparts : ∀ j : Fin 2, ∃ v, p v = j)
    (i : Fin 2) (W : Finset V) (k : ℕ) :
    ∀ D₀ : Finset (Finset V), PackInv p G W D₀ →
      ((W.card : ℝ) + 3 * (D₀.card + k) < α * Fintype.card V) →
      ∃ D : Finset (Finset V), PackInv p G W D ∧ D.card = D₀.card + k ∧
        ∀ τ, typeCount p D τ = typeCount p D₀ τ + if τ = typeOf i then k else 0 := by
  classical
  induction k with
  | zero =>
    intro D₀ h₀ _
    exact ⟨D₀, h₀, rfl, fun τ => by simp⟩
  | succ k ih =>
    intro D₀ h₀ hb
    have hb' : (W.card : ℝ) + 3 * (D₀.card + k) < α * Fintype.card V := by
      push_cast at hb ⊢; linarith
    obtain ⟨D₁, h₁, hc₁, ht₁⟩ := ih D₀ h₀ hb'
    have hU : ((W ∪ D₁.biUnion id).card : ℝ) < α * Fintype.card V := by
      have h1 : (W ∪ D₁.biUnion id).card ≤ W.card + 3 * D₁.card :=
        (card_union_le _ _).trans (by have := card_biUnion_id_le h₁; omega)
      have h2 : ((W ∪ D₁.biUnion id).card : ℝ) ≤ W.card + 3 * D₁.card := by exact_mod_cast h1
      rw [hc₁] at h2
      push_cast at hb h2
      linarith
    obtain ⟨s, hs, hst, hsd⟩ := exists_fresh_triangle p G α hanti hparts i _ hU
    have hsW : Disjoint s W := hsd.mono_right subset_union_left
    have hsD : ∀ u ∈ D₁, Disjoint s u := fun u hu =>
      hsd.mono_right ((subset_biUnion_of_mem id hu).trans subset_union_right)
    have hsnot : s ∉ D₁ := by
      intro hmem
      have := hsD s hmem
      rw [disjoint_self_iff_empty] at this
      have h3 := hs.1.card_eq
      rw [this, card_empty] at h3
      omega
    refine ⟨insert s D₁, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact ⟨hs, hsW⟩
      · exact h₁.1 u hu
    · rw [coe_insert]
      refine h₁.2.insert fun u hu _ => ?_
      exact hsD u hu
    · rw [card_insert_of_notMem hsnot, hc₁]; ring
    · intro τ
      rw [typeCount, filter_insert]
      by_cases hτ : τ = typeOf i
      · subst hτ
        rw [ite_eq_left hst, card_insert_of_notMem (fun h => hsnot (mem_filter.mp h).1)]
        have := ht₁ (typeOf i)
        rw [typeCount] at this
        rw [this, typeCount]; simp; ring
      · rw [ite_eq_right (by rw [hst]; exact Ne.symm hτ)]
        have := ht₁ τ
        rw [typeCount] at this
        rw [this, typeCount]; simp [hτ]

omit [DecidableEq V] in
/-- **Fresh packing with prescribed type counts.** -/
theorem exists_fresh_packing (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hanti : AntiEdgeful p F0 G α) (hparts : ∀ j : Fin 2, ∃ v, p v = j)
    (W : Finset V) (n₀ n₁ : ℕ)
    (hb : (W.card : ℝ) + 3 * (n₀ + n₁) < α * Fintype.card V) :
    ∃ D : Finset (Finset V), PackInv p G W D ∧ D.card = n₀ + n₁ ∧
      typeCount p D {0, 0, 1} = n₀ ∧ typeCount p D {0, 1, 1} = n₁ := by
  classical
  have h0 : PackInv p G W ∅ := ⟨by simp, by simp⟩
  obtain ⟨D₁, h₁, hc₁, ht₁⟩ := extend_packing p G α hanti hparts 0 W n₀ ∅ h0
    (by simp only [card_empty, Nat.cast_zero, zero_add]; linarith)
  obtain ⟨D₂, h₂, hc₂, ht₂⟩ := extend_packing p G α hanti hparts 1 W n₁ D₁ h₁
    (by rw [hc₁]; push_cast at hb ⊢; simp only [card_empty, Nat.cast_zero, zero_add]; linarith)
  refine ⟨D₂, h₂, by rw [hc₂, hc₁]; simp, ?_, ?_⟩
  · rw [ht₂, ht₁]
    simp [typeCount, typeOf]
  · rw [ht₂, ht₁]
    simp [typeCount, typeOf]

omit [Fintype V] in
theorem pairwiseDisjoint_triEdges_of_vertex {D : Finset (Finset V)}
    (h : (D : Set (Finset V)).PairwiseDisjoint id) :
    (D : Set (Finset V)).PairwiseDisjoint triEdges := by
  intro s hs u hu hsu
  rw [Function.onFun, disjoint_left]
  intro e hes heu
  have hd := h hs hu hsu
  induction e using Sym2.ind with
  | _ a b =>
    simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff] at hes heu
    exact disjoint_left.mp hd hes.1.1 heu.1.1

/-- **Fresh destination for a certified source.** For a source with a signed physical
certificate and an excluded set `W ⊇ Z`, under `|W| + |P| < α n` there is an F0-decomposable
`Q ⊆ E(G)`, a vertex-disjoint union of F0 triangles of `G`, with no vertex in `W` and with
the same `00`, `11` and `01` edge counts as `P`. -/
theorem exists_fresh_destination {ι : Type*} [Fintype ι] (p : V → Fin 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (hanti : AntiEdgeful p F0 G α)
    (hparts : ∀ j : Fin 2, ∃ v, p v = j) {P : Finset (Sym2 V)} {t : ι → Finset V}
    {c : ι → ℤ} (hcert : IsSignedCert p G P t c) (W : Finset V)
    (hb : (W.card : ℝ) + P.card < α * Fintype.card V) :
    ∃ (Q : Finset (Sym2 V)) (D : Finset (Finset V)), IsDecomp p F0 Q D ∧
      (D : Set (Finset V)).PairwiseDisjoint id ∧ Q ⊆ G.edgeFinset ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ W) ∧ Q.card = P.card ∧
      pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
      pairCount p Q 0 1 = pairCount p P 0 1 := by
  have hcoarse := coarse_charge_of_cert p G hcert
  have h01 := pairCount01_of_cert p G hcert
  have hcard := card_eq_of_cert p G hcert
  set n₀ := pairCount p P 0 0
  set n₁ := pairCount p P 1 1
  have hsum : ((n₀ + n₁ : ℕ) : ℤ) = ∑ j, c j := by push_cast; linarith
  have hP3 : (P.card : ℤ) = 3 * (n₀ + n₁ : ℕ) := by rw [hcard, hsum]
  obtain ⟨D, hinv, hDc, ht0, ht1⟩ := exists_fresh_packing p G α hanti hparts W n₀ n₁
    (by
      have : (P.card : ℝ) = 3 * ((n₀ : ℝ) + n₁) := by exact_mod_cast hP3
      linarith)
  have htyped : ∀ s ∈ D, IsTypedTri p F0 s := fun s hs =>
    ⟨(hinv.1 s hs).1.1.card_eq, (hinv.1 s hs).1.2⟩
  have hpd := pairwiseDisjoint_triEdges_of_vertex hinv.2
  have hdec : IsDecomp p F0 (D.biUnion triEdges) D := ⟨htyped, hpd, rfl⟩
  -- edge counts of a vertex-disjoint union
  have hpc : ∀ a b : Fin 2, (pairCount p (D.biUnion triEdges) a b : ℤ) =
      ∑ s ∈ D, (pairCount p (triEdges s) a b : ℤ) := by
    intro a b
    rw [pairCount, filter_biUnion, card_biUnion]
    · push_cast; rfl
    · intro s hs u hu hsu
      exact disjoint_filter_filter (hpd hs hu hsu)
  have htc : ∀ τ, ((typeCount p D τ : ℕ) : ℤ) =
      ∑ s ∈ D, (if s.val.map p = τ then 1 else 0 : ℤ) := by
    intro τ
    rw [typeCount, card_filter]; push_cast; rfl
  refine ⟨D.biUnion triEdges, D, hdec, hinv.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    have hcl := (hinv.1 s hs).1.1
    induction e using Sym2.ind with
    | _ a b =>
      have hab := mem_of_mk_mem_triEdges' hes
      have hne : a ≠ b := by
        simp only [triEdges, mem_filter, Sym2.mk_isDiag_iff] at hes
        exact hes.2
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hcl.1 hab.1 hab.2 hne
  · intro e he v hv
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have hab := mem_of_mk_mem_triEdges' hes
      have hsW := (hinv.1 s hs).2
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact disjoint_left.mp hsW hab.1
      · exact disjoint_left.mp hsW hab.2
  · have : ((D.biUnion triEdges).card : ℤ) = 3 * D.card := by
      rw [card_biUnion hpd]; push_cast
      rw [Finset.sum_congr rfl fun s hs =>
        congrArg (fun n : ℕ => (n : ℤ)) (tri_counts p (htyped s hs).1 (htyped s hs).2).2.2.2]
      simp [mul_comm]
    have h2 : ((D.biUnion triEdges).card : ℤ) = P.card := by rw [this, hP3, hDc]
    exact_mod_cast h2
  · have : (pairCount p (D.biUnion triEdges) 0 0 : ℤ) = n₀ := by
      rw [hpc, ← ht0, htc]
      exact Finset.sum_congr rfl fun s hs => (tri_counts p (htyped s hs).1 (htyped s hs).2).1
    exact_mod_cast this
  · have : (pairCount p (D.biUnion triEdges) 1 1 : ℤ) = n₁ := by
      rw [hpc, ← ht1, htc]
      exact Finset.sum_congr rfl fun s hs => (tri_counts p (htyped s hs).1 (htyped s hs).2).2.1
    exact_mod_cast this
  · have : (pairCount p (D.biUnion triEdges) 0 1 : ℤ) = pairCount p P 0 1 := by
      rw [hpc, Finset.sum_congr rfl fun s hs =>
        (tri_counts p (htyped s hs).1 (htyped s hs).2).2.2.1]
      rw [sum_const, nsmul_eq_mul, hDc]; push_cast; linarith
    exact_mod_cast this

end PartitionedTriangleAbsorption.SignedCertificate
