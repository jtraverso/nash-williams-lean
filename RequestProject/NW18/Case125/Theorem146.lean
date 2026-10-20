/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Defs
public import RequestProject.NW18.Case125.Claim1464
public import RequestProject.NW18.Theorem124

@[expose] public section

/-!
# Theorem 14.6 (idealized `F₀`-decomposition) from Theorem 13.16

`theorem_14_6_of_hingeful` applies the authorised hypothesis `h1316 : Theorem1316Statement` to
a two-partitioned host satisfying hypotheses (a), (b) of Theorem 14.6 and proves all premises of
Theorem 13.16 except hingefulness:

* Claim 14.6.1 (`isRegularAlmostPacking_F0`): the constant weighting
  `φ ≡ 2 / ((1 + 4ε₀) n)` of the `F₀`-copies is an `8`-regular `14ε₀`-almost fractional
  `F₀`-packing.  (The paper uses the weight `2 / ((1 + 2ε₀) n)`; with it the load of a cross
  edge can exceed `1` by a factor `(1 + 4ε₀)/(1 + 2ε₀)`, so we use `1 + 4ε₀` instead.)
* Claim 14.6.2 (`isFracDiv_F0_of_isIntDiv`): fractional `F₀`-divisibility follows from integral
  `F₀`-divisibility when every internal degree is at most the cross degree.
* Claim 14.6.3 (`antiEdgeful_F0`): `1/5`-`F₀`-anti-edgefulness.

The remaining premise, Claim 14.6.4 (`(c, 8)`-`F₀`-hingefulness, normalised as
`c n^{i-4}`), is the statement `claim_14_6_4` (proved in `Claim1464.lean`), and `theorem_14_6`
combines both.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)
open PartitionedTriangleAbsorption.F0ParallelObstruction (typeEdgeVec_001 typeEdgeVec_011
  typeDegVec_001 typeDegVec_011 F0_sum F0_filter_mem)

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma degVec_edgeFinset_eq_partDeg (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (v : V) (i : Fin 2) : degVec p G.edgeFinset v i = (partDeg G p v i : ℤ) :=
  PartitionedTriangleAbsorption.TypedLoadCounterexample.degVec_edgeFinset p G v i

omit [Fintype V] [DecidableEq V] in
lemma edgeVec_nonneg {t : ℕ} (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    0 ≤ edgeVec p E i j := by
  unfold edgeVec
  rw [Finset.sum_apply, Finset.sum_apply]
  refine sum_nonneg fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => simp only [pairVec, Sym2.lift_mk]; split_ifs <;> norm_num

/-- **Claim 14.6.2.** Integral `F₀`-divisibility and `IntDeg(v) ≤ CrossDeg(v)` for every vertex
give fractional `F₀`-divisibility. -/
lemma isFracDiv_F0_of_isIntDiv (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (hint : IsIntDiv p F0 G.edgeFinset)
    (hdeg : ∀ v i, i ≠ p v → partDeg G p v (p v) ≤ partDeg G p v i) :
    IsFracDiv p F0 G.edgeFinset := by
  obtain ⟨⟨c, hc⟩, hv⟩ := hint
  have hc1 : 0 ≤ c {0, 0, 1} := by
    have h00 := congrFun (congrFun hc 0) 0
    rw [F0_sum, typeEdgeVec_001, typeEdgeVec_011] at h00
    have := edgeVec_nonneg p G.edgeFinset 0 0
    have h' : edgeVec p G.edgeFinset 0 0 = c {0, 0, 1} * 2 := by simpa using h00
    omega
  have hc2 : 0 ≤ c {0, 1, 1} := by
    have h11 := congrFun (congrFun hc 1) 1
    rw [F0_sum, typeEdgeVec_001, typeEdgeVec_011] at h11
    have := edgeVec_nonneg p G.edgeFinset 1 1
    have h' : edgeVec p G.edgeFinset 1 1 = c {0, 1, 1} * 2 := by simpa using h11
    omega
  refine ⟨⟨fun τ => ((max (c τ) 0 : ℤ) : ℝ), fun τ => by positivity, ?_⟩, fun v => ?_⟩
  · funext i j
    have := congrFun (congrFun hc i) j
    rw [F0_sum] at this ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [max_eq_left hc1, max_eq_left hc2]
    exact_mod_cast this
  · obtain ⟨d, hd⟩ := hv v
    rw [F0_filter_mem, F0_sum] at hd
    have hd0 := congrFun hd 0
    have hd1 := congrFun hd 1
    rw [degVec_edgeFinset_eq_partDeg] at hd0 hd1
    rw [F0_filter_mem]
    rcases Fin.exists_fin_two.mp ⟨p v, rfl⟩ with h | h
    · -- `v` in part `0`
      have hle := hdeg v 1 (by rw [h]; decide)
      rw [h] at hle
      rw [h, typeDegVec_001, typeDegVec_011] at hd0 hd1
      rw [h]
      simp at hd0 hd1
      refine ⟨fun τ => if τ = {0, 0, 1} then (partDeg G p v 0 : ℝ)
        else ((partDeg G p v 1 : ℝ) - partDeg G p v 0) / 2, fun τ => ?_, ?_⟩
      · dsimp (config := { failIfUnchanged := false }) only
        split_ifs
        · positivity
        · have : (partDeg G p v 0 : ℝ) ≤ partDeg G p v 1 := by exact_mod_cast hle
          linarith
      · rw [F0_sum]
        simp only [typeDegVec_001, typeDegVec_011]
        funext i
        fin_cases i
        · simp [degVec_edgeFinset_eq_partDeg]
        · simp [degVec_edgeFinset_eq_partDeg]
    · -- `v` in part `1`
      have hle := hdeg v 0 (by rw [h]; decide)
      rw [h] at hle
      rw [h, typeDegVec_001, typeDegVec_011] at hd0 hd1
      rw [h]
      simp at hd0 hd1
      refine ⟨fun τ => if τ = {0, 0, 1} then ((partDeg G p v 0 : ℝ) - partDeg G p v 1) / 2
        else (partDeg G p v 1 : ℝ), fun τ => ?_, ?_⟩
      · dsimp (config := { failIfUnchanged := false }) only
        split_ifs
        · have : (partDeg G p v 1 : ℝ) ≤ partDeg G p v 0 := by exact_mod_cast hle
          linarith
        · positivity
      · rw [F0_sum]
        simp only [typeDegVec_001, typeDegVec_011]
        funext i
        fin_cases i
        · simp [degVec_edgeFinset_eq_partDeg]
        · simp [degVec_edgeFinset_eq_partDeg]


/-! ### Counting in an idealized host -/

omit [DecidableEq V] in
lemma mem_copies_iff' {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {s : Finset V} : s ∈ copies p F G ↔ IsCopy p F G s := by
  simp only [copies, mem_filter, mem_powersetCard, subset_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h.1.card_eq, h⟩⟩

/-- The `F₀`-copies through an edge `uv` correspond to the common neighbours `w` of `u, v`
such that `u, v, w` are not all in the same part. -/
lemma card_copies_through (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : G.Adj u v) :
    ((copies p F0 G).filter (fun s => s(u, v) ∈ triEdges s)).card =
      (univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ ¬ (p u = p v ∧ p w = p u))).card := by
  symm
  refine card_bij (fun w _ => ({u, v, w} : Finset V)) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨huw, hwv, hty⟩ := hw
    have h1 : u ≠ v := G.ne_of_adj huv
    have h2 : u ≠ w := G.ne_of_adj huw
    have h3 : v ≠ w := (G.ne_of_adj hwv).symm
    refine mem_filter.mpr ⟨mem_copies_iff'.mpr ⟨SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, huw, hwv.symm⟩, ?_⟩, mk_mem_triEdges.mpr ⟨by simp, by simp, h1⟩⟩
    rw [triple_val_map p h1 h2 h3, mem_F0_iff]
    rintro ⟨ha, hb⟩
    exact hty ⟨ha, by rw [← hb, ← ha]⟩
  · intro w hw w' hw' h
    simp only [mem_filter, mem_univ, true_and] at hw hw'
    have h' : ({u, v, w} : Finset V) = {u, v, w'} := h
    have hw_mem : w ∈ ({u, v, w'} : Finset V) := by
      rw [← h']; simp
    simp only [mem_insert, mem_singleton] at hw_mem
    rcases hw_mem with rfl | rfl | rfl
    · exact absurd hw.1 (SimpleGraph.irrefl G)
    · exact absurd hw.2.1 (SimpleGraph.irrefl G)
    · rfl
  · intro s hs
    obtain ⟨hsC, hes⟩ := mem_filter.mp hs
    obtain ⟨hcl, hty⟩ := mem_copies_iff'.mp hsC
    obtain ⟨hus, hvs, huv'⟩ := mk_mem_triEdges.mp hes
    have hsub : ({u, v} : Finset V) ⊆ s := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    have hcard : (s \ {u, v}).card = 1 := by
      rw [card_sdiff_of_subset hsub, hcl.card_eq, card_pair huv']
    obtain ⟨w, hw⟩ := card_eq_one.mp hcard
    have hws : w ∈ s \ {u, v} := by rw [hw]; simp
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hws
    obtain ⟨hws, hwu, hwv⟩ := hws
    have hseq : s = {u, v, w} := by
      ext x
      constructor
      · intro hx
        by_cases hxu : x = u
        · simp [hxu]
        by_cases hxv : x = v
        · simp [hxv]
        have : x ∈ s \ {u, v} := by simp [hx, hxu, hxv]
        rw [hw] at this
        simp at this; simp [this]
      · intro hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    have hadj := hcl.1
    have huw : G.Adj u w := hadj hus hws (Ne.symm hwu)
    have hvw : G.Adj v w := hadj hvs hws (Ne.symm hwv)
    refine ⟨w, ?_, hseq.symm⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨huw, hvw.symm, ?_⟩
    rw [hseq, triple_val_map p huv' (Ne.symm hwu) (Ne.symm hwv), mem_F0_iff] at hty
    rintro ⟨ha, hb⟩
    exact hty ⟨ha, by rw [hb, ha]⟩

/-- Common neighbours of `u, v` in the part `k`. -/
def comNbPart (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (u v : V) (k : Fin 2) :
    Finset V :=
  univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)

lemma card_comNbPart_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (u v : V)
    (k : Fin 2) :
    (partDeg G p u k : ℝ) + partDeg G p v k - (partClass p k).card ≤
      ((comNbPart G p u v k).card : ℝ) := by
  set A := univ.filter (fun w => G.Adj u w ∧ p w = k)
  set B := univ.filter (fun w => G.Adj v w ∧ p w = k)
  have hAB : A ∩ B = comNbPart G p u v k := by
    ext w; simp only [A, B, comNbPart, mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, -⟩; exact ⟨h1, h3.symm, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3.symm, h2⟩
  have hU : A ∪ B ⊆ partClass p k := by
    intro w hw
    simp only [A, B, mem_union, mem_filter, mem_univ, true_and] at hw
    simp only [partClass, mem_filter, mem_univ, true_and]
    rcases hw with h | h <;> exact h.2
  have h1 := card_union_add_card_inter A B
  have h2 := card_le_card hU
  have e1 : (partDeg G p u k : ℝ) = A.card := rfl
  have e2 : (partDeg G p v k : ℝ) = B.card := rfl
  rw [← hAB, e1, e2]
  have h1' : ((A ∪ B).card : ℝ) + (A ∩ B).card = A.card + B.card := by exact_mod_cast h1
  have h2' : ((A ∪ B).card : ℝ) ≤ (partClass p k).card := by exact_mod_cast h2
  linarith

omit [DecidableEq V] in
lemma card_comNbPart_le_left (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (u v : V) (k : Fin 2) : (comNbPart G p u v k).card ≤ partDeg G p u k :=
  card_le_card fun w hw => by
    simp only [comNbPart, mem_filter, mem_univ, true_and] at hw
    simp only [mem_filter, mem_univ, true_and]; exact ⟨hw.1, hw.2.2⟩

omit [DecidableEq V] in
lemma card_comNbPart_le_right (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (u v : V) (k : Fin 2) : (comNbPart G p u v k).card ≤ partDeg G p v k :=
  card_le_card fun w hw => by
    simp only [comNbPart, mem_filter, mem_univ, true_and] at hw
    simp only [mem_filter, mem_univ, true_and]; exact ⟨hw.2.1.symm, hw.2.2⟩

omit [DecidableEq V] in
lemma card_comNbPart_le_class (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (u v : V) (k : Fin 2) : (comNbPart G p u v k).card ≤ (partClass p k).card :=
  card_le_card fun w hw => by
    simp only [comNbPart, mem_filter, mem_univ, true_and] at hw
    simp only [partClass, mem_filter, mem_univ, true_and]; exact hw.2.2

lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by revert i; decide

omit [DecidableEq V] in
lemma card_partClass_add (p : V → Fin 2) :
    (partClass p 0).card + (partClass p 1).card = Fintype.card V := by
  have h : partClass p 1 = univ.filter (fun v => ¬ p v = 0) := by
    ext v; simp only [partClass, mem_filter, mem_univ, true_and]
    rcases fin2_cases (p v) with h | h <;> simp [h]
  rw [h, partClass, card_filter_add_card_filter_not, card_univ]

omit [DecidableEq V] in
lemma card_partClass_le {ε₀ : ℝ} {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 2}
    (h : IsF0Idealized ε₀ G p) (k : Fin 2) :
    ((partClass p k).card : ℝ) ≤ (1 + ε₀) * Fintype.card V / 2 := by
  have hs : ((partClass p 0).card : ℝ) + (partClass p 1).card = Fintype.card V := by
    exact_mod_cast card_partClass_add p
  have h0 := h.1 0
  have h1 := h.1 1
  rcases fin2_cases k with rfl | rfl <;> linarith

omit [DecidableEq V] in
lemma partDeg_ge_of_idealized {ε₀ : ℝ} {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : V → Fin 2} (h : IsF0Idealized ε₀ G p)
    (v : V) (k : Fin 2) : (1 / 4 - ε₀) * Fintype.card V ≤ (partDeg G p v k : ℝ) := by
  by_cases hk : k = p v
  · subst hk; exact (h.2.1 v).1
  · have := h.2.2 v k hk
    nlinarith

/-- **Claim 14.6.3.** An idealized host (`ε₀ ≤ 1/50`) is `1/5`-`F₀`-anti-edgeful. -/
lemma antiEdgeful_F0 {ε₀ : ℝ} (hε : ε₀ ≤ 1 / 50) {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : V → Fin 2} (h : IsF0Idealized ε₀ G p) : AntiEdgeful p F0 G (1 / 5) := by
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  intro τ hτ i j k hτeq u v _ hu hv
  subst hτeq
  rw [mem_F0_iff] at hτ
  have hbound := card_comNbPart_ge G p u v k
  have hcl := card_partClass_le h k
  have hu' := partDeg_ge_of_idealized h u k
  have hv' := partDeg_ge_of_idealized h v k
  have hcross : (1 / 2 - ε₀) * Fintype.card V ≤ (partDeg G p u k : ℝ) ∨
      (1 / 2 - ε₀) * Fintype.card V ≤ (partDeg G p v k : ℝ) := by
    by_cases hku : k = i
    · right; refine h.2.2 v k ?_
      rw [hv]; intro hkj; exact hτ ⟨hku.symm.trans hkj, hkj.symm⟩
    · left; exact h.2.2 u k (by rw [hu]; exact hku)
  have e : ((comNbPart G p u v k).card : ℝ) =
      ((univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)).card : ℝ) := rfl
  rw [← e]
  rcases hcross with hc | hc <;> nlinarith

/-- **Claim 14.6.1.** In an idealized host (`0 ≤ ε₀ ≤ 1/100`, `n > 0`) the constant weighting
`φ ≡ 2 / ((1 + 4ε₀) n)` of the `F₀`-copies is an `8`-regular `ε`-almost fractional
`F₀`-packing for every `ε ≥ 14 ε₀`. -/
lemma isRegularAlmostPacking_F0 {ε₀ ε : ℝ} (hε0 : 0 ≤ ε₀) (hε : ε₀ ≤ 1 / 100)
    (hεε : 14 * ε₀ ≤ ε) {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 2}
    (hn : 0 < Fintype.card V) (h : IsF0Idealized ε₀ G p) :
    IsRegularAlmostPacking p F0 G 8 ε (fun _ => 2 / ((1 + 4 * ε₀) * Fintype.card V)) := by
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : 0 < (1 + 4 * ε₀) * (Fintype.card V : ℝ) := by positivity
  refine ⟨fun s _ => ⟨?_, ?_⟩, fun e he => ?_⟩
  · rw [div_le_div_iff₀ (by positivity) hd]; nlinarith
  · rw [div_le_div_iff₀ hd hn']; nlinarith
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := by simpa using he
  rw [sum_const, card_copies_through p G huv, nsmul_eq_mul]
  set c : ℝ := ((univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧
    ¬ (p u = p v ∧ p w = p u))).card : ℝ) with hc
  suffices hcb : (1 - ε) * ((1 + 4 * ε₀) * Fintype.card V) / 2 ≤ c ∧
      c ≤ (1 + 4 * ε₀) * Fintype.card V / 2 by
    obtain ⟨h1, h2⟩ := hcb
    constructor
    · rw [mul_div_assoc', le_div_iff₀ hd]; linarith
    · rw [mul_div_assoc', div_le_one hd]; linarith
  by_cases hpuv : p u = p v
  · -- internal edge: the third vertex lies in the other part
    obtain ⟨k, hk⟩ : ∃ k, k ≠ p u := ⟨p u + 1, by
      rcases Fin.exists_fin_two.mp ⟨p u, rfl⟩ with h' | h' <;> rw [h'] <;> decide⟩
    have hceq : c = ((comNbPart G p u v k).card : ℝ) := by
      rw [hc]; congr 2; ext w
      simp only [comNbPart, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, ?_⟩
        have : p w ≠ p u := fun h' => h3 ⟨hpuv, h'⟩
        rcases Fin.exists_fin_two.mp ⟨p w, rfl⟩ with h' | h' <;>
          rcases Fin.exists_fin_two.mp ⟨p u, rfl⟩ with h'' | h'' <;>
          rcases Fin.exists_fin_two.mp ⟨k, rfl⟩ with h''' | h''' <;>
          simp_all
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun h' => hk (h3 ▸ h'.2)⟩
    have hlow := card_comNbPart_ge G p u v k
    have hu := h.2.2 u k hk
    have hv := h.2.2 v k (hpuv ▸ hk)
    have hup' : ((comNbPart G p u v k).card : ℝ) ≤ (partClass p k).card := by
      exact_mod_cast card_comNbPart_le_class G p u v k
    have hclk := card_partClass_le h k
    rw [hceq]
    constructor <;> nlinarith
  · -- cross edge: the third vertex may lie in either part
    have hceq : c = ((comNbPart G p u v (p u)).card : ℝ) + (comNbPart G p u v (p v)).card := by
      rw [hc]
      have hdisj : Disjoint (comNbPart G p u v (p u)) (comNbPart G p u v (p v)) :=
        disjoint_filter.mpr fun w _ h1 h2 => hpuv (h1.2.2.symm.trans h2.2.2)
      rw [← Nat.cast_add, ← card_union_of_disjoint hdisj]
      congr 2; ext w
      simp only [comNbPart, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, -⟩
        rcases Fin.exists_fin_two.mp ⟨p w, rfl⟩ with h' | h' <;>
          rcases Fin.exists_fin_two.mp ⟨p u, rfl⟩ with h'' | h'' <;>
          rcases Fin.exists_fin_two.mp ⟨p v, rfl⟩ with h''' | h''' <;>
          simp_all
      · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2, fun h' => hpuv h'.1⟩
    have hl1 := card_comNbPart_ge G p u v (p u)
    have hl2 := card_comNbPart_ge G p u v (p v)
    have hu1 := (h.2.1 u).1
    have hu2 := (h.2.1 u).2
    have hv1 := (h.2.1 v).1
    have hv2 := (h.2.1 v).2
    have hcu := h.2.2 u (p v) (Ne.symm hpuv)
    have hcv := h.2.2 v (p u) hpuv
    have hclu := card_partClass_le h (p u)
    have hclv := card_partClass_le h (p v)
    have hup1 : ((comNbPart G p u v (p u)).card : ℝ) ≤ partDeg G p u (p u) := by
      exact_mod_cast card_comNbPart_le_left G p u v (p u)
    have hup2 : ((comNbPart G p u v (p v)).card : ℝ) ≤ partDeg G p v (p v) := by
      exact_mod_cast card_comNbPart_le_right G p u v (p v)
    rw [hceq]
    constructor <;> nlinarith


/-! ### Theorem 14.6 -/

omit [DecidableEq V] in
lemma IsF0Idealized.mono {ε ε' : ℝ} (hle : ε ≤ ε') {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : V → Fin 2} (h : IsF0Idealized ε G p) : IsF0Idealized ε' G p := by
  have hn' : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  refine ⟨fun i => le_trans (by nlinarith) (h.1 i), fun v => ⟨le_trans (by nlinarith)
    (h.2.1 v).1, le_trans (h.2.1 v).2 (by nlinarith)⟩, fun v i hi =>
    le_trans (by nlinarith) (h.2.2 v i hi)⟩

/-- **Theorem 14.6 from Theorem 13.16, up to hingefulness.**  For every `c > 0` there are
`ε₀ > 0` and `n₀` such that every integrally `F₀`-divisible two-partitioned graph on
`n ≥ n₀` vertices satisfying (a), (b) of Theorem 14.6 for `ε₀` and which is
`(c, 8)`-`F₀`-hingeful (normalised as `c n^{i-4}`) has an `F₀`-decomposition.
Theorem 13.16 is applied (hypothesis `h1316`) with `t = 2`, `F = F₀`, `α = min c (1/5)` and
`C = 8`; its premises are Claims 14.6.1–14.6.3, proved above. -/
theorem theorem_14_6_of_hingeful (h1316 : Theorem1316Statement) :
    ∀ c : ℝ, 0 < c → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V)
        [DecidableRel G.Adj], n₀ ≤ Fintype.card V → IsIntDiv p F0 G.edgeFinset →
        IsF0Idealized ε₀ G p → HingefulN p F0 G c 8 → HasDecomp p F0 G.edgeFinset := by
  intro c hc
  obtain ⟨ε, hε, n₁, h⟩ := h1316 2 F0 (by decide) (min c (1 / 5)) (lt_min hc (by norm_num))
    8 (by norm_num)
  refine ⟨min (ε / 14) (1 / 100), lt_min (by positivity) (by norm_num), max n₁ 1,
    fun V _ _ p G _ hn hint hid hhinge => ?_⟩
  set ε₀ := min (ε / 14) (1 / 100)
  have hε0 : 0 ≤ ε₀ := le_min (by positivity) (by norm_num)
  have hε1 : ε₀ ≤ 1 / 100 := min_le_right _ _
  have hε2 : 14 * ε₀ ≤ ε := by have := min_le_left (ε / 14) (1 / 100); linarith
  have hnpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) hn
  refine h V p G (le_trans (le_max_left _ _) hn) ?_
    ⟨fun _ => 2 / ((1 + 4 * ε₀) * Fintype.card V), ?_⟩ hint ?_ ?_
  · refine isFracDiv_F0_of_isIntDiv G p hint fun v i hi => ?_
    have h1 := (hid.2.1 v).2
    have h2 := hid.2.2 v i hi
    have hn' : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have : (partDeg G p v (p v) : ℝ) ≤ partDeg G p v i := by nlinarith
    exact_mod_cast this
  · have := isRegularAlmostPacking_F0 hε0 hε1 hε2 hnpos hid
    simpa using this
  · exact AntiEdgeful.mono (min_le_right _ _) (antiEdgeful_F0 (by linarith) hid)
  · exact hhinge.mono (min_le_left _ _) le_rfl

/-- **Claim 14.6.4** (`F₀`-hingefulness of an idealized host).  For every `α > 0` there
are `ε₀ > 0`, `c > 0` and `n₀` such that every two-partitioned graph on `n ≥ n₀` vertices
satisfying (a), (b) of Theorem 14.6 for `ε₀`, one of whose parts `V_i` induces a graph that is
not `α`-close to `T₂(|V_i|)` or `T̄₂(|V_i|)` (hypothesis (c)), is `(c, 8)`-`F₀`-hingeful
(normalised as `c n^{i-4}`).

Proved in `Claim1464.lean` (`claim_14_6_4_proof`): `F₀`-hinges on `6` vertices when the shared
edge is a cross edge, and on `8` vertices (from walks in common neighbourhoods, via the
stability lemma for walks of length four, which replaces the paper's Lemma 14.2) otherwise. -/
theorem claim_14_6_4 :
    ∀ α : ℝ, 0 < α → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V)
        [DecidableRel G.Adj], n₀ ≤ Fintype.card V → IsF0Idealized ε₀ G p →
        (∃ i, ¬ IsSideClose α G (partClass p i)) → HingefulN p F0 G c 8 :=
  claim_14_6_4_proof

/-- **Theorem 14.6 as a proposition** (open premise of branch (2), Theorem 12.5): the
idealized `F₀`-decomposition theorem, with the host conditions (a), (b), (c) actually available
in the proof of Theorem 12.5.  Condition (c) (some side is not `α`-close to `T₂` or `T̄₂`)
excludes the hosts built from disjoint cliques inside the sides, for which aggregated
`F₀`-divisibility does not imply membership in the `F₀`-triangle lattice.  It is implied by
`Theorem1316Statement` (`theorem_14_6`).  **Not proved.** -/
def Theorem146Statement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V)
      [DecidableRel G.Adj], n₀ ≤ Fintype.card V → IsIntDiv p F0 G.edgeFinset →
      IsF0Idealized ε₀ G p → (∃ i, ¬ IsSideClose α G (partClass p i)) →
      HasDecomp p F0 G.edgeFinset

/-- **Theorem 14.6 (idealized `F₀`-decomposition theorem).**  For every `α > 0` there is
`ε₀ > 0` such that for all large `n`: every integrally `F₀`-divisible two-partitioned graph on
`n` vertices satisfying (a) `|V_i| ≥ (1 − ε₀) n/2`, (b) `(1/4 − ε₀) n ≤ d_i(v) ≤ (1/4 + ε₀) n`,
`d_{3−i}(v) ≥ (1/2 − ε₀) n` for `v ∈ V_i`, and (c) some `V_i` is not `α`-close to `T₂(|V_i|)`
or `T̄₂(|V_i|)`, has an `F₀`-decomposition.  Proved from `h1316` and Claim 14.6.4. -/
theorem theorem_14_6 (h1316 : Theorem1316Statement) : Theorem146Statement := by
  intro α hα
  obtain ⟨ε₁, hε₁, c, hc, n₁, hhinge⟩ := claim_14_6_4 α hα
  obtain ⟨ε₂, hε₂, n₂, hdec⟩ := theorem_14_6_of_hingeful h1316 c hc
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, max n₁ n₂, fun V _ _ p G _ hn hint hid hside => ?_⟩
  exact hdec V p G (le_trans (le_max_right _ _) hn) hint (hid.mono (min_le_right _ _))
    (hhinge V p G (le_trans (le_max_left _ _) hn) (hid.mono (min_le_left _ _)) hside)

end NashWilliams18
