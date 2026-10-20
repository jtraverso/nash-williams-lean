/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostCycles
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.TokenLayer

/-! # Physical charge tokens in the complete four-class host

A token is one rectangle (plus tokens) or the union of two rectangles (minus tokens) of
prescribed kinds, so that its charge is `±4` for the corrected charge `χ` and `0` for the
preserved charge `χ'`:

* first layer (`χ = chi3a`, `χ' = chi3b`): plus = kind 2, minus = kinds 1 and 3;
* second layer (`χ = chi3b`, `χ' = chi3a`): plus = kind 3, minus = kinds 1 and 2.

`host_tokens` realizes every finite set of token identities by pairwise edge-disjoint physical
tokens avoiding a sparse edge set `B`, with the total token incidence at every vertex at most
`r + 2q`; this is exactly a `TokReal` supply for `token_layer`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection TypedApplicationLinks TypedRefinerCharge RefinerF0

variable {V : Type*}

theorem pathEdges_charge [DecidableEq V] {t : ℕ} (χ : Fin t → Fin t → ℤ) (p : V → Fin t) {a b x : V}
    (hab : a ≠ b) : charge χ p (pathEdges a b x) =
      (χ (p a) (p x) + χ (p x) (p a)) + (χ (p b) (p x) + χ (p x) (p b)) := by
  have hne : s(a, x) ≠ s(b, x) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hab h1
    · exact hab (h1.trans h2)
  rw [charge_eq_sum, pathEdges, sum_pair hne, pair_pairVec, pair_pairVec]

/-- The four vertices of a typed rectangle are pairwise distinct. -/
structure RectOK (cls : V → Fin 4) (ρ : Fin 4) (a b x y : V) : Prop where
  ρne : ρ ≠ 0
  ca : cls a = 0
  cb : cls b = ρ
  cx : cls x = mid ρ false
  cy : cls y = mid ρ true

namespace RectOK

variable {cls : V → Fin 4} {ρ : Fin 4} {a b x y : V} (h : RectOK cls ρ a b x y)
include h

theorem ab : a ≠ b := fun e => h.ρne (by rw [← h.cb, ← e, h.ca])
theorem ax : a ≠ x := fun e => (mid_spec ρ h.ρne false).1 (by rw [← h.cx, ← e, h.ca])
theorem ay : a ≠ y := fun e => (mid_spec ρ h.ρne true).1 (by rw [← h.cy, ← e, h.ca])
theorem bx : b ≠ x := fun e => (mid_spec ρ h.ρne false).2.1 (by rw [← h.cx, ← e, h.cb])
theorem bY : b ≠ y := fun e => (mid_spec ρ h.ρne true).2.1 (by rw [← h.cy, ← e, h.cb])
theorem xy : x ≠ y := fun e => (mid_spec ρ h.ρne false).2.2 (by rw [← h.cx, ← h.cy, e])

omit h

variable [DecidableEq V]
include h

theorem disjoint_paths : Disjoint (pathEdges a b x) (pathEdges a b y) := by
  have d1 := h.ab; have d2 := h.ax; have d3 := h.ay
  have d4 := h.bx; have d5 := h.bY; have d6 := h.xy
  rw [disjoint_left]
  intro e he he'
  simp only [pathEdges, mem_insert, mem_singleton] at he he'
  rcases he with rfl | rfl <;> rcases he' with h' | h' <;>
    rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind

theorem charge_rect (χ : Fin 4 → Fin 4 → ℤ) : charge χ cls (rect a b x y) = c4charge χ ρ := by
  rw [rect, charge_union _ _ h.disjoint_paths, pathEdges_charge _ _ h.ab,
    pathEdges_charge _ _ h.ab, h.ca, h.cb, h.cx, h.cy, c4charge]
  ring

theorem even_rect (z : V) : Even (incidentLoad (rect a b x y) z) := by
  rw [rect, OnePart.incidentLoad_union h.disjoint_paths,
    incidentLoad_pathEdges h.ab h.ax h.bx, incidentLoad_pathEdges h.ab h.ay h.bY]
  exact ⟨(if a = z then 1 else 0) + (if b = z then 1 else 0) + (if x = z then 1 else 0) +
    (if y = z then 1 else 0), by ring⟩

theorem loop_rect : ∀ e ∈ rect a b x y, ¬ e.IsDiag := by
  intro e he
  simp only [rect, pathEdges, mem_union, mem_insert, mem_singleton] at he
  rcases he with (rfl | rfl) | (rfl | rfl) <;> simp [h.ax, h.bx, h.ay, h.bY]

end RectOK

theorem card_rect_le [DecidableEq V] (a b x y : V) : (rect a b x y).card ≤ 4 :=
  (card_union_le _ _).trans (Nat.add_le_add card_le_two card_le_two)

theorem incidentLoad_biUnion_eq [DecidableEq V] {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 V))
    (hdis : (s : Set ι).PairwiseDisjoint E) (w : V) :
    ∑ i ∈ s, incidentLoad (E i) w = incidentLoad (s.biUnion E) w := by
  unfold incidentLoad
  rw [filter_biUnion, card_biUnion]
  intro i hi j hj hij
  exact disjoint_filter_filter (hdis hi hj hij)

/-- **Physical tokens.** -/
theorem host_tokens [Fintype V] [DecidableEq V] (cls : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (γ : ℝ) (hanti : AntiEdgeful cls F3 G γ)
    (hpos : ∀ i, 0 < (classSet cls i).card)
    (B : Finset (Sym2 V)) (d : ℝ) (hB : DegBounded B d) {κ : Type*}
    (S : Finset (Tok κ)) (kP kM1 kM2 : Fin 4) (hkP : kP ≠ 0) (hkM1 : kM1 ≠ 0) (hkM2 : kM2 ≠ 0)
    (χ χ' : Fin 4 → Fin 4 → ℤ) (hP : c4charge χ kP = 4)
    (hM : c4charge χ kM1 + c4charge χ kM2 = -4) (hP' : c4charge χ' kP = 0)
    (hM' : c4charge χ' kM1 + c4charge χ' kM2 = 0) (q r : ℕ) (hq : 0 < q)
    (hr : ∀ i, 4 * (2 * S.card / (classSet cls i).card + 1) ≤ r)
    (hbudget : (4 * S.card : ℝ) / q + 2 * (d + r + 2 * q) < γ * Fintype.card V) :
    ∃ tokE : Tok κ → Finset (Sym2 V), TokReal χ χ' cls 4 8 B S tokE ∧
      (∀ τ ∈ S, tokE τ ⊆ G.edgeFinset) ∧
      (∀ v, ∑ τ ∈ S, incidentLoad (tokE τ) v ≤ r + 2 * q) := by
  classical
  set K := 2 * S.card with hK
  let signAt : ℕ → Prop := fun k => ∃ τ ∈ S, UniversalRefiner.pos S τ = k / 2 ∧ τ.sign = true
  let ρ : ℕ → Fin 4 := fun k => if signAt k then kP else if k % 2 = 0 then kM1 else kM2
  have hρ : ∀ k, ρ k ≠ 0 := by
    intro k
    simp only [ρ]
    split_ifs
    · exact hkP
    · exact hkM1
    · exact hkM2
  obtain ⟨a, b, x, y, hab, hxy, hG', hBd, hdis, hload⟩ := exists_rectangles cls G γ hanti hpos
    B d hB K ρ hρ q r hq hr (by
      have e : (2 * ((2 * S.card : ℕ) : ℝ)) / q = 4 * S.card / q := by push_cast; ring
      rw [hK, e]; exact hbudget)
  have hok : ∀ k < K, RectOK cls (ρ k) (a k) (b k) (x k) (y k) := fun k hk =>
    ⟨hρ k, (hab k).1, (hab k).2, (hxy k hk).1, (hxy k hk).2⟩
  set R : ℕ → Finset (Sym2 V) := fun k => rect (a k) (b k) (x k) (y k) with hR
  have hsignAt : ∀ τ ∈ S, ∀ e < 2, (signAt (2 * UniversalRefiner.pos S τ + e) ↔ τ.sign = true) := by
    intro τ hτ e he
    have hdiv : (2 * UniversalRefiner.pos S τ + e) / 2 = UniversalRefiner.pos S τ := by omega
    simp only [signAt, hdiv]
    constructor
    · rintro ⟨τ', hτ', hpos', hs⟩
      rw [UniversalRefiner.pos_inj hτ' hτ hpos'] at hs
      exact hs
    · intro hs
      exact ⟨τ, hτ, rfl, hs⟩
  have hlt : ∀ τ ∈ S, ∀ e < 2, 2 * UniversalRefiner.pos S τ + e < K := by
    intro τ hτ e he
    have := UniversalRefiner.pos_lt hτ
    omega
  let ids : Tok κ → Finset ℕ := fun τ =>
    if τ.sign then {2 * UniversalRefiner.pos S τ}
    else {2 * UniversalRefiner.pos S τ, 2 * UniversalRefiner.pos S τ + 1}
  let tokE : Tok κ → Finset (Sym2 V) := fun τ => (ids τ).biUnion R
  have hids : ∀ τ ∈ S, ids τ ⊆ range K := by
    intro τ hτ k hk
    simp only [ids] at hk
    split_ifs at hk
    · rw [mem_singleton.mp hk]; exact mem_range.mpr (by simpa using hlt τ hτ 0 (by norm_num))
    · rcases mem_insert.mp hk with rfl | hk
      · exact mem_range.mpr (by simpa using hlt τ hτ 0 (by norm_num))
      · rw [mem_singleton.mp hk]; exact mem_range.mpr (hlt τ hτ 1 (by norm_num))
  have hidsdis : (S : Set (Tok κ)).PairwiseDisjoint ids := by
    intro τ hτ τ' hτ' hne
    rw [Function.onFun, disjoint_left]
    intro k hk hk'
    have h1 : k / 2 = UniversalRefiner.pos S τ := by
      simp only [ids] at hk; split_ifs at hk <;> simp at hk <;> omega
    have h2 : k / 2 = UniversalRefiner.pos S τ' := by
      simp only [ids] at hk'; split_ifs at hk' <;> simp at hk' <;> omega
    exact hne (UniversalRefiner.pos_inj hτ hτ' (h1.symm.trans h2))
  have hRdis : ((range K : Finset ℕ) : Set ℕ).PairwiseDisjoint R := hdis
  have hRsub : ∀ τ ∈ S, (ids τ : Set ℕ) ⊆ range K := fun τ hτ => by
    intro k hk; exact hids τ hτ hk
  -- charge of a token
  have hchgTok : ∀ τ ∈ S, ∀ χ0 : Fin 4 → Fin 4 → ℤ, charge χ0 cls (tokE τ) =
      if τ.sign then c4charge χ0 kP else c4charge χ0 kM1 + c4charge χ0 kM2 := by
    intro τ hτ χ0
    have h0 := hlt τ hτ 0 (by norm_num)
    have h1 := hlt τ hτ 1 (by norm_num)
    rw [add_zero] at h0
    have hs0 := hsignAt τ hτ 0 (by norm_num)
    have hs1 := hsignAt τ hτ 1 (by norm_num)
    rw [add_zero] at hs0
    simp only [tokE]
    rw [charge_biUnion _ _ _ _ (hRdis.subset (hRsub τ hτ))]
    simp only [ids]
    by_cases hsg : τ.sign = true
    · rw [ite_eq_left hsg, ite_eq_left hsg, sum_singleton, hR]
      beta_reduce
      rw [(hok _ h0).charge_rect χ0]
      simp only [ρ, ite_eq_left (hs0.mpr hsg)]
    · rw [ite_eq_right hsg, ite_eq_right hsg, sum_pair (by omega), hR]
      beta_reduce
      rw [(hok _ h0).charge_rect χ0, (hok _ h1).charge_rect χ0]
      have hn0 : ¬ signAt (2 * UniversalRefiner.pos S τ) := fun h => hsg (hs0.mp h)
      have hn1 : ¬ signAt (2 * UniversalRefiner.pos S τ + 1) := fun h => hsg (hs1.mp h)
      simp only [ρ, ite_eq_right hn0, ite_eq_right hn1]
      rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  refine ⟨tokE, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro τ hτ τ' hτ' hne
    simp only [Function.onFun, tokE]
    rw [disjoint_biUnion_left]
    intro k hk
    rw [disjoint_biUnion_right]
    intro k' hk'
    refine hRdis (hRsub τ hτ hk) (hRsub τ' hτ' hk') ?_
    rintro rfl
    exact disjoint_left.mp (hidsdis hτ hτ' hne) hk hk'
  · intro τ hτ
    simp only [tokE]
    rw [disjoint_biUnion_left]
    intro k hk
    exact hBd k (mem_range.mp (hids τ hτ hk))
  · intro τ hτ e he
    obtain ⟨k, hk, he⟩ := mem_biUnion.mp he
    exact (hok k (mem_range.mp (hids τ hτ hk))).loop_rect e he
  · intro τ hτ
    exact OnePart.even_incidentLoad_biUnion _ _ (hRdis.subset (hRsub τ hτ))
      (fun k hk z => (hok k (mem_range.mp (hids τ hτ hk))).even_rect z)
  · intro τ hτ
    rw [hchgTok τ hτ χ]
    split_ifs
    · exact hP
    · exact hM
  · intro τ hτ
    rw [hchgTok τ hτ χ']
    split_ifs
    · exact hP'
    · exact hM'
  · intro τ hτ
    refine card_biUnion_le.trans ?_
    calc ∑ k ∈ ids τ, (R k).card ≤ ∑ _k ∈ ids τ, 4 := sum_le_sum fun k _ => card_rect_le _ _ _ _
      _ = 4 * (ids τ).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 * 2 := by
          refine Nat.mul_le_mul_left 4 ?_
          simp only [ids]
          split_ifs
          · simp
          · exact card_le_two
      _ = 8 := by norm_num
  · intro τ hτ e he
    obtain ⟨k, hk, he⟩ := mem_biUnion.mp he
    exact hG' k (mem_range.mp (hids τ hτ hk)) he
  · intro v
    have htdis : (S : Set (Tok κ)).PairwiseDisjoint tokE := by
      intro τ hτ τ' hτ' hne
      simp only [Function.onFun, tokE]
      rw [disjoint_biUnion_left]
      intro k hk
      rw [disjoint_biUnion_right]
      intro k' hk'
      refine hRdis (hRsub τ hτ hk) (hRsub τ' hτ' hk') ?_
      rintro rfl
      exact disjoint_left.mp (hidsdis hτ hτ' hne) hk hk'
    rw [incidentLoad_biUnion_eq S tokE htdis v]
    refine (ModThreeLayer.incidentLoad_mono ?_ v).trans (hload v)
    intro e he
    obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp he
    obtain ⟨k, hk, he⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨k, hids τ hτ hk, he⟩

end PartitionedTriangleAbsorption.StructuralF3General
