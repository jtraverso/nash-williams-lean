/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.Clean126
public import RequestProject.NW18.Case127.Extremal

@[expose] public section

/-!
# Removing the abnormal edges (Claim 12.7.7)

After Lemma 15.9, the graph `H = cleanGraph G A C W` still contains abnormal edges: edges inside
a side of `P*` joining two classes not joined in `F₂` (between the classes `0` and `1`, or
inside the class `2` or `3`).  They have maximum degree at most `s n`, and their ends have
almost `n/2` common neighbours on the other side; Lemma 15.17 covers them by edge-disjoint
cross triangles of `H` of maximum degree `O(s n)`.
-/

namespace NashWilliams18.C127

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

variable {V : Type*} [Fintype V] [DecidableEq V]

section

variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V} {s : ℝ}

lemma card_side_ge (h : Setup127 G p A s) (σ : Fin 2) :
    (Fintype.card V : ℝ) / 2 - 2 ≤ ((univ.filter (fun z => side4 (p z) = σ)).card : ℝ) := by
  rcases side_cases σ with rfl | rfl
  · rw [card_side_zero]; push_cast; linarith [h.cls_lo 0, h.cls_lo 1]
  · rw [card_side_one]; push_cast; linarith [h.cls_lo 2, h.cls_lo 3]

omit [Fintype V] in
lemma card_filter_edge_le (Z : Finset V) (C : Finset (Sym2 V)) (x : V) :
    (Z.filter (fun z => s(x, z) ∈ C)).card ≤ (C.filter (fun e => x ∈ e)).card := by
  refine card_le_card_of_injOn (fun z => s(x, z)) (fun z hz => ?_) (fun z _ z' _ hzz => ?_)
  · simp only [coe_filter, Set.mem_setOf_eq] at hz
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨hz.2, Sym2.mem_mk_left _ _⟩
  · simp only [Sym2.eq_iff, true_and] at hzz
    rcases hzz with h' | ⟨h1, h2⟩
    · exact h'
    · rw [h2, h1]

/-- **Claim 12.7.7**: the abnormal edges of `cleanGraph G A C W` are covered by edge-disjoint
cross triangles of small maximum degree. -/
lemma step_15_17 (h : Setup127 G p A s) (hs : s ≤ 1 / 1000)
    (hsn : 1000 ≤ s * (Fintype.card V : ℝ)) (C W : Finset (Sym2 V)) (c : ℝ)
    (hc : c ≤ (Fintype.card V : ℝ) / 100)
    (hCdeg : ∀ a, a ∉ A → ((C.filter (fun e => a ∈ e)).card : ℝ) ≤ c)
    (hW : ∀ x, (W.filter (fun e => x ∈ e)).card ≤ 4) :
    ∃ T2 : Finset (Finset V), IsTrianglePacking (cleanGraph G A C W) T2 ∧
      (∀ x y, (cleanGraph G A C W).Adj x y → ¬ AllowedT F2 (p x) (p y) →
        s(x, y) ∈ T2.biUnion triEdges) ∧
      (∀ t ∈ T2, ¬ IsInteriorTri (sideP G p A) t) ∧
      ∀ x, (((T2.biUnion triEdges).filter (fun e => x ∈ e)).card : ℝ) ≤ 12 * s * Fintype.card V := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by by_contra hneg; push_neg at hneg; nlinarith
  set H := cleanGraph G A C W with hH
  set q := sideP G p A with hq
  set O : Finset (Sym2 V) := H.edgeFinset.filter
    (fun e => ∃ x y, e = s(x, y) ∧ ¬ AllowedT F2 (p x) (p y)) with hO
  have hbad : ∀ x y, s(x, y) ∈ O → H.Adj x y ∧ ¬ AllowedT F2 (p x) (p y) := by
    intro x y hxy
    simp only [hO, mem_filter, SimpleGraph.mem_edgeFinset] at hxy
    obtain ⟨hadj, x', y', he, hna⟩ := hxy
    refine ⟨hadj, ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hna
    · rwa [allowedT_F2_comm]
  have hside : ∀ x y, H.Adj x y → ¬ AllowedT F2 (p x) (p y) → q x = q y := by
    intro x y hxy hna
    rw [hq, sideP_of_not_mem hxy.2.1, sideP_of_not_mem hxy.2.2.1]
    exact side_eq_of_not_allowedT_F2 hna
  set d : ℕ := ⌊s * n⌋₊ with hd
  set K : ℕ := ⌈4 * s * n⌉₊ with hK
  set m : ℕ := ⌈n / 3⌉₊ with hm
  have hdle : (d : ℝ) ≤ s * n := Nat.floor_le (by positivity)
  have hKlo : 4 * s * n ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) < 4 * s * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmlo : n / 3 ≤ (m : ℝ) := Nat.le_ceil _
  -- the `O`-degree
  have hOdeg : ∀ v, (O.filter (fun e => v ∈ e)).card ≤ d := by
    intro v
    by_cases hvA : v ∈ A
    · have : O.filter (fun e => v ∈ e) = ∅ := by
        rw [filter_eq_empty_iff]
        intro e he hve
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
        exact (hbad v w he).1.2.1 hvA
      rw [this]; simp
    · apply Nat.le_floor
      refine le_trans ?_ (h.normal v hvA)
      refine Nat.cast_le.mpr (le_trans (card_le_card
        (t := (abnSet G p v).image (fun w => s(v, w))) ?_) card_image_le)
      · intro e he
        simp only [mem_filter] at he
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp he.2
        obtain ⟨hadj, hna⟩ := hbad v w he.1
        refine mem_image.mpr ⟨w, ?_, rfl⟩
        simp only [abnSet, mem_filter, mem_univ, true_and]
        exact ⟨fun hw => hadj.1.ne hw.symm, fun hiff => hna (hiff.mp hadj.1)⟩
  -- common neighbours on the other side
  have hcomR : ∀ x y, s(x, y) ∈ O →
      n / 3 ≤ ((univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z)).card : ℝ) := by
    intro x y hxy
    obtain ⟨hadj, hna⟩ := hbad x y hxy
    have hxA := hadj.2.1
    have hyA := hadj.2.2.1
    have hqxy := hside x y hadj hna
    have hpxy : side4 (p x) = side4 (p y) := by
      rw [hq, sideP_of_not_mem hxA, sideP_of_not_mem hyA] at hqxy; exact hqxy
    set σ : Fin 2 := 1 - side4 (p x) with hσ
    have hσne : ∀ z, side4 (p z) = σ → side4 (p z) ≠ side4 (p x) := by
      intro z hz; rw [hz, hσ]; generalize side4 (p x) = i; revert i; decide
    set Z := univ.filter (fun z => side4 (p z) = σ) with hZ
    have hZc := card_side_ge h σ
    -- bad sets
    have bad : ∀ u, u ∉ A → side4 (p u) = side4 (p x) →
        ((Z.filter (fun z => ¬ G.Adj u z)).card : ℝ) +
          (Z.filter (fun z => s(u, z) ∈ C)).card + (Z.filter (fun z => s(u, z) ∈ W)).card ≤
          s * n + c + 4 := by
      intro u huA hu
      have h1 : (Z.filter (fun z => ¬ G.Adj u z)).card ≤ (abnSet G p u).card := by
        apply card_le_card
        intro z hz
        simp only [hZ, mem_filter, mem_univ, true_and] at hz
        simp only [abnSet, mem_filter, mem_univ, true_and]
        have hne := hσne z hz.1
        refine ⟨fun hzu => hne (by rw [hzu, hu]), fun hiff => hz.2 (hiff.mpr ?_)⟩
        exact allowedT_F2_of_side_ne (by rw [hu]; exact fun h' => hne h'.symm)
      have h2 := card_filter_edge_le Z C u
      have h3 := (card_filter_edge_le Z W u).trans (hW u)
      have h1R : ((Z.filter (fun z => ¬ G.Adj u z)).card : ℝ) ≤ s * n :=
        (Nat.cast_le.mpr h1).trans (h.normal u huA)
      have h2R : ((Z.filter (fun z => s(u, z) ∈ C)).card : ℝ) ≤ c :=
        (Nat.cast_le.mpr h2).trans (hCdeg u huA)
      have h3R : ((Z.filter (fun z => s(u, z) ∈ W)).card : ℝ) ≤ 4 := by exact_mod_cast h3
      linarith
    have bx := bad x hxA rfl
    have bY := bad y hyA hpxy.symm
    have hsub : Z ⊆ univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z) ∪
        (A ∪ ((Z.filter (fun z => ¬ G.Adj x z) ∪ Z.filter (fun z => s(x, z) ∈ C) ∪
          Z.filter (fun z => s(x, z) ∈ W)) ∪
          (Z.filter (fun z => ¬ G.Adj y z) ∪ Z.filter (fun z => s(y, z) ∈ C) ∪
          Z.filter (fun z => s(y, z) ∈ W)))) := by
      intro z hz
      have hz' := hz
      simp only [hZ, mem_filter, mem_univ, true_and] at hz'
      simp only [mem_union, mem_filter, mem_univ, true_and]
      by_cases hzA : z ∈ A
      · exact Or.inr (Or.inl hzA)
      by_cases hgx : G.Adj x z ∧ s(x, z) ∉ C ∧ s(x, z) ∉ W
      · by_cases hgy : G.Adj y z ∧ s(y, z) ∉ C ∧ s(y, z) ∉ W
        · left
          refine ⟨?_, ⟨hgx.1, hxA, hzA, hgx.2.1, hgx.2.2⟩, ⟨hgy.1, hyA, hzA, hgy.2.1, hgy.2.2⟩⟩
          rw [hq, sideP_of_not_mem hzA, sideP_of_not_mem hxA]; exact hσne z hz'
        · right; right; right
          by_cases h1 : G.Adj y z
          · by_cases h2 : s(y, z) ∈ C
            · exact Or.inl (Or.inr ⟨hz, h2⟩)
            · exact Or.inr ⟨hz, by tauto⟩
          · exact Or.inl (Or.inl ⟨hz, h1⟩)
      · right; right; left
        by_cases h1 : G.Adj x z
        · by_cases h2 : s(x, z) ∈ C
          · exact Or.inl (Or.inr ⟨hz, h2⟩)
          · exact Or.inr ⟨hz, by tauto⟩
        · exact Or.inl (Or.inl ⟨hz, h1⟩)
    have hcard := (card_le_card hsub).trans (card_union_le _ _)
    have u1 := card_union_le A ((Z.filter (fun z => ¬ G.Adj x z) ∪ Z.filter (fun z => s(x, z) ∈ C) ∪
          Z.filter (fun z => s(x, z) ∈ W)) ∪
          (Z.filter (fun z => ¬ G.Adj y z) ∪ Z.filter (fun z => s(y, z) ∈ C) ∪
          Z.filter (fun z => s(y, z) ∈ W)))
    have u2 := card_union_le (Z.filter (fun z => ¬ G.Adj x z) ∪ Z.filter (fun z => s(x, z) ∈ C) ∪
          Z.filter (fun z => s(x, z) ∈ W))
          (Z.filter (fun z => ¬ G.Adj y z) ∪ Z.filter (fun z => s(y, z) ∈ C) ∪
          Z.filter (fun z => s(y, z) ∈ W))
    have u3 := card_union_le (Z.filter (fun z => ¬ G.Adj x z) ∪ Z.filter (fun z => s(x, z) ∈ C))
          (Z.filter (fun z => s(x, z) ∈ W))
    have u4 := card_union_le (Z.filter (fun z => ¬ G.Adj x z)) (Z.filter (fun z => s(x, z) ∈ C))
    have u5 := card_union_le (Z.filter (fun z => ¬ G.Adj y z) ∪ Z.filter (fun z => s(y, z) ∈ C))
          (Z.filter (fun z => s(y, z) ∈ W))
    have u6 := card_union_le (Z.filter (fun z => ¬ G.Adj y z)) (Z.filter (fun z => s(y, z) ∈ C))
    have hfin : (Z.card : ℝ) ≤ ((univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z)).card : ℝ) +
        (A.card + ((Z.filter (fun z => ¬ G.Adj x z)).card + (Z.filter (fun z => s(x, z) ∈ C)).card +
          (Z.filter (fun z => s(x, z) ∈ W)).card) +
          ((Z.filter (fun z => ¬ G.Adj y z)).card + (Z.filter (fun z => s(y, z) ∈ C)).card +
          (Z.filter (fun z => s(y, z) ∈ W)).card)) := by
      have : Z.card ≤ (univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z)).card +
        (A.card + ((Z.filter (fun z => ¬ G.Adj x z)).card + (Z.filter (fun z => s(x, z) ∈ C)).card +
          (Z.filter (fun z => s(x, z) ∈ W)).card) +
          ((Z.filter (fun z => ¬ G.Adj y z)).card + (Z.filter (fun z => s(y, z) ∈ C)).card +
          (Z.filter (fun z => s(y, z) ∈ W)).card)) := by omega
      exact_mod_cast this
    have := h.A_card
    nlinarith
  have hcom : ∀ x y, s(x, y) ∈ O →
      m ≤ (univ.filter (fun z => q z ≠ q x ∧ H.Adj x z ∧ H.Adj y z)).card :=
    fun x y hxy => Nat.ceil_le.mpr (hcomR x y hxy)
  -- the size of `O`
  have hOcard : (O.card : ℝ) ≤ n * d := by
    have h1 : O.card ≤ ∑ v, (O.filter (fun e => v ∈ e)).card := by
      rw [sum_card_filter_mem]
      calc O.card = ∑ _e ∈ O, 1 := by simp
        _ ≤ _ := sum_le_sum fun e _ => by
          induction e using Sym2.ind with
          | _ a b => exact card_pos.mpr ⟨a, by simp⟩
    have h2 : ∑ v, (O.filter (fun e => v ∈ e)).card ≤ ∑ _v : V, d := sum_le_sum fun v _ => hOdeg v
    rw [sum_const, card_univ, smul_eq_mul] at h2
    have : O.card ≤ Fintype.card V * d := h1.trans h2
    rw [hndef]; exact_mod_cast this
  have hcond : O.card + K * (4 * (d + K)) < K * m := by
    have hR : (O.card : ℝ) + K * (4 * (d + K)) < K * m := by
      have hKm : (K : ℝ) * (n / 3) ≤ K * m := mul_le_mul_of_nonneg_left hmlo (by positivity)
      have hK0 : (0 : ℝ) ≤ K := by positivity
      have e1 : (K : ℝ) * (4 * (d + K)) ≤ (4 * s * n + 1) * (4 * (s * n + (4 * s * n + 1))) := by
        apply mul_le_mul hKhi.le _ (by positivity) (by positivity)
        linarith
      have e2 : (4 * s * n) * (n / 3) ≤ (K : ℝ) * (n / 3) :=
        mul_le_mul_of_nonneg_right hKlo (by positivity)
      have hsn' : s * n * (s * n) ≤ s * n * (n / 1000) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
      nlinarith
    exact_mod_cast hR
  obtain ⟨T2, hT2, hOT, hT2form, hT2deg⟩ := lemma_15_17 H q O d m K
    (fun x y hxy => (hbad x y hxy).1) (fun x y hxy => hside x y (hbad x y hxy).1 (hbad x y hxy).2)
    hOdeg hcom hcond
  refine ⟨T2, hT2, fun x y hxy hna => hOT ?_, fun t ht hint => ?_, fun x => ?_⟩
  · simp only [hO, mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨hxy, x, y, rfl, hna⟩
  · obtain ⟨x, y, z, rfl, -, hzx, -⟩ := hT2form t ht
    obtain ⟨i, hi⟩ := hint
    exact hzx ((hi z (by simp)).trans (hi x (by simp)).symm)
  · have := hT2deg x
    have hR : (((T2.biUnion triEdges).filter (fun e => x ∈ e)).card : ℝ) ≤ 2 * (d + K) := by
      exact_mod_cast this
    nlinarith

end

end NashWilliams18.C127
