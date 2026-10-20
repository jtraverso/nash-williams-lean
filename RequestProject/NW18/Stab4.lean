/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib

/-!
# Stability for graphs with few walks of length four

A generic stability lemma used for Lemma 14.4.  Let `D` be a set of `m` vertices of a graph
in which every vertex has at least `(1/2 - ε) m` neighbours in `D`.  If two vertices `s, t` are
joined by few walks `s a b c t` of length four with `a, b, c ∈ D`, then `D` is close to a
balanced complete bipartite graph or to a disjoint union of two cliques, and the neighbourhoods
of `s` and `t` in `D` are close to the two sides.
-/

namespace NashWilliams18

open Finset

section Stab

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `y` inside `D`. -/
def nbIn (D : Finset V) (y : V) : Finset V := D.filter (G.Adj y)

/-- The number of walks `s a b c t` with `a, b, c ∈ D`. -/
def walk4 (D : Finset V) (s t : V) : ℕ :=
  ∑ a ∈ nbIn G D s, ∑ c ∈ nbIn G D t, (nbIn G D a ∩ nbIn G D c).card

/-- The target neighbourhood of `x` for the structure given by the side `D1 ⊆ D`: the other
side (`bip = true`, complete bipartite) or its own side (`bip = false`, two cliques). -/
def tgt (D D1 : Finset V) (bip : Bool) (x : V) : Finset V :=
  if bip then (if x ∈ D1 then D \ D1 else D1) else (if x ∈ D1 then D1 else D \ D1)

omit [DecidableEq V] in
lemma nbIn_subset (D : Finset V) (y : V) : nbIn G D y ⊆ D := filter_subset _ _

omit [DecidableEq V] in
lemma mem_nbIn {D : Finset V} {y z : V} : z ∈ nbIn G D y ↔ z ∈ D ∧ G.Adj y z := mem_filter

lemma tgt_subset (D D1 : Finset V) (bip : Bool) (x : V) (h : D1 ⊆ D) : tgt D D1 bip x ⊆ D := by
  unfold tgt; split_ifs <;> first | exact h | exact sdiff_subset

lemma card_symmDiff (A B : Finset V) : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
  rw [symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff]

lemma card_symmDiff_triangle (A B C : Finset V) :
    (symmDiff A C).card ≤ (symmDiff A B).card + (symmDiff B C).card :=
  (card_le_card (symmDiff_triangle A B C)).trans (card_union_le _ _)

lemma card_symmDiff_comm (A B : Finset V) : (symmDiff A B).card = (symmDiff B A).card := by
  rw [symmDiff_comm]

/-- If `A, C ⊆ D` have small intersection, `A` is close to the complement of `C`. -/
lemma card_symmDiff_compl_eq {D A C : Finset V} (hA : A ⊆ D) (hC : C ⊆ D) :
    (symmDiff A (D \ C)).card + A.card + C.card = D.card + 2 * (A ∩ C).card := by
  rw [card_symmDiff]
  have h1 : A \ (D \ C) = A ∩ C := by
    ext x; simp only [mem_sdiff, mem_inter, not_and, not_not]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, h' (hA h)⟩
    · rintro ⟨h, h'⟩; exact ⟨h, fun _ => h'⟩
  have h2 : (D \ C) \ A = D \ (A ∪ C) := by
    ext x; simp only [mem_sdiff, mem_union]; tauto
  rw [h1, h2]
  have h3 := card_sdiff_add_card_inter D (A ∪ C)
  have h4 : D ∩ (A ∪ C) = A ∪ C := inter_eq_right.mpr (union_subset hA hC)
  rw [h4] at h3
  have h5 := card_union_add_card_inter A C
  omega

/-- Markov's inequality for counting. -/
lemma markov_card {ι : Type*} (S : Finset ι) (F : ι → ℝ) (hF : ∀ x ∈ S, 0 ≤ F x) (T : ℝ) :
    ((S.filter (fun x => ¬ F x ≤ T)).card : ℝ) * T ≤ ∑ x ∈ S, F x := by
  calc ((S.filter (fun x => ¬ F x ≤ T)).card : ℝ) * T
      = ∑ x ∈ S.filter (fun x => ¬ F x ≤ T), T := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S.filter (fun x => ¬ F x ≤ T), F x :=
        sum_le_sum fun x hx => le_of_lt (not_le.mp (mem_filter.mp hx).2)
    _ ≤ ∑ x ∈ S, F x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x hx _ => hF x hx)

/-- Averaging: some element is at most the average. -/
lemma exists_mul_card_le_sum {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (F : ι → ℝ) :
    ∃ x ∈ S, F x * S.card ≤ ∑ y ∈ S, F y := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  obtain ⟨x, hx, hle⟩ := exists_le_of_sum_le (f := F) (g := fun _ => (∑ y ∈ S, F y) / S.card)
    hS (by rw [sum_const, nsmul_eq_mul]; field_simp; rfl)
  exact ⟨x, hx, by rwa [le_div_iff₀ hc] at hle⟩

omit [DecidableEq V] in
/-- Double counting of edges between two sets. -/
lemma sum_card_nbIn_comm (A B : Finset V) :
    ∑ y ∈ A, (nbIn G B y).card = ∑ x ∈ B, (nbIn G A x).card := by
  simp only [nbIn, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp only [G.adj_comm]

/-- **Consistency.**  If every vertex of `T ⊆ X` has neighbourhood within `d` of `Y`, and
`|X \ T| ≤ e`, then `(|X \ Y| - e)(|X ∩ Y| - d) ≤ (d + e) |D|` for `X ⊆ D`. -/
lemma consistency {D X Y T : Finset V} (hX : X ⊆ D) {d e : ℝ} (hD0 : 0 ≤ d)
    (hd : ∀ x ∈ T, ((symmDiff (nbIn G D x) Y).card : ℝ) ≤ d) (he : ((X \ T).card : ℝ) ≤ e)
    (h2 : d ≤ (X ∩ Y).card) :
    ((X \ Y).card - e) * ((X ∩ Y).card - d) ≤ (d + e) * D.card := by
  -- S = number of adjacent pairs (y, x) with y ∈ X \ Y, x ∈ X ∩ Y
  have hcomm := sum_card_nbIn_comm G (X \ Y) (X ∩ Y)
  -- upper bound
  have hup : (∑ x ∈ X ∩ Y, ((nbIn G (X \ Y) x).card : ℝ)) ≤ (d + e) * D.card := by
    have hsplit := sum_filter_add_sum_filter_not (X ∩ Y) (fun x => x ∈ T)
      (fun x => ((nbIn G (X \ Y) x).card : ℝ))
    rw [← hsplit]
    have hA : ∑ x ∈ (X ∩ Y).filter (fun x => x ∈ T), ((nbIn G (X \ Y) x).card : ℝ) ≤
        d * D.card := by
      calc _ ≤ ∑ x ∈ (X ∩ Y).filter (fun x => x ∈ T), d := by
            refine sum_le_sum fun x hx => ?_
            obtain ⟨hxXY, hxT⟩ := mem_filter.mp hx
            refine le_trans ?_ (hd x hxT)
            rw [card_symmDiff]
            have : nbIn G (X \ Y) x ⊆ nbIn G D x \ Y := by
              intro z hz
              rw [mem_nbIn] at hz
              rw [mem_sdiff, mem_nbIn]
              exact ⟨⟨hX (mem_sdiff.mp hz.1).1, hz.2⟩, (mem_sdiff.mp hz.1).2⟩
            exact_mod_cast le_add_right (card_le_card this)
        _ = ((X ∩ Y).filter (fun x => x ∈ T)).card * d := by rw [sum_const, nsmul_eq_mul]
        _ ≤ D.card * d := by
            refine mul_le_mul_of_nonneg_right ?_ hD0
            exact_mod_cast card_le_card ((filter_subset _ _).trans
              (inter_subset_left.trans hX))
        _ = d * D.card := mul_comm _ _
    have hB : ∑ x ∈ (X ∩ Y).filter (fun x => x ∉ T), ((nbIn G (X \ Y) x).card : ℝ) ≤
        e * D.card := by
      calc _ ≤ ∑ x ∈ (X ∩ Y).filter (fun x => x ∉ T), (D.card : ℝ) := by
            refine sum_le_sum fun x _ => ?_
            exact_mod_cast card_le_card ((nbIn_subset G _ _).trans (sdiff_subset.trans hX))
        _ = ((X ∩ Y).filter (fun x => x ∉ T)).card * (D.card : ℝ) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ e * D.card := by
            refine mul_le_mul_of_nonneg_right (le_trans ?_ he) (by positivity)
            exact_mod_cast card_le_card (fun x hx => by
              obtain ⟨h1, h2⟩ := mem_filter.mp hx
              exact mem_sdiff.mpr ⟨(mem_inter.mp h1).1, h2⟩)
    linarith
  -- lower bound
  have hlow : ((X \ Y).card - e) * ((X ∩ Y).card - d) ≤
      ∑ y ∈ X \ Y, ((nbIn G (X ∩ Y) y).card : ℝ) := by
    have hTY : ((X \ Y).card : ℝ) - e ≤ ((X \ Y).filter (fun y => y ∈ T)).card := by
      have := card_filter_add_card_filter_not (s := X \ Y) (fun y => y ∈ T)
      have hsub : ((X \ Y).filter (fun y => y ∉ T)).card ≤ (X \ T).card :=
        card_le_card (fun y hy => by
          obtain ⟨h1, h2⟩ := mem_filter.mp hy
          exact mem_sdiff.mpr ⟨(mem_sdiff.mp h1).1, h2⟩)
      have : ((X \ Y).card : ℝ) = ((X \ Y).filter (fun y => y ∈ T)).card +
          ((X \ Y).filter (fun y => y ∉ T)).card := by exact_mod_cast this.symm
      have : (((X \ Y).filter (fun y => y ∉ T)).card : ℝ) ≤ (X \ T).card := by
        exact_mod_cast hsub
      linarith
    calc ((X \ Y).card - e) * ((X ∩ Y).card - d)
        ≤ ((X \ Y).filter (fun y => y ∈ T)).card * ((X ∩ Y).card - d) :=
          mul_le_mul_of_nonneg_right hTY (by linarith)
      _ = ∑ y ∈ (X \ Y).filter (fun y => y ∈ T), (((X ∩ Y).card : ℝ) - d) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ (X \ Y).filter (fun y => y ∈ T), ((nbIn G (X ∩ Y) y).card : ℝ) := by
          refine sum_le_sum fun y hy => ?_
          obtain ⟨hyXY, hyT⟩ := mem_filter.mp hy
          have hdy := hd y hyT
          rw [card_symmDiff] at hdy
          push_cast at hdy
          -- X ∩ Y ⊆ nbIn (X ∩ Y) y ∪ (Y \ nbIn D y)
          have hsub : X ∩ Y ⊆ nbIn G (X ∩ Y) y ∪ (Y \ nbIn G D y) := by
            intro z hz
            by_cases hz' : G.Adj y z
            · exact mem_union_left _ ((mem_nbIn G).mpr ⟨hz, hz'⟩)
            · refine mem_union_right _ (mem_sdiff.mpr ⟨(mem_inter.mp hz).2, fun h => hz' ?_⟩)
              exact ((mem_nbIn G).mp h).2
          have := (card_le_card hsub).trans (card_union_le _ _)
          have : ((X ∩ Y).card : ℝ) ≤ (nbIn G (X ∩ Y) y).card + (Y \ nbIn G D y).card := by
            exact_mod_cast this
          have : (0 : ℝ) ≤ ((nbIn G D y \ Y).card : ℝ) := by positivity
          linarith
      _ ≤ ∑ y ∈ X \ Y, ((nbIn G (X ∩ Y) y).card : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have hcomm' : (∑ y ∈ X \ Y, ((nbIn G (X ∩ Y) y).card : ℝ)) =
      ∑ x ∈ X ∩ Y, ((nbIn G (X \ Y) x).card : ℝ) := by exact_mod_cast hcomm
  linarith

lemma symmDiff_sdiff_sdiff {D A B : Finset V} (hA : A ⊆ D) (hB : B ⊆ D) :
    symmDiff (D \ A) (D \ B) = symmDiff A B := by
  ext x
  simp only [mem_symmDiff, mem_sdiff]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
    · exact Or.inr ⟨by tauto, h2⟩
    · exact Or.inl ⟨by tauto, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨⟨hA h1, h2⟩, fun h => h.2 h1⟩
    · exact Or.inl ⟨⟨hB h1, h2⟩, fun h => h.2 h1⟩

lemma card_sdiff_of_subset' {D A : Finset V} (h : A ⊆ D) : (D \ A).card + A.card = D.card := by
  have := card_sdiff_add_card_inter D A
  rwa [inter_eq_right.mpr h] at this

lemma card_le_symmDiff_left (A B : Finset V) : (A \ B).card ≤ (symmDiff A B).card := by
  rw [card_symmDiff]; omega

lemma card_le_symmDiff_right (A B : Finset V) : (B \ A).card ≤ (symmDiff A B).card := by
  rw [card_symmDiff]; omega

lemma card_sdiff_le_sdiff_add (A B C : Finset V) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  refine (card_le_card (fun x hx => ?_)).trans (card_union_le _ _)
  rw [mem_sdiff] at hx
  by_cases hB : x ∈ B
  · exact mem_union_right _ (mem_sdiff.mpr ⟨hB, hx.2⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hx.1, hB⟩)

lemma symmDiff_self_sdiff {D Z : Finset V} (h : Z ⊆ D) : symmDiff Z (D \ Z) = D := by
  ext x; simp only [mem_symmDiff, mem_sdiff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨⟨h1, -⟩, -⟩)
    · exact h h1
    · exact h1
  · intro hx; by_cases hz : x ∈ Z
    · exact Or.inl ⟨hz, fun h' => h'.2 hz⟩
    · exact Or.inr ⟨⟨hx, hz⟩, hz⟩

lemma card_sdiff_sdiff_add {D Z P : Finset V} (hP : P ⊆ D) :
    ((D \ Z) \ P).card + (P \ Z).card = (D \ Z).card := by
  have := card_sdiff_add_card_inter (D \ Z) P
  have h2 : (D \ Z) ∩ P = P \ Z := by
    ext x; simp only [mem_inter, mem_sdiff]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hP h1, h2⟩, h1⟩
  rwa [h2] at this

/-- Deviation of a vertex with small codegree with `c`: its neighbourhood is close to the
complement of `N(c)`. -/
lemma dev_of_codeg {D : Finset V} {a c : V} {ε β : ℝ}
    (ha : (1 / 2 - ε) * D.card ≤ (nbIn G D a).card)
    (hc : (1 / 2 - ε) * D.card ≤ (nbIn G D c).card)
    (hac : ((nbIn G D a ∩ nbIn G D c).card : ℝ) ≤ β * D.card) :
    ((symmDiff (nbIn G D a) (D \ nbIn G D c)).card : ℝ) ≤ (2 * ε + 2 * β) * D.card := by
  have h := card_symmDiff_compl_eq (nbIn_subset G D a) (nbIn_subset G D c)
  have h' : ((symmDiff (nbIn G D a) (D \ nbIn G D c)).card : ℝ) + (nbIn G D a).card +
      (nbIn G D c).card = D.card + 2 * (nbIn G D a ∩ nbIn G D c).card := by exact_mod_cast h
  linarith

/-- The conclusion of the stability lemma. -/
def StabConcl (D : Finset V) (s t : V) (σ : ℝ) : Prop :=
  ∃ D1 ⊆ D, ∃ bip : Bool, ∃ E ⊆ D, (E.card : ℝ) ≤ 20 * σ * D.card ∧
    (∀ x ∈ D, x ∉ E →
      ((symmDiff (nbIn G D x) (tgt D D1 bip x)).card : ℝ) ≤ 20 * σ * D.card) ∧
    ((symmDiff (nbIn G D s) D1).card : ℝ) ≤ 20 * σ * D.card ∧
    ((symmDiff (nbIn G D t) (D \ D1)).card : ℝ) ≤ 20 * σ * D.card

/-- The data produced in the first half of the proof of the stability lemma. -/
structure StabData (D P Q Z TP TQ : Finset V) (s t : V) (σ ε : ℝ) : Prop where
  hσ0 : 0 < σ
  hσ : σ ≤ 1 / 10
  hε0 : 0 ≤ ε
  hε : ε ≤ σ ^ 2
  hm : 0 < D.card
  hP : P = nbIn G D s
  hQ : Q = nbIn G D t
  hZD : Z ⊆ D
  hTPP : TP ⊆ P
  hTQQ : TQ ⊆ Q
  hPc : (1 / 2 - ε) * D.card ≤ P.card
  hQc : (1 / 2 - ε) * D.card ≤ Q.card
  hZup : (Z.card : ℝ) ≤ (1 / 2 + ε) * D.card
  hZlow : (1 / 2 - ε) * D.card - 4 * σ ^ 2 * D.card ≤ Z.card
  hdevP : ∀ a ∈ TP, ((symmDiff (nbIn G D a) Z).card : ℝ) ≤ 4 * σ ^ 2 * D.card
  hdevQ : ∀ c ∈ TQ, ((symmDiff (nbIn G D c) (D \ Z)).card : ℝ) ≤ 8 * σ ^ 2 * D.card
  hPTP : ((P \ TP).card : ℝ) ≤ 3 * σ ^ 4 * D.card
  hQTQ : ((Q \ TQ).card : ℝ) ≤ 3 * σ ^ 4 * D.card

variable {G}

lemma StabData.atoms {D P Q Z TP TQ : Finset V} {s t : V} {σ ε : ℝ}
    (h : StabData G D P Q Z TP TQ s t σ ε) :
    (0 : ℝ) < D.card ∧ 0 < σ * D.card ∧ ε * D.card ≤ σ ^ 2 * D.card ∧
      σ ^ 2 * D.card ≤ σ * D.card / 10 ∧ σ ^ 4 * D.card ≤ σ ^ 2 * D.card / 100 ∧
      0 ≤ σ ^ 4 * D.card ∧ σ * D.card ≤ D.card / 10 := by
  have hm0 : (0 : ℝ) < D.card := Nat.cast_pos.mpr h.hm
  have hσ0 := h.hσ0
  have hσ := h.hσ
  have hσ2 : σ ^ 2 ≤ σ / 10 := by nlinarith
  have hσ4 : σ ^ 4 ≤ σ ^ 2 / 100 := by nlinarith [sq_nonneg σ]
  refine ⟨hm0, by positivity, mul_le_mul_of_nonneg_right h.hε hm0.le, ?_, ?_, by positivity, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

lemma StabData.PQ {D P Q Z TP TQ : Finset V} {s t : V} {σ ε : ℝ}
    (h : StabData G D P Q Z TP TQ s t σ ε) : ((P ∩ Q).card : ℝ) ≤ 6 * σ ^ 4 * D.card := by
  obtain ⟨hm0, hσm, hεm, hA1, hA2, -, hA4⟩ := h.atoms
  have hdisj : ∀ x, x ∈ TP → x ∈ TQ → False := by
    intro x hxP hxQ
    have h1 := h.hdevP x hxP
    have h2 := h.hdevQ x hxQ
    have h3 := card_symmDiff_triangle Z (nbIn G D x) (D \ Z)
    rw [symmDiff_self_sdiff h.hZD, card_symmDiff_comm Z] at h3
    have h3' : (D.card : ℝ) ≤
        (symmDiff (nbIn G D x) Z).card + (symmDiff (nbIn G D x) (D \ Z)).card := by
      exact_mod_cast h3
    linarith
  have hsub : P ∩ Q ⊆ (P \ TP) ∪ (Q \ TQ) := by
    intro x hx
    obtain ⟨hxP, hxQ⟩ := mem_inter.mp hx
    by_cases h1 : x ∈ TP
    · by_cases h2 : x ∈ TQ
      · exact (hdisj x h1 h2).elim
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hxQ, h2⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hxP, h1⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  have : ((P ∩ Q).card : ℝ) ≤ (P \ TP).card + (Q \ TQ).card := by exact_mod_cast this
  linarith [h.hPTP, h.hQTQ]

lemma StabData.dich {D P Q Z TP TQ : Finset V} {s t : V} {σ ε : ℝ}
    (h : StabData G D P Q Z TP TQ s t σ ε) :
    ((P \ Z).card : ℝ) ≤ 4 * σ * D.card ∨ ((P ∩ Z).card : ℝ) ≤ 4 * σ * D.card := by
  obtain ⟨hm0, hσm, hεm, hA1, hA2, hA3, hA4⟩ := h.atoms
  have hPD : P ⊆ D := h.hP ▸ nbIn_subset G D s
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hcons := consistency G hPD (T := TP) (d := 4 * σ ^ 2 * D.card)
    (e := 3 * σ ^ 4 * D.card) (by positivity) h.hdevP h.hPTP (by linarith)
  have ha : 3 * (σ * D.card) < (P \ Z).card - 3 * σ ^ 4 * D.card := by linarith
  have hb : 3 * (σ * D.card) < (P ∩ Z).card - 4 * σ ^ 2 * D.card := by linarith
  have hprod : (3 * (σ * D.card)) * (3 * (σ * D.card)) <
      ((P \ Z).card - 3 * σ ^ 4 * D.card) * ((P ∩ Z).card - 4 * σ ^ 2 * D.card) :=
    mul_lt_mul'' ha hb (by positivity) (by positivity)
  have h5 : (4 * σ ^ 2 * D.card + 3 * σ ^ 4 * D.card) * D.card ≤
      5 * (σ ^ 2 * D.card) * D.card := by
    have : 4 * σ ^ 2 * D.card + 3 * σ ^ 4 * D.card ≤ 5 * (σ ^ 2 * D.card) := by linarith
    exact mul_le_mul_of_nonneg_right this hm0.le
  have h6 : 5 * (σ ^ 2 * D.card) * D.card < 9 * ((σ * D.card) * (σ * D.card)) := by
    have : (σ * D.card) * (σ * D.card) = σ ^ 2 * D.card * D.card := by ring
    rw [this]
    have : 0 < σ ^ 2 * D.card * D.card := mul_pos (mul_pos (pow_pos h.hσ0 2) hm0) hm0
    linarith
  linarith

lemma StabData.caseA {D P Q Z TP TQ : Finset V} {s t : V} {σ ε : ℝ}
    (h : StabData G D P Q Z TP TQ s t σ ε) (hA : ((P \ Z).card : ℝ) ≤ 4 * σ * D.card) :
    StabConcl G D s t σ := by
  obtain ⟨hm0, hσm, hεm, hA1, hA2, hA3, hA4⟩ := h.atoms
  have hPQ := h.PQ
  have hPD : P ⊆ D := h.hP ▸ nbIn_subset G D s
  have hQD : Q ⊆ D := h.hQ ▸ nbIn_subset G D t
  have hZD := h.hZD
  have hPc := h.hPc
  have hQc := h.hQc
  have hZup := h.hZup
  have hZlow := h.hZlow
  have hPTP := h.hPTP
  have hQTQ := h.hQTQ
  have hPsplit : ((P \ Z).card : ℝ) + (P ∩ Z).card = P.card := by
    exact_mod_cast card_sdiff_add_card_inter P Z
  have hZsplit : ((Z \ P).card : ℝ) + (P ∩ Z).card = Z.card := by
    rw [inter_comm]; exact_mod_cast card_sdiff_add_card_inter Z P
  have hQZ : ((Q ∩ Z).card : ℝ) ≤ (P ∩ Q).card + (Z \ P).card := by
    have hsub : Q ∩ Z ⊆ (P ∩ Q) ∪ (Z \ P) := by
      intro x hx
      obtain ⟨hxQ, hxZ⟩ := mem_inter.mp hx
      by_cases hxP : x ∈ P
      · exact mem_union_left _ (mem_inter.mpr ⟨hxP, hxQ⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hxZ, hxP⟩)
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hs : ((symmDiff P Z).card : ℝ) = (P \ Z).card + (Z \ P).card := by
    exact_mod_cast card_symmDiff P Z
  have ht : ((symmDiff Q (D \ Z)).card : ℝ) + Q.card + Z.card = D.card + 2 * (Q ∩ Z).card := by
    exact_mod_cast card_symmDiff_compl_eq hQD hZD
  have hE1 : ((Z \ TP).card : ℝ) ≤ (Z \ P).card + (P \ TP).card := by
    exact_mod_cast card_sdiff_le_sdiff_add Z P TP
  have hE2 : (((D \ Z) \ TQ).card : ℝ) ≤ ((D \ Z) \ Q).card + (Q \ TQ).card := by
    exact_mod_cast card_sdiff_le_sdiff_add (D \ Z) Q TQ
  have hE3 : (((D \ Z) \ Q).card : ℝ) ≤ (symmDiff Q (D \ Z)).card := by
    exact_mod_cast card_le_symmDiff_right Q (D \ Z)
  have hEu : (((Z \ TP) ∪ ((D \ Z) \ TQ)).card : ℝ) ≤ (Z \ TP).card + ((D \ Z) \ TQ).card := by
    exact_mod_cast card_union_le (Z \ TP) ((D \ Z) \ TQ)
  refine ⟨Z, hZD, false, (Z \ TP) ∪ ((D \ Z) \ TQ),
    union_subset (sdiff_subset.trans hZD) (sdiff_subset.trans sdiff_subset), by linarith,
    ?_, ?_, ?_⟩
  · intro x hxD hxE
    simp only [mem_union, mem_sdiff, not_or, not_and, not_not] at hxE
    by_cases hxZ : x ∈ Z
    · have hxTP := hxE.1 hxZ
      simp only [tgt, hxZ, if_true, Bool.false_eq_true, if_false]
      have := h.hdevP x hxTP
      linarith
    · have hxTQ := hxE.2 ⟨hxD, hxZ⟩
      simp only [tgt, hxZ, if_false, Bool.false_eq_true]
      have := h.hdevQ x hxTQ
      linarith
  · rw [← h.hP]; linarith
  · rw [← h.hQ]; linarith

lemma StabData.caseB {D P Q Z TP TQ : Finset V} {s t : V} {σ ε : ℝ}
    (h : StabData G D P Q Z TP TQ s t σ ε) (hB : ((P ∩ Z).card : ℝ) ≤ 4 * σ * D.card) :
    StabConcl G D s t σ := by
  obtain ⟨hm0, hσm, hεm, hA1, hA2, hA3, hA4⟩ := h.atoms
  have hPQ := h.PQ
  have hPD : P ⊆ D := h.hP ▸ nbIn_subset G D s
  have hQD : Q ⊆ D := h.hQ ▸ nbIn_subset G D t
  have hZD := h.hZD
  have hPc := h.hPc
  have hQc := h.hQc
  have hZup := h.hZup
  have hZlow := h.hZlow
  have hPTP := h.hPTP
  have hQTQ := h.hQTQ
  have hDDZ : D \ (D \ Z) = Z := Finset.sdiff_sdiff_eq_self hZD
  have hDZc : ((D \ Z).card : ℝ) + Z.card = D.card := by
    exact_mod_cast card_sdiff_of_subset' hZD
  have hPsplit : ((P \ Z).card : ℝ) + (P ∩ Z).card = P.card := by
    exact_mod_cast card_sdiff_add_card_inter P Z
  have hQsplit : ((Q \ Z).card : ℝ) + (Q ∩ Z).card = Q.card := by
    exact_mod_cast card_sdiff_add_card_inter Q Z
  have hDZP : (((D \ Z) \ P).card : ℝ) + (P \ Z).card = (D \ Z).card := by
    exact_mod_cast card_sdiff_sdiff_add (Z := Z) hPD
  have hQZ : ((Q \ Z).card : ℝ) ≤ (P ∩ Q).card + ((D \ Z) \ P).card := by
    have hsub : Q \ Z ⊆ (P ∩ Q) ∪ ((D \ Z) \ P) := by
      intro x hx
      obtain ⟨hxQ, hxZ⟩ := mem_sdiff.mp hx
      by_cases hxP : x ∈ P
      · exact mem_union_left _ (mem_inter.mpr ⟨hxP, hxQ⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hQD hxQ, hxZ⟩, hxP⟩)
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hs : ((symmDiff P (D \ Z)).card : ℝ) + P.card + Z.card = D.card + 2 * (P ∩ Z).card := by
    exact_mod_cast card_symmDiff_compl_eq hPD hZD
  have hZQsplit : ((Z \ Q).card : ℝ) + (Q ∩ Z).card = Z.card := by
    rw [inter_comm]; exact_mod_cast card_sdiff_add_card_inter Z Q
  have ht : ((symmDiff Q Z).card : ℝ) = (Q \ Z).card + (Z \ Q).card := by
    exact_mod_cast card_symmDiff Q Z
  have hE1 : (((D \ Z) \ TP).card : ℝ) ≤ ((D \ Z) \ P).card + (P \ TP).card := by
    exact_mod_cast card_sdiff_le_sdiff_add (D \ Z) P TP
  have hE2 : ((Z \ TQ).card : ℝ) ≤ (Z \ Q).card + (Q \ TQ).card := by
    exact_mod_cast card_sdiff_le_sdiff_add Z Q TQ
  have hEu : ((((D \ Z) \ TP) ∪ (Z \ TQ)).card : ℝ) ≤ ((D \ Z) \ TP).card + (Z \ TQ).card := by
    exact_mod_cast card_union_le ((D \ Z) \ TP) (Z \ TQ)
  refine ⟨D \ Z, sdiff_subset, true, ((D \ Z) \ TP) ∪ (Z \ TQ),
    union_subset (sdiff_subset.trans sdiff_subset) (sdiff_subset.trans hZD), by linarith,
    ?_, ?_, ?_⟩
  · intro x hxD hxE
    simp only [mem_union, mem_sdiff, not_or, not_and, not_not] at hxE
    by_cases hxZ : x ∈ Z
    · have hxTQ := hxE.2 hxZ
      have hx1 : x ∉ D \ Z := fun h => (mem_sdiff.mp h).2 hxZ
      simp only [tgt, hx1, if_true, if_false]
      have := h.hdevQ x hxTQ
      linarith
    · have hxTP := hxE.1 ⟨hxD, hxZ⟩
      have hx1 : x ∈ D \ Z := mem_sdiff.mpr ⟨hxD, hxZ⟩
      simp only [tgt, hx1, if_true, hDDZ]
      have := h.hdevP x hxTP
      linarith
  · rw [← h.hP]; linarith
  · rw [hDDZ, ← h.hQ]; linarith

lemma StabData.concl {D P Q Z TP TQ : Finset V} {s t : V} {σ ε : ℝ}
    (h : StabData G D P Q Z TP TQ s t σ ε) : StabConcl G D s t σ :=
  h.dich.elim h.caseA h.caseB

variable (G)


/-- **Stability for few walks of length four.** -/
theorem stab4 (D : Finset V) (s t : V) {σ ε κ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 10)
    (hε0 : 0 ≤ ε) (hε : ε ≤ σ ^ 2) (hκ : κ ≤ σ ^ 6) (hm : 0 < D.card)
    (hdeg : ∀ y, (1 / 2 - ε) * D.card ≤ (nbIn G D y).card)
    (hW : (walk4 G D s t : ℝ) ≤ κ * D.card ^ 3) :
    ∃ D1 ⊆ D, ∃ bip : Bool, ∃ E ⊆ D, (E.card : ℝ) ≤ 20 * σ * D.card ∧
      (∀ x ∈ D, x ∉ E →
        ((symmDiff (nbIn G D x) (tgt D D1 bip x)).card : ℝ) ≤ 20 * σ * D.card) ∧
      ((symmDiff (nbIn G D s) D1).card : ℝ) ≤ 20 * σ * D.card ∧
      ((symmDiff (nbIn G D t) (D \ D1)).card : ℝ) ≤ 20 * σ * D.card := by
  set m : ℝ := (D.card : ℝ) with hmdef
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set P := nbIn G D s with hP
  set Q := nbIn G D t with hQ
  set cd : V → V → ℝ := fun a c => ((nbIn G D a ∩ nbIn G D c).card : ℝ) with hcd
  have hcd0 : ∀ a c, 0 ≤ cd a c := fun a c => by positivity
  have hσ2 : σ ^ 2 ≤ σ / 10 := by nlinarith
  have hσ4 : σ ^ 4 ≤ σ ^ 2 / 100 := by nlinarith [sq_nonneg σ]
  have hσ6 : σ ^ 6 = σ ^ 2 * σ ^ 4 := by ring
  have hσ2pos : 0 < σ ^ 2 := by positivity
  have hεm : ε * m ≤ σ ^ 2 * m := mul_le_mul_of_nonneg_right hε hm0.le
  have hA1 : σ ^ 2 * m ≤ σ * m / 10 := by nlinarith
  have hA2 : σ ^ 4 * m ≤ σ ^ 2 * m / 100 := by nlinarith
  have hσm : 0 < σ * m := by positivity
  have hthird : ∀ y, m / 3 ≤ (nbIn G D y).card := fun y => by
    have := hdeg y; nlinarith
  -- the walk count as a double sum
  have hWsum : (walk4 G D s t : ℝ) = ∑ a ∈ P, ∑ c ∈ Q, cd a c := by
    simp [walk4, hcd, P, Q]
  -- choose `c₀`
  have hQne : Q.Nonempty := by
    rw [← card_pos]; have := hthird t; exact_mod_cast (show (0:ℝ) < Q.card by linarith)
  obtain ⟨c0, hc0Q, hc0⟩ := exists_mul_card_le_sum Q hQne (fun c => ∑ a ∈ P, cd a c)
  have hc0' : (∑ a ∈ P, cd a c0) ≤ 3 * σ ^ 6 * m ^ 2 := by
    have h1 : (∑ c ∈ Q, ∑ a ∈ P, cd a c) ≤ κ * m ^ 3 := by rw [sum_comm, ← hWsum]; exact hW
    have h2 : (0 : ℝ) ≤ ∑ a ∈ P, cd a c0 := sum_nonneg fun a _ => hcd0 a c0
    have h3 := hthird t
    have : (∑ a ∈ P, cd a c0) * (m / 3) ≤ κ * m ^ 3 := by
      calc _ ≤ (∑ a ∈ P, cd a c0) * Q.card := mul_le_mul_of_nonneg_left h3 h2
        _ ≤ _ := hc0.trans h1
    have : (∑ a ∈ P, cd a c0) * (m / 3) ≤ σ ^ 6 * m ^ 3 :=
      this.trans (mul_le_mul_of_nonneg_right hκ (by positivity))
    nlinarith
  set TP := P.filter (fun a => cd a c0 ≤ σ ^ 2 * m) with hTP
  have hTPP : TP ⊆ P := filter_subset _ _
  have hPTP : ((P \ TP).card : ℝ) ≤ 3 * σ ^ 4 * m := by
    have h := markov_card P (fun a => cd a c0) (fun a _ => hcd0 a c0) (σ ^ 2 * m)
    rw [filter_not] at h
    have : ((P \ TP).card : ℝ) * (σ ^ 2 * m) ≤ 3 * σ ^ 4 * m * (σ ^ 2 * m) := by
      calc _ ≤ _ := h
        _ ≤ 3 * σ ^ 6 * m ^ 2 := hc0'
        _ = _ := by ring
    exact le_of_mul_le_mul_right this (by positivity)
  set Z := D \ nbIn G D c0 with hZ
  have hZD : Z ⊆ D := sdiff_subset
  have hdevP : ∀ a ∈ TP, ((symmDiff (nbIn G D a) Z).card : ℝ) ≤ 4 * σ ^ 2 * m := by
    intro a ha
    have := dev_of_codeg G (hdeg a) (hdeg c0) (mem_filter.mp ha).2
    linarith
  have hTPc : m / 3 ≤ (TP.card : ℝ) := by
    have h1 := card_sdiff_of_subset' hTPP
    have h2 : ((P \ TP).card : ℝ) + TP.card = P.card := by exact_mod_cast h1
    have := hdeg s
    nlinarith
  have hTPne : TP.Nonempty := by
    rw [← card_pos]; exact_mod_cast (show (0:ℝ) < TP.card by linarith)
  -- choose `a₀`
  obtain ⟨a0, ha0TP, ha0⟩ := exists_mul_card_le_sum TP hTPne (fun a => ∑ c ∈ Q, cd a c)
  have ha0' : (∑ c ∈ Q, cd a0 c) ≤ 3 * σ ^ 6 * m ^ 2 := by
    have h1 : (∑ a ∈ TP, ∑ c ∈ Q, cd a c) ≤ κ * m ^ 3 := by
      refine le_trans ?_ (hWsum ▸ hW)
      exact sum_le_sum_of_subset_of_nonneg hTPP
        (fun a _ _ => sum_nonneg fun c _ => hcd0 a c)
    have h2 : (0 : ℝ) ≤ ∑ c ∈ Q, cd a0 c := sum_nonneg fun c _ => hcd0 a0 c
    have : (∑ c ∈ Q, cd a0 c) * (m / 3) ≤ κ * m ^ 3 := by
      calc _ ≤ (∑ c ∈ Q, cd a0 c) * TP.card := mul_le_mul_of_nonneg_left hTPc h2
        _ ≤ _ := ha0.trans h1
    have : (∑ c ∈ Q, cd a0 c) * (m / 3) ≤ σ ^ 6 * m ^ 3 :=
      this.trans (mul_le_mul_of_nonneg_right hκ (by positivity))
    nlinarith
  set TQ := Q.filter (fun c => cd a0 c ≤ σ ^ 2 * m) with hTQ
  have hTQQ : TQ ⊆ Q := filter_subset _ _
  have hQTQ : ((Q \ TQ).card : ℝ) ≤ 3 * σ ^ 4 * m := by
    have h := markov_card Q (fun c => cd a0 c) (fun c _ => hcd0 a0 c) (σ ^ 2 * m)
    rw [filter_not] at h
    have : ((Q \ TQ).card : ℝ) * (σ ^ 2 * m) ≤ 3 * σ ^ 4 * m * (σ ^ 2 * m) := by
      calc _ ≤ _ := h
        _ ≤ 3 * σ ^ 6 * m ^ 2 := ha0'
        _ = _ := by ring
    exact le_of_mul_le_mul_right this (by positivity)
  have hdevQ : ∀ c ∈ TQ, ((symmDiff (nbIn G D c) (D \ Z)).card : ℝ) ≤ 8 * σ ^ 2 * m := by
    intro c hc
    have h1 := dev_of_codeg G (hdeg c) (hdeg a0) (ε := ε) (β := σ ^ 2)
      (by rw [inter_comm]; exact (mem_filter.mp hc).2)
    have h2 : symmDiff (D \ nbIn G D a0) (D \ Z) = symmDiff (nbIn G D a0) Z :=
      symmDiff_sdiff_sdiff (nbIn_subset G D a0) hZD
    have h3 := card_symmDiff_triangle (nbIn G D c) (D \ nbIn G D a0) (D \ Z)
    rw [h2] at h3
    have h4 := hdevP a0 ha0TP
    have h3' : ((symmDiff (nbIn G D c) (D \ Z)).card : ℝ) ≤
        (symmDiff (nbIn G D c) (D \ nbIn G D a0)).card + (symmDiff (nbIn G D a0) Z).card := by
      exact_mod_cast h3
    linarith
  have hZc : (Z.card : ℝ) + (nbIn G D c0).card = m := by
    have := card_sdiff_of_subset' (nbIn_subset G D c0)
    rw [hmdef]; exact_mod_cast this
  have hc0c := hdeg c0
  have hZlow : (1 / 2 - ε) * m - 4 * σ ^ 2 * m ≤ Z.card := by
    have h1 := card_sdiff_add_card_inter (nbIn G D a0) Z
    have h2 := card_le_symmDiff_left (nbIn G D a0) Z
    have h3 : (nbIn G D a0 ∩ Z).card ≤ Z.card := card_le_card inter_subset_right
    have h4 := hdevP a0 ha0TP
    have h5 := hdeg a0
    have : ((nbIn G D a0 \ Z).card : ℝ) + (nbIn G D a0 ∩ Z).card = (nbIn G D a0).card := by
      exact_mod_cast h1
    have : ((nbIn G D a0 \ Z).card : ℝ) ≤ (symmDiff (nbIn G D a0) Z).card := by
      exact_mod_cast h2
    have : ((nbIn G D a0 ∩ Z).card : ℝ) ≤ Z.card := by exact_mod_cast h3
    linarith
  exact (StabData.mk (G := G) (D := D) (P := P) (Q := Q) (Z := Z) (TP := TP) (TQ := TQ)
    (s := s) (t := t) hσ0 hσ hε0 hε hm rfl rfl sdiff_subset hTPP hTQQ (hdeg s) (hdeg t)
    (by linarith) hZlow hdevP hdevQ hPTP hQTQ).concl

end Stab

end NashWilliams18
