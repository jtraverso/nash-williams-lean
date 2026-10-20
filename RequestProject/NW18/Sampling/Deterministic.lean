/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Sampling.SetCount
import RequestProject.NW18.Sampling.Glue
import RequestProject.NW18.Sampling.Hybrid

/-!
# Deterministic part of Lemma 11.6

If an injective sequence `ω` of vertices (other than `u, v`) avoids the bad events
(low sampled degrees, too few sampled high-degree vertices, too large sampled cuts), then the
induced graph on `S = {u, v} ∪ {ω j}` has large minimum degree and is not `σ/2`-extremal.
-/

namespace NashWilliams18.Sampling

open Finset

/-- An elementary estimate used for all degree bounds. -/
lemma frac_ge {a F N c : ℝ} (hN : 0 < N) (ha0 : 0 ≤ a) (haN : a ≤ N) (hF : c * N - 2 ≤ F) :
    a * c - 2 ≤ a * F / N := by
  rw [le_div_iff₀ hN]
  nlinarith [mul_le_mul_of_nonneg_left hF ha0]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Restricting a predicate to the vertices other than `u, v` loses at most two of them. -/
lemma card_filter_rest_ge (u v : V) (q : V → Prop) [DecidablePred q] :
    ((univ.filter q).card : ℝ) ≤ ((univ.filter fun b : Rest u v => q b.val).card : ℝ) + 2 := by
  have hsub : univ.filter q ⊆
      ((univ.filter fun b : Rest u v => q b.val).image Subtype.val) ∪ {u, v} := by
    intro x hx
    by_cases h : x ≠ u ∧ x ≠ v
    · apply mem_union_left
      exact mem_image.mpr ⟨⟨x, h⟩, by simpa using (mem_filter.mp hx).2, rfl⟩
    · apply mem_union_right
      simp only [not_and_or, not_not] at h
      rcases h with h | h <;> simp [h]
  have h1 := card_le_card hsub
  have h2 := card_union_le ((univ.filter fun b : Rest u v => q b.val).image Subtype.val)
    ({u, v} : Finset V)
  have h3 := card_image_le (s := univ.filter fun b : Rest u v => q b.val) (f := Subtype.val)
  have h4 : ({u, v} : Finset V).card ≤ 2 := card_le_two
  have : (univ.filter q).card ≤ (univ.filter fun b : Rest u v => q b.val).card + 2 := by omega
  exact_mod_cast this

lemma degree_le_filter_rest (G : SimpleGraph V) [DecidableRel G.Adj] (u v x : V) :
    (G.degree x : ℝ) ≤ ((univ.filter fun b : Rest u v => G.Adj x b.val).card : ℝ) + 2 := by
  have := card_filter_rest_ge u v (G.Adj x)
  rwa [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

omit [Fintype V] in
lemma mem_setOf_u (u v : V) {m : ℕ} (ω : Fin m → Rest u v) : u ∈ setOf u v ω := by
  simp [setOf]

omit [Fintype V] in
lemma mem_setOf_v (u v : V) {m : ℕ} (ω : Fin m → Rest u v) : v ∈ setOf u v ω := by
  simp [setOf]

omit [Fintype V] in
lemma mem_setOf_j (u v : V) {m : ℕ} (ω : Fin m → Rest u v) (j : Fin m) :
    (ω j).val ∈ setOf u v ω := by
  simp [setOf]

omit [Fintype V] in
lemma mem_setOf_cases {u v : V} {m : ℕ} {ω : Fin m → Rest u v} {x : V}
    (hx : x ∈ setOf u v ω) : x = u ∨ x = v ∨ ∃ j, x = (ω j).val := by
  simp only [setOf, mem_insert, mem_image, mem_univ, true_and] at hx
  rcases hx with h | h | ⟨j, hj⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨j, hj.symm⟩)

/-- The sample positions as vertices of `G[S]`. -/
def embS (u v : V) {m : ℕ} (ω : Fin m → Rest u v) : Fin m → ↥(setOf u v ω : Set V) :=
  fun j => ⟨(ω j).val, mem_setOf_j u v ω j⟩

omit [Fintype V] in
lemma embS_injective (u v : V) {m : ℕ} {ω : Fin m → Rest u v} (hω : Function.Injective ω) :
    Function.Injective (embS u v ω) := by
  intro a b h
  apply hω
  apply Subtype.ext
  have := congrArg Subtype.val h
  simpa [embS] using this

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
lemma induce_degree_ge {u v : V} {m : ℕ} {ω : Fin m → Rest u v} (hω : Function.Injective ω)
    (x : V) (hx : x ∈ setOf u v ω) :
    (((univ.filter fun j => G.Adj x (ω j).val).card : ℕ) : ℝ) ≤
      ((G.induce (setOf u v ω : Set V)).degree ⟨x, by simpa using hx⟩ : ℝ) := by
  have := degree_ge_count (G.induce (setOf u v ω : Set V)) (embS u v ω) (embS_injective u v hω)
    ⟨x, by simpa using hx⟩
  convert this using 4 <;> rfl


/-- Minimum degree of `G[S]`. -/
theorem mindeg_of_events {u v : V} {m : ℕ} {ω : Fin m → Rest u v}
    (hω : Function.Injective ω) {ε t : ℝ}
    (hNpos : 0 < (Fintype.card (Rest u v) : ℝ))
    (hNn : (Fintype.card (Rest u v) : ℝ) ≤ Fintype.card V)
    (hmN : (m : ℝ) ≤ Fintype.card (Rest u v)) (hm1 : 1 ≤ m)
    (hε38 : ε < 3 / 8) (ht : t ≤ ε * m / 8) (hmε : 5 ≤ ε * m)
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ))
    (hdeg : ∀ i, (m - 1) * ((univ.filter fun b : Rest u v => G.Adj (ω i).val b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => G.Adj (ω i).val (ω j).val).card : ℕ) : ℝ))
    (hu : ∀ x, x = u ∨ x = v →
      m * ((univ.filter fun b : Rest u v => G.Adj x b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => G.Adj x (ω j).val).card : ℕ) : ℝ)) :
    (3 / 4 - 2 * ε) * ((m : ℝ) + 2) ≤
      ((G.induce (setOf u v ω : Set V)).minDegree : ℝ) := by
  set Nr := (Fintype.card (Rest u v) : ℝ)
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hε0 : 0 < ε := by
    by_contra h; push_neg at h; nlinarith
  haveI : Nonempty ↥(setOf u v ω : Set V) := ⟨⟨u, by simpa using mem_setOf_u u v ω⟩⟩
  have hreal : ∀ y : ↥(setOf u v ω : Set V),
      (3 / 4 - 2 * ε) * ((m : ℝ) + 2) ≤ ((G.induce (setOf u v ω : Set V)).degree y : ℝ) := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ setOf u v ω := by simpa using hx
    have hdS := induce_degree_ge G hω x hx'
    have hFx := degree_le_filter_rest G u v x
    have hdx : (G.minDegree : ℝ) ≤ G.degree x := by exact_mod_cast G.minDegree_le_degree x
    have hc : 0 ≤ 3 / 4 - ε := by linarith
    have hF : (3 / 4 - ε) * Nr - 2 ≤
        ((univ.filter fun b : Rest u v => G.Adj x b.val).card : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hNn hc]
    rcases mem_setOf_cases hx' with h | h | ⟨j, rfl⟩
    · have h1 := hu x (Or.inl h)
      have h2 := frac_ge hNpos (by positivity) hmN hF
      nlinarith
    · have h1 := hu x (Or.inr h)
      have h2 := frac_ge hNpos (by positivity) hmN hF
      nlinarith
    · have h1 := hdeg j
      have h2 := frac_ge hNpos (by linarith : (0 : ℝ) ≤ m - 1) (by linarith) hF
      nlinarith
  rcases le_or_gt (3 / 4 - 2 * ε) 0 with hneg | hpos
  · have : (3 / 4 - 2 * ε) * ((m : ℝ) + 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
    exact this.trans (by positivity)
  have hk := SimpleGraph.le_minDegree_of_forall_le_degree (G.induce (setOf u v ω : Set V))
    ⌈(3 / 4 - 2 * ε) * ((m : ℝ) + 2)⌉₊ fun y => Nat.ceil_le.mpr (hreal y)
  exact (Nat.le_ceil _).trans (by exact_mod_cast hk)


/-- Condition (i) of `σ/2`-extremality fails for `G[S]` when `G` has many high-degree vertices. -/
theorem not_ext_i_of_events {u v : V} (huv : u ≠ v) {m : ℕ} {ω : Fin m → Rest u v}
    (hω : Function.Injective ω) {σ t : ℝ}
    (hNpos : 0 < (Fintype.card (Rest u v) : ℝ))
    (hNn : (Fintype.card (Rest u v) : ℝ) ≤ Fintype.card V)
    (hmN : (m : ℝ) ≤ Fintype.card (Rest u v)) (hm1 : 1 ≤ m)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : t ≤ σ * m / 8) (hmσ : 18 ≤ σ * m)
    (hB : σ * Fintype.card V <
      ((univ.filter fun x => (3 / 4 + σ) * (Fintype.card V : ℝ) < G.degree x).card : ℝ))
    (hdeg : ∀ i, (m - 1) * ((univ.filter fun b : Rest u v => G.Adj (ω i).val b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => G.Adj (ω i).val (ω j).val).card : ℕ) : ℝ))
    (hcnt : m * ((univ.filter fun b : Rest u v =>
          (3 / 4 + σ) * (Fintype.card V : ℝ) < G.degree b.val).card : ℝ) /
        Fintype.card (Rest u v) - t ≤
        (((univ.filter fun j => (3 / 4 + σ) * (Fintype.card V : ℝ) < G.degree (ω j).val).card :
          ℕ) : ℝ)) :
    ¬ ((1 - σ / 2) * (Fintype.card ↥(setOf u v ω : Set V) : ℝ) ≤
      ((univ.filter fun y => ((G.induce (setOf u v ω : Set V)).degree y : ℝ) ≤
        (3 / 4 + σ / 2) * (Fintype.card ↥(setOf u v ω : Set V) : ℝ)).card : ℝ)) := by
  set Nr := (Fintype.card (Rest u v) : ℝ)
  set n := (Fintype.card V : ℝ)
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hS : (Fintype.card ↥(setOf u v ω : Set V) : ℝ) = m + 2 := by
    simp [card_setOf huv ω hω]
  rw [hS]
  set X := (3 / 4 + σ / 2) * ((m : ℝ) + 2)
  have hlow := card_low_le (G.induce (setOf u v ω : Set V)) (embS u v ω)
    (embS_injective u v hω) X
  rw [hS] at hlow
  have hc : (0 : ℝ) ≤ 3 / 4 + σ := by linarith
  have hsub : (univ.filter fun j => (3 / 4 + σ) * n < G.degree (ω j).val) ⊆
      (univ.filter fun j => X < ((G.induce (setOf u v ω : Set V)).degree (embS u v ω j) : ℝ)) := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    simp only [mem_filter, mem_univ, true_and]
    have hdS := induce_degree_ge G hω (ω j).val (mem_setOf_j u v ω j)
    have hFx := degree_le_filter_rest G u v (ω j).val
    have hF : (3 / 4 + σ) * Nr - 2 ≤
        ((univ.filter fun b : Rest u v => G.Adj (ω j).val b.val).card : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hNn hc]
    have h1 := hdeg j
    have h2 := frac_ge hNpos (by linarith : (0 : ℝ) ≤ m - 1) (by linarith) hF
    have : X < ((G.induce (setOf u v ω : Set V)).degree ⟨(ω j).val, by
        simpa using mem_setOf_j u v ω j⟩ : ℝ) := by
      simp only [X]; nlinarith
    exact this
  have hsubc := card_le_card hsub
  have hgc := card_filter_rest_ge u v (fun x => (3 / 4 + σ) * n < G.degree x)
  have hF : σ * Nr - 2 ≤ ((univ.filter fun b : Rest u v =>
      (3 / 4 + σ) * n < G.degree b.val).card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hNn hσ0.le]
  have h2 := frac_ge hNpos (by positivity) hmN hF
  have hsubr : (((univ.filter fun j => (3 / 4 + σ) * n < G.degree (ω j).val).card : ℕ) : ℝ) ≤
      (((univ.filter fun j => X <
        ((G.induce (setOf u v ω : Set V)).degree (embS u v ω j) : ℝ)).card : ℕ) : ℝ) := by
    exact_mod_cast hsubc
  intro hcon
  nlinarith

/-- Condition (ii) of `σ/2`-extremality fails for `G[S]` when all sampled cuts are small. -/
theorem not_ext_ii_of_events {u v : V} (huv : u ≠ v) {m : ℕ} {ω : Fin m → Rest u v}
    (hω : Function.Injective ω) {σ η K : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hη : η ≤ σ / 16) (hm4 : 4 ≤ m) (hmσ : 96 ≤ σ * m)
    (hKN : K / (Fintype.card (Rest u v) : ℝ) ^ 2 ≤ (1 - σ) * (1 + σ / 4) / 2)
    (hmc : ∀ a : Fin m → Bool, cutQ (G.comap (Subtype.val : Rest u v → V)) ω a <
      (m : ℝ) ^ 2 * (K / (Fintype.card (Rest u v) : ℝ) ^ 2) + η * (m : ℝ) ^ 2) :
    ¬ ∃ T : Finset ↥(setOf u v ω : Set V),
      (1 - σ / 2) * (Fintype.card ↥(setOf u v ω : Set V) : ℝ) ^ 2 / 4 ≤
        (cutSize (G.induce (setOf u v ω : Set V)) T : ℝ) := by
  rintro ⟨T, hT⟩
  have hSn : Fintype.card ↥(setOf u v ω : Set V) = m + 2 := by
    simp [card_setOf huv ω hω]
  have hS : (Fintype.card ↥(setOf u v ω : Set V) : ℝ) = m + 2 := by
    rw [hSn]; push_cast; ring
  rw [hS] at hT
  set X : ↥(setOf u v ω : Set V) → Bool := fun x => decide (x ∈ T)
  have h1 := cutSize_le_pairs (G.induce (setOf u v ω : Set V)) T
  have h2 := doubled_eq (fun x y => (G.induce (setOf u v ω : Set V)).Adj x y)
    (fun x y h => h.symm) X
  have hpairs : (∑ x, ∑ y, if (G.induce (setOf u v ω : Set V)).Adj x y ∧ x ∈ T ∧ y ∉ T
      then (1 : ℝ) else 0) = ∑ x, ∑ y, if (G.induce (setOf u v ω : Set V)).Adj x y ∧
        X x = true ∧ X y = false then (1 : ℝ) else 0 := by
    simp [X]
  have h3 := sum_pairs_le_of_injective (embS u v ω) (embS_injective u v hω) hSn
    (fun x y => if (G.induce (setOf u v ω : Set V)).Adj x y ∧ X x ≠ X y then (1 : ℝ) else 0)
    (fun x y => by constructor <;> split_ifs <;> norm_num)
  have h4 : (∑ i, ∑ j, if (G.induce (setOf u v ω : Set V)).Adj (embS u v ω i) (embS u v ω j) ∧
      X (embS u v ω i) ≠ X (embS u v ω j) then (1 : ℝ) else 0) =
      cutQ (G.comap (Subtype.val : Rest u v → V)) ω (fun j => X (embS u v ω j)) := by
    unfold cutQ; rfl
  have h5 := hmc (fun j => X (embS u v ω j))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  have hKm := mul_le_mul_of_nonneg_left hKN hm0
  have hm4r : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hmm := mul_le_mul_of_nonneg_right hmσ (by positivity : (0 : ℝ) ≤ m)
  have hηm := mul_le_mul_of_nonneg_right hη hm0
  nlinarith [sq_nonneg (σ * m)]

omit [DecidableEq V] in
lemma sum_subtype_le {p : V → Prop} [DecidablePred p] (φ : V → ℝ) (hφ : ∀ x, 0 ≤ φ x) :
    (∑ a : {x // p x}, φ a.val) ≤ ∑ x, φ x := by
  classical
  rw [← sum_image (s := (univ : Finset {x // p x})) (g := Subtype.val)
    (fun a _ b _ h => Subtype.ext h)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => hφ x

/-- If every cut of `G` is small, every doubled cut of `G - u - v` is small. -/
lemma doubled_cut_rest_le (u v : V) {K : ℝ}
    (hcut : ∀ T : Finset V, (cutSize G T : ℝ) < K / 2) (X : Rest u v → Bool) :
    (∑ a, ∑ b, if (G.comap (Subtype.val : Rest u v → V)).Adj a b ∧ X a ≠ X b then (1 : ℝ)
      else 0) ≤ K := by
  set X' : V → Bool := fun x => if h : x ≠ u ∧ x ≠ v then X ⟨x, h⟩ else false
  have hX' : ∀ a : Rest u v, X' a.val = X a := fun a => by simp [X', a.2]
  have h0 : (∑ a, ∑ b, if (G.comap (Subtype.val : Rest u v → V)).Adj a b ∧ X a ≠ X b then
      (1 : ℝ) else 0) = ∑ a : Rest u v, ∑ b : Rest u v,
        (if G.Adj a.val b.val ∧ X' a.val ≠ X' b.val then (1 : ℝ) else 0) := by
    simp only [hX']; rfl
  have h1 : (∑ a : Rest u v, ∑ b : Rest u v,
      (if G.Adj a.val b.val ∧ X' a.val ≠ X' b.val then (1 : ℝ) else 0)) ≤
      ∑ x, ∑ y, (if G.Adj x y ∧ X' x ≠ X' y then (1 : ℝ) else 0) := by
    refine (sum_le_sum fun a _ => sum_subtype_le
      (fun y => if G.Adj a.val y ∧ X' a.val ≠ X' y then (1 : ℝ) else 0)
      (fun y => by split_ifs <;> norm_num)).trans ?_
    exact sum_subtype_le (fun x => ∑ y, if G.Adj x y ∧ X' x ≠ X' y then (1 : ℝ) else 0)
      (fun x => sum_nonneg fun y _ => by split_ifs <;> norm_num)
  have h2 := doubled_eq (fun x y => G.Adj x y) (fun x y h => h.symm) X'
  set T := univ.filter fun x => X' x = true
  have h3 : (∑ x, ∑ y, if G.Adj x y ∧ X' x = true ∧ X' y = false then (1 : ℝ) else 0) =
      ∑ x, ∑ y, if G.Adj x y ∧ x ∈ T ∧ y ∉ T then (1 : ℝ) else 0 := by
    simp [T]
  have h4 := pairs_le_cutSize G T
  have h5 := hcut T
  rw [h0]
  linarith

end NashWilliams18.Sampling
