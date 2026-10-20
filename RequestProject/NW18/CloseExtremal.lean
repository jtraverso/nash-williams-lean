/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Defs

@[expose] public section

/-!
# Closeness to the extremal graphs implies extremality

If `G` is `α`-close to one of `T₂(n/2)+T₂(n/2)`, `T̄₂(n/2)+T₂(n/2)`, `T̄₂(n/2)+T̄₂(n/2)` with
`α ≤ β²/8` and `α ≤ β/8`, and `n` is large, then `G` is `β`-extremal.

The proof only uses two features of the three target graphs `X` on `Fin n`: every vertex is
non-adjacent to a whole class of the four-class layout (each class has at least `(n-3)/4`
vertices), and the two halves are completely joined.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

lemma card_filter_fin_interval (n a b : ℕ) (hb : b ≤ n) :
    ((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < b)).card = b - a := by
  have : ((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < b)).map
      Fin.valEmbedding = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · rintro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map, this, Nat.card_Ico]

/-- The vertices of class `b` in the four-class layout of `Fin n`. -/
def classOf (n : ℕ) (b : Fin 4) : Finset (Fin n) := univ.filter (fun j => quarter n j = b)

/-- Every class of the four-class layout has at least `(n - 3)/4` vertices. -/
lemma card_classOf (n : ℕ) (b : Fin 4) : n ≤ 4 * (classOf n b).card + 3 := by
  have key : ∀ lo hi : ℕ, hi ≤ n → (∀ j : Fin n, quarter n j = b ↔ lo ≤ j.val ∧ j.val < hi) →
      (classOf n b).card = hi - lo := by
    intro lo hi hhi h
    rw [← card_filter_fin_interval n lo hi hhi]
    congr 1; ext j; simp [classOf, h j]
  fin_cases b
  · rw [key 0 (n / 2 / 2) (by omega) (fun j => by
      simp only [quarter]; split_ifs <;> simp <;> omega)]; omega
  · rw [key (n / 2 / 2) (n / 2) (by omega) (fun j => by
      simp only [quarter]; split_ifs <;> simp <;> omega)]; omega
  · rw [key (n / 2) (n / 2 + (n - n / 2) / 2) (by omega) (fun j => by
      simp only [quarter]; split_ifs <;> simp <;> omega)]; omega
  · rw [key (n / 2 + (n - n / 2) / 2) n le_rfl (fun j => by
      simp only [quarter]; split_ifs <;> simp <;> omega)]; omega

lemma quarter_lt_two_iff (n : ℕ) (j : Fin n) : (quarter n j).val < 2 ↔ j.val < n / 2 := by
  simp only [quarter]; split_ifs <;> simp <;> omega

lemma card_filter_mem_sym2_le {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V) :
    (univ.filter (fun v => v ∈ e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    calc (univ.filter (fun v => v ∈ s(a, b))).card ≤ ({a, b} : Finset V).card := by
          apply card_le_card; intro v; simp
      _ ≤ 2 := card_le_two

/-- Handshake bound: the incidences of an edge set `D` number at most `2 |D|`. -/
lemma sum_card_incident_le {V : Type*} [Fintype V] [DecidableEq V] (D : Finset (Sym2 V))
    (B : Finset V) : ∑ v ∈ B, (D.filter (fun e => v ∈ e)).card ≤ 2 * D.card := by
  calc ∑ v ∈ B, (D.filter (fun e => v ∈ e)).card
      ≤ ∑ v, (D.filter (fun e => v ∈ e)).card :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ e ∈ D, (univ.filter (fun v => v ∈ e)).card := by
        simp only [card_eq_sum_ones, sum_filter]
        rw [sum_comm]
    _ ≤ ∑ e ∈ D, 2 := sum_le_sum fun e _ => card_filter_mem_sym2_le e
    _ = 2 * D.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Closeness to a graph with the two structural features above implies extremality. -/
theorem extremal_of_isClose_generic {β : ℝ} {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (hn : Fintype.card V = n)
    (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (hnon : ∀ i, ∃ b, ∀ j, quarter n j = b → ¬ X.Adj i j)
    (hcross : ∀ i j, (quarter n i).val < 2 → ¬ (quarter n j).val < 2 → X.Adj i j)
    (hnβ : 2 ≤ β * n) {α : ℝ} (hα1 : α ≤ β ^ 2 / 8) (hα2 : α ≤ β / 8)
    (hc : IsClose α G X) : IsExtremal β G := by
  obtain ⟨e, hD⟩ := hc
  unfold IsExtremal
  rw [hn] at hD ⊢
  have hcardV : (univ : Finset V).card = n := by rw [card_univ, hn]
  set X' := SimpleGraph.comap (⇑e) X
  set D := symmDiff G.edgeFinset X'.edgeFinset with hD_def
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ β * n := by linarith
  -- membership in `D`
  have memD_of_G : ∀ u w, G.Adj u w → ¬ X.Adj (e u) (e w) → s(u, w) ∈ D := by
    intro u w h1 h2
    rw [hD_def, mem_symmDiff]
    left; refine ⟨by simpa using h1, ?_⟩
    simpa [X'] using h2
  have memD_of_X : ∀ u w, X.Adj (e u) (e w) → ¬ G.Adj u w → s(u, w) ∈ D := by
    intro u w h1 h2
    rw [hD_def, mem_symmDiff]
    right; refine ⟨by simpa [X'] using h1, by simpa using h2⟩
  constructor
  · -- degree condition
    set B := univ.filter (fun v => ¬ (G.degree v : ℝ) ≤ (3 / 4 + β) * n) with hB
    have hbad : ∀ v ∈ B, β * n / 2 ≤ ((D.filter (fun f => v ∈ f)).card : ℝ) := by
      intro v hv
      simp only [hB, mem_filter, mem_univ, true_and, not_le] at hv
      obtain ⟨b, hb⟩ := hnon (e v)
      set K := univ.filter (fun w => quarter n (e w) = b)
      have hK : (K.card : ℕ) = (classOf n b).card := by
        apply card_bij (fun w _ => e w)
        · intro w hw; simpa [classOf, K] using hw
        · intro w₁ _ w₂ _ h; exact e.injective h
        · intro j hj; exact ⟨e.symm j, by simpa [K, classOf] using hj, by simp⟩
      have hcl := card_classOf n b
      -- neighbours of `v` inside `K` give edges of `D`
      have hsplit : G.degree v ≤ (Kᶜ).card + (D.filter (fun f => v ∈ f)).card := by
        rw [← G.card_neighborFinset_eq_degree]
        have : G.neighborFinset v ⊆ Kᶜ ∪ (G.neighborFinset v ∩ K) := by
          intro w hw; by_cases hwK : w ∈ K
          · exact mem_union_right _ (mem_inter.mpr ⟨hw, hwK⟩)
          · exact mem_union_left _ (mem_compl.mpr hwK)
        refine (card_le_card this).trans ((card_union_le _ _).trans ?_)
        gcongr
        apply card_le_card_of_injOn (fun w => s(v, w))
        · intro w hw
          simp only [coe_inter, Set.mem_inter_iff, mem_coe, SimpleGraph.mem_neighborFinset]
            at hw
          simp only [coe_filter, Set.mem_setOf_eq]
          refine ⟨memD_of_G v w hw.1 (hb (e w) ?_), Sym2.mem_mk_left _ _⟩
          simpa [K] using hw.2
        · intro w₁ _ w₂ _ h
          rcases (by simpa using h : w₁ = w₂ ∨ v = w₂ ∧ w₁ = v) with h | ⟨h1, h2⟩
          · exact h
          · exact h2.trans h1
      have hKc : (Kᶜ).card + K.card = n := by
        rw [add_comm, card_add_card_compl, hn]
      have h1 : (G.degree v : ℝ) ≤ (Kᶜ).card + (D.filter (fun f => v ∈ f)).card := by
        exact_mod_cast hsplit
      have h2 : ((Kᶜ).card : ℝ) + K.card = n := by exact_mod_cast hKc
      have h3 : (n : ℝ) ≤ 4 * K.card + 3 := by rw [hK]; exact_mod_cast hcl
      nlinarith
    have hsum : β * n / 2 * B.card ≤ 2 * α * n ^ 2 := by
      have h1 : ∑ v ∈ B, β * n / 2 ≤ ∑ v ∈ B, ((D.filter (fun f => v ∈ f)).card : ℝ) :=
        sum_le_sum hbad
      have h2 : (∑ v ∈ B, ((D.filter (fun f => v ∈ f)).card : ℝ)) ≤ 2 * D.card := by
        exact_mod_cast sum_card_incident_le D B
      rw [sum_const, nsmul_eq_mul] at h1
      nlinarith
    have hBcard : (B.card : ℝ) ≤ β * n / 2 := by
      by_contra hcon
      push_neg at hcon
      have hβn : 0 < β * n := by linarith
      have : β * n / 2 * (β * n / 2) < β * n / 2 * B.card :=
        mul_lt_mul_of_pos_left hcon (by linarith)
      nlinarith
    have hcompl : (univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + β) * n)).card + B.card
        = n := by
      rw [hB, card_filter_add_card_filter_not, hcardV]
    have : ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + β) * n)).card : ℝ) + B.card
        = n := by exact_mod_cast hcompl
    nlinarith
  · -- the cut between the two halves
    set S := univ.filter (fun v => (e v).val < n / 2) with hS
    refine ⟨S, ?_⟩
    have hScard : S.card = n / 2 := by
      have : S.card = ((univ : Finset (Fin n)).filter (fun j => 0 ≤ j.val ∧ j.val < n / 2)).card
          := by
        apply card_bij (fun w _ => e w)
        · intro w hw; simpa [S] using hw
        · intro w₁ _ w₂ _ h; exact e.injective h
        · intro j hj; exact ⟨e.symm j, by simpa [S] using hj, by simp⟩
      rw [this, card_filter_fin_interval n 0 (n / 2) (by omega)]; simp
    have hScompl : (Sᶜ).card = n - n / 2 := by
      have := card_add_card_compl S
      rw [hScard, hn] at this; omega
    -- every pair across the cut is an edge of `G` or an element of `D`
    have hpairs : (S ×ˢ Sᶜ).card ≤ cutSize G S + D.card := by
      have hsub : (S ×ˢ Sᶜ).image (fun p => s(p.1, p.2)) ⊆
          G.edgeFinset.filter (fun f => ∃ u v, f = s(u, v) ∧ u ∈ S ∧ v ∉ S) ∪ D := by
        intro f hf
        simp only [mem_image, mem_product, mem_compl] at hf
        obtain ⟨⟨u, w⟩, ⟨hu, hw⟩, rfl⟩ := hf
        by_cases hG : G.Adj u w
        · exact mem_union_left _ (mem_filter.mpr ⟨by simpa using hG, u, w, rfl, hu, hw⟩)
        · refine mem_union_right _ (memD_of_X u w ?_ hG)
          apply hcross
          · rw [quarter_lt_two_iff]; simpa [S] using hu
          · rw [quarter_lt_two_iff]; simpa [S] using hw
      have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (S ×ˢ Sᶜ : Finset (V × V)) := by
        intro p hp q hq h
        simp only [coe_product, Set.mem_prod, mem_coe, coe_compl, Set.mem_compl_iff] at hp hq
        simp only [Sym2.eq_iff] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · exact absurd (h1 ▸ hp.1) hq.2
      rw [← card_image_of_injOn hinj]
      exact (card_le_card hsub).trans (card_union_le _ _)
    rw [card_product, hScard, hScompl] at hpairs
    have hprod : (n : ℝ) ^ 2 - 1 ≤ 4 * ((n / 2 : ℕ) : ℝ) * ((n - n / 2 : ℕ) : ℝ) := by
      have : n ^ 2 ≤ 4 * (n / 2) * (n - n / 2) + 1 := by
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · have h1 : 2 * k / 2 = k := by omega
          have h2 : 2 * k - k = k := by omega
          rw [h1, h2]; ring_nf; omega
        · have h1 : (2 * k + 1) / 2 = k := by omega
          have h2 : 2 * k + 1 - k = k + 1 := by omega
          rw [h1, h2]; ring_nf; omega
      have : ((n ^ 2 : ℕ) : ℝ) ≤ ((4 * (n / 2) * (n - n / 2) + 1 : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at this; linarith
    have hpairsR : ((n / 2 : ℕ) : ℝ) * ((n - n / 2 : ℕ) : ℝ) ≤ cutSize G S + D.card := by
      exact_mod_cast hpairs
    have hnpos : (1 : ℝ) ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0] at hnβ; simp at hnβ; linarith
      · exact_mod_cast h0
    have hn2 : (2 : ℝ) ≤ β * n ^ 2 := by nlinarith
    have hαn : α * n ^ 2 ≤ β / 8 * n ^ 2 := mul_le_mul_of_nonneg_right hα2 (sq_nonneg _)
    nlinarith

/-- Closeness to an extremal graph implies extremality. -/
theorem extremal_of_isCloseToExtremal {β : ℝ} (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], n₀ ≤ Fintype.card V → ∀ α : ℝ, α ≤ β ^ 2 / 8 → α ≤ β / 8 →
        IsCloseToExtremal α G → IsExtremal β G := by
  refine ⟨⌈2 / β⌉₊, fun V _ _ G _ hn α hα1 hα2 hc => ?_⟩
  have hnβ : 2 ≤ β * Fintype.card V := by
    have : 2 / β ≤ Fintype.card V := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hβ] at this; linarith
  have gen : ∀ (P : Fin 4 → Fin 4 → Bool) (hP : ∀ a b, P a b = P b a),
      (∀ a, ∃ b, P a b = false) → (∀ a b : Fin 4, a.val < 2 → ¬ b.val < 2 → P a b = true) →
      ∀ [DecidableRel (patternGraph (Fintype.card V) P hP).Adj],
      IsClose α G (patternGraph (Fintype.card V) P hP) → IsExtremal β G := by
    intro P hP hnon hcross _ hc
    refine extremal_of_isClose_generic G rfl _ (fun i => ?_) (fun i j hi hj => ?_) hnβ hα1 hα2
      hc
    · obtain ⟨b, hb⟩ := hnon (quarter _ i)
      exact ⟨b, fun j hj h => by simp [patternGraph, hj, hb] at h⟩
    · refine ⟨fun h => ?_, hcross _ _ hi hj⟩
      subst h; exact hj hi
  rcases hc with hc | hc | hc
  · exact gen patT2T2 _ (by decide) (by decide) hc
  · exact gen patT2bT2 _ (by decide) (by decide) hc
  · exact gen patT2bT2b _ (by decide) (by decide) hc

end NashWilliams18
