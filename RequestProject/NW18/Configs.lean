/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.FinalGlue

/-!
# The configuration count for Lemma 14.4

If a graph with `δ(G) ≥ 3n/4` has few homomorphic copies of both model hinges on two triangles
`u₁u₂v₁`, `u₁u₂v₂`, then it is close to one of the three extremal graphs (`close_of_few_homs`).
Consequently (`lemma_14_4_configs`), a graph that is not close to the extremal graphs has
`Ω(n⁴)` configurations of type 1 or of type 2.
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Phase 2.**  Among the sets `D w` (`w ∈ L`), all large, one carries a structure. -/
lemma phase2 (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (L : Finset V) (Dof : V → Finset V)
    (v₁ v₂ : V) {s c : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100) (hn0 : 0 < Fintype.card V)
    (hDlarge : ∀ w ∈ L, (1 / 2 - s ^ 2 / 50) * Fintype.card V ≤ (Dof w).card)
    (hL : (Fintype.card V : ℝ) / 8 ≤ L.card)
    (hW : ∑ w ∈ L, (walk4 G (Dof w) v₁ v₂ : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 4)
    (hc : 216 * c ≤ s ^ 6) :
    ∃ w ∈ L, ∃ B₁ ⊆ Dof w, ∃ b₂ : Bool, ∃ E₂ ⊆ Dof w,
      (E₂.card : ℝ) ≤ 20 * s * (Dof w).card ∧
      (∀ x ∈ Dof w, x ∉ E₂ →
        ((symmDiff (nbIn G (Dof w) x) (tgt (Dof w) B₁ b₂ x)).card : ℝ) ≤ 20 * s * (Dof w).card) ∧
      (B₁.card : ℝ) ≤ (1 / 2 + s ^ 2) * (Dof w).card + 20 * s * (Dof w).card ∧
      (((Dof w) \ B₁).card : ℝ) ≤ (1 / 2 + s ^ 2) * (Dof w).card + 20 * s * (Dof w).card := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hLne : L.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < L.card := by linarith
    exact_mod_cast this
  obtain ⟨w, hwL, hw⟩ := exists_mul_card_le_sum L hLne (fun w => (walk4 G (Dof w) v₁ v₂ : ℝ))
  set D := Dof w with hD
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have hDl := hDlarge w hwL
  have hD3 : n / 3 ≤ (D.card : ℝ) := by nlinarith
  have hD0 : 0 < D.card := by
    have : (0 : ℝ) < D.card := by linarith
    exact_mod_cast this
  have hwalk : (walk4 G D v₁ v₂ : ℝ) ≤ s ^ 6 * (D.card : ℝ) ^ 3 := by
    have h1 : (walk4 G D v₁ v₂ : ℝ) * (n / 8) ≤ c * n ^ 4 := by
      calc _ ≤ (walk4 G D v₁ v₂ : ℝ) * L.card := mul_le_mul_of_nonneg_left hL (by positivity)
        _ ≤ _ := hw.trans hW
    have hc0 : 0 ≤ c * n ^ 4 := le_trans (by positivity) h1
    have hc0' : 0 ≤ c := by
      by_contra h; push_neg at h
      have : c * n ^ 4 < 0 := mul_neg_of_neg_of_pos h (by positivity)
      linarith
    have h2 : (walk4 G D v₁ v₂ : ℝ) ≤ 8 * c * n ^ 3 := by
      have : (walk4 G D v₁ v₂ : ℝ) * n ≤ (8 * c * n ^ 3) * n := by nlinarith
      exact le_of_mul_le_mul_right this hn0'
    have h3 : (n / 3) ^ 3 ≤ (D.card : ℝ) ^ 3 := by gcongr
    have h4 : 8 * c * n ^ 3 ≤ s ^ 6 * (n / 3) ^ 3 := by
      have : s ^ 6 * (n / 3) ^ 3 = (s ^ 6 / 27) * n ^ 3 := by ring
      rw [this]
      have : 8 * c ≤ s ^ 6 / 27 := by linarith
      have : 0 ≤ n ^ 3 := by positivity
      nlinarith
    have h5 : s ^ 6 * (n / 3) ^ 3 ≤ s ^ 6 * (D.card : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hdeg : ∀ y, (1 / 2 - s ^ 2) * (D.card : ℝ) ≤ (nbIn G D y).card := by
    intro y
    have h1 := card_nbIn_ge G hδ D y
    have : n / 4 ≤ (1 / 2 + s ^ 2) * D.card := by nlinarith
    linarith
  obtain ⟨B₁, hB₁, b₂, E₂, hE₂, hE₂c, hdev, hs1, ht1⟩ :=
    stab4 G D v₁ v₂ (ε := s ^ 2) (κ := s ^ 6) hs0 (by linarith) (by positivity) le_rfl le_rfl
      hD0 hdeg hwalk
  refine ⟨w, hwL, B₁, hB₁, b₂, E₂, hE₂, hE₂c, hdev, ?_, ?_⟩
  · have h1 := card_ge_of_symmDiff (nbIn G D v₂) (D \ B₁)
    have h2 := hdeg v₂
    have h3 : (B₁.card : ℝ) + (D \ B₁).card = D.card := by
      have := card_sdiff_of_subset' hB₁
      exact_mod_cast (by omega : B₁.card + (D \ B₁).card = D.card)
    nlinarith
  · have h1 := card_ge_of_symmDiff (nbIn G D v₁) B₁
    have h2 := hdeg v₁
    have h3 : (B₁.card : ℝ) + (D \ B₁).card = D.card := by
      have := card_sdiff_of_subset' hB₁
      exact_mod_cast (by omega : B₁.card + (D \ B₁).card = D.card)
    nlinarith

/-- **Few homomorphic hinges force closeness.**  If a graph with `δ(G) ≥ 3n/4` has at most
`c n⁴` homomorphic copies of each of the two model hinges on `u₁, u₂, v₁, v₂`, where `c` is
small compared to `s`, then it is `300 s`-close to one of the three extremal graphs. -/
theorem close_of_few_homs (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (u₁ u₂ v₁ v₂ : V)
    {s c : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 100) (hsn : 2 ≤ s * Fintype.card V)
    (hc : c ≤ (s ^ 2 / 10000) ^ 6 / 500)
    (hW₁ : (homCount mH1 G u₁ u₂ v₁ v₂ : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 4)
    (hW₂ : (homCount mH2 G u₁ u₂ v₁ v₂ : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 4) :
    IsCloseToExtremal (6 * (50 * s)) G := by
  have hn0 : (0 : ℝ) < Fintype.card V := by nlinarith
  have hn0' : 0 < Fintype.card V := by exact_mod_cast hn0
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set N := comNb G v₁ v₂ with hN
  set σ₁ : ℝ := s ^ 2 / 10000 with hσ₁
  have hσ₁0 : 0 < σ₁ := by positivity
  have hs2 : s ^ 2 ≤ s / 100 := by nlinarith
  have hσ₁s : σ₁ ≤ s / 1000000 := by rw [hσ₁]; linarith
  have hσ₁1 : σ₁ ≤ 1 / 240 := by linarith
  have hσ₁6 : σ₁ ^ 6 ≤ σ₁ := pow_le_of_le_one hσ₁0.le (by linarith) (by norm_num)
  have hσ₁6' : σ₁ ^ 6 ≤ s ^ 6 := pow_le_pow_left₀ hσ₁0.le (by linarith) 6
  have hc6 : 0 ≤ σ₁ ^ 6 := by positivity
  have hm1 := card_comNb_ge G hδ v₁ v₂
  have hdegN := card_nbIn_ge G hδ N
  have hW₁' : ∑ d ∈ nbIn G N u₂, (walk4 G N u₁ d : ℝ) ≤ c * n ^ 4 := by
    have := walk_le_hom1 G u₁ u₂ v₁ v₂
    have h' : (∑ d ∈ nbIn G N u₂, walk4 G N u₁ d : ℝ) ≤ (homCount mH1 G u₁ u₂ v₁ v₂ : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hn4 : 0 < n ^ 4 := by positivity
  -- `|N| ≤ (1/2 + s²/100) n`
  have hm2 : (N.card : ℝ) ≤ (1 / 2 + s ^ 2 / 100) * n := by
    by_contra h
    push_neg at h
    have h1 := phase1a G N u₁ u₂ (γ := s ^ 2 / 100) (by positivity) hdegN h.le
    have h2 : c * n ^ 4 < s ^ 2 / 100 * n ^ 4 / 64 := by
      have : c < s ^ 2 / 100 / 64 := by
        have : σ₁ ^ 6 / 500 < s ^ 2 / 100 / 64 := by
          have : σ₁ < s ^ 2 / 100 / 64 * 500 := by rw [hσ₁]; nlinarith
          linarith
        linarith
      have := mul_lt_mul_of_pos_right this hn4
      linarith
    linarith
  -- Phase 1
  obtain ⟨N₁, hN₁, b₁, E₁, hE₁, hE₁c, hdev₁, hN₁c, hN₂c, hu₂⟩ :=
    phase1 G N u₁ u₂ hσ₁0 hσ₁1 hn0' hm1 hdegN (by
      have : c ≤ σ₁ ^ 6 / 32 := by linarith
      have := mul_le_mul_of_nonneg_right this hn4.le
      linarith)
  have hmn : (N.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast card_le_univ N
  have he1 : 20 * σ₁ * N.card ≤ s ^ 2 * n / 500 := by
    have : 20 * σ₁ * N.card ≤ 20 * σ₁ * n := mul_le_mul_of_nonneg_left hmn (by positivity)
    have : 20 * σ₁ * n = s ^ 2 * n / 500 := by rw [hσ₁]; ring
    linarith
  -- the vertices `w`
  set L := nbIn G N u₁ \ E₁ with hL
  have hLc : n / 8 ≤ (L.card : ℝ) := by
    have h1 := card_sdiff_ge (nbIn G N u₁) E₁
    have h2 := hdegN u₁
    have : s ^ 2 * n / 500 ≤ n / 8 := by nlinarith
    linarith
  set Dof : V → Finset V := fun w => (univ \ N).filter (fun y => G.Adj w y ∧ G.Adj u₂ y)
    with hDof
  have hrest : ∀ w ∈ L, (((univ \ N) \ Dof w).card : ℝ) ≤ 90 * σ₁ * n := by
    intro w hw
    obtain ⟨hwN, hwE⟩ := mem_sdiff.mp hw
    have hwN' : w ∈ N := nbIn_subset G N u₁ hwN
    have h1 := cross_bound G hδ (univ \ N) w
    rw [Finset.sdiff_sdiff_eq_self (subset_univ N)] at h1
    have h2 := card_nbIn_le_tgt G N N₁ b₁ w (hdev₁ w hwN' hwE)
    have h3 := card_tgt_le N N₁ b₁ w hN₁c hN₂c
    have h4 := cross_bound G hδ (univ \ N) u₂
    rw [Finset.sdiff_sdiff_eq_self (subset_univ N)] at h4
    have hsub : (univ \ N) \ Dof w ⊆ ((univ \ N) \ univ.filter (G.Adj w)) ∪
        ((univ \ N) \ univ.filter (G.Adj u₂)) := by
      intro y hy
      simp only [hDof, mem_sdiff, mem_filter, mem_univ, true_and, not_and, mem_union] at hy ⊢
      tauto
    have h5 : (((univ \ N) \ Dof w).card : ℝ) ≤ ((univ \ N) \ univ.filter (G.Adj w)).card +
        ((univ \ N) \ univ.filter (G.Adj u₂)).card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have h6 : 50 * σ₁ * N.card ≤ 50 * σ₁ * n := mul_le_mul_of_nonneg_left hmn (by positivity)
    have h7 : 20 * σ₁ * N.card ≤ 20 * σ₁ * n := mul_le_mul_of_nonneg_left hmn (by positivity)
    linarith
  have hbm : ((univ \ N).card : ℝ) + N.card = n := by
    have := card_sdiff_of_subset' (subset_univ N)
    rw [card_univ] at this; rw [hn]; exact_mod_cast this
  have h90 : 90 * σ₁ * n ≤ s ^ 2 * n / 100 := by
    have e : 90 * σ₁ * n = (9 / 1000) * (s ^ 2 * n) := by rw [hσ₁]; ring
    have : 0 ≤ s ^ 2 * n := by positivity
    rw [e]; linarith
  have hDlarge : ∀ w ∈ L, (1 / 2 - s ^ 2 / 50) * n ≤ (Dof w).card := by
    intro w hw
    have h1 := hrest w hw
    have h2 : (((univ \ N) \ Dof w).card : ℝ) + (Dof w).card = (univ \ N).card := by
      exact_mod_cast card_sdiff_of_subset' (filter_subset _ _)
    clear_value Dof L σ₁ N n
    linarith
  have hW₂' : ∑ w ∈ L, (walk4 G (Dof w) v₁ v₂ : ℝ) ≤ c * n ^ 4 := by
    have := walk_le_hom2 G u₁ u₂ v₁ v₂ L Dof
      (fun w hw => by
        obtain ⟨hwN, -⟩ := mem_sdiff.mp hw
        obtain ⟨hwN', hu⟩ := (mem_nbIn G).mp hwN
        have := (mem_filter.mp hwN').2
        exact ⟨SimpleGraph.Adj.symm hu, SimpleGraph.Adj.symm this.1, SimpleGraph.Adj.symm this.2⟩)
      (fun w _ y hy => (mem_filter.mp hy).2)
    have h' : (∑ w ∈ L, walk4 G (Dof w) v₁ v₂ : ℝ) ≤ (homCount mH2 G u₁ u₂ v₁ v₂ : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  obtain ⟨w, hwL, B₁, hB₁, b₂, E₂, -, hE₂c, hdev₂, hB₁c, hB₂c⟩ :=
    phase2 G hδ L Dof v₁ v₂ hs0 hs hn0' hDlarge hLc hW₂' (by linarith)
  refine final_glue G hδ N N₁ (Dof w) B₁ E₁ E₂ b₁ b₂ hs0 hs hsn hN₁ (filter_subset _ _) hB₁
    hm1 hm2 (by positivity) he1 hE₁c hdev₁ hN₁c hN₂c ?_ hE₂c hdev₂ hB₁c hB₂c
  have := hrest w hwL
  linarith

/-- **Configuration count for Lemma 14.4.**  There is `α₀ > 0` such that for every
`α ∈ (0, α₀]` there are `c > 0` and `n₀` such that: if `G` has `n ≥ n₀` vertices,
`δ(G) ≥ 3n/4` and `G` is not `α`-close to any of the three extremal graphs, then for every two
triangles `u₁u₂v₁`, `u₁u₂v₂` (four distinct vertices) there are at least `c n⁴` configurations of
type 1, or of type 2, or of type 2 with the roles of `u₁, u₂` exchanged. -/
theorem lemma_14_4_configs_proof :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 3 * Fintype.card V ≤ 4 * G.minDegree →
        ¬ IsCloseToExtremal α G →
        ∀ u₁ u₂ v₁ v₂ : V, Function.Injective ![u₁, u₂, v₁, v₂] →
          G.Adj u₁ u₂ → G.Adj u₁ v₁ → G.Adj u₂ v₁ → G.Adj u₁ v₂ → G.Adj u₂ v₂ →
          c * (Fintype.card V : ℝ) ^ 4 ≤ cfgCount mH1 G u₁ u₂ v₁ v₂ ∨
          c * (Fintype.card V : ℝ) ^ 4 ≤ cfgCount mH2 G u₁ u₂ v₁ v₂ ∨
          c * (Fintype.card V : ℝ) ^ 4 ≤ cfgCount mH2 G u₂ u₁ v₁ v₂ := by
  refine ⟨1, one_pos, fun α hα hα1 => ?_⟩
  set s : ℝ := α / 300 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 / 100 := by rw [hs]; linarith
  set c : ℝ := (s ^ 2 / 10000) ^ 6 / 500 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c / 2, by positivity, ⌈2 / s + 44 / c⌉₊, ?_⟩
  intro V _ _ G _ hn hδ hnc u₁ u₂ v₁ v₂ hinj _ _ _ _ _
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, -⟩ := hcon
  apply hnc
  have hnr : 2 / s + 44 / c ≤ (Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < Fintype.card V := by
    have : 0 < 2 / s + 44 / c := by positivity
    linarith
  have hsn : 2 ≤ s * Fintype.card V := by
    have : 2 / s ≤ Fintype.card V := by
      have : 0 ≤ 44 / c := by positivity
      linarith
    rw [div_le_iff₀ hs0] at this; linarith
  have hcn : 22 * (Fintype.card V : ℝ) ^ 3 ≤ c / 2 * (Fintype.card V : ℝ) ^ 4 := by
    have : 44 / c ≤ Fintype.card V := by
      have : 0 ≤ 2 / s := by positivity
      linarith
    rw [div_le_iff₀ hc0] at this
    have h3 : 0 ≤ (Fintype.card V : ℝ) ^ 3 := by positivity
    have : 44 * (Fintype.card V : ℝ) ^ 3 ≤ Fintype.card V * c * (Fintype.card V : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right this h3
    nlinarith
  have hW : ∀ M : Finset (Sym2 (Fin 8)),
      (cfgCount M G u₁ u₂ v₁ v₂ : ℝ) < c / 2 * (Fintype.card V : ℝ) ^ 4 →
      (homCount M G u₁ u₂ v₁ v₂ : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 4 := by
    intro M hM
    have := homCount_le M G hinj
    have h' : (homCount M G u₁ u₂ v₁ v₂ : ℝ) ≤ cfgCount M G u₁ u₂ v₁ v₂ +
        22 * (Fintype.card V : ℝ) ^ 3 := by exact_mod_cast this
    linarith
  have := close_of_few_homs G hδ u₁ u₂ v₁ v₂ hs0 hs1 hsn le_rfl (hW mH1 h1) (hW mH2 h2)
  rwa [show 6 * (50 * s) = α by rw [hs]; ring] at this

end NashWilliams18
