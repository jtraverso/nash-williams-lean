/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Theorem26

/-!
# Proof of Theorem 2.6 from Theorem 1.6 and Lemma 11.6 (Lemma 11.10, averaging)
-/

namespace NashWilliams18

open Finset

lemma choose_ratio (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    (n - 2).choose (k - 2) * (k - 2) = (n - 2) * (n - 3).choose (k - 3) := by
  have h1 : n - 2 = (n - 3) + 1 := by omega
  have h2 : k - 2 = (k - 3) + 1 := by omega
  rw [h1, h2, Nat.add_one_mul_choose_eq]

/-- At most `n - 2` triangles contain two given distinct vertices. -/
lemma card_triangles_through_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) :
    ((G.cliqueFinset 3).filter (fun T => u ∈ T ∧ v ∈ T)).card ≤ Fintype.card V := by
  calc ((G.cliqueFinset 3).filter (fun T => u ∈ T ∧ v ∈ T)).card
      ≤ ((univ.powersetCard 3).filter (fun T => ({u, v} : Finset V) ⊆ T)).card := by
        apply card_le_card
        intro T hT
        simp only [mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hT
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
        refine ⟨hT.1.2, ?_⟩
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hT.2.1
        · exact hT.2.2
    _ ≤ (Fintype.card V - ({u, v} : Finset V).card).choose (3 - ({u, v} : Finset V).card) :=
        card_supsets_le _ 3
    _ ≤ Fintype.card V := by rw [card_pair huv]; simp

/-- **Lemma 11.10** (averaging), in the form used for Theorem 2.6.  Let `Good` be a family of
`k`-sets such that every edge lies in at least `(1 - ρ) C(n-2, k-2)` of them, and on every
`S ∈ Good` every target with values in `[1 - θ, 1]` (where `ε₀ + ρ ≤ θ`) is the load of a
fractional triangle packing of `G[S]`.  Then `G` has a `(1/ε₀ + 4k + 1)`-regular fractional
triangle decomposition. -/
theorem averaging_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Good : Finset (Finset V)) (k : ℕ) (hk3 : 3 ≤ k)
    (hGood : ∀ S ∈ Good, S.card = k) (hn : k + 4 ≤ Fintype.card V)
    {ρ ε₀ θ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hθ : ε₀ + ρ ≤ θ)
    (hcnt : ∀ u v, G.Adj u v → (1 - ρ) * ((Fintype.card V - 2).choose (k - 2) : ℝ) ≤
      ((Good.filter (fun S => u ∈ S ∧ v ∈ S)).card : ℝ))
    (hach : ∀ S ∈ Good, ∀ φ : Sym2 V → ℝ,
      (∀ u v, u ∈ S → v ∈ S → G.Adj u v → 1 - θ ≤ φ s(u, v) ∧ φ s(u, v) ≤ 1) →
      ∃ ψ : Finset V → ℝ, (∀ T, 0 ≤ ψ T) ∧ (∀ T, ¬ T ⊆ S → ψ T = 0) ∧
        (∀ T ∈ G.cliqueFinset 3, ψ T ≤ 1) ∧
        ∀ u v, G.Adj u v → load G ψ u v = if u ∈ S ∧ v ∈ S then φ s(u, v) else 0) :
    ∃ w, IsRegularFracDecomp G (1 / ε₀ + 4 * k + 1) w := by
  classical
  obtain ⟨n, hn_def⟩ : ∃ n, n = Fintype.card V := ⟨_, rfl⟩
  rw [← hn_def] at hn hcnt
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨B, hB_def⟩ : ∃ B, B = (n - 2).choose (k - 2) := ⟨_, rfl⟩
  obtain ⟨M, hM_def⟩ : ∃ M, M = (n - 3).choose (k - 3) := ⟨_, rfl⟩
  rw [← hB_def] at hcnt
  have hBpos : 0 < B := by rw [hB_def]; exact Nat.choose_pos (by omega)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  obtain ⟨h₀, hh₀_def⟩ : ∃ h₀ : ℝ, h₀ = (1 - ρ) * B := ⟨_, rfl⟩
  rw [← hh₀_def] at hcnt
  have hh₀ : 0 < h₀ := by
    have : 0 < 1 - ρ := by linarith
    rw [hh₀_def]; positivity
  obtain ⟨w₀, hw₀_def⟩ : ∃ w₀ : ℝ, w₀ = ε₀ / n := ⟨_, rfl⟩
  obtain ⟨cntF, hcntF_def⟩ : ∃ f : V → V → ℕ,
      ∀ u v, f u v = ((G.cliqueFinset 3).filter (fun T => u ∈ T ∧ v ∈ T)).card :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨cntH, hcntH_def⟩ : ∃ f : V → V → ℕ,
      ∀ u v, f u v = (Good.filter (fun S => u ∈ S ∧ v ∈ S)).card := ⟨_, fun _ _ => rfl⟩
  have hcntF_symm : ∀ u v, cntF u v = cntF v u := by
    intro u v; rw [hcntF_def, hcntF_def]; simp only [and_comm]
  have hcntH_symm : ∀ u v, cntH u v = cntH v u := by
    intro u v; rw [hcntH_def, hcntH_def]; simp only [and_comm]
  have hcntF_le : ∀ u v, u ≠ v → cntF u v ≤ n := by
    intro u v huv; rw [hcntF_def, hn_def]; exact card_triangles_through_le G huv
  have hcntH_le : ∀ u v, u ≠ v → cntH u v ≤ B := by
    intro u v huv
    rw [hcntH_def]
    calc (Good.filter (fun S => u ∈ S ∧ v ∈ S)).card
        ≤ ((univ.powersetCard k).filter (fun S => ({u, v} : Finset V) ⊆ S)).card := by
          apply card_le_card
          intro S hS
          simp only [mem_filter] at hS
          simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
          refine ⟨hGood S hS.1, ?_⟩
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hS.2.1
          · exact hS.2.2
      _ ≤ (Fintype.card V - ({u, v} : Finset V).card).choose (k - ({u, v} : Finset V).card) :=
          card_supsets_le _ k
      _ = B := by rw [card_pair huv, hB_def, hn_def]
  have hcntH_ge : ∀ u v, G.Adj u v → h₀ ≤ cntH u v := by
    intro u v huv; rw [hcntH_def]; exact hcnt u v huv
  -- the target loads
  obtain ⟨φ, hφuv⟩ : ∃ φ : Sym2 V → ℝ,
      ∀ u v, φ s(u, v) = (1 - w₀ * cntF u v) * h₀ / cntH u v :=
    ⟨Sym2.lift ⟨fun u v => (1 - w₀ * cntF u v) * h₀ / cntH u v, fun u v => by
      dsimp (config := { failIfUnchanged := false }) only; rw [hcntF_symm u v, hcntH_symm u v]⟩, fun _ _ => rfl⟩
  have hφ_bounds : ∀ u v, G.Adj u v → 1 - θ ≤ φ s(u, v) ∧ φ s(u, v) ≤ 1 := by
    intro u v huv
    rw [hφuv]
    have hF : (cntF u v : ℝ) ≤ n := by exact_mod_cast hcntF_le u v huv.ne
    have hH1 := hcntH_ge u v huv
    have hH2 : (cntH u v : ℝ) ≤ B := by exact_mod_cast hcntH_le u v huv.ne
    have hHpos : (0 : ℝ) < cntH u v := lt_of_lt_of_le hh₀ hH1
    have hwF : w₀ * cntF u v ≤ ε₀ := by
      rw [hw₀_def, div_mul_eq_mul_div, div_le_iff₀ hnpos]
      exact mul_le_mul_of_nonneg_left hF hε₀.le
    have hwF0 : 0 ≤ w₀ * cntF u v := by rw [hw₀_def]; positivity
    have hratio1 : h₀ / cntH u v ≤ 1 := by rw [div_le_one hHpos]; exact hH1
    have hratio2 : 1 - ρ ≤ h₀ / cntH u v := by
      rw [le_div_iff₀ hHpos, hh₀_def]
      have : 0 ≤ 1 - ρ := by linarith
      exact mul_le_mul_of_nonneg_left hH2 this
    rw [mul_div_assoc]
    constructor
    · have : (1 - ε₀) * (1 - ρ) ≤ (1 - w₀ * cntF u v) * (h₀ / cntH u v) :=
        mul_le_mul (by linarith) hratio2 (by linarith) (by linarith)
      nlinarith
    · calc (1 - w₀ * cntF u v) * (h₀ / cntH u v) ≤ 1 * 1 :=
            mul_le_mul (by linarith) hratio1 (by positivity) (by norm_num)
        _ = 1 := by norm_num
  have hach' : ∀ S ∈ Good, ∃ ψ : Finset V → ℝ, (∀ T, 0 ≤ ψ T) ∧ (∀ T, ¬ T ⊆ S → ψ T = 0) ∧
      (∀ T ∈ G.cliqueFinset 3, ψ T ≤ 1) ∧
      ∀ u v, G.Adj u v → load G ψ u v = if u ∈ S ∧ v ∈ S then φ s(u, v) else 0 :=
    fun S hS => hach S hS φ (fun u v _ _ huv => hφ_bounds u v huv)
  choose! ψ hψ0 hψS hψ1 hψload using hach'
  -- the averaged weighting
  refine ⟨fun T => w₀ + (1 / h₀) * ∑ S ∈ Good, ψ S T, ⟨fun T => ?_, fun u v huv => ?_⟩,
    fun T hT => ?_⟩
  · have : 0 ≤ ∑ S ∈ Good, ψ S T := sum_nonneg fun S hS => hψ0 S hS T
    have : 0 ≤ w₀ := by rw [hw₀_def]; positivity
    positivity
  · -- the loads are all `1`
    have hsplit : ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t,
        (w₀ + (1 / h₀) * ∑ S ∈ Good, ψ S t) =
        w₀ * cntF u v + (1 / h₀) * ∑ S ∈ Good, load G (ψ S) u v := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, hcntF_def, mul_comm]
      congr 2
      unfold load
      rw [sum_comm]
    rw [hsplit]
    have hsum : ∑ S ∈ Good, load G (ψ S) u v = cntH u v * φ s(u, v) := by
      rw [sum_congr rfl fun S hS => hψload S hS u v huv, ← sum_filter, sum_const,
        nsmul_eq_mul, hcntH_def]
    rw [hsum, hφuv]
    have hHpos : (0 : ℝ) < cntH u v := lt_of_lt_of_le hh₀ (hcntH_ge u v huv)
    field_simp
    ring
  · -- regularity
    rw [← hn_def]
    have hTsum : ∑ S ∈ Good, ψ S T ≤ M := by
      have hT3 : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hT).2
      have hcard : (Good.filter (fun S => T ⊆ S)).card ≤ M := by
        calc (Good.filter (fun S => T ⊆ S)).card ≤
            ((univ.powersetCard k).filter (fun S => T ⊆ S)).card := by
              apply card_le_card
              intro S hS
              simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS ⊢
              exact ⟨hGood S hS.1, hS.2⟩
          _ ≤ (Fintype.card V - T.card).choose (k - T.card) := card_supsets_le T k
          _ = M := by rw [hT3, hM_def, hn_def]
      calc ∑ S ∈ Good, ψ S T = ∑ S ∈ Good.filter (fun S => T ⊆ S), ψ S T := by
            rw [sum_filter_of_ne]
            intro S hS hne
            by_contra h
            exact hne (hψS S hS T h)
        _ ≤ ∑ S ∈ Good.filter (fun S => T ⊆ S), (1 : ℝ) :=
            sum_le_sum fun S hS => hψ1 S (mem_filter.mp hS).1 T hT
        _ = (Good.filter (fun S => T ⊆ S)).card := by simp
        _ ≤ M := by exact_mod_cast hcard
    have hTnonneg : 0 ≤ ∑ S ∈ Good, ψ S T := sum_nonneg fun S hS => hψ0 S hS T
    have hrest : 0 ≤ (1 / h₀) * ∑ S ∈ Good, ψ S T := by positivity
    constructor
    · have h1 : 1 / ((1 / ε₀ + 4 * k + 1) * n) ≤ ε₀ / n := by
        rw [div_le_div_iff₀ (by positivity) hnpos]
        have h2 : 1 ≤ ε₀ * (1 / ε₀ + 4 * k + 1) := by
          rw [mul_add, mul_add, mul_one_div_cancel hε₀.ne']
          have : 0 ≤ ε₀ * (4 * k) := by positivity
          linarith
        nlinarith
      rw [← hw₀_def] at h1
      linarith
    · -- `M / h₀ ≤ 4k/n`
      have hratio : (B : ℝ) * (k - 2) = (n - 2) * M := by
        have := choose_ratio n k (by omega) hk3
        rw [← hB_def, ← hM_def] at this
        have h' : ((B * (k - 2) : ℕ) : ℝ) = (((n - 2) * M : ℕ) : ℝ) := by rw [this]
        push_cast [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 2 ≤ n by omega)] at h'
        linarith
      have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hMh : (M : ℝ) / h₀ ≤ 4 * k / n := by
        rw [div_le_div_iff₀ hh₀ hnpos, hh₀_def]
        have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
        have h1 : (M : ℝ) * (n - 2) ≤ B * k := by nlinarith
        have h3 : (1 : ℝ) / 2 ≤ 1 - ρ := by linarith
        have h4 : (M : ℝ) * n ≤ 2 * (B * k) := by nlinarith
        nlinarith
      have hstep : (1 / h₀) * ∑ S ∈ Good, ψ S T ≤ M / h₀ := by
        rw [one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right hTsum hh₀.le
      calc w₀ + (1 / h₀) * ∑ S ∈ Good, ψ S T ≤ ε₀ / n + 4 * k / n := by
            rw [hw₀_def]; linarith
        _ ≤ (1 / ε₀ + 4 * k + 1) / n := by
            rw [← add_div]
            apply div_le_div_of_nonneg_right _ hnpos.le
            have : 1 ≤ 1 / ε₀ := by rw [le_div_iff₀ hε₀]; linarith
            linarith

/-- **Theorem 2.6.** For each sufficiently small `σ > 0` there are `ε > 0` and `C ≥ 1` such that
for all large `n`: every graph `G` on `n` vertices with `δ(G) ≥ (3/4 - ε) n` that has no
`C`-regular fractional triangle decomposition is `σ`-extremal.
Proved from Theorem 1.6 and Lemma 11.6 by the averaging argument of Lemma 11.10. -/
theorem theorem_2_6 :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        (¬ ∃ w, IsRegularFracDecomp G C w) → IsExtremal σ G := by
  classical
  obtain ⟨σ₀, hσ₀, h16⟩ := theorem_1_6
  refine ⟨4 * σ₀, by positivity, fun σ hσ hσσ₀ => ?_⟩
  obtain ⟨ε₁, hε₁, n₁, h16'⟩ := h16 (σ / 4) (by positivity) (by linarith)
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = min (ε₁ / 2) (σ / 4) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; exact lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε₁ / 2 := by rw [hη_def]; exact min_le_left _ _
  have hησ : η ≤ σ / 4 := by rw [hη_def]; exact min_le_right _ _
  obtain ⟨C', hC'_def⟩ : ∃ C' : ℕ, C' = ⌈8 / η⌉₊ + 1 := ⟨_, rfl⟩
  have hC'1 : 1 ≤ C' := by omega
  have hC'R : (1 : ℝ) ≤ C' := by exact_mod_cast hC'1
  have hC'η : 8 / η ≤ (C' : ℝ) := by
    calc 8 / η ≤ ⌈8 / η⌉₊ := Nat.le_ceil _
      _ ≤ (C' : ℝ) := by rw [hC'_def]; push_cast; linarith
  have hρ : (0 : ℝ) < 1 / (2 * C') := by positivity
  have hρ2 : 1 / (2 * (C' : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hε₀1 : 1 / (2 * (C' : ℝ)) ≤ 1 := by linarith
  have hθ : 1 / (2 * (C' : ℝ)) + 1 / (2 * C') ≤ 1 / C' := by
    rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨k₀, hk₀⟩ := lemma_11_6 (η / 4) (1 / (2 * C')) σ (by positivity) hρ hσ
  obtain ⟨k, hk_def⟩ : ∃ k : ℕ, k = max k₀ (max n₁ (max 3 ⌈4 / η⌉₊)) := ⟨_, rfl⟩
  have hkk₀ : k₀ ≤ k := by rw [hk_def]; exact le_max_left _ _
  have hkn₁ : n₁ ≤ k := by rw [hk_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hk3 : 3 ≤ k := by
    rw [hk_def]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hkη : 4 / η ≤ (k : ℝ) := by
    calc 4 / η ≤ ⌈4 / η⌉₊ := Nat.le_ceil _
      _ ≤ (k : ℝ) := by
        rw [hk_def]
        exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_max_right _ _)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨n₂, hn₂⟩ := hk₀ k hkk₀
  obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = ⌊η * k / 2⌋₊ := ⟨_, rfl⟩
  have hηk : 2 ≤ η * k / 2 := by
    rw [div_le_iff₀ hη] at hkη
    linarith
  have hd_le : (d : ℝ) ≤ η * k / 2 := by rw [hd_def]; exact Nat.floor_le (by positivity)
  have hd_ge : η * k / 4 ≤ (d : ℝ) := by
    have := Nat.lt_floor_add_one (η * k / 2)
    rw [← hd_def] at this
    linarith
  have hd_main : 2 * (η / 4) * k + d ≤ ε₁ * k := by nlinarith
  have hd_σ : (d : ℝ) ≤ σ * k / 4 := by nlinarith
  have hC'd : 2 * k ≤ C' * d := by
    have h1 : (2 * k : ℝ) ≤ C' * d := by
      have : 8 / η * (η * k / 4) = 2 * k := by field_simp; ring
      calc (2 * k : ℝ) = 8 / η * (η * k / 4) := this.symm
        _ ≤ C' * d := mul_le_mul hC'η hd_ge (by positivity) (by positivity)
    exact_mod_cast h1
  refine ⟨η / 4, by positivity, 1 / (1 / (2 * C')) + 4 * k + 1, ?_, max n₂ (k + 4),
    fun V _ _ G _ hn hδ hno => ?_⟩
  · have : 0 < 1 / (1 / (2 * (C' : ℝ))) := by positivity
    have : (0 : ℝ) ≤ 4 * k := by positivity
    linarith
  by_contra hnx
  apply hno
  refine averaging_regular G (((univ : Finset V).powersetCard k).filter
      (fun S => IsGoodSet G (η / 4) σ S)) k hk3 (fun S hS => ?_) (le_trans (le_max_right _ _) hn)
    hρ hρ2 hρ hε₀1 hθ (fun u v huv => ?_) (fun S hS φ hφ => ?_)
  · simp only [mem_filter, mem_powersetCard] at hS; exact hS.1.2
  · refine (hn₂ V G (le_trans (le_max_left _ _) hn) hδ hnx u v huv).trans (le_of_eq ?_)
    congr 2
    ext S
    simp only [mem_filter]
    tauto
  · simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS
    obtain ⟨hSk, hSgood⟩ := hS
    exact good_set_achievable G hσ.le h16' S hSgood (by rw [hSk]; exact hkn₁) d C'
      (by rw [hSk]; exact hd_main) (by rw [hSk]; exact hd_σ) hC'1 (by rw [hSk]; exact hC'd) φ hφ

end NashWilliams18
