/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.GlobalSetup

/-!
# Claim 10.9.2: the structure of the pairs in `E₂ ∩ H`

Every negative pair `f ∈ E₂` of weight at least `(3/4) F₀` has a common neighbourhood of size at
most `(1/2 + 2t) n` (`claim2_cn`) and an `α`-balanced bipartition (`claim2_bip`).  The second
part uses the local structure lemma (Lemma 9.6) through the hypotheses `hLS1`, `hLS2`.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

lemma isBip_mono {α α' : ℝ} (hαα' : α ≤ α') {u v : V} (huv : φ s(u, v) < 0)
    (h : IsBip G φ α u v) : IsBip G φ α' u v := by
  classical
  obtain ⟨A, hA, hN⟩ := h
  refine ⟨A, hA, le_trans ?_ (le_trans hN ?_)⟩
  · have : 0 ≤ ((cn G u v).card : ℝ) ^ 2 / 4 := by positivity
    nlinarith
  · unfold normalCount
    exact_mod_cast card_le_card (monotone_filter_right _ fun p _ hp =>
      normalPair_mono G φ hαα' huv hp)

/-- Each vertex lies in at most `2n` ordered pairs as a first or second coordinate. -/
lemma card_incPairs_le (f : V × V) :
    ((incPairs G φ f).card : ℝ) ≤ 4 * Fintype.card V := by
  have hsub : incPairs G φ f ⊆ (({f.1, f.2} : Finset V) ×ˢ univ) ∪ (univ ×ˢ {f.1, f.2}) := by
    intro g hg
    simp only [incPairs, mem_filter] at hg
    simp only [mem_union, mem_product, mem_insert, mem_singleton, mem_univ, and_true, true_and]
    tauto
  have h1 := card_le_card hsub
  have h2 := card_union_le (({f.1, f.2} : Finset V) ×ˢ (univ : Finset V))
    ((univ : Finset V) ×ˢ ({f.1, f.2} : Finset V))
  rw [card_product, card_product, card_univ] at h2
  have h3 : ({f.1, f.2} : Finset V).card ≤ 2 := card_le_two
  have : (incPairs G φ f).card ≤ 4 * Fintype.card V := by nlinarith
  exact_mod_cast this

/-- **Claim 10.9.2 (i).** -/
lemma claim2_cn (hφ : GoodWeighting G φ) {ε t : ℝ} (hε0 : 0 ≤ ε) (hεt : ε ≤ t ^ 2) (ht0 : 0 < t)
    (ht : t ≤ 1 / 20) (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    {f : V × V} (hf : f ∈ E2 G φ t) :
    ((cn G f.1 f.2).card : ℝ) ≤ (1 / 2 + 2 * t) * Fintype.card V := by
  simp only [E2, mem_sdiff, mem_union, not_or] at hf
  obtain ⟨hfN, hf0, -⟩ := hf
  have hfN' := (mem_negPairs G φ).1 hfN
  have hch : chNeg G φ f.1 f.2 ≤ t * (-φ s(f.1, f.2)) := by
    simp only [E0, mem_filter, not_and, not_le] at hf0
    exact (hf0 hfN).le
  exact small_charge_cn G φ hφ hε0 hεt ht0 ht hδ hfN'.1 hfN'.2 hch

/-- A negative pair heavier than `F₀` lies in `Q'` (if `F₀` bounds the weights in `E₂`). -/
lemma mem_Qp_of_heavy {t F₀ : ℝ} (hF₀ : 0 < F₀) (hmax : ∀ g ∈ E2 G φ t, negW φ g ≤ F₀)
    {f : V × V} (hf : f ∈ negPairs G φ) (hw : F₀ < negW φ f) : f ∈ Qp G φ t F₀ := by
  simp only [Qp, HH, mem_sdiff, mem_filter]
  exact ⟨⟨hf, by linarith⟩, fun h => absurd (hmax f h) (not_le.2 hw)⟩

/-- Rule 1 seen from the receiving pair: if `f ∉ E₀` and every pair of `T ⊆ E₀` shares a vertex
with `f` and has charge at least `X ≥ 0`, then `ch₁(f) ≥ ch_F(f) + |T| X / (8 n)`. -/
lemma ch1_ge_local {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {f : V × V} (hf : f ∉ E0 G φ t)
    (T : Finset (V × V)) (hT : T ⊆ E0 G φ t) (hTf : ∀ f' ∈ T, f ∈ incPairs G φ f')
    (hTX : ∀ f' ∈ T, X ≤ ch0 G φ f') :
    ch0 G φ f + T.card * X / (8 * Fintype.card V) ≤ ch1 G φ t f := by
  have h0 : ∀ f ∈ E0 G φ t, 0 ≤ ch0 G φ f := fun f hf => ch0_nonneg_of_mem_E0 G φ ht hf
  have hloc := recv_ge_local G φ h0 f T hT hTf
  have h1 : ch1 G φ t f = ch0 G φ f + _ := stepCh_of_not_mem G φ hf
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hterm : ∀ f' ∈ T, X / (8 * Fintype.card V) ≤ ch0 G φ f' / (2 * ((incPairs G φ f').card : ℝ)) := by
    intro f' hf'
    have hI := card_incPairs_le G φ f'
    have hIpos : (0 : ℝ) < (incPairs G φ f').card := by
      exact_mod_cast card_pos.2 ⟨f, hTf f' hf'⟩
    have hnpos : (0 : ℝ) < Fintype.card V := by
      exact_mod_cast Fintype.card_pos_iff.2 ⟨f.1⟩
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := hTX f' hf'
    nlinarith
  have hs := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hs
  have : (T.card : ℝ) * X / (8 * Fintype.card V) = T.card * (X / (8 * Fintype.card V)) := by ring
  linarith

open Classical in
/-- **Claim 10.9.2 (ii).** Every pair `f ∈ E₂` of weight at least `(3/4) F₀` has an
`α`-balanced bipartition.  The local structure lemma enters through `hLS1` and `hLS2`. -/
lemma claim2_bip (hφ : GoodWeighting G φ) {ε t γ α F₀ : ℝ} (hε : ε ≤ 1 / 12)
    (ht0 : 0 < t) (htγ : t ≤ γ) (hγ2 : t + 4 * ε ≤ γ ^ 2) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2)
    (hF₀ : 0 < F₀) (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hmax : ∀ g ∈ E2 G φ t, negW φ g ≤ F₀)
    (hQ1 : ((Qp G φ t F₀).card : ℝ) < (Fintype.card V : ℝ) ^ 2 / 45)
    (hQ2 : ((Qp G φ t F₀).card : ℝ) < γ * (Fintype.card V : ℝ) ^ 2 / 100)
    (hLS1 : ∀ u v, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ γ * (-φ s(u, v)) →
      LocallySmall G φ (4 * γ) u v ∨ IsBip G φ (α ^ 2 / 2) u v)
    (hLS2 : ∀ u v, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ 2 * γ * (-φ s(u, v)) →
      LocallySmall G φ (1 / 200) u v ∨ IsBip G φ (1 / 5) u v)
    {f : V × V} (hf : f ∈ E2 G φ t) (hfH : f ∈ HH G φ F₀) :
    ∃ A, IsBalBip G φ α f.1 f.2 A := by
  obtain ⟨u, v⟩ := f
  have hf' := hf
  simp only [E2, mem_sdiff, mem_union, not_or] at hf'
  obtain ⟨hfN, hf0, hf1⟩ := hf'
  obtain ⟨huv, hneg⟩ := (mem_negPairs G φ).1 hfN
  simp (config := { failIfUnchanged := false }) only at huv hneg
  set F := -φ s(u, v) with hFdef
  have hF : 0 < F := by linarith
  have hFH : 3 / 4 * F₀ ≤ F := (mem_filter.1 hfH).2
  have hch : chNeg G φ u v < t * F := by
    simp only [E0, mem_filter, not_and, not_le] at hf0
    exact hf0 hfN
  have hγ0 : 0 < γ := lt_of_lt_of_le ht0 htγ
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  rcases hLS1 u v huv hneg (by nlinarith) with hsmall | hbip
  swap
  · exact balBip_of_bip G φ hα0 hα hneg hbip
  exfalso
  -- the heavy negative edges at `u`
  set R := univ.filter fun w => G.Adj u w ∧ φ s(u, w) < 0 ∧ 2 * F ≤ -φ s(u, w)
  have hR : 4 * γ * n ≤ (R.card : ℝ) := hsmall.1
  have hRQ : ∀ w ∈ R, (u, w) ∈ Qp G φ t F₀ := by
    intro w hw
    simp only [R, mem_filter, mem_univ, true_and] at hw
    exact mem_Qp_of_heavy G φ hF₀ hmax ((mem_negPairs G φ).2 ⟨hw.1, hw.2.1⟩)
      (by unfold negW; simp (config := { failIfUnchanged := false }) only; linarith)
  set R' := R.filter fun w => 2 * γ * (-φ s(u, w)) ≤ chNeg G φ u w
  by_cases hR' : 2 * γ * n ≤ (R'.card : ℝ)
  · -- Rule 1 pushes `f` into `E₁`
    set T := R'.image fun w => (u, w)
    have hTcard : T.card = R'.card := card_image_of_injective _ (fun a b h => by
      simp only [Prod.mk.injEq] at h; exact h.2)
    have hT : T ⊆ E0 G φ t := by
      intro f' hf'
      simp only [T, mem_image] at hf'
      obtain ⟨w, hw, rfl⟩ := hf'
      simp only [R', R, mem_filter, mem_univ, true_and] at hw
      apply Finset.mem_filter.mpr
      refine ⟨(mem_negPairs G φ).2 ⟨hw.1.1, hw.1.2.1⟩, ?_⟩
      change t * (-φ s(u, w)) ≤ chNeg G φ u w
      have : t * (-φ s(u, w)) ≤ 2 * γ * (-φ s(u, w)) := by nlinarith
      linarith
    have hTf : ∀ f' ∈ T, (u, v) ∈ incPairs G φ f' := by
      intro f' hf'
      simp only [T, mem_image] at hf'
      obtain ⟨w, -, rfl⟩ := hf'
      simp [incPairs, hfN]
    have hTX : ∀ f' ∈ T, 4 * γ * F ≤ ch0 G φ f' := by
      intro f' hf'
      simp only [T, mem_image] at hf'
      obtain ⟨w, hw, rfl⟩ := hf'
      simp only [R', R, mem_filter, mem_univ, true_and] at hw
      simp only [ch0]
      nlinarith
    have h1 := ch1_ge_local G φ ht0.le (by positivity) hf0 T hT hTf hTX
    rw [hTcard] at h1
    have hlb := chNeg_lb G φ hφ hδ huv hneg
    have hch0 : ch0 G φ (u, v) = chNeg G φ u v := rfl
    have hgain : γ ^ 2 * F ≤ (R'.card : ℝ) * (4 * γ * F) / (8 * n) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hR' (by positivity : (0:ℝ) ≤ 4 * γ * F)
      linarith
    have e1 : -4 * ε * F ≤ ch0 G φ (u, v) := by rw [hch0]; exact hlb
    have e2 : t * F ≤ (γ ^ 2 - 4 * ε) * F := mul_le_mul_of_nonneg_right (by linarith) hF.le
    have hE1 : (u, v) ∈ E1 G φ t := by
      simp only [E1, mem_filter]
      exact ⟨hfN, by linarith⟩
    exact hf1 hE1
  · push_neg at hR'
    set R2 := R \ R'
    have hR2 : 2 * γ * n ≤ (R2.card : ℝ) := by
      have : R2.card + R'.card = R.card := card_sdiff_add_card_eq_card (filter_subset _ _)
      have : (R2.card : ℝ) + R'.card = R.card := by exact_mod_cast this
      linarith
    have hR2ls : ∀ w ∈ R2, LocallySmall G φ (1 / 200) u w ∨ IsBip G φ (1 / 5) u w := by
      intro w hw
      simp only [R2, R', R, mem_sdiff, mem_filter, mem_univ, true_and, not_and, not_le] at hw
      exact hLS2 u w hw.1.1 hw.1.2.1 (hw.2 hw.1).le
    by_cases hb : ∃ w ∈ R2, IsBip G φ (1 / 5) u w
    · obtain ⟨w, hw, A, hA, hN⟩ := hb
      have hw' : w ∈ R := (mem_sdiff.1 hw).1
      simp only [R, mem_filter, mem_univ, true_and] at hw'
      -- all normal pairs are in `Q'`
      have hwF : 2 * F ≤ -φ s(u, w) := hw'.2.2
      have hsub : ((A ×ˢ (cn G u w \ A)).filter fun p => NormalPair G φ (1 / 5) u w p.1 p.2) ⊆
          Qp G φ t F₀ := by
        intro p hp
        simp only [mem_filter] at hp
        obtain ⟨hpa, hpn, hpw⟩ := hp.2
        refine mem_Qp_of_heavy G φ hF₀ hmax ((mem_negPairs G φ).2 ⟨hpa, hpn⟩) ?_
        unfold negW
        linarith
      have hcard := card_le_card hsub
      have hc : (1 / 2 - 2 * ε) * n ≤ (cn G u w).card := (cn_bounds_of_minDegree G hδ u w).1
      have hc3 : n / 3 ≤ ((cn G u w).card : ℝ) := by nlinarith
      have hsq := pow_le_pow_left₀ (by positivity) hc3 2
      have hcard' : (normalCount G φ (1 / 5) u w A (cn G u w \ A) : ℝ) ≤ (Qp G φ t F₀).card := by
        unfold normalCount; exact_mod_cast hcard
      have : (1 - 1 / 5) * (n / 3) ^ 2 / 4 ≤ (1 - 1 / 5) * ((cn G u w).card : ℝ) ^ 2 / 4 := by
        linarith
      have : (1 - 1 / 5) * (n / 3) ^ 2 / 4 = n ^ 2 / 45 := by ring
      linarith
    · push_neg at hb
      have hls : ∀ w ∈ R2, LocallySmall G φ (1 / 200) u w := fun w hw =>
        (hR2ls w hw).resolve_right (hb w hw)
      -- many heavy pairs at the vertices of `R2`
      set P := R2.sigma fun w => univ.filter fun z =>
        G.Adj w z ∧ φ s(w, z) < 0 ∧ 2 * (-φ s(u, w)) ≤ -φ s(w, z)
      have hPcard : (P.card : ℝ) = ∑ w ∈ R2, ((univ.filter fun z =>
          G.Adj w z ∧ φ s(w, z) < 0 ∧ 2 * (-φ s(u, w)) ≤ -φ s(w, z)).card : ℝ) := by
        rw [card_sigma]; push_cast; rfl
      have hPle : P.card ≤ (Qp G φ t F₀).card := by
        refine card_le_card_of_injOn (fun p => (p.1, p.2)) ?_ ?_
        · intro p hp
          simp only [P, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_univ,
            true_and] at hp
          have hw : p.1 ∈ R := (mem_sdiff.1 hp.1).1
          simp only [R, mem_filter, mem_univ, true_and] at hw
          have hw2 : 2 * F ≤ -φ s(u, p.1) := hw.2.2
          have hp3 : 2 * (-φ s(u, p.1)) ≤ -φ s(p.1, p.2) := hp.2.2.2
          refine mem_Qp_of_heavy G φ hF₀ hmax ((mem_negPairs G φ).2 ⟨hp.2.1, hp.2.2.1⟩) ?_
          unfold negW; simp (config := { failIfUnchanged := false }) only; linarith
        · intro p _ q _ h
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.1 (heq_of_eq h.2)
      have hPge : (R2.card : ℝ) * (1 / 200 * n) ≤ P.card := by
        rw [hPcard, ← nsmul_eq_mul, ← sum_const]
        exact sum_le_sum fun w hw => (hls w hw).2
      have hPle' : (P.card : ℝ) ≤ (Qp G φ t F₀).card := by exact_mod_cast hPle
      have : 2 * γ * n * (1 / 200 * n) ≤ (R2.card : ℝ) * (1 / 200 * n) :=
        mul_le_mul_of_nonneg_right hR2 (by positivity)
      have : 2 * γ * n * (1 / 200 * n) = γ * n ^ 2 / 100 := by ring
      linarith

end NashWilliams.Frac
