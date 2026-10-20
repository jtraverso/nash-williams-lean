/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.Charge
import RequestProject.FracStab.BipMain

/-!
# Local structure of extremal edges (§9.2 and §10.2 of the paper)

* `LocallySmall` and `IsBip` — Definition 9.4 (`α`-locally-small and `α`-bipartite edges);
* `IsBalBip` — Definition 10.5 (`α`-balanced bipartitions);
* `local_structure` — Lemma 9.6 (second part, via Lemma 9.5): a negative edge with small final
  charge is locally small or nearly bipartite;
* `balBip_of_bip` — Proposition 10.6;
* `card_not_normalVtx_le` — Proposition 10.7;
* `card_obtuse_le` — Proposition 10.8.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- The negative edge `uv` is `α`-locally-small (Definition 9.4): both `u` and `v` are incident
with at least `α n` negative edges of weight at least twice that of `uv` in absolute value. -/
def LocallySmall (α : ℝ) (u v : V) : Prop :=
  α * Fintype.card V ≤ ((univ.filter fun w =>
      G.Adj u w ∧ φ s(u, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(u, w)).card : ℝ) ∧
  α * Fintype.card V ≤ ((univ.filter fun w =>
      G.Adj v w ∧ φ s(v, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(v, w)).card : ℝ)

/-- The pair `ab` is `α`-normal with respect to the negative edge `uv` (Definition 10.5): `ab` is
a negative edge with `|φ(ab)| ≥ (1 - α) |φ(uv)|`. -/
def NormalPair (α : ℝ) (u v a b : V) : Prop :=
  G.Adj a b ∧ φ s(a, b) < 0 ∧ (1 - α) * (-φ s(u, v)) ≤ -φ s(a, b)

open Classical in
/-- Number of `α`-normal pairs between `A` and `B`. -/
noncomputable def normalCount (α : ℝ) (u v : V) (A B : Finset V) : ℕ :=
  ((A ×ˢ B).filter fun p => NormalPair G φ α u v p.1 p.2).card

/-- The negative edge `uv` is `α`-bipartite (Definition 9.4). -/
def IsBip (α : ℝ) (u v : V) : Prop :=
  ∃ A ⊆ cn G u v, (1 - α) * ((cn G u v).card : ℝ) ^ 2 / 4 ≤
    (normalCount G φ α u v A (cn G u v \ A) : ℝ)

/-- `A` (together with `B = N(u) ∩ N(v) ∖ A`) is an `α`-balanced bipartition for the negative
edge `uv` (Definition 10.5): both sides have at most `(c + 1)/2` vertices, where
`c = |N(u) ∩ N(v)|`, and there are at least `(1 - α) c² / 4` normal pairs between them. -/
def IsBalBip (α : ℝ) (u v : V) (A : Finset V) : Prop :=
  A ⊆ cn G u v ∧ 2 * A.card ≤ (cn G u v).card + 1 ∧ 2 * (cn G u v \ A).card ≤ (cn G u v).card + 1 ∧
    (1 - α) * ((cn G u v).card : ℝ) ^ 2 / 4 ≤ (normalCount G φ α u v A (cn G u v \ A) : ℝ)

/-- **Lemma 9.6** (second part; contains Lemma 9.5).  For every `η > 0` there is `γ₀ > 0` such
that for `0 < γ ≤ γ₀`, `n` large, `0 ≤ ε ≤ γ²` and `0 < α < 1`: if `δ(G) ≥ (3/4 - ε) n` and the
negative edge `uv` has `ch_F(uv) ≤ γ |φ(uv)|`, then `uv` is `α`-locally-small or
`(36 α + η)`-bipartite. -/
theorem local_structure (η : ℝ) (hη : 0 < η) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ n₀ : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ γ ^ 2 →
      ∀ α : ℝ, 0 < α → α < 1 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (φ : Sym2 V → ℝ), n₀ ≤ Fintype.card V → GoodWeighting G φ →
        (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree →
        ∀ u v : V, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ γ * (-φ s(u, v)) →
        LocallySmall G φ α u v ∨ IsBip G φ (36 * α + η) u v := by
  classical
  set η' : ℝ := min η (1/2) with hη'def
  have hη'0 : 0 < η' := by positivity
  have hη'1 : η' ≤ η := min_le_left _ _
  have hη'2 : η' ≤ 1/2 := min_le_right _ _
  obtain ⟨ε0, hε0, hab⟩ := abstract_bip hη'0
  refine ⟨min (1/20) (ε0/26), by positivity, fun γ hγ0 hγ => ⟨0, fun ε hε hεγ α hα0 hα1 V _ _ G
    _ φ _ hφ hδ u v huv hneg hch => ?_⟩⟩
  by_cases hLS : LocallySmall G φ α u v
  · exact Or.inl hLS
  right
  have hγ1 : γ ≤ 1/20 := le_trans hγ (min_le_left _ _)
  have hγ2 : γ ≤ ε0/26 := le_trans hγ (min_le_right _ _)
  set F := -φ s(u, v) with hFdef
  have hF : 0 < F := by linarith
  set C := cn G u v with hCdef
  set c : ℝ := (C.card : ℝ) with hcdef
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hval := small_charge_value G φ hφ hε hεγ hγ0 hγ1 hδ huv hneg hch
  have hb := bsum_aW_eq G φ u v hneg
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
  have hbs : (1 - ε0) * (C.card : ℝ) ^ 2 / 2 ≤ bsum (aW G φ u v) C C := by
    rw [hb, le_div_iff₀ hF]
    have h1 : (1 - ε0) * c ^ 2 ≤ (1 - 26 * γ) * c ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hc2
    have h2 := mul_le_mul_of_nonneg_left h1 hF.le
    linarith only [hval, h2]
  -- the small sides
  have hsub1 : SuG G φ u v ⊆ univ.filter fun w =>
      G.Adj v w ∧ φ s(v, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(v, w) := by
    intro x hx
    have hx' := Finset.mem_filter.mp (show x ∈ (cn G u v).filter
      (fun w => UG φ u v w ∧ 2 * (-φ s(u, v)) ≤ -φ s(v, w)) from hx)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, ((mem_cn G).mp hx'.1).2, hx'.2.1.2, hx'.2.2⟩
  have hsub2 : SvG G φ u v ⊆ univ.filter fun w =>
      G.Adj u w ∧ φ s(u, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(u, w) := by
    intro x hx
    have hx' := Finset.mem_filter.mp (show x ∈ (cn G u v).filter
      (fun w => WG φ u v w ∧ 2 * (-φ s(u, v)) ≤ -φ s(u, w)) from hx)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, ((mem_cn G).mp hx'.1).1, hx'.2.1.2, hx'.2.2⟩
  have hS : min ((SuG G φ u v).card : ℝ) (SvG G φ u v).card ≤ α * n := by
    unfold LocallySmall at hLS
    have k1 := card_le_card hsub1
    have k2 := card_le_card hsub2
    have k1' : ((SuG G φ u v).card : ℝ) ≤ ((univ.filter fun w =>
        G.Adj v w ∧ φ s(v, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(v, w)).card : ℝ) := by
      exact_mod_cast k1
    have k2' : ((SvG G φ u v).card : ℝ) ≤ ((univ.filter fun w =>
        G.Adj u w ∧ φ s(u, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(u, w)).card : ℝ) := by
      exact_mod_cast k2
    by_cases hu : α * n ≤ ((univ.filter fun w =>
        G.Adj u w ∧ φ s(u, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(u, w)).card : ℝ)
    · have hv : ¬ α * n ≤ ((univ.filter fun w =>
          G.Adj v w ∧ φ s(v, w) < 0 ∧ 2 * (-φ s(u, v)) ≤ -φ s(v, w)).card : ℝ) :=
        fun h => hLS ⟨hu, h⟩
      push_neg at hv
      exact le_trans (min_le_left _ _) (le_trans k1' hv.le)
    · push_neg at hu
      exact le_trans (min_le_right _ _) (le_trans k2' hu.le)
  obtain ⟨B, hB, hN⟩ := hab (locFacts_of_graph hφ huv hneg) hbs hS
  refine ⟨B, hB, ?_⟩
  have hmono : nrm (gG G φ u v) η' B (C \ B) ≤ normalCount G φ (36 * α + η) u v B (C \ B) := by
    unfold nrm normalCount
    refine card_le_card (monotone_filter_right _ fun p _ hp => ?_)
    have hpos : 0 < gG G φ u v p.1 p.2 := by linarith
    have hadj := gG_pos hpos
    rw [gG_of hadj] at hp
    refine ⟨hadj.1, hadj.2, ?_⟩
    rw [le_div_iff₀ hF] at hp
    have : (1 - (36 * α + η)) * F ≤ (1 - η') * F :=
      mul_le_mul_of_nonneg_right (by linarith) hF.le
    linarith
  have hmono' : (nrm (gG G φ u v) η' B (C \ B) : ℝ) ≤
      normalCount G φ (36 * α + η) u v B (C \ B) := by exact_mod_cast hmono
  -- `n ≤ 3 c`
  obtain ⟨hcn, -⟩ := cn_bounds_of_minDegree G hδ u v
  have hγsq : γ ^ 2 ≤ 1/400 := by nlinarith only [hγ0, hγ1]
  have hε' : ε ≤ 1/400 := le_trans hεγ hγsq
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hεn := mul_le_mul_of_nonneg_right hε' hn0
  have hn3 : n ≤ 3 * c := by linarith only [hcn, hεn, hn0]
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hαn : 2 * (α * n) * c ≤ 6 * α * c ^ 2 := by
    have := mul_le_mul_of_nonneg_left hn3 (mul_nonneg (mul_nonneg zero_le_two hα0.le) hc0)
    linarith only [this]
  have hfin : (1 - (36 * α + η)) * c ^ 2 / 4 ≤ (1 - η') * c ^ 2 / 4 - 2 * (α * n) * c := by
    have h1 : η' * c ^ 2 ≤ η * c ^ 2 := mul_le_mul_of_nonneg_right hη'1 hc2
    have h2 : 0 ≤ α * c ^ 2 := mul_nonneg hα0.le hc2
    linarith only [h1, h2, hαn]
  linarith only [hfin, hN, hmono']

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma normalPair_symm {α : ℝ} {u v a b : V} (h : NormalPair G φ α u v a b) :
    NormalPair G φ α u v b a := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : s(b, a) = s(a, b) := Sym2.eq_swap
  exact ⟨h1.symm, by rw [e]; exact h2, by rw [e]; exact h3⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma normalPair_mono {α α' : ℝ} (hαα' : α ≤ α') {u v a b : V} (huv : φ s(u, v) < 0)
    (h : NormalPair G φ α u v a b) : NormalPair G φ α' u v a b := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by nlinarith⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma normalCount_comm (α : ℝ) (u v : V) (A B : Finset V) :
    normalCount G φ α u v A B = normalCount G φ α u v B A := by
  classical
  unfold normalCount
  refine card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, normalPair_symm G φ hp.2⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro q hq
    simp only [mem_filter, mem_product] at hq
    exact ⟨(q.2, q.1), by simp only [mem_filter, mem_product]; exact ⟨⟨hq.1.2, hq.1.1⟩,
      normalPair_symm G φ hq.2⟩, rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma normalCount_le_mul (α : ℝ) (u v : V) (A B : Finset V) :
    normalCount G φ α u v A B ≤ A.card * B.card := by
  classical
  unfold normalCount
  rw [← card_product]; exact card_filter_le _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma normalCount_mono_left (α : ℝ) (u v : V) {A A' : Finset V} (h : A ⊆ A') (B : Finset V) :
    normalCount G φ α u v A B ≤ normalCount G φ α u v A' B := by
  classical
  unfold normalCount
  exact card_le_card (filter_subset_filter _ (product_subset_product h (Subset.refl _)))

omit [Fintype V] [DecidableRel G.Adj] in
/-- Removing `S` from the right side loses at most `|A| |S|` normal pairs. -/
lemma normalCount_sdiff (α : ℝ) (u v : V) (A B S : Finset V) :
    normalCount G φ α u v A B ≤ normalCount G φ α u v A (B \ S) + A.card * S.card := by
  classical
  unfold normalCount
  have hsub : (A ×ˢ B).filter (fun p => NormalPair G φ α u v p.1 p.2) ⊆
      ((A ×ˢ (B \ S)).filter fun p => NormalPair G φ α u v p.1 p.2) ∪ (A ×ˢ S) := by
    intro p hp
    simp only [mem_filter, mem_product, mem_union, mem_sdiff] at hp ⊢
    by_cases hS : p.2 ∈ S
    · exact Or.inr ⟨hp.1.1, hS⟩
    · exact Or.inl ⟨⟨hp.1.1, hp.1.2, hS⟩, hp.2⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ = _ := by rw [card_product]

/-- Real-number core of Proposition 10.6. -/
lemma balance_loss {a b m α : ℝ} (hα0 : 0 ≤ α) (ha : 0 ≤ a) (hab : a ≤ b)
    (hm : a + b = m) (hN : (1 - α ^ 2 / 2) * m ^ 2 / 4 ≤ a * b) :
    a * ((b - a) / 2) ≤ 3 * α * m ^ 2 / 16 := by
  have hx : (b - a) ^ 2 ≤ α ^ 2 / 2 * m ^ 2 := by nlinarith
  have hx' : b - a ≤ 3 * α / 4 * m := by
    have hm0 : 0 ≤ m := by linarith
    nlinarith [sq_nonneg (b - a - 3 * α / 4 * m), mul_nonneg hα0 hm0]
  have h2a : 2 * a ≤ m := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hx' ha]

/-- **Proposition 10.6.** An `α²/2`-bipartite negative edge has an `α`-balanced bipartition
(for `0 ≤ α ≤ 1/2`). -/
theorem balBip_of_bip {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) {u v : V} (huv : φ s(u, v) < 0)
    (h : IsBip G φ (α ^ 2 / 2) u v) : ∃ A, IsBalBip G φ α u v A := by
  classical
  obtain ⟨A₀, hA₀, hN⟩ := h
  -- monotonicity in the parameter
  have hmono : ∀ A B : Finset V, normalCount G φ (α ^ 2 / 2) u v A B ≤ normalCount G φ α u v A B := by
    intro A B
    unfold normalCount
    exact card_le_card (monotone_filter_right _ fun p _ hp =>
      normalPair_mono G φ (by nlinarith) huv hp)
  -- a version with the smaller side first
  have key : ∀ A B : Finset V, A ⊆ (cn G u v) → B = (cn G u v) \ A → A.card ≤ B.card →
      (1 - α ^ 2 / 2) * ((cn G u v).card : ℝ) ^ 2 / 4 ≤ (normalCount G φ (α ^ 2 / 2) u v A B : ℝ) →
      ∃ A', IsBalBip G φ α u v A' := by
    intro A B hA hB hle hcnt
    have hAC := card_le_card hA
    have hcard : A.card + B.card = (cn G u v).card := by
      rw [hB, card_sdiff_of_subset hA]; omega
    obtain ⟨S, hSB, hScard⟩ := exists_subset_card_eq (s := B) (n := (B.card - A.card) / 2)
      (by omega)
    refine ⟨A ∪ S, union_subset hA (hSB.trans (by rw [hB]; exact sdiff_subset)), ?_, ?_, ?_⟩
    · have hdisj : Disjoint A S := by
        rw [disjoint_left]; intro x hxA hxS
        have := hSB hxS; rw [hB, mem_sdiff] at this; exact this.2 hxA
      rw [card_union_of_disjoint hdisj, hScard]; omega
    · have he : (cn G u v) \ (A ∪ S) = B \ S := by
        rw [hB]; ext x; simp only [mem_sdiff, mem_union]; tauto
      rw [he, card_sdiff_of_subset hSB, hScard]; omega
    · have he : (cn G u v) \ (A ∪ S) = B \ S := by
        rw [hB]; ext x; simp only [mem_sdiff, mem_union]; tauto
      rw [he]
      have h1 := normalCount_sdiff G φ α u v A B S
      have h2 := normalCount_mono_left G φ α u v (subset_union_left (s₁ := A) (s₂ := S)) (B \ S)
      have h3 := hmono A B
      have h4 := normalCount_le_mul G φ (α ^ 2 / 2) u v A B
      have hS2 : (S.card : ℝ) ≤ ((B.card : ℝ) - A.card) / 2 := by
        rw [hScard]
        have := Nat.cast_div_le (α := ℝ) (m := B.card - A.card) (n := 2)
        rw [Nat.cast_sub hle] at this
        simpa using this
      have hcard' : (A.card : ℝ) + B.card = (cn G u v).card := by exact_mod_cast hcard
      have h4' : (normalCount G φ (α ^ 2 / 2) u v A B : ℝ) ≤ A.card * B.card := by
        exact_mod_cast h4
      have hloss := balance_loss hα0 (Nat.cast_nonneg A.card) (by exact_mod_cast hle) hcard'
        (le_trans hcnt h4')
      have h1' : (normalCount G φ α u v A B : ℝ) ≤
          normalCount G φ α u v A (B \ S) + A.card * S.card := by exact_mod_cast h1
      have h2' : (normalCount G φ α u v A (B \ S) : ℝ) ≤
          normalCount G φ α u v (A ∪ S) (B \ S) := by exact_mod_cast h2
      have h3' : (normalCount G φ (α ^ 2 / 2) u v A B : ℝ) ≤ normalCount G φ α u v A B := by
        exact_mod_cast h3
      have hAS : (A.card : ℝ) * S.card ≤ A.card * (((B.card : ℝ) - A.card) / 2) :=
        mul_le_mul_of_nonneg_left hS2 (Nat.cast_nonneg _)
      have hfin := mul_nonneg (mul_nonneg hα0 (by linarith : (0:ℝ) ≤ 1 / 2 - α))
        (sq_nonneg ((cn G u v).card : ℝ))
      nlinarith
  rcases le_total A₀.card ((cn G u v) \ A₀).card with hle | hle
  · exact key A₀ ((cn G u v) \ A₀) hA₀ rfl hle hN
  · refine key ((cn G u v) \ A₀) A₀ sdiff_subset (by rw [Finset.sdiff_sdiff_eq_self hA₀]) ?_ ?_
    · exact hle
    · rw [normalCount_comm]; exact hN

end NashWilliams.Frac
