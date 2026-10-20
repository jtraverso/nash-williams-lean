/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Lemma156
import RequestProject.NW18.FinalGlue

/-!
# One side is not close to `T₂` or `T̄₂`

Proof of Theorem 12.5, first paragraph: since `G` is not `α`-close to any of the three
extremal graphs and the cut `(V₁, V₂)` is almost complete, one of the two sides `G[V_i]` is
not `α/24`-close to `T₂(|V_i|)` or `T̄₂(|V_i|)` (the paper states `α/3`; any fixed fraction of
`α` works for the rest of the argument).

If both sides were close, the two near-optimal splits glue (`glueMap`) to a four-class layout
whose pattern cost is at most `2θ n² + β n²/2`, and `isCloseToExtremal_of_glue` gives
closeness of `G` to one of the three extremal graphs.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma pat_glue_same {N X Y : Finset V} (b₀ b₁ : Bool)
    {x y : V} (hx : x ∈ N) (hy : y ∈ N) :
    Pat b₀ b₁ (glueMap N X Y x) (glueMap N X Y y) = true ↔ sideTarget X b₀ x y := by
  by_cases h1 : x ∈ X <;> by_cases h2 : y ∈ X <;> cases b₀ <;>
    simp [glueMap, Pat, sideTarget, hx, hy, h1, h2]

omit [Fintype V] in
lemma pat_glue_other {N X Y : Finset V} (b₀ b₁ : Bool)
    {x y : V} (hx : x ∉ N) (hy : y ∉ N) :
    Pat b₀ b₁ (glueMap N X Y x) (glueMap N X Y y) = true ↔ sideTarget Y b₁ x y := by
  by_cases h1 : x ∈ Y <;> by_cases h2 : y ∈ Y <;> cases b₁ <;>
    simp [glueMap, Pat, sideTarget, hx, hy, h1, h2]

omit [Fintype V] in
lemma pat_glue_cross {N X Y : Finset V} (b₀ b₁ : Bool) {x y : V} (h : (x ∈ N ↔ y ∉ N)) :
    Pat b₀ b₁ (glueMap N X Y x) (glueMap N X Y y) = true := by
  by_cases hx : x ∈ N
  · have hy : y ∉ N := h.mp hx
    by_cases h1 : x ∈ X <;> by_cases h2 : y ∈ Y <;> simp [glueMap, Pat, hx, hy, h1, h2]
  · have hy : y ∈ N := by by_contra hy; exact hx (h.mpr hy)
    by_cases h1 : x ∈ Y <;> by_cases h2 : y ∈ X <;> simp [glueMap, Pat, hx, hy, h1, h2]

open Classical in
omit [Fintype V] [DecidableEq V] in
lemma card_filter_product_eq_sum (D : Finset V) (P : V → V → Prop) :
    ((D ×ˢ D).filter (fun q => P q.1 q.2)).card = ∑ x ∈ D, (D.filter (fun y => P x y)).card := by
  rw [card_filter, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [card_filter]

/-- The pattern cost of the glued layout. -/
lemma patCost_glue (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {X Y : Finset V}
    (hY : Y ⊆ partClass p 1) (b₀ b₁ : Bool) :
    (patCost G (Pat b₀ b₁) (glueMap (partClass p 0) X Y) : ℝ) ≤
      sideCost G (partClass p 0) X b₀ + sideCost G (partClass p 1) Y b₁ +
      2 * (((partClass p 0).card : ℝ) * (partClass p 1).card - cutSize G (partClass p 0)) := by
  classical
  set N := partClass p 0
  set M := partClass p 1
  have hMN : ∀ y, y ∈ M ↔ y ∉ N := by
    intro y; simp only [N, M, partClass, mem_filter, mem_univ, true_and]
    rcases fin2_cases (p y) with h | h <;> simp [h]
  have hYN : Disjoint Y N := disjoint_left.mpr fun y hy hyN => (hMN y).mp (hY hy) hyN
  set f := glueMap N X Y
  -- per-vertex description
  have hsd : ∀ x, (symmDiff (univ.filter (G.Adj x)) (patNb (Pat b₀ b₁) f x)).card =
      (univ.filter (fun y => ¬ (G.Adj x y ↔ (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card := by
    intro x; congr 1; ext y
    simp only [mem_symmDiff, mem_filter, mem_univ, true_and, patNb]
    tauto
  have hsplit : ∀ x, (univ.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card =
      (N.filter (fun y => ¬ (G.Adj x y ↔ (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card +
      (M.filter (fun y => ¬ (G.Adj x y ↔ (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card := by
    intro x
    rw [← card_union_of_disjoint (disjoint_filter_filter (disjoint_left.mpr fun y h1 h2 =>
      (hMN y).mp h2 h1))]
    congr 1; ext y; simp only [mem_filter, mem_univ, true_and, mem_union]
    by_cases hy : y ∈ N
    · simp [hy]
    · simp [hy, (hMN y).mpr hy]
  -- the four blocks
  have hNN : ∀ x ∈ N, (N.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))) =
      N.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget X b₀ x y)) := by
    intro x hx; ext y; simp only [mem_filter]
    constructor
    · rintro ⟨hy, h⟩
      refine ⟨hy, fun hxy => h ?_, fun h' => h ?_⟩
      · subst hxy; simp
      · rw [pat_glue_same (X := X) (Y := Y) b₀ b₁ hx hy]
        constructor
        · intro ha; exact ⟨(G.ne_of_adj ha).symm, h'.mp ha⟩
        · rintro ⟨-, hs⟩; exact h'.mpr hs
    · rintro ⟨hy, hxy, h⟩
      refine ⟨hy, fun h' => h ?_⟩
      rw [pat_glue_same (X := X) (Y := Y) b₀ b₁ hx hy] at h'
      constructor
      · intro ha; exact (h'.mp ha).2
      · intro hs; exact h'.mpr ⟨Ne.symm hxy, hs⟩
  have hMM : ∀ x ∈ M, (M.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))) =
      M.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget Y b₁ x y)) := by
    intro x hx; ext y; simp only [mem_filter]
    have hxN := (hMN x).mp hx
    constructor
    · rintro ⟨hy, h⟩
      refine ⟨hy, fun hxy => h ?_, fun h' => h ?_⟩
      · subst hxy; simp
      · rw [pat_glue_other (X := X) (Y := Y) b₀ b₁ hxN ((hMN y).mp hy)]
        constructor
        · intro ha; exact ⟨(G.ne_of_adj ha).symm, h'.mp ha⟩
        · rintro ⟨-, hs⟩; exact h'.mpr hs
    · rintro ⟨hy, hxy, h⟩
      refine ⟨hy, fun h' => h ?_⟩
      rw [pat_glue_other (X := X) (Y := Y) b₀ b₁ hxN ((hMN y).mp hy)] at h'
      constructor
      · intro ha; exact (h'.mp ha).2
      · intro hs; exact h'.mpr ⟨Ne.symm hxy, hs⟩
  have hNM : ∀ x ∈ N, (M.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card = M.card - partDeg G p x 1 := by
    intro x hx
    have e : M.filter (fun y => ¬ (G.Adj x y ↔ (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true))) =
        M.filter (fun y => ¬ G.Adj x y) := by
      ext y; simp only [mem_filter]
      constructor
      · rintro ⟨hy, h⟩; refine ⟨hy, fun ha => h ⟨fun _ => ⟨?_, ?_⟩, fun _ => ha⟩⟩
        · intro hyx; subst hyx; exact (hMN _).mp hy hx
        · exact pat_glue_cross b₀ b₁ ⟨fun _ => (hMN y).mp hy, fun _ => hx⟩
      · rintro ⟨hy, h⟩; exact ⟨hy, fun h' => h (h'.mpr ⟨by intro hyx; subst hyx; exact (hMN _).mp hy hx,
          pat_glue_cross b₀ b₁ ⟨fun _ => (hMN y).mp hy, fun _ => hx⟩⟩)⟩
    rw [e]
    have h2 : (M.filter (fun y => G.Adj x y)).card = partDeg G p x 1 := by
      unfold partDeg; congr 1; ext y
      simp only [M, partClass, mem_filter, mem_univ, true_and]; tauto
    have h3 := card_filter_add_card_filter_not (s := M) (fun y => G.Adj x y)
    omega
  have hMN' : ∀ x ∈ M, (N.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card = N.card - partDeg G p x 0 := by
    intro x hx
    have hxN := (hMN x).mp hx
    have e : N.filter (fun y => ¬ (G.Adj x y ↔ (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true))) =
        N.filter (fun y => ¬ G.Adj x y) := by
      ext y; simp only [mem_filter]
      constructor
      · rintro ⟨hy, h⟩; refine ⟨hy, fun ha => h ⟨fun _ => ⟨?_, ?_⟩, fun _ => ha⟩⟩
        · intro hyx; subst hyx; exact hxN hy
        · exact pat_glue_cross b₀ b₁ ⟨fun h' => absurd h' hxN, fun h'' => absurd hy h''⟩
      · rintro ⟨hy, h⟩; exact ⟨hy, fun h' => h (h'.mpr ⟨by intro hyx; subst hyx; exact hxN hy,
          pat_glue_cross b₀ b₁ ⟨fun h' => absurd h' hxN, fun h'' => absurd hy h''⟩⟩)⟩
    rw [e]
    have h2 : (N.filter (fun y => G.Adj x y)).card = partDeg G p x 0 := by
      unfold partDeg; congr 1; ext y
      simp only [N, partClass, mem_filter, mem_univ, true_and]; tauto
    have h3 := card_filter_add_card_filter_not (s := N) (fun y => G.Adj x y)
    omega
  -- assemble
  have hcostN : sideCost G N X b₀ =
      ∑ x ∈ N, (N.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget X b₀ x y))).card := by
    unfold sideCost
    rw [card_filter, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]
    exact sum_congr rfl fun y _ => by congr 1
  have hcostM : sideCost G M Y b₁ =
      ∑ x ∈ M, (M.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget Y b₁ x y))).card := by
    unfold sideCost
    rw [card_filter, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]
    exact sum_congr rfl fun y _ => by congr 1
  obtain ⟨hc0, hc1⟩ := cutSize_eq_sum_partDeg G p
  have hunivNM : (univ : Finset V) = N ∪ M := by
    ext y; simp only [mem_univ, mem_union, true_iff]
    by_cases hy : y ∈ N
    · exact Or.inl hy
    · exact Or.inr ((hMN y).mpr hy)
  have hdisjNM : Disjoint N M := disjoint_left.mpr fun y h1 h2 => (hMN y).mp h2 h1
  have hsumsplit : ∀ F : V → ℕ, ∑ x, F x = ∑ x ∈ N, F x + ∑ x ∈ M, F x := fun F => by
    rw [← sum_union hdisjNM, ← hunivNM]
  unfold patCost
  rw [hsumsplit]
  simp only [hsd, hsplit]
  have eN : ∑ x ∈ N, ((N.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card + (M.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card) =
      sideCost G N X b₀ + ∑ x ∈ N, (M.card - partDeg G p x 1) := by
    rw [sum_add_distrib, hcostN]
    congr 1
    · exact sum_congr rfl (fun x hx => by rw [hNN x hx])
    · exact sum_congr rfl hNM
  have eM : ∑ x ∈ M, ((N.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card + (M.filter (fun y => ¬ (G.Adj x y ↔
      (y ≠ x ∧ Pat b₀ b₁ (f x) (f y) = true)))).card) =
      ∑ x ∈ M, (N.card - partDeg G p x 0) + sideCost G M Y b₁ := by
    rw [sum_add_distrib, hcostM]
    congr 1
    · exact sum_congr rfl hMN'
    · exact sum_congr rfl (fun x hx => by rw [hMM x hx])
  rw [eN, eM]
  have hle1 : ∀ x ∈ N, partDeg G p x 1 ≤ M.card := fun x _ => partDeg_le_card_partClass G p x 1
  have hle0 : ∀ x ∈ M, partDeg G p x 0 ≤ N.card := fun x _ => partDeg_le_card_partClass G p x 0
  have s1 : ∑ x ∈ N, ((M.card - partDeg G p x 1 : ℕ) : ℝ) =
      N.card * M.card - cutSize G N := by
    rw [sum_congr rfl (fun x hx => Nat.cast_sub (hle1 x hx)), sum_sub_distrib,
      sum_const, nsmul_eq_mul, hc0]
    push_cast; ring
  have s2 : ∑ x ∈ M, ((N.card - partDeg G p x 0 : ℕ) : ℝ) =
      N.card * M.card - cutSize G N := by
    rw [sum_congr rfl (fun x hx => Nat.cast_sub (hle0 x hx)), sum_sub_distrib,
      sum_const, nsmul_eq_mul, hc1]
    push_cast; ring
  push_cast
  rw [s1, s2]
  linarith

end

set_option maxHeartbeats 1000000 in
/-- If `G` is not `α`-close to any of the three extremal graphs and the bipartition `p` has an
almost complete cut, then one side is not `α/24`-close to `T₂` or `T̄₂`. -/
theorem exists_side_not_close :
    ∀ α : ℝ, 0 < α → ∃ β₁ : ℝ, 0 < β₁ ∧ ∃ n₁ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 2) (β : ℝ), 0 ≤ β → β ≤ β₁ → n₁ ≤ Fintype.card V →
        (1 - β) * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (cutSize G (partClass p 0) : ℝ) →
        ¬ IsCloseToExtremal α G → ∃ i, ¬ IsSideClose (α / 24) G (partClass p i) := by
  intro α hα
  refine ⟨min (α / 6) ((α / 3) ^ 2), lt_min (by positivity) (by positivity), ⌈54 / α⌉₊ + 1,
    fun V _ _ G _ p β hβ0 hβ hn hcut hnc => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨X, hX, hXc, b₀, hX'⟩ := hcon 0
  obtain ⟨Y, hY, hYc, b₁, hY'⟩ := hcon 1
  apply hnc
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set a : ℝ := ((partClass p 0).card : ℝ)
  set b : ℝ := ((partClass p 1).card : ℝ)
  have hab : a + b = n := by
    have := card_partClass_add p
    simp only [a, b, hndef]; exact_mod_cast this
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hα54 : 54 ≤ α * n := by
    have h1 : ((⌈54 / α⌉₊ + 1 : ℕ) : ℝ) ≤ n := by simp only [hndef]; exact_mod_cast hn
    have h2 := Nat.le_ceil (54 / α)
    push_cast at h1
    have : 54 / α ≤ n := by linarith
    rwa [div_le_iff₀ hα, mul_comm] at this
  have hβ6 : β ≤ α / 6 := hβ.trans (min_le_left _ _)
  have hβ3 : β ≤ (α / 3) ^ 2 := hβ.trans (min_le_right _ _)
  set c : ℝ := (cutSize G (partClass p 0) : ℝ)
  have hcab : c ≤ a * b := by
    obtain ⟨hc0, -⟩ := cutSize_eq_sum_partDeg G p
    have : cutSize G (partClass p 0) ≤ (partClass p 0).card * (partClass p 1).card := by
      rw [hc0]
      calc ∑ v ∈ partClass p 0, partDeg G p v 1 ≤ ∑ _v ∈ partClass p 0, (partClass p 1).card :=
            sum_le_sum fun v _ => partDeg_le_card_partClass G p v 1
        _ = _ := by rw [sum_const, smul_eq_mul]
    simp only [c, a, b]; exact_mod_cast this
  -- balance of the two sides
  have hsq : (a - n / 2) ^ 2 ≤ (α / 3 * n / 2) ^ 2 := by
    have e1 : a * b = n ^ 2 / 4 - (a - n / 2) ^ 2 := by rw [← hab]; ring
    have e2 : β * n ^ 2 ≤ (α / 3) ^ 2 * n ^ 2 := mul_le_mul_of_nonneg_right hβ3 (sq_nonneg _)
    nlinarith
  have habs : |a - n / 2| ≤ α / 3 * n / 2 := by
    have := abs_le_of_sq_le_sq' hsq (by positivity)
    exact abs_le.mpr this
  obtain ⟨ha1, ha2⟩ := abs_le.mp habs
  -- the cost
  have hcost := patCost_glue G p (X := X) hY b₀ b₁
  have hcostθ : (patCost G (Pat b₀ b₁) (glueMap (partClass p 0) X Y) : ℝ) ≤
      α / 6 * n ^ 2 := by
    have e1 : (sideCost G (partClass p 0) X b₀ : ℝ) ≤ 2 * (α / 24) * a ^ 2 := hX'
    have e2 : (sideCost G (partClass p 1) Y b₁ : ℝ) ≤ 2 * (α / 24) * b ^ 2 := hY'
    have e3 : a ^ 2 + b ^ 2 ≤ n ^ 2 := by
      have ha0 : 0 ≤ a := Nat.cast_nonneg _
      have hb0 : 0 ≤ b := Nat.cast_nonneg _
      rw [← hab]; nlinarith
    have e4 : a * b ≤ n ^ 2 / 4 := by rw [← hab]; nlinarith [sq_nonneg (a - b)]
    have e5 : β * n ^ 2 ≤ α / 6 * n ^ 2 := mul_le_mul_of_nonneg_right hβ6 (sq_nonneg _)
    nlinarith
  -- the classes
  have hfib : ∀ i, |(fib (glueMap (partClass p 0) X Y) i : ℝ) - n / 4| ≤ α / 6 * n := by
    have hMN : ∀ y, y ∈ partClass p 1 ↔ y ∉ partClass p 0 := by
      intro y; simp only [partClass, mem_filter, mem_univ, true_and]
      rcases fin2_cases (p y) with h | h <;> simp [h]
    have hYN : Disjoint Y (partClass p 0) :=
      disjoint_left.mpr fun y hy hyN => (hMN y).mp (hY hy) hyN
    obtain ⟨f0, f1, f2, f3⟩ := fib_glueMap (partClass p 0) X Y hX hYN
    have hcomp : univ \ partClass p 0 = partClass p 1 := by
      ext y; simp only [mem_sdiff, mem_univ, true_and]; exact (hMN y).symm
    rw [hcomp] at f3
    have hXc' : (X.card : ℝ) * 2 ≤ a ∧ a ≤ X.card * 2 + 1 := by
      constructor
      · have : X.card * 2 ≤ (partClass p 0).card := by omega
        simp only [a]; exact_mod_cast this
      · have : (partClass p 0).card ≤ X.card * 2 + 1 := by omega
        simp only [a]; exact_mod_cast this
    have hYc' : (Y.card : ℝ) * 2 ≤ b ∧ b ≤ Y.card * 2 + 1 := by
      constructor
      · have : Y.card * 2 ≤ (partClass p 1).card := by omega
        simp only [b]; exact_mod_cast this
      · have : (partClass p 1).card ≤ Y.card * 2 + 1 := by omega
        simp only [b]; exact_mod_cast this
    have hXs : ((partClass p 0 \ X).card : ℝ) = a - X.card := by
      rw [card_sdiff_of_subset hX]; simp only [a]; push_cast [card_le_card hX]; ring
    have hYs : ((partClass p 1 \ Y).card : ℝ) = b - Y.card := by
      rw [card_sdiff_of_subset hY]; simp only [b]; push_cast [card_le_card hY]; ring
    have hb1 : b - n / 2 ≤ α / 3 * n / 2 := by linarith only [hab, ha1, ha2]
    have hb2 : -(α / 3 * n / 2) ≤ b - n / 2 := by linarith only [hab, ha1, ha2]
    have g0 : |(X.card : ℝ) - n / 4| ≤ α / 6 * n :=
      abs_le.mpr ⟨by linarith only [hXc'.1, hXc'.2, ha1, ha2, hα54], by linarith only [hXc'.1, hXc'.2, ha1, ha2, hα54]⟩
    have g1 : |(a - X.card : ℝ) - n / 4| ≤ α / 6 * n :=
      abs_le.mpr ⟨by linarith only [hXc'.1, hXc'.2, ha1, ha2, hα54], by linarith only [hXc'.1, hXc'.2, ha1, ha2, hα54]⟩
    have g2 : |(Y.card : ℝ) - n / 4| ≤ α / 6 * n :=
      abs_le.mpr ⟨by linarith only [hYc'.1, hYc'.2, hb1, hb2, hα54], by linarith only [hYc'.1, hYc'.2, hb1, hb2, hα54]⟩
    have g3 : |(b - Y.card : ℝ) - n / 4| ≤ α / 6 * n :=
      abs_le.mpr ⟨by linarith only [hYc'.1, hYc'.2, hb1, hb2, hα54], by linarith only [hYc'.1, hYc'.2, hb1, hb2, hα54]⟩
    have e0 : (fib (glueMap (partClass p 0) X Y) 0 : ℝ) = X.card := by rw [f0]
    have e1 : (fib (glueMap (partClass p 0) X Y) 1 : ℝ) = a - X.card := by rw [f1, hXs]
    have e2 : (fib (glueMap (partClass p 0) X Y) 2 : ℝ) = Y.card := by rw [f2]
    have e3 : (fib (glueMap (partClass p 0) X Y) 3 : ℝ) = b - Y.card := by rw [f3, hYs]
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [e0]; exact g0
    · rw [e1]; exact g1
    · rw [e2]; exact g2
    · rw [e3]; exact g3
  have := isCloseToExtremal_of_glue G (partClass p 0) X Y b₀ b₁ hcostθ hfib (by linarith)
  have h6 : 6 * (α / 6) = α := by ring
  rwa [h6] at this

end NashWilliams18
