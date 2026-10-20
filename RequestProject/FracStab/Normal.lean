/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.Structure

@[expose] public section

/-!
# Normal vertices and obtuse vertices of balanced bipartitions (Propositions 10.7 and 10.8)

For a balanced bipartition `A`, `B = (N(u) ∩ N(v)) ∖ A` of the common neighbourhood of a negative
edge `uv`:

* `otherSide` — the side not containing a given vertex;
* `IsNormalV α r u v A x` — `x` is in at most `r c` non-normal pairs with the other side
  (`c = |N(u) ∩ N(v)|`); this is our version of `α`-normal vertices;
* `card_not_normalV_le` (Proposition 10.7): at most `α c / (2 r)` vertices are not normal;
* `card_obtuse_le` (Proposition 10.8): for `p ∈ {u, v}`, at most `(1/2 + r) c + 1` vertices
  `y` of the common neighbourhood have `φ(py) < 0` (if `α ≤ 4 r²`);
* `card_normal_partners` — a normal vertex has at least `(c - 1)/2 - r c` normal partners.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- The side of the bipartition `(A, N(u) ∩ N(v) ∖ A)` not containing `x`. -/
def otherSide (u v : V) (A : Finset V) (x : V) : Finset V :=
  if x ∈ A then cn G u v \ A else A

open Classical in
/-- `x` is normal for the bipartition: it lies in at most `r c` non-normal pairs with the other
side. -/
def IsNormalV (α r : ℝ) (u v : V) (A : Finset V) (x : V) : Prop :=
  (((otherSide G u v A x).filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) ≤
    r * (cn G u v).card

lemma otherSide_subset {u v : V} {A : Finset V} (hA : A ⊆ cn G u v) (x : V) :
    otherSide G u v A x ⊆ cn G u v := by
  unfold otherSide; split_ifs
  · exact sdiff_subset
  · exact hA

lemma not_mem_otherSide {u v : V} {A : Finset V} {x : V} :
    x ∉ otherSide G u v A x := by
  unfold otherSide; split_ifs with h
  · simp [h]
  · exact h

lemma card_otherSide_ge {α : ℝ} {u v : V} {A : Finset V} (hA : IsBalBip G φ α u v A) (x : V) :
    ((cn G u v).card : ℝ) - 1 ≤ 2 * ((otherSide G u v A x).card : ℝ) := by
  obtain ⟨hA, h1, h2, -⟩ := hA
  have hs := card_sdiff_of_subset hA
  have hAc := card_le_card hA
  unfold otherSide; split_ifs
  · rw [hs, Nat.cast_sub hAc]
    have : (2 * A.card : ℝ) ≤ (cn G u v).card + 1 := by exact_mod_cast h1
    linarith
  · rw [hs] at h2
    have : (2 * ((cn G u v).card - A.card : ℕ) : ℝ) ≤ (cn G u v).card + 1 := by exact_mod_cast h2
    rw [Nat.cast_sub hAc] at this
    linarith

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Counting non-normal pairs from one side. -/
lemma sum_bad_eq (α : ℝ) (u v : V) (A B : Finset V) :
    (∑ x ∈ A, ((B.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ)) =
      (A.card : ℝ) * B.card - normalCount G φ α u v A B := by
  have h1 : ∀ x ∈ A, ((B.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) =
      B.card - ((B.filter fun b => NormalPair G φ α u v x b).card : ℝ) := by
    intro x _
    have := card_filter_add_card_filter_not (s := B) (fun b => NormalPair G φ α u v x b)
    have : ((B.filter fun b => NormalPair G φ α u v x b).card : ℝ) +
        ((B.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) = B.card := by
      exact_mod_cast this
    linarith
  rw [sum_congr rfl h1, sum_sub_distrib, sum_const, nsmul_eq_mul]
  congr 1
  unfold normalCount
  rw [card_filter, sum_product]
  push_cast
  refine sum_congr rfl fun x _ => ?_
  rw [card_filter]; push_cast; rfl

open Classical in
/-- **Proposition 10.7.** At most `α c / (2 r)` vertices of the common neighbourhood are not
normal for an `α`-balanced bipartition. -/
theorem card_not_normalV_le {α r : ℝ} (hr : 0 < r) {u v : V} {A : Finset V}
    (hA : IsBalBip G φ α u v A) :
    (((cn G u v).filter fun x => ¬ IsNormalV G φ α r u v A x).card : ℝ) ≤
      α * (cn G u v).card / (2 * r) := by
  obtain ⟨hAs, -, -, hN⟩ := hA
  set B := cn G u v \ A with hB
  set c : ℝ := ((cn G u v).card : ℝ) with hc
  have hcard : (A.card : ℝ) + B.card = c := by
    rw [hc, hB, card_sdiff_of_subset hAs, Nat.cast_sub (card_le_card hAs)]; ring
  have hAB : (A.card : ℝ) * B.card ≤ c ^ 2 / 4 := by nlinarith [sq_nonneg ((A.card : ℝ) - B.card)]
  set NA := A.filter fun x => ¬ IsNormalV G φ α r u v A x
  set NB := B.filter fun x => ¬ IsNormalV G φ α r u v A x
  have hsplit : (cn G u v).filter (fun x => ¬ IsNormalV G φ α r u v A x) ⊆ NA ∪ NB := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_union, mem_filter, mem_filter, hB, mem_sdiff]
    by_cases h : x ∈ A
    · exact Or.inl ⟨h, hx.2⟩
    · exact Or.inr ⟨⟨hx.1, h⟩, hx.2⟩
  -- bound for `NA`
  have bA : (NA.card : ℝ) * (r * c) ≤ α * c ^ 2 / 4 := by
    have hs := sum_bad_eq G φ α u v A B
    have : ∑ x ∈ NA, r * c ≤ ∑ x ∈ A, ((B.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) := by
      calc ∑ x ∈ NA, r * c ≤ ∑ x ∈ NA, ((B.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) := by
            refine sum_le_sum fun x hx => ?_
            rw [mem_filter] at hx
            have h2 := hx.2
            unfold IsNormalV otherSide at h2
            rw [if_pos hx.1] at h2
            push_neg at h2; exact h2.le
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    rw [sum_const, nsmul_eq_mul] at this
    nlinarith
  have bB : (NB.card : ℝ) * (r * c) ≤ α * c ^ 2 / 4 := by
    have hs := sum_bad_eq G φ α u v B A
    rw [normalCount_comm] at hs
    have : ∑ x ∈ NB, r * c ≤ ∑ x ∈ B, ((A.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) := by
      calc ∑ x ∈ NB, r * c ≤ ∑ x ∈ NB, ((A.filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) := by
            refine sum_le_sum fun x hx => ?_
            rw [mem_filter] at hx
            have h2 := hx.2
            unfold IsNormalV otherSide at h2
            have hxA : x ∉ A := (mem_sdiff.1 hx.1).2
            rw [if_neg hxA] at h2
            push_neg at h2; exact h2.le
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    rw [sum_const, nsmul_eq_mul] at this
    nlinarith
  have hle : (((cn G u v).filter fun x => ¬ IsNormalV G φ α r u v A x).card : ℝ) ≤ NA.card + NB.card := by
    exact_mod_cast (card_le_card hsplit).trans (card_union_le _ _)
  rcases (Nat.cast_nonneg (α := ℝ) (cn G u v).card).eq_or_lt with h0 | hcpos
  · have : (cn G u v).filter (fun x => ¬ IsNormalV G φ α r u v A x) = ∅ := by
      have : (cn G u v) = ∅ := by
        rw [← card_eq_zero]; exact_mod_cast h0.symm
      rw [this]; rfl
    rw [this, hc, ← h0]; simp
  · rw [← hc] at hcpos
    rw [le_div_iff₀ (by positivity)]
    have : ((NA.card : ℝ) + NB.card) * (r * c) ≤ α * c ^ 2 / 2 := by linarith
    have h3 : (((cn G u v).filter fun x => ¬ IsNormalV G φ α r u v A x).card : ℝ) * (r * c) ≤
        α * c ^ 2 / 2 := le_trans (mul_le_mul_of_nonneg_right hle (by positivity)) this
    nlinarith

open Classical in
/-- **Proposition 10.8.** If `p ∈ {u, v}` (more precisely `p` is adjacent to every common
neighbour) and `α ≤ 4 r²`, then at most `(1/2 + r) c + 1` common neighbours `y` have
`φ(py) < 0`. -/
theorem card_obtuse_le (hφ : GoodWeighting G φ) {α r : ℝ} (hr : 0 ≤ r) (hαr : α ≤ 4 * r ^ 2)
    {u v : V} {A : Finset V} (hA : IsBalBip G φ α u v A) (p : V)
    (hp : ∀ y ∈ cn G u v, G.Adj p y) :
    (((cn G u v).filter fun y => φ s(p, y) < 0).card : ℝ) ≤ (1 / 2 + r) * (cn G u v).card + 1 := by
  obtain ⟨hAs, h1, h2, hN⟩ := hA
  set B := cn G u v \ A with hB
  set c : ℝ := ((cn G u v).card : ℝ) with hc
  set P := (cn G u v).filter fun y => φ s(p, y) < 0
  set PA := A.filter fun y => φ s(p, y) < 0
  set PB := B.filter fun y => φ s(p, y) < 0
  have hcard : (A.card : ℝ) + B.card = c := by
    rw [hc, hB, card_sdiff_of_subset hAs, Nat.cast_sub (card_le_card hAs)]; ring
  have hAB : (A.card : ℝ) * B.card ≤ c ^ 2 / 4 := by nlinarith [sq_nonneg ((A.card : ℝ) - B.card)]
  have hPsplit : (P.card : ℝ) = PA.card + PB.card := by
    have : P = PA ∪ PB := by
      ext y; simp only [P, PA, PB, hB, mem_filter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨hy, hpy⟩
        by_cases h : y ∈ A
        · exact Or.inl ⟨h, hpy⟩
        · exact Or.inr ⟨⟨hy, h⟩, hpy⟩
      · rintro (⟨h, hpy⟩ | ⟨⟨hy, -⟩, hpy⟩)
        · exact ⟨hAs h, hpy⟩
        · exact ⟨hy, hpy⟩
    rw [this, card_union_of_disjoint]
    · push_cast; ring
    · rw [disjoint_left]; intro y hyA hyB
      simp only [PA, PB, hB, mem_filter, mem_sdiff] at hyA hyB
      exact hyB.1.2 hyA.1
  -- pairs between `PA` and `PB` are not normal
  have hdisj : Disjoint ((A ×ˢ B).filter fun q => NormalPair G φ α u v q.1 q.2) (PA ×ˢ PB) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ hq hq'
    simp only [mem_filter, mem_product, PA, PB] at hq hq'
    obtain ⟨⟨haA, hbB⟩, hab, habn, -⟩ := hq
    have hbcn : b ∈ cn G u v := (mem_sdiff.1 hbB).1
    have := hφ.cov p a b (hp a (hAs haA)) (hp b hbcn) hab
    linarith [hq'.1.2, hq'.2.2]
  have hsub : ((A ×ˢ B).filter fun q => NormalPair G φ α u v q.1 q.2) ∪ (PA ×ˢ PB) ⊆ A ×ˢ B :=
    union_subset (filter_subset _ _) (product_subset_product (filter_subset _ _) (filter_subset _ _))
  have hcnt := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_product, card_product] at hcnt
  have hcnt' : (normalCount G φ α u v A B : ℝ) + PA.card * PB.card ≤ A.card * B.card := by
    unfold normalCount; exact_mod_cast hcnt
  have hprod : (PA.card : ℝ) * PB.card ≤ r ^ 2 * c ^ 2 := by
    have : 0 ≤ c ^ 2 := sq_nonneg _
    nlinarith
  have hPA : (PA.card : ℝ) ≤ (c + 1) / 2 := by
    have := card_le_card (filter_subset (fun y => φ s(p, y) < 0) A)
    have h1' : (2 * A.card : ℝ) ≤ c + 1 := by rw [hc]; exact_mod_cast h1
    have : (PA.card : ℝ) ≤ A.card := by exact_mod_cast this
    linarith
  have hPB : (PB.card : ℝ) ≤ (c + 1) / 2 := by
    have := card_le_card (filter_subset (fun y => φ s(p, y) < 0) B)
    have h2' : (2 * B.card : ℝ) ≤ c + 1 := by rw [hc]; exact_mod_cast h2
    have : (PB.card : ℝ) ≤ B.card := by exact_mod_cast this
    linarith
  by_contra hcon
  push_neg at hcon
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have ha : r * c < PA.card := by linarith
  have hb : r * c < PB.card := by linarith
  have hrc : 0 ≤ r * c := mul_nonneg hr hc0
  have : (r * c) * (r * c) < PA.card * PB.card :=
    mul_lt_mul'' ha hb hrc hrc
  nlinarith

open Classical in
/-- A normal vertex has at least `(c - 1)/2 - r c` normal partners on the other side. -/
lemma card_normal_partners {α r : ℝ} {u v : V} {A : Finset V} (hA : IsBalBip G φ α u v A)
    {x : V} (hx : IsNormalV G φ α r u v A x) :
    ((cn G u v).card : ℝ) - 1 - 2 * r * (cn G u v).card ≤
      2 * (((otherSide G u v A x).filter fun b => NormalPair G φ α u v x b).card : ℝ) := by
  have h1 := card_otherSide_ge G φ hA x
  have h2 := card_filter_add_card_filter_not (s := otherSide G u v A x)
    (fun b => NormalPair G φ α u v x b)
  have h2' : (((otherSide G u v A x).filter fun b => NormalPair G φ α u v x b).card : ℝ) +
      (((otherSide G u v A x).filter fun b => ¬ NormalPair G φ α u v x b).card : ℝ) =
      (otherSide G u v A x).card := by exact_mod_cast h2
  unfold IsNormalV at hx
  linarith

end NashWilliams.Frac
