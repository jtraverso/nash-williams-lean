/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashBridge

/-! # BlowupB.KeevashPadded — the padded interface of `L3F0.KeevashF0Spec`, for every family

`L3F0/Keevash.lean` states the F₀ interface `KeevashF0Spec` (attributed there to Keevash,
*Coloured and directed designs*, arXiv:1807.05770v2, Theorem 5.15) with padded patterns, weights on
labelled embeddings (`PaddedRegular`) and extendability over all bounded templates
(`Extendable`). This file states the same shape for an arbitrary family `F` of 3-element types
on `t` classes:

* positions `PosT t m = Fin t × Fin (m + 3)` (class of `(c, j)` is `c`), `q = t (m + 3)`;
* the pattern of a type `τ`: the first `count c τ` positions of each class;
* `PaddedRegularT`: weights `y ∈ [ω n^{2−q}, ω⁻¹ n^{2−q}]` on valid copies, loads `1 ± c`;
* `ExtendableT`: every bounded template, with required pairs restricted to **allowed** class
  pairs (for `F₀` every class pair is allowed, so nothing is lost there);
* `KeevashPaddedSpec F`, with Keevash's `h = 2^{50 q³}`, `δ = 2^{−1000 q⁵}`, `c = ω^{h^{20}}`.

This part proves the counting lemma `count_ext` (sequential extensions of a partial embedding)
and `extendableT_of_cnExt`: common-neighbourhood extendability gives template extendability.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

/-- Positions of the padded patterns. -/
abbrev PosT (t m : ℕ) := Fin t × Fin (m + 3)

/-- `q = t (m + 3)`. -/
abbrev qT (t m : ℕ) : ℕ := t * (m + 3)

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pattern of a type: the first `count c τ` positions of each class `c`. -/
def patPosT (m : ℕ) (τ : Multiset (Fin t)) : Finset (PosT t m) :=
  univ.filter fun x => x.2.val < τ.count x.1

/-- The physical triangle of a copy. -/
def copyTriT (m : ℕ) (τ : Multiset (Fin t)) (φ : PosT t m → V) : Finset V := (patPosT m τ).image φ

/-- Class-respecting embedding of all positions. -/
def IsEmbT (m : ℕ) (p : V → Fin t) (φ : PosT t m → V) : Prop :=
  Function.Injective φ ∧ ∀ x, p (φ x) = x.1

/-- A copy of the pattern of `τ` in `J`. -/
def ValidCopyT (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V)) (τ : Multiset (Fin t))
    (φ : PosT t m → V) : Prop :=
  IsEmbT m p φ ∧ triEdges (copyTriT m τ φ) ⊆ J

open Classical in
/-- Padded regularity for the family `F`. -/
def PaddedRegularT (m : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V)) (ω c : ℝ) : Prop :=
  ∃ y : Multiset (Fin t) → (PosT t m → V) → ℝ,
    (∀ τ ∈ F, ∀ φ, ValidCopyT m p J τ φ →
      ω / (Fintype.card V : ℝ) ^ (qT t m - 2) ≤ y τ φ ∧
        y τ φ ≤ 1 / (ω * (Fintype.card V : ℝ) ^ (qT t m - 2))) ∧
    ∀ e ∈ J, |(∑ τ ∈ F, ∑ φ ∈ univ.filter (fun φ => ValidCopyT m p J τ φ ∧
      e ∈ triEdges (copyTriT m τ φ)), y τ φ) - 1| ≤ c

/-- The good extensions of `φ` from the roots `S` (domain `D`, labels `κ`, required pairs `T`). -/
noncomputable def goodExt {D : Type*} [Fintype D] [DecidableEq D] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V)) (κ : D → Fin t) (T : Finset (Sym2 D))
    (S : Finset D) (φ : D → V) : Finset (D → V) := by
  classical exact univ.filter fun ψ : D → V => (∀ x ∈ S, ψ x = φ x) ∧ Function.Injective ψ ∧
    (∀ x, p (ψ x) = κ x) ∧
    ∀ x y, s(x, y) ∈ T → x ≠ y → (x ∉ S ∨ y ∉ S) → AllowedPair F (κ x) (κ y) → s(ψ x, ψ y) ∈ J

/-- Template extendability for the family `F` (required pairs only on allowed class pairs). -/
def ExtendableT (K : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V))
    (ω : ℝ) : Prop :=
  ∀ k ≤ K, ∀ (κ : Fin k → Fin t) (S : Finset (Fin k)) (T : Finset (Sym2 (Fin k)))
    (φ : Fin k → V), Set.InjOn φ S → (∀ x ∈ S, p (φ x) = κ x) →
    ω * (Fintype.card V : ℝ) ^ (k - S.card) ≤ ((goodExt p F J κ T S φ).card : ℝ)

end Defs

/-- Keevash's `h = 2^{50 q³}`. -/
def hKT (t m : ℕ) : ℕ := 2 ^ (50 * qT t m ^ 3)

/-- Keevash's `δ = 2^{−1000 q⁵}`. -/
noncomputable def δKT (t m : ℕ) : ℝ := (2 : ℝ) ^ (-(1000 * (qT t m : ℝ) ^ 5))

/-- **Padded interface for the family `F`** (the shape of `L3F0.KeevashF0Spec`). -/
def KeevashPaddedSpec (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ m : ℕ, ∃ ω0 : ℝ, 0 < ω0 ∧ ∃ n0 : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V], n0 < Fintype.card V → ∀ ω : ℝ,
      (Fintype.card V : ℝ) ^ (-δKT t m) < ω → ω < ω0 →
      ∀ (p : V → Fin t) (J : Finset (Sym2 V)), (∀ e ∈ J, ¬ e.IsDiag) →
        (∀ u v, s(u, v) ∈ J → AllowedPair F (p u) (p v)) →
        (∀ i, (Fintype.card V : ℝ) / hKT t m ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        IsIntDiv p F J → PaddedRegularT m p F J ω (ω ^ (hKT t m ^ 20)) →
        ExtendableT (qT t m * hKT t m) p F J ω → HasDecomp p F J

section Count

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Sequential extension count.** If every class keeps `≥ s` admissible candidates outside
any `≤ |D|` used vertices, adjacent to any prescribed subset joined by allowed pairs, then a
partial embedding on `S` has `≥ s^{|D| − |S|}` good extensions. -/
theorem count_ext {D : Type*} [Fintype D] [DecidableEq D] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V)) (κ : D → Fin t) (T : Finset (Sym2 D))
    (s : ℝ) (hs : 0 ≤ s)
    (hcn : ∀ (S' A : Finset V) (i : Fin t), S'.card ≤ Fintype.card D → A ⊆ S' →
      (∀ a ∈ A, AllowedPair F (p a) i) →
      s ≤ ((univ.filter fun v => p v = i ∧ v ∉ S' ∧ ∀ a ∈ A, s(a, v) ∈ J).card : ℝ)) :
    ∀ (d : ℕ) (S : Finset D) (φ : D → V), Fintype.card D - S.card = d → Set.InjOn φ S →
      (∀ x ∈ S, p (φ x) = κ x) → s ^ d ≤ ((goodExt p F J κ T S φ).card : ℝ) := by
  classical
  intro d
  induction d with
  | zero =>
    intro S φ hd hinj hlab
    have hS : S = univ := by
      apply eq_univ_of_card
      have := card_le_univ S
      omega
    subst hS
    have hmem : φ ∈ goodExt p F J κ T univ φ := by
      unfold goodExt
      rw [mem_filter]
      refine ⟨mem_univ _, fun _ _ => rfl, fun a b h => hinj (mem_coe.mpr (mem_univ a))
        (mem_coe.mpr (mem_univ b)) h, fun x => hlab x (mem_univ x), ?_⟩
      intro x y _ _ h
      rcases h with h | h <;> exact absurd (mem_univ _) h
    rw [pow_zero]
    exact_mod_cast card_pos.mpr ⟨φ, hmem⟩
  | succ d ih =>
    intro S φ hd hinj hlab
    have hlt : S.card < (univ : Finset D).card := by rw [card_univ]; omega
    obtain ⟨x, -, hxS⟩ := exists_mem_notMem_of_card_lt_card hlt
    set Sset := S.image φ with hSset
    set A := (S.filter fun y => s(x, y) ∈ T ∧ AllowedPair F (κ x) (κ y)).image φ with hA
    set cand := univ.filter fun v => p v = κ x ∧ v ∉ Sset ∧ ∀ a ∈ A, s(a, v) ∈ J with hcand
    have hcs : s ≤ (cand.card : ℝ) := by
      refine hcn Sset A (κ x) (card_image_le.trans (card_le_univ S)) ?_ ?_
      · exact image_subset_image (filter_subset _ _)
      · intro a ha
        obtain ⟨y, hy, rfl⟩ := mem_image.mp ha
        obtain ⟨hyS, -, hal⟩ := mem_filter.mp hy
        rw [hlab y hyS]
        exact hal.symm
    -- extensions through each candidate
    let φv : V → D → V := fun v => Function.update φ x v
    have hd' : Fintype.card D - (insert x S).card = d := by
      rw [card_insert_of_notMem hxS]; omega
    have hgood : ∀ v ∈ cand, s ^ d ≤ ((goodExt p F J κ T (insert x S) (φv v)).card : ℝ) := by
      intro v hv
      obtain ⟨hvx, hvS, -⟩ := (mem_filter.mp hv).2
      refine ih (insert x S) (φv v) hd' ?_ ?_
      · intro a ha b hb hab
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
        simp only [φv] at hab
        by_cases hax : a = x <;> by_cases hbx : b = x
        · rw [hax, hbx]
        · have hbS : b ∈ S := hb.resolve_left hbx
          rw [hax, Function.update_self, Function.update_of_ne hbx] at hab
          exact absurd (hab ▸ mem_image_of_mem φ hbS) hvS
        · have haS : a ∈ S := ha.resolve_left hax
          rw [hbx, Function.update_self, Function.update_of_ne hax] at hab
          exact absurd (hab.symm ▸ mem_image_of_mem φ haS) hvS
        · rw [Function.update_of_ne hax, Function.update_of_ne hbx] at hab
          exact hinj (ha.resolve_left hax) (hb.resolve_left hbx) hab
      · intro y hy
        by_cases hyx : y = x
        · rw [hyx]; simp only [φv, Function.update_self]; exact hvx
        · have hyS : y ∈ S := (mem_insert.mp hy).resolve_left hyx
          simp only [φv, Function.update_of_ne hyx]; exact hlab y hyS
    have hsub : cand.biUnion (fun v => goodExt p F J κ T (insert x S) (φv v)) ⊆
        goodExt p F J κ T S φ := by
      intro ψ hψ
      obtain ⟨v, hv, hψv⟩ := mem_biUnion.mp hψ
      obtain ⟨hvx, hvS, hvA⟩ := (mem_filter.mp hv).2
      simp only [goodExt, mem_filter, mem_univ, true_and] at hψv ⊢
      obtain ⟨h1, h2, h3, h4⟩ := hψv
      have hψx : ψ x = v := by
        have := h1 x (mem_insert_self x S); simpa [φv] using this
      have hψS : ∀ y ∈ S, ψ y = φ y := fun y hy => by
        have := h1 y (mem_insert_of_mem hy)
        simpa [φv, Function.update_of_ne (show y ≠ x by rintro rfl; exact hxS hy)] using this
      refine ⟨hψS, h2, h3, ?_⟩
      intro a b hab hne hout hal
      by_cases hout' : a ∉ insert x S ∨ b ∉ insert x S
      · exact h4 a b hab hne hout' hal
      push Not at hout'
      obtain ⟨ha', hb'⟩ := hout'
      rcases hout with ha | hb
      · have hax : a = x := by
          rcases mem_insert.mp ha' with h | h
          · exact h
          · exact absurd h ha
        subst hax
        have hbS : b ∈ S := by
          rcases mem_insert.mp hb' with h | h
          · exact absurd h.symm hne
          · exact h
        have hbA : φ b ∈ A := mem_image_of_mem φ (mem_filter.mpr ⟨hbS, hab, hal⟩)
        rw [hψx, hψS b hbS, Sym2.eq_swap]
        exact hvA _ hbA
      · have hbx : b = x := by
          rcases mem_insert.mp hb' with h | h
          · exact h
          · exact absurd h hb
        subst hbx
        have haS : a ∈ S := by
          rcases mem_insert.mp ha' with h | h
          · exact absurd h hne
          · exact h
        have haA : φ a ∈ A := mem_image_of_mem φ (mem_filter.mpr ⟨haS,
          by rw [Sym2.eq_swap]; exact hab, hal.symm⟩)
        rw [hψx, hψS a haS]
        exact hvA _ haA
    have hdisj : (cand : Set V).PairwiseDisjoint (fun v => goodExt p F J κ T (insert x S) (φv v)) := by
      intro v _ w _ hvw
      refine disjoint_left.mpr fun ψ hψv hψw => hvw ?_
      simp only [goodExt, mem_filter, mem_univ, true_and] at hψv hψw
      have e1 := hψv.1 x (mem_insert_self x S)
      have e2 := hψw.1 x (mem_insert_self x S)
      simp only [φv, Function.update_self] at e1 e2
      rw [← e1, ← e2]
    have hcard := card_le_card hsub
    rw [card_biUnion hdisj] at hcard
    have hsum : (cand.card : ℝ) * s ^ d ≤
        ∑ v ∈ cand, ((goodExt p F J κ T (insert x S) (φv v)).card : ℝ) := by
      have := card_nsmul_le_sum cand (fun v => ((goodExt p F J κ T (insert x S) (φv v)).card : ℝ))
        (s ^ d) hgood
      rwa [nsmul_eq_mul] at this
    have hcardR : ∑ v ∈ cand, ((goodExt p F J κ T (insert x S) (φv v)).card : ℝ) ≤
        ((goodExt p F J κ T S φ).card : ℝ) := by
      exact_mod_cast hcard
    calc s ^ (d + 1) = s * s ^ d := by ring
      _ ≤ (cand.card : ℝ) * s ^ d := mul_le_mul_of_nonneg_right hcs (pow_nonneg hs d)
      _ ≤ _ := hsum.trans hcardR

/-- **Common-neighbourhood extendability gives template extendability.** -/
theorem extendableT_of_cnExt {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω : ℝ} {K : ℕ} (hω : 0 < ω) (hω1 : ω ≤ 1) (hC : CNExt p F J ω K) :
    ExtendableT K p F J (ω ^ K) := by
  intro k hk κ S T φ hinj hlab
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hcount := count_ext p F J κ T (ω * Fintype.card V) (mul_nonneg hω.le hn)
    (fun S' A i hS' hA hal => hC S' A i (by rw [Fintype.card_fin] at hS'; omega) hA hal)
    (Fintype.card (Fin k) - S.card) S φ rfl hinj hlab
  rw [Fintype.card_fin] at hcount
  have hj : k - S.card ≤ K := by omega
  calc ω ^ K * (Fintype.card V : ℝ) ^ (k - S.card)
      ≤ ω ^ (k - S.card) * (Fintype.card V : ℝ) ^ (k - S.card) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hω.le hω1 hj) (pow_nonneg hn _)
    _ = (ω * Fintype.card V) ^ (k - S.card) := (mul_pow _ _ _).symm
    _ ≤ _ := hcount

end Count

end PartitionedTriangleAbsorption.BlowupB
