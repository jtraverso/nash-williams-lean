/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TypicalReserveMain

/-! # BlowupB.TeoremaB — Theorem B (nearly complete blowups, every family) from Keevash

**`teoremaB_of_keevash`**. Let `F` be a family of 3-element types and assume the typed Keevash
interface `KeevashTypedSpec F`. For every `γ, ω₁ > 0` there are `ε, δ > 0` and `N` such that
every graph `G` on `n ≥ N` vertices using only allowed pairs, with at most `δ n` allowed
non-neighbours per vertex and classes of size `≥ γ n`, which is integrally `F`-divisible
(Definition 13.5) and admits **type weights** `ω₁ ≤ wt τ ≤ 1/ω₁` solving the load equations of
the complete blowup up to `ε`,

`|∑_τ wt τ · (∑_{c : c ::ₘ {a,b} = τ} (|V_c| - count c {a,b})) / n - 1| ≤ ε` for allowed `ab`,

has an `F`-decomposition. No hinge hypothesis is needed. The weight condition is the
fractional hypothesis required by `typeLoad_obstruction_001_012` (it fails for `{001, 012}` with
equal classes).

Proof: `G` is `CNExt` (common neighbourhoods lose at most `h δ n`), `TriRegular` by
`triRegular_union` with `L = ∅` (typed-thirds counts are within `2 δ n + 2 t` of the complete
counts), and `IsIntDiv`; apply the interface.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

section Host

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Typed-thirds counts in a nearly complete host. -/
theorem thirds_host_count (F : Finset (Multiset (Fin t))) (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hmiss : ∀ v, missDeg p F G v ≤ d)
    (hadj : ∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) {u v : V} (huv : u ≠ v)
    {τ : Multiset (Fin t)} (hτ : τ ∈ F) :
    |((thirdsT p G.edgeFinset u v τ).card : ℝ) -
      ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
        nPrime (clsz p) {p u, p v} c| ≤ 2 * d + 2 * t := by
  classical
  set K3f : Finset V := univ.filter fun w => w ≠ u ∧ w ≠ v ∧
    ({p u, p v, p w} : Multiset (Fin t)) = τ with hK3f
  have hsub : thirdsT p G.edgeFinset u v τ ⊆ K3f := by
    intro w hw
    simp only [thirdsT, mem_filter, mem_univ, true_and] at hw
    exact mem_filter.mpr ⟨mem_univ _, hw.1, hw.2.1, hw.2.2.2.2⟩
  have hdiff : (K3f \ thirdsT p G.edgeFinset u v τ) ⊆ missSet p F G u ∪ missSet p F G v := by
    intro w hw
    obtain ⟨hwf, hwT⟩ := mem_sdiff.mp hw
    obtain ⟨h1, h2, h5⟩ := (mem_filter.mp hwf).2
    have hτ' : p w ::ₘ ({p u, p v} : Multiset (Fin t)) ∈ F := by rw [← triRot3, h5]; exact hτ
    obtain ⟨-, hwu, hwv⟩ := allowed_of_cons hτ'
    by_cases hu : G.Adj u w
    · by_cases hv : G.Adj v w
      · exfalso; apply hwT
        simp only [thirdsT, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet]
        exact ⟨h1, h2, hu, hv, h5⟩
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, Ne.symm h2, hwv.symm, hv⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, Ne.symm h1, hwu.symm, hu⟩)
  have hcardd : ((K3f \ thirdsT p G.edgeFinset u v τ).card : ℝ) ≤ 2 * d := by
    have := (card_le_card hdiff).trans (card_union_le _ _)
    have h1 := hmiss u; have h2 := hmiss v
    unfold missDeg at h1 h2
    have : (K3f \ thirdsT p G.edgeFinset u v τ).card ≤ 2 * d := by omega
    exact_mod_cast this
  have hsplit : ((K3f).card : ℝ) = (thirdsT p G.edgeFinset u v τ).card +
      (K3f \ thirdsT p G.edgeFinset u v τ).card := by
    rw [← card_sdiff_add_card_eq_card hsub]; push_cast; ring
  -- `K3f` against the complete counts
  set Wc : Fin t → Finset V := fun c => univ.filter fun w => p w = c ∧ w ≠ u ∧ w ≠ v with hWc
  have hfib : ((K3f).card : ℝ) =
      ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ), ((Wc c).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum,
      ← sum_fiberwise_of_maps_to (g := p) (t := (univ : Finset (Fin t))) (fun _ _ => mem_univ _),
      sum_filter]
    refine sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · have e : K3f.filter (fun w => p w = c) = Wc c := by
        ext w
        simp only [hK3f, hWc, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, h2, -⟩, h4⟩; exact ⟨h4, h1, h2⟩
        · rintro ⟨h4, h1, h2⟩
          refine ⟨⟨h1, h2, ?_⟩, h4⟩
          rw [triRot3, h4]; exact hc
      rw [e]
      simp
    · refine sum_eq_zero fun w hw => ?_
      exfalso
      obtain ⟨hwf, hwc⟩ := mem_filter.mp hw
      obtain ⟨-, -, h5⟩ := (mem_filter.mp hwf).2
      apply hc
      rw [← hwc, ← triRot3]; exact h5
  have hfull : |((K3f).card : ℝ) -
      ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
        nPrime (clsz p) {p u, p v} c| ≤ 2 * t := by
    rw [hfib, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
        |((Wc c).card : ℝ) - nPrime (clsz p) {p u, p v} c| ≤ 2 := by
      intro c _
      have hw1 := card_filter_ne_ne_le p u v c
      have hw2 := clsz_le_card_filter_ne_ne p u v c
      have hc2 := count_pair_le_two (p u) (p v) c
      have hc0 := count_nonneg' ({p u, p v} : Multiset (Fin t)) c
      unfold nPrime
      rw [abs_sub_le_iff]; constructor <;> linarith
    calc ∑ c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ),
          |((Wc c).card : ℝ) - nPrime (clsz p) {p u, p v} c|
        ≤ ∑ _c ∈ univ.filter (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ), (2 : ℝ) :=
          sum_le_sum hterm
      _ ≤ 2 * t := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have := card_filter_le (univ : Finset (Fin t))
            (fun c => c ::ₘ ({p u, p v} : Multiset (Fin t)) = τ)
          rw [card_univ, Fintype.card_fin] at this
          exact_mod_cast this
  have h0 : (0 : ℝ) ≤ (K3f \ thirdsT p G.edgeFinset u v τ).card := Nat.cast_nonneg _
  rw [abs_sub_le_iff] at hfull ⊢
  constructor <;> linarith [hfull.1, hfull.2]

/-- Common neighbourhoods in a nearly complete host. -/
theorem cnExt_host (F : Finset (Multiset (Fin t))) (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (d h : ℕ) (γ ω : ℝ) (hmiss : ∀ v, missDeg p F G v ≤ d)
    (hcls : ∀ i, γ * Fintype.card V ≤ clsz p i)
    (hbig : ω * Fintype.card V + h + h * d ≤ γ * Fintype.card V) :
    CNExt p F G.edgeFinset ω h := by
  classical
  intro S A i hS hA hal
  have hsub : (univ.filter fun x => p x = i) ⊆
      (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ G.edgeFinset) ∪ S ∪
        A.biUnion (fun a => missSet p F G a) := by
    intro x hx
    have hxi : p x = i := (mem_filter.mp hx).2
    by_cases hxS : x ∈ S
    · exact mem_union_left _ (mem_union_right _ hxS)
    by_cases hall : ∀ a ∈ A, s(a, x) ∈ G.edgeFinset
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hxi, hxS, hall⟩))
    · push Not at hall
      obtain ⟨a, ha, haE⟩ := hall
      refine mem_union_right _ (mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩⟩)
      · rintro rfl; exact hxS (hA ha)
      · rw [hxi]; exact hal a ha
      · intro hadj; exact haE (SimpleGraph.mem_edgeFinset.mpr hadj)
  have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have h2 : (A.biUnion fun a => missSet p F G a).card ≤ h * d := by
    refine card_biUnion_le.trans ?_
    calc ∑ a ∈ A, (missSet p F G a).card ≤ ∑ _a ∈ A, d := sum_le_sum fun a _ => hmiss a
      _ = A.card * d := by rw [sum_const, smul_eq_mul]
      _ ≤ h * d := Nat.mul_le_mul_right _ ((card_le_card hA).trans hS)
  have h3 : ((univ.filter fun x => p x = i).card : ℝ) ≤
      ((univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ G.edgeFinset).card : ℝ) +
        h + h * d := by
    have : (univ.filter fun x => p x = i).card ≤
        (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ G.edgeFinset).card +
          h + h * d := by omega
    exact_mod_cast this
  have := hcls i
  unfold clsz at this
  linarith

end Host

/-- **Theorem B for every family, from the typed Keevash interface.** -/
theorem teoremaB_of_keevash {F : Finset (Multiset (Fin t))} (hK : KeevashTypedSpec F)
    (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin t) → ℝ, (∀ τ ∈ F, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, AllowedPair F a b →
            |(∑ τ ∈ F, wt τ * ((∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) = τ),
              nPrime (clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset := by
  obtain ⟨h, ω₀, hω₀, hKv⟩ := hK γ hγ
  set ω : ℝ := min (min ω₁ ω₀) (γ / 2) with hωdef
  have hω : 0 < ω := lt_min (lt_min hω₁ hω₀) (by positivity)
  have hωω₁ : ω ≤ ω₁ := (min_le_left _ _).trans (min_le_left _ _)
  obtain ⟨c, hc, n₀, hKn⟩ := hKv ω hω ((min_le_left _ _).trans (min_le_right _ _))
  set ε : ℝ := c / (4 * (1 + F.card / ω₁)) with hεdef
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, max n₀ (max ⌈4 * ((t : ℝ) + h + 1) / min ε γ⌉₊ 1),
    min (ε / 4) (γ / (4 * ((h : ℝ) + 1))), lt_min (by positivity) (by positivity), ?_⟩
  intro V _ _ G _ p d hN hadj hmiss hd hcls hwt hdiv
  classical
  have hn0 : n₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  have hNb : ⌈4 * ((t : ℝ) + h + 1) / min ε γ⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hnb : 4 * ((t : ℝ) + h + 1) / min ε γ ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNb)
  have hmεγ : 0 < min ε γ := lt_min hε hγ
  have hnb' : 4 * ((t : ℝ) + h + 1) ≤ min ε γ * Fintype.card V := by
    have := (div_le_iff₀ hmεγ).mp hnb; linarith
  have hεn : 4 * ((t : ℝ) + h + 1) ≤ ε * Fintype.card V :=
    hnb'.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le)
  have hγn : 4 * ((t : ℝ) + h + 1) ≤ γ * Fintype.card V :=
    hnb'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le)
  have hdε : (d : ℝ) ≤ ε / 4 * Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le)
  have hdγ : (d : ℝ) ≤ γ / (4 * ((h : ℝ) + 1)) * Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le)
  obtain ⟨wt, hwtb, hload⟩ := hwt
  have hedge : ∀ u v, s(u, v) ∈ G.edgeFinset ∪ ∅ → u ≠ v ∧ AllowedPair F (p u) (p v) := by
    intro u v huv
    rw [union_empty, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
    exact ⟨huv.ne, hadj u v huv⟩
  refine hKn p G.edgeFinset hn0 hcls ?_ (fun u v huv => hadj u v
    (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp huv))) ?_ ?_ hdiv
  · intro e he hdiag
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he) hdiag
  · -- regularity
    have hreg := triRegular_union (p := p) (F := F) (C := G.edgeFinset) (L := ∅) (ω := ω)
      (ωR := ω₁) (ε := ε) (c := c) wt
      (fun τ a b => (∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin t)) = τ),
        nPrime (clsz p) {a, b} c) / Fintype.card V) hn hω hωω₁ hwtb hload hedge
      (by
        intro u v huv hal τ hτ
        have := thirds_host_count F p G d hmiss hadj huv hτ
        rw [div_mul_cancel₀ _ hn.ne']
        have h2 : (2 : ℝ) * d + 2 * t ≤ ε * Fintype.card V := by linarith
        exact this.trans h2)
      (by
        have hW : ∑ τ ∈ F, wt τ ≤ F.card / ω₁ := by
          have := sum_le_card_nsmul F wt (1 / ω₁) fun τ hτ => (hwtb τ hτ).2
          rw [nsmul_eq_mul] at this
          calc ∑ τ ∈ F, wt τ ≤ (F.card : ℝ) * (1 / ω₁) := this
            _ = F.card / ω₁ := by ring
        have hA : 0 < 1 + (F.card : ℝ) / ω₁ := by positivity
        have e : ε * (1 + F.card / ω₁) = c / 4 := by rw [hεdef]; field_simp
        have h1 : ε * (1 + ∑ τ ∈ F, wt τ) ≤ ε * (1 + F.card / ω₁) :=
          mul_le_mul_of_nonneg_left (by linarith) hε.le
        rw [card_empty, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
        nlinarith)
    rwa [union_empty] at hreg
  · -- extendability
    refine cnExt_host F p G d h γ ω hmiss hcls ?_
    have h1 : ω * Fintype.card V ≤ γ / 2 * Fintype.card V :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le
    have h2 : (h : ℝ) * d ≤ γ / 4 * Fintype.card V := by
      have e1 : (h : ℝ) * d ≤ h * (γ / (4 * ((h : ℝ) + 1)) * Fintype.card V) :=
        mul_le_mul_of_nonneg_left hdγ (Nat.cast_nonneg _)
      have e2 : (h : ℝ) * (γ / (4 * ((h : ℝ) + 1)) * Fintype.card V) ≤
          γ / 4 * Fintype.card V := by
        have : (h : ℝ) * (γ / (4 * ((h : ℝ) + 1))) ≤ γ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        nlinarith
      linarith
    have h3 : (h : ℝ) ≤ γ / 4 * Fintype.card V := by linarith
    linarith

end PartitionedTriangleAbsorption.BlowupB
