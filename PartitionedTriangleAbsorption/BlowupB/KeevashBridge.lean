/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Splitting
public import PartitionedTriangleAbsorption.BlowupB.IntVec

/-! # BlowupB.KeevashBridge — nearly-complete absorbers from a typed Keevash interface

Two interfaces, stated in the language of this library:

* `KeevashTypedSpec F`: modelled on Keevash, *The existence of designs II*
  (arXiv 1802.05900v1), Theorem 3.1 (our own specialisation, not checked against any other
  formalisation; see `KeevashPadded` for the form of `L3F0.KeevashF0Spec`), with labels `Fin t × Fin 3`, one molecule per type, and
  `IsIntDiv` as lattice (`isIntDiv_iff_physDiv_uniform`). Regularity is stated with weights on
  typed triangles (`TriRegular`), extendability with common neighbourhoods (`CNExt`). Splitting
  triangle weights uniformly over the labelled embeddings gives Keevash's Definition 2.37;
  sequential embedding gives his Definitions 2.9–2.10.
* `ReserveSpec F h`: a sparse decomposable reserve `C` avoiding `B ∪ X` whose typed-triangle
  counts through every allowed pair are `(1 ± ε) κ n`, with type weights solving the load
  equations. (Paper proof: binomial graph with densities in the interior of the type cone,
  Chernoff, and an almost perfect packing by Keevash's Lemma 3.6; see
  `cegis/b0_refiner/KEEVASH_RESERVA_PRUEBA_20261011.md`.)

**`nearlyAbsorbing_of_keevash`**: the two interfaces give `NearlyAbsorbing F`. The deterministic
part is proved here: regularity of `C ∪ L` for every `L ⊆ X` with `|X| ≤ K`
(`triRegular_union`), monotonicity of extendability, and divisibility of `C ∪ L`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Third vertices `w` closing a triangle `{u, v, w}` of type `τ` with `uw, vw ∈ G`. -/
def thirdsT (p : V → Fin t) (G : Finset (Sym2 V)) (u v : V) (τ : Multiset (Fin t)) :
    Finset V :=
  univ.filter fun w => w ≠ u ∧ w ≠ v ∧ s(u, w) ∈ G ∧ s(v, w) ∈ G ∧
    ({p u, p v, p w} : Multiset (Fin t)) = τ

/-- Regularity with weights on typed triangles: every typed triangle of `G` has weight in
`[ω/n, 1/(ω n)]` and every edge of `G` has load `1 ± c`. -/
def TriRegular (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : Finset (Sym2 V))
    (ω c : ℝ) : Prop :=
  ∃ y : Finset V → ℝ,
    (∀ s : Finset V, IsTypedTri p F s → triEdges s ⊆ G →
      ω / Fintype.card V ≤ y s ∧ y s ≤ 1 / (ω * Fintype.card V)) ∧
    ∀ u v, s(u, v) ∈ G → |(∑ τ ∈ F, ∑ w ∈ thirdsT p G u v τ, y {u, v, w}) - 1| ≤ c

/-- Extendability by common neighbourhoods: for every `S` with `|S| ≤ h`, every class `i` and
every `A ⊆ S` joined to `i` by allowed pairs, at least `ω n` vertices of class `i` outside `S`
are `G`-adjacent to all of `A`. -/
def CNExt (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : Finset (Sym2 V)) (ω : ℝ)
    (h : ℕ) : Prop :=
  ∀ (S A : Finset V) (i : Fin t), S.card ≤ h → A ⊆ S → (∀ a ∈ A, AllowedPair F (p a) i) →
    ω * Fintype.card V ≤
      ((univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ G).card : ℝ)

end Defs

/-- **Typed Keevash interface** (specialisation of Keevash, Designs II, Theorem 3.1). -/
def KeevashTypedSpec (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ γ : ℝ, 0 < γ →
  ∃ (h : ℕ) (ω₀ : ℝ), 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin t) (G : Finset (Sym2 V)),
      n₀ ≤ Fintype.card V →
      (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
      (∀ e ∈ G, ¬ e.IsDiag) →
      (∀ u v, s(u, v) ∈ G → AllowedPair F (p u) (p v)) →
      TriRegular p F G ω c → CNExt p F G ω h → IsIntDiv p F G → HasDecomp p F G

/-- **Reserve interface**: sparse decomposable reserves with controlled typed-triangle counts. -/
def ReserveSpec (F : Finset (Multiset (Fin t))) (h : ℕ) : Prop :=
  ∀ (K : ℕ) (gamma eta : ℝ), 0 < gamma → 0 < eta → ∃ ωR : ℝ, 0 < ωR ∧
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, gamma * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        ∀ B X : Finset (Sym2 V), DegBounded B (δ * Fintype.card V) →
          X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
          ∃ C ⊆ G.edgeFinset, Disjoint C (B ∪ X) ∧ HasDecomp p F C ∧
            DegBounded C (eta * Fintype.card V) ∧ CNExt p F C ωR h ∧
            ∃ (wt : Multiset (Fin t) → ℝ) (κ : Multiset (Fin t) → Fin t → Fin t → ℝ),
              (∀ τ ∈ F, ωR ≤ wt τ ∧ wt τ ≤ 1 / ωR) ∧
              (∀ a b, AllowedPair F a b → |(∑ τ ∈ F, wt τ * κ τ a b) - 1| ≤ ε) ∧
              ∀ u v, u ≠ v → AllowedPair F (p u) (p v) → ∀ τ ∈ F,
                |((thirdsT p C u v τ).card : ℝ) - κ τ (p u) (p v) * Fintype.card V| ≤
                  ε * Fintype.card V

section Deterministic

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem map_val_triple (p : V → Fin t) {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v, w} : Finset V).val.map p = ({p u, p v, p w} : Multiset (Fin t)) := by
  rw [Finset.insert_val_of_notMem (by simp [huv, huw]),
    Finset.insert_val_of_notMem (by simp [hvw])]
  simp

theorem thirdsT_mono (p : V → Fin t) {G G' : Finset (Sym2 V)} (hG : G ⊆ G') (u v : V)
    (τ : Multiset (Fin t)) : thirdsT p G u v τ ⊆ thirdsT p G' u v τ := by
  intro w hw
  simp only [thirdsT, mem_filter, mem_univ, true_and] at hw ⊢
  exact ⟨hw.1, hw.2.1, hG hw.2.2.1, hG hw.2.2.2.1, hw.2.2.2.2⟩

theorem card_filter_pair_le (L : Finset (Sym2 V)) (u : V) :
    (univ.filter fun w => s(u, w) ∈ L).card ≤ L.card := by
  refine card_le_card_of_injOn (fun w => s(u, w)) ?_ ?_
  · intro w hw
    exact (mem_filter.mp hw).2
  · intro a _ b _ hab
    exact Sym2.congr_right.mp hab

theorem card_thirdsT_union_le (p : V → Fin t) (C L : Finset (Sym2 V)) (u v : V)
    (τ : Multiset (Fin t)) :
    (thirdsT p (C ∪ L) u v τ).card ≤ (thirdsT p C u v τ).card + 2 * L.card := by
  have hsub : thirdsT p (C ∪ L) u v τ ⊆ thirdsT p C u v τ ∪
      ((univ.filter fun w => s(u, w) ∈ L) ∪ (univ.filter fun w => s(v, w) ∈ L)) := by
    intro w hw
    simp only [thirdsT, mem_filter, mem_univ, true_and, mem_union] at hw ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw
    by_cases hu : s(u, w) ∈ L
    · exact Or.inr (Or.inl hu)
    by_cases hv : s(v, w) ∈ L
    · exact Or.inr (Or.inr hv)
    exact Or.inl ⟨h1, h2, h3.resolve_right hu, h4.resolve_right hv, h5⟩
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have := (card_union_le (univ.filter fun w => s(u, w) ∈ L)
    (univ.filter fun w => s(v, w) ∈ L)).trans
    (add_le_add (card_filter_pair_le L u) (card_filter_pair_le L v))
  omega

theorem CNExt.mono {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G G' : Finset (Sym2 V)}
    {ω ω' : ℝ} {h : ℕ} (hGG : G ⊆ G') (hω : ω' ≤ ω) (hC : CNExt p F G ω h) :
    CNExt p F G' ω' h := by
  intro S A i hS hA hal
  refine le_trans (mul_le_mul_of_nonneg_right hω (Nat.cast_nonneg _))
    (le_trans (hC S A i hS hA hal) ?_)
  exact_mod_cast card_le_card fun v hv => by
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    exact ⟨hv.1, hv.2.1, fun a ha => hGG (hv.2.2 a ha)⟩

/-- **Regularity of `C ∪ L`** from type weights solving the load equations up to `ε` and
typed-triangle counts `κ n ± ε n` in `C`. -/
theorem triRegular_union {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {C L : Finset (Sym2 V)} {ω ωR ε c : ℝ}
    (wt : Multiset (Fin t) → ℝ) (κ : Multiset (Fin t) → Fin t → Fin t → ℝ)
    (hn : 0 < (Fintype.card V : ℝ)) (hω : 0 < ω) (hωR : ω ≤ ωR)
    (hwt : ∀ τ ∈ F, ωR ≤ wt τ ∧ wt τ ≤ 1 / ωR)
    (hload : ∀ a b, AllowedPair F a b → |(∑ τ ∈ F, wt τ * κ τ a b) - 1| ≤ ε)
    (hedge : ∀ u v, s(u, v) ∈ C ∪ L → u ≠ v ∧ AllowedPair F (p u) (p v))
    (hcount : ∀ u v, u ≠ v → AllowedPair F (p u) (p v) → ∀ τ ∈ F,
      |((thirdsT p C u v τ).card : ℝ) - κ τ (p u) (p v) * Fintype.card V| ≤
        ε * Fintype.card V)
    (hsmall : ε + ε * (∑ τ ∈ F, wt τ) + 2 * L.card * (∑ τ ∈ F, wt τ) / Fintype.card V ≤ c) :
    TriRegular p F (C ∪ L) ω c := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hwt0 : ∀ τ ∈ F, 0 ≤ wt τ := fun τ hτ => le_trans (hω.le.trans hωR) (hwt τ hτ).1
  refine ⟨fun s => wt (s.val.map p) / n, ?_, ?_⟩
  · intro s hs _
    have hτ := hwt _ hs.2
    refine ⟨(div_le_div_iff_of_pos_right hn).2 (le_trans hωR hτ.1), ?_⟩
    rw [← div_div]
    exact (div_le_div_iff_of_pos_right hn).2
      (le_trans hτ.2 (one_div_le_one_div_of_le hω hωR))
  · intro u v huv
    obtain ⟨hne, hal⟩ := hedge u v huv
    have hsum : ∀ τ ∈ F, ∑ w ∈ thirdsT p (C ∪ L) u v τ, wt (({u, v, w} : Finset V).val.map p) / n =
        ((thirdsT p (C ∪ L) u v τ).card : ℝ) * (wt τ / n) := by
      intro τ _
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_congr rfl fun w hw => ?_
      simp only [thirdsT, mem_filter, mem_univ, true_and] at hw
      obtain ⟨hwu, hwv, _, _, hτ⟩ := hw
      rw [map_val_triple p hne (Ne.symm hwu) (Ne.symm hwv), hτ]
    rw [sum_congr rfl hsum]
    have hlow : ∀ τ ∈ F, wt τ * κ τ (p u) (p v) - ε * wt τ ≤
        ((thirdsT p (C ∪ L) u v τ).card : ℝ) * (wt τ / n) := by
      intro τ hτ
      have h1 : κ τ (p u) (p v) * n - ε * n ≤ ((thirdsT p (C ∪ L) u v τ).card : ℝ) := by
        have h2 : ((thirdsT p C u v τ).card : ℝ) ≤ (thirdsT p (C ∪ L) u v τ).card := by
          exact_mod_cast card_le_card (thirdsT_mono p subset_union_left u v τ)
        linarith [(abs_sub_le_iff.mp (hcount u v hne hal τ hτ)).2]
      calc wt τ * κ τ (p u) (p v) - ε * wt τ = (κ τ (p u) (p v) * n - ε * n) * (wt τ / n) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (div_nonneg (hwt0 τ hτ) hn.le)
    have hup : ∀ τ ∈ F, ((thirdsT p (C ∪ L) u v τ).card : ℝ) * (wt τ / n) ≤
        wt τ * κ τ (p u) (p v) + ε * wt τ + 2 * L.card * wt τ / n := by
      intro τ hτ
      have h1 : ((thirdsT p (C ∪ L) u v τ).card : ℝ) ≤
          κ τ (p u) (p v) * n + ε * n + 2 * L.card := by
        have := card_thirdsT_union_le p C L u v τ
        have h2 : ((thirdsT p (C ∪ L) u v τ).card : ℝ) ≤
            (thirdsT p C u v τ).card + 2 * L.card := by exact_mod_cast this
        linarith [(abs_sub_le_iff.mp (hcount u v hne hal τ hτ)).1]
      calc ((thirdsT p (C ∪ L) u v τ).card : ℝ) * (wt τ / n)
          ≤ (κ τ (p u) (p v) * n + ε * n + 2 * L.card) * (wt τ / n) :=
            mul_le_mul_of_nonneg_right h1 (div_nonneg (hwt0 τ hτ) hn.le)
        _ = wt τ * κ τ (p u) (p v) + ε * wt τ + 2 * L.card * wt τ / n := by
            field_simp
    set S := ∑ τ ∈ F, wt τ * κ τ (p u) (p v) with hSdef
    set W := ∑ τ ∈ F, wt τ with hWdef
    have hS := abs_sub_le_iff.mp (hload _ _ hal)
    have eL : ∑ τ ∈ F, (wt τ * κ τ (p u) (p v) - ε * wt τ) = S - ε * W := by
      rw [sum_sub_distrib, ← mul_sum]
    have eU : ∑ τ ∈ F, (wt τ * κ τ (p u) (p v) + ε * wt τ + 2 * L.card * wt τ / n) =
        S + ε * W + 2 * L.card * W / n := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_div, ← mul_sum]
    have sL := sum_le_sum hlow
    have sU := sum_le_sum hup
    rw [eL] at sL
    rw [eU] at sU
    have hpos : 0 ≤ 2 * (L.card : ℝ) * W / n :=
      div_nonneg (mul_nonneg (by positivity) (sum_nonneg hwt0)) hn.le
    rw [abs_sub_le_iff]
    constructor <;> linarith

end Deterministic

/-- **Nearly-complete absorbers from the typed Keevash interface and a reserve.** -/
theorem nearlyAbsorbing_of_keevash {F : Finset (Multiset (Fin t))} (hK : KeevashTypedSpec F)
    (hR : ∀ h, ReserveSpec F h) : NearlyAbsorbing F := by
  intro K gamma eta hg he
  obtain ⟨h, ω₀, hω₀, hKv⟩ := hK gamma hg
  obtain ⟨ωR, hωR, hRes⟩ := hR h K gamma eta hg he
  have hω : 0 < min ωR ω₀ := lt_min hωR hω₀
  obtain ⟨c, hc, n₀, hKn⟩ := hKv (min ωR ω₀) hω (min_le_right _ _)
  obtain ⟨N₁, δ, hδ, hinst⟩ := hRes (c / (4 * (1 + F.card / ωR))) (by positivity)
  refine ⟨max (max N₁ n₀) (max ⌈8 * (K : ℝ) * F.card / (ωR * c)⌉₊ 1), δ, hδ, ?_⟩
  intro V _ _ G _ p d hN hadj hmiss hd hcls B X hB hXG hXB hXK
  have hN1 : N₁ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn0 : n₀ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : ⌈8 * (K : ℝ) * F.card / (ωR * c)⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hpos1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos1
  obtain ⟨C, hCG, hCdisj, hCdec, hCdeg, hCN, wt, κ, hwt, hload, hcount⟩ :=
    hinst G p d hN1 hadj hmiss hd hcls B X hB hXG hXB hXK
  refine ⟨C, hCG, hCdisj, hCdec, hCdeg, fun L hLX hLdiv => ?_⟩
  have hLG : C ∪ L ⊆ G.edgeFinset := union_subset hCG (hLX.trans hXG)
  have hCL : Disjoint C L := disjoint_of_subset_right (hLX.trans subset_union_right) hCdisj
  have hedge : ∀ u v, s(u, v) ∈ C ∪ L → u ≠ v ∧ AllowedPair F (p u) (p v) := by
    intro u v huv
    have hadj' : G.Adj u v := by simpa using hLG huv
    exact ⟨hadj'.ne, hadj u v hadj'⟩
  refine hKn p (C ∪ L) hn0 hcls ?_ (fun u v huv => (hedge u v huv).2) ?_ ?_ ?_
  · intro e he hdiag
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hLG he)) hdiag
  · refine triRegular_union wt κ hn hω (min_le_left _ _) hwt hload hedge hcount ?_
    have hS0 : 0 ≤ ∑ τ ∈ F, wt τ := sum_nonneg fun τ hτ => le_trans hωR.le (hwt τ hτ).1
    have hS : ∑ τ ∈ F, wt τ ≤ F.card / ωR := by
      have := sum_le_card_nsmul F wt (1 / ωR) fun τ hτ => (hwt τ hτ).2
      rw [nsmul_eq_mul] at this
      calc ∑ τ ∈ F, wt τ ≤ (F.card : ℝ) * (1 / ωR) := this
        _ = F.card / ωR := by ring
    have hLK : (L.card : ℝ) ≤ K := by exact_mod_cast (card_le_card hLX).trans hXK
    have hnb : 8 * (K : ℝ) * F.card / (ωR * c) ≤ Fintype.card V :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN2)
    have h1 : 2 * (L.card : ℝ) * (∑ τ ∈ F, wt τ) ≤ 2 * K * (F.card / ωR) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hLK (by norm_num)) hS hS0 (by positivity)
    have h2 : 2 * (K : ℝ) * (F.card / ωR) = c / 4 * (8 * K * F.card / (ωR * c)) := by
      field_simp
      ring
    have h3 : c / 4 * (8 * (K : ℝ) * F.card / (ωR * c)) ≤ c / 4 * Fintype.card V :=
      mul_le_mul_of_nonneg_left hnb (by positivity)
    have h4 : 2 * (L.card : ℝ) * (∑ τ ∈ F, wt τ) / Fintype.card V ≤ c / 4 :=
      (div_le_iff₀ hn).2 (by linarith)
    have h5 : c / (4 * (1 + F.card / ωR)) + c / (4 * (1 + F.card / ωR)) * (∑ τ ∈ F, wt τ) ≤
        c / 4 := by
      have hA : 0 < 1 + (F.card : ℝ) / ωR := by positivity
      have : c / (4 * (1 + F.card / ωR)) * (1 + ∑ τ ∈ F, wt τ) ≤
          c / (4 * (1 + F.card / ωR)) * (1 + F.card / ωR) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : c / (4 * (1 + F.card / ωR)) * (1 + F.card / ωR) = c / 4 := by
        field_simp
      nlinarith
    linarith
  · exact CNExt.mono subset_union_left (min_le_left _ _) hCN
  · exact (isIntDiv_of_hasDecomp hCdec).union hLdiv hCL

end PartitionedTriangleAbsorption.BlowupB
