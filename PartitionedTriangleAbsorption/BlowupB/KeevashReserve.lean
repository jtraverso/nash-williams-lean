/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashBridge
public import PartitionedTriangleAbsorption.TypedNearConsumer

/-! # BlowupB.KeevashReserve — the reserve from a typical graph and the typed nibble

`TypicalReserveSpec F h` asks only for a *typical* sparse graph `R ⊆ G \ (B ∪ X)` (the outcome
of the binomial random graph with densities in the interior of the type cone): degrees at most
`eta n` (`eta ≤ 1/2`), common-neighbourhood extendability, and typed-triangle counts
`κ n ± ε n` through every allowed pair, with type weights solving the load equations up to `ε`.

**`reserveSpec_of_typical`**: such `R` yields the decomposable reserve of `ReserveSpec`. The
almost perfect packing is `TypedNearConsumer.typed_nibble_packing_near` (proved in this tree);
the leave has degree `≤ η' n`, which costs `2η' n` in every count and `h η' n` in every common
neighbourhood. Hence `nearlyAbsorbing_of_keevash_typical`: Keevash + typicality ⇒
`NearlyAbsorbing F`.

`sum_copies_through` identifies the nibble's loads (sums over copies through an edge) with the
third-vertex sums used in `TriRegular`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

/-- **Typical reserve interface** (binomial random graph outcome). -/
def TypicalReserveSpec (F : Finset (Multiset (Fin t))) (h : ℕ) : Prop :=
  ∀ (K : ℕ) (gamma eta : ℝ), 0 < gamma → 0 < eta → eta ≤ 1 / 2 → ∃ ωT : ℝ, 0 < ωT ∧
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, gamma * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        ∀ B X : Finset (Sym2 V), DegBounded B (δ * Fintype.card V) →
          X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
          ∃ R ⊆ G.edgeFinset, Disjoint R (B ∪ X) ∧
            DegBounded R (eta * Fintype.card V) ∧ CNExt p F R ωT h ∧
            ∃ (wt : Multiset (Fin t) → ℝ) (κ : Multiset (Fin t) → Fin t → Fin t → ℝ),
              (∀ τ ∈ F, ωT ≤ wt τ ∧ wt τ ≤ 1 / ωT) ∧
              (∀ a b, AllowedPair F a b → |(∑ τ ∈ F, wt τ * κ τ a b) - 1| ≤ ε) ∧
              ∀ u v, u ≠ v → AllowedPair F (p u) (p v) → ∀ τ ∈ F,
                |((thirdsT p R u v τ).card : ℝ) - κ τ (p u) (p v) * Fintype.card V| ≤
                  ε * Fintype.card V

section Loads

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Third vertices of all typed triangles through `uv`. -/
def thirdsAll (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : Finset (Sym2 V)) (u v : V) :
    Finset V :=
  univ.filter fun w => w ≠ u ∧ w ≠ v ∧ s(u, w) ∈ G ∧ s(v, w) ∈ G ∧
    ({p u, p v, p w} : Multiset (Fin t)) ∈ F

theorem sum_thirdsAll (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : Finset (Sym2 V))
    (u v : V) (f : V → ℝ) :
    ∑ w ∈ thirdsAll p F G u v, f w = ∑ τ ∈ F, ∑ w ∈ thirdsT p G u v τ, f w := by
  rw [← sum_fiberwise_of_maps_to (g := fun w => ({p u, p v, p w} : Multiset (Fin t)))
    (t := F) (fun w hw => by
      simp only [thirdsAll, mem_filter, mem_univ, true_and] at hw
      exact hw.2.2.2.2)]
  refine sum_congr rfl fun τ _ => sum_congr ?_ fun _ _ => rfl
  ext w
  simp only [thirdsAll, thirdsT, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, -⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3, h4, h5 ▸ ‹τ ∈ F›⟩, h5⟩

/-- Loads over copies through `uv` are third-vertex sums. -/
theorem sum_copies_through (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : SimpleGraph V)
    [DecidableRel J.Adj] (φ : Finset V → ℝ) {u v : V} (huv : J.Adj u v) :
    ∑ s ∈ copies p F J with s(u, v) ∈ triEdges s, φ s =
      ∑ τ ∈ F, ∑ w ∈ thirdsT p J.edgeFinset u v τ, φ {u, v, w} := by
  rw [← sum_thirdsAll]
  symm
  refine sum_bij (fun w _ => ({u, v, w} : Finset V)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [thirdsAll, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] at hw
    obtain ⟨hwu, hwv, huw, hvw, hτ⟩ := hw
    refine mem_filter.mpr ⟨TypedNibble.mem_copies_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩
    · rw [map_val_triple p huv.ne (Ne.symm hwu) (Ne.symm hwv)]
      exact hτ
    · exact TypedNibble.mem_triEdges_iff.mpr ⟨by simp, by simp, huv.ne⟩
  · intro a ha b hb hab
    simp only [thirdsAll, mem_filter, mem_univ, true_and] at ha hb
    have hb' : b ∈ ({u, v, a} : Finset V) := by rw [hab]; simp
    simp only [mem_insert, mem_singleton] at hb'
    rcases hb' with h | h | h
    · exact absurd h hb.1
    · exact absurd h hb.2.1
    · exact h.symm
  · intro s hs
    obtain ⟨hsc, hsuv⟩ := mem_filter.mp hs
    have hcopy := TypedNibble.mem_copies_iff.mp hsc
    obtain ⟨hu, hv, hne⟩ := TypedNibble.mem_triEdges_iff.mp hsuv
    obtain ⟨c, huc, hvc, rfl⟩ := TypedNibble.exists_third_of_card_three hcopy.1.card_eq hu hv hne
    refine ⟨c, ?_, rfl⟩
    have hcl := SimpleGraph.is3Clique_triple_iff.mp hcopy.1
    simp only [thirdsAll, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    refine ⟨Ne.symm huc, Ne.symm hvc, hcl.2.1, hcl.2.2, ?_⟩
    rw [← map_val_triple p hne huc hvc]
    exact hcopy.2

theorem card_filter_star_le (E : Finset (Sym2 V)) (a : V) :
    (univ.filter fun w => s(a, w) ∈ E).card ≤ (E.filter fun e => a ∈ e).card := by
  refine card_le_card_of_injOn (fun w => s(a, w)) ?_ ?_
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2, Sym2.mem_mk_left a w⟩
  · intro x _ y _ hxy
    exact Sym2.congr_right.mp hxy

end Loads

/-- **The reserve from a typical graph** (typed nibble). -/
theorem reserveSpec_of_typical {F : Finset (Multiset (Fin t))} {h : ℕ}
    (hT : TypicalReserveSpec F h) : ReserveSpec F h := by
  intro K gamma eta hg he
  obtain ⟨ωT, hωT, hTy⟩ := hT K gamma (min eta (1 / 2)) hg (lt_min he (by norm_num))
    (min_le_right _ _)
  refine ⟨ωT / 2, by positivity, fun ε hε => ?_⟩
  -- the nibble leave
  set η' : ℝ := min (ε / 4) (ωT / (2 * (h + 1))) with hη'
  have hη'0 : 0 < η' := lt_min (by positivity) (by positivity)
  obtain ⟨δN, hδN, -, NN, hNN⟩ :=
    TypedNearConsumer.typed_nibble_packing_near (1 / ωT) η' (1 / 2) (by positivity) hη'0
      (by norm_num)
  set ε' : ℝ := min (ε / 2) (δN / (1 + F.card / ωT)) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by positivity)
  obtain ⟨N₁, δ, hδ, hR⟩ := hTy ε' hε'0
  refine ⟨max (max N₁ NN) 1, δ, hδ, ?_⟩
  intro V _ _ G _ p d hN hadj hmiss hd hcls B X hB hXG hXB hXK
  have hN1 : N₁ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN' : NN ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_max_right _ _) hN
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  obtain ⟨R, hRG, hRdisj, hRdeg, hRN, wt, κ, hwt, hload, hcount⟩ :=
    hR G p d hN1 hadj hmiss hd hcls B X hB hXG hXB hXK
  classical
  -- the graph of `R`
  let J : SimpleGraph V := SimpleGraph.fromRel fun u v => s(u, v) ∈ R
  have hJE : J.edgeFinset = R := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨-, h | h⟩
        · exact h
        · rwa [Sym2.eq_swap]
      · intro he
        exact ⟨(G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hRG he))).ne, Or.inl he⟩
  have hwt0 : ∀ τ ∈ F, 0 ≤ wt τ := fun τ hτ => le_trans hωT.le (hwt τ hτ).1
  have hW : ∑ τ ∈ F, wt τ ≤ F.card / ωT := by
    have := sum_le_card_nsmul F wt (1 / ωT) fun τ hτ => (hwt τ hτ).2
    rw [nsmul_eq_mul] at this
    calc ∑ τ ∈ F, wt τ ≤ (F.card : ℝ) * (1 / ωT) := this
      _ = F.card / ωT := by ring
  -- nibble input
  obtain ⟨D, Q, -, hQD, hQJ, -, hQdec, hleave⟩ := hNN V hNN' t p F J
    (fun s => wt (s.val.map p) / Fintype.card V)
    (fun s hs => ⟨div_nonneg (hwt0 _ hs.2) hn.le,
      (div_le_div_iff_of_pos_right hn).2 (hwt _ hs.2).2⟩)
    (by
      rw [hJE]
      intro v
      refine (hRdeg v).trans ?_
      have : min eta (1 / 2) ≤ 1 - 1 / 2 := by
        have := min_le_right eta (1 / 2 : ℝ); linarith
      exact mul_le_mul_of_nonneg_right this hn.le)
    (by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : J.Adj u v := J.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
        have hu : s(u, v) ∈ R := by rw [← hJE]; exact he
        have hne : u ≠ v := huv.ne
        have hal : AllowedPair F (p u) (p v) := hadj u v (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hRG hu)))
        rw [sum_copies_through p F J _ huv, hJE]
        have hsum : ∀ τ ∈ F, ∑ w ∈ thirdsT p R u v τ,
            wt (({u, v, w} : Finset V).val.map p) / Fintype.card V =
            ((thirdsT p R u v τ).card : ℝ) * (wt τ / Fintype.card V) := by
          intro τ _
          rw [← nsmul_eq_mul, ← sum_const]
          refine sum_congr rfl fun w hw => ?_
          simp only [thirdsT, mem_filter, mem_univ, true_and] at hw
          obtain ⟨hwu, hwv, _, _, hτ⟩ := hw
          rw [map_val_triple p hne (Ne.symm hwu) (Ne.symm hwv), hτ]
        rw [sum_congr rfl hsum]
        have hterm : ∀ τ ∈ F, |((thirdsT p R u v τ).card : ℝ) * (wt τ / Fintype.card V) -
            wt τ * κ τ (p u) (p v)| ≤ ε' * wt τ := by
          intro τ hτ
          have e1 : ((thirdsT p R u v τ).card : ℝ) * (wt τ / Fintype.card V) -
              wt τ * κ τ (p u) (p v) =
              (((thirdsT p R u v τ).card : ℝ) - κ τ (p u) (p v) * Fintype.card V) *
                (wt τ / Fintype.card V) := by
            field_simp
          rw [e1, abs_mul, abs_of_nonneg (div_nonneg (hwt0 τ hτ) hn.le)]
          calc |((thirdsT p R u v τ).card : ℝ) - κ τ (p u) (p v) * Fintype.card V| *
                (wt τ / Fintype.card V)
              ≤ (ε' * Fintype.card V) * (wt τ / Fintype.card V) :=
                mul_le_mul_of_nonneg_right (hcount u v hne hal τ hτ)
                  (div_nonneg (hwt0 τ hτ) hn.le)
            _ = ε' * wt τ := by field_simp
        have hdiff : |(∑ τ ∈ F, ((thirdsT p R u v τ).card : ℝ) * (wt τ / Fintype.card V)) -
            ∑ τ ∈ F, wt τ * κ τ (p u) (p v)| ≤ ε' * ∑ τ ∈ F, wt τ := by
          rw [← sum_sub_distrib, mul_sum]
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
        have hl := hload _ _ hal
        have hε'1 : ε' ≤ δN / (1 + F.card / ωT) := min_le_right _ _
        have hA : 0 < 1 + (F.card : ℝ) / ωT := by positivity
        have hb : ε' + ε' * ∑ τ ∈ F, wt τ ≤ δN := by
          have h1 : ε' * (1 + ∑ τ ∈ F, wt τ) ≤ ε' * (1 + F.card / ωT) :=
            mul_le_mul_of_nonneg_left (by linarith) hε'0.le
          have h2 : ε' * (1 + F.card / ωT) ≤ δN := by
            rwa [le_div_iff₀ hA] at hε'1
          nlinarith
        calc _ ≤ |(∑ τ ∈ F, ((thirdsT p R u v τ).card : ℝ) * (wt τ / Fintype.card V)) -
              ∑ τ ∈ F, wt τ * κ τ (p u) (p v)| + |(∑ τ ∈ F, wt τ * κ τ (p u) (p v)) - 1| :=
              abs_sub_le _ _ _
          _ ≤ ε' * ∑ τ ∈ F, wt τ + ε' := add_le_add hdiff hl
          _ ≤ δN := by linarith)
  rw [hJE] at hQJ hleave
  -- the reserve is `Q`
  have hcntQ : ∀ u v τ, (thirdsT p R u v τ).card ≤ (thirdsT p Q u v τ).card +
      ((univ.filter fun w => s(u, w) ∈ R \ Q).card +
        (univ.filter fun w => s(v, w) ∈ R \ Q).card) := by
    intro u v τ
    have hsub : thirdsT p R u v τ ⊆ thirdsT p Q u v τ ∪
        ((univ.filter fun w => s(u, w) ∈ R \ Q) ∪ (univ.filter fun w => s(v, w) ∈ R \ Q)) := by
      intro w hw
      simp only [thirdsT, mem_filter, mem_univ, true_and, mem_union, mem_sdiff] at hw ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := hw
      by_cases hu : s(u, w) ∈ Q
      · by_cases hv : s(v, w) ∈ Q
        · exact Or.inl ⟨h1, h2, hu, hv, h5⟩
        · exact Or.inr (Or.inr ⟨h4, hv⟩)
      · exact Or.inr (Or.inl ⟨h3, hu⟩)
    exact (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
  have hstar : ∀ a, ((univ.filter fun w => s(a, w) ∈ R \ Q).card : ℝ) ≤ η' * Fintype.card V :=
    fun a => le_trans (by exact_mod_cast card_filter_star_le (R \ Q) a) (hleave a)
  refine ⟨Q, hQJ.trans hRG, disjoint_of_subset_left hQJ hRdisj, hQdec, ?_, ?_, wt, κ, ?_,
    fun a b hab => (hload a b hab).trans (min_le_left _ _ |>.trans (by linarith)), ?_⟩
  · intro v
    refine le_trans (by exact_mod_cast card_le_card (filter_subset_filter _ hQJ)) ((hRdeg v).trans ?_)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le
  · intro S A i hS hA hal
    have hbase := hRN S A i hS hA hal
    have hsub : (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ R) ⊆
        (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ Q) ∪
          A.biUnion (fun a => univ.filter fun w => s(a, w) ∈ R \ Q) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_biUnion, mem_sdiff] at hv ⊢
      by_cases hall : ∀ a ∈ A, s(a, v) ∈ Q
      · exact Or.inl ⟨hv.1, hv.2.1, hall⟩
      · push Not at hall
        obtain ⟨a, ha, haQ⟩ := hall
        exact Or.inr ⟨a, ha, hv.2.2 a ha, haQ⟩
    have hbu : ((A.biUnion (fun a => univ.filter fun w => s(a, w) ∈ R \ Q)).card : ℝ) ≤
        h * (η' * Fintype.card V) := by
      have h1 := card_biUnion_le (s := A) (t := fun a => univ.filter fun w => s(a, w) ∈ R \ Q)
      have h2 : (∑ a ∈ A, ((univ.filter fun w => s(a, w) ∈ R \ Q).card : ℝ)) ≤
          A.card * (η' * Fintype.card V) := by
        have := sum_le_card_nsmul A (fun a => ((univ.filter fun w => s(a, w) ∈ R \ Q).card : ℝ))
          (η' * Fintype.card V) fun a _ => hstar a
        rwa [nsmul_eq_mul] at this
      have h3 : (A.card : ℝ) ≤ h := by exact_mod_cast (card_le_card hA).trans hS
      calc ((A.biUnion (fun a => univ.filter fun w => s(a, w) ∈ R \ Q)).card : ℝ)
          ≤ ∑ a ∈ A, ((univ.filter fun w => s(a, w) ∈ R \ Q).card : ℝ) := by exact_mod_cast h1
        _ ≤ A.card * (η' * Fintype.card V) := h2
        _ ≤ h * (η' * Fintype.card V) := mul_le_mul_of_nonneg_right h3 (by positivity)
    have hcu := card_union_le (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ Q)
      (A.biUnion (fun a => univ.filter fun w => s(a, w) ∈ R \ Q))
    have hsubR : (((univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ R)).card : ℝ) ≤
        ((univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ Q).card : ℝ) +
          (A.biUnion (fun a => univ.filter fun w => s(a, w) ∈ R \ Q)).card := by
      exact_mod_cast (card_le_card hsub).trans hcu
    have hη2 : (h : ℝ) * η' ≤ ωT / 2 := by
      have h1 : η' ≤ ωT / (2 * (h + 1)) := min_le_right _ _
      have h2 : (h : ℝ) * η' ≤ (h + 1) * (ωT / (2 * (h + 1))) :=
        mul_le_mul (by linarith) h1 hη'0.le (by positivity)
      have h3 : ((h : ℝ) + 1) * (ωT / (2 * (h + 1))) = ωT / 2 := by field_simp
      linarith
    have : (h : ℝ) * (η' * Fintype.card V) ≤ ωT / 2 * Fintype.card V := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hη2 hn.le
    linarith
  · intro τ hτ
    refine ⟨le_trans (by linarith) (hwt τ hτ).1, le_trans (hwt τ hτ).2 ?_⟩
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hωT]
    norm_num
  · intro u v huv hal τ hτ
    have hc := abs_sub_le_iff.mp (hcount u v huv hal τ hτ)
    have hQR : ((thirdsT p Q u v τ).card : ℝ) ≤ (thirdsT p R u v τ).card := by
      exact_mod_cast card_le_card (thirdsT_mono p hQJ u v τ)
    have hRQ : ((thirdsT p R u v τ).card : ℝ) ≤ (thirdsT p Q u v τ).card +
        (η' * Fintype.card V + η' * Fintype.card V) := by
      have := hcntQ u v τ
      have h2 : ((thirdsT p R u v τ).card : ℝ) ≤ (thirdsT p Q u v τ).card +
          (((univ.filter fun w => s(u, w) ∈ R \ Q).card : ℝ) +
            (univ.filter fun w => s(v, w) ∈ R \ Q).card) := by exact_mod_cast this
      linarith [hstar u, hstar v]
    have hε'2 : ε' ≤ ε / 2 := min_le_left _ _
    have hη'4 : η' ≤ ε / 4 := min_le_left _ _
    have e1 : ε' * Fintype.card V ≤ ε / 2 * Fintype.card V :=
      mul_le_mul_of_nonneg_right hε'2 hn.le
    have e2 : η' * Fintype.card V ≤ ε / 4 * Fintype.card V :=
      mul_le_mul_of_nonneg_right hη'4 hn.le
    rw [abs_sub_le_iff]
    constructor <;> nlinarith

/-- **Keevash + typical reserves ⇒ nearly-complete absorbers for every family.** -/
theorem nearlyAbsorbing_of_keevash_typical {F : Finset (Multiset (Fin t))}
    (hK : KeevashTypedSpec F) (hT : ∀ h, TypicalReserveSpec F h) : NearlyAbsorbing F :=
  nearlyAbsorbing_of_keevash hK fun h => reserveSpec_of_typical (hT h)

end PartitionedTriangleAbsorption.BlowupB
