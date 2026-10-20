/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPaddedBridge

/-! # BlowupB.KeevashPaddedMain — splitting the weights, and the bridge theorem

* `sum_split_eq`: for one type `τ` and one edge `uv`, the padded load of the split weights
  `y_T / N_T` equals the triangle load `∑_{w} y {u, v, w}`;
* `paddedRegularT_of_triRegular`: `TriRegular` with classes `≥ γ n` gives `PaddedRegularT` with
  `ω' = ω · min (1/27) ((γ/2)^{q−3})` and the same load error;
* **`keevashTypedSpec_of_padded`**: `KeevashPaddedSpec F → KeevashTypedSpec F`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

section Split

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangles of type `τ` with edges in `G` through `uv` correspond to third vertices. -/
theorem sum_tset_eq_thirds (p : V → Fin t) (G : Finset (Sym2 V)) {u v : V} (huv : u ≠ v)
    (hG : s(u, v) ∈ G) (τ : Multiset (Fin t)) (f : Finset V → ℝ) :
    ∑ T ∈ univ.filter (fun T : Finset V => T.card = 3 ∧ T.val.map p = τ ∧ triEdges T ⊆ G ∧
        s(u, v) ∈ triEdges T), f T = ∑ w ∈ thirdsT p G u v τ, f {u, v, w} := by
  classical
  symm
  refine sum_bij (fun w _ => ({u, v, w} : Finset V)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [thirdsT, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hwu, hwv, huw, hvw, hτ⟩ := hw
    refine mem_filter.mpr ⟨mem_univ _, card_eq_three.mpr ⟨u, v, w, huv, Ne.symm hwu,
      Ne.symm hwv, rfl⟩, ?_, ?_, ?_⟩
    · rw [map_val_triple p huv (Ne.symm hwu) (Ne.symm hwv)]; exact hτ
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha, hb, hab⟩ := TypedNibble.mem_triEdges_iff.mp he
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        all_goals first
          | exact absurd rfl hab
          | exact hG
          | exact huw
          | exact hvw
          | (rw [Sym2.eq_swap]; exact hG)
          | (rw [Sym2.eq_swap]; exact huw)
          | (rw [Sym2.eq_swap]; exact hvw)
    · exact TypedNibble.mem_triEdges_iff.mpr ⟨by simp, by simp, huv⟩
  · intro a ha b hb hab
    simp only [thirdsT, mem_filter, mem_univ, true_and] at ha hb
    have hb' : b ∈ ({u, v, a} : Finset V) := by rw [hab]; simp
    simp only [mem_insert, mem_singleton] at hb'
    rcases hb' with h | h | h
    · exact absurd h hb.1
    · exact absurd h hb.2.1
    · exact h.symm
  · intro T hT
    obtain ⟨hT3, hTp, hTG, hTuv⟩ := (mem_filter.mp hT).2
    obtain ⟨hu, hv, -⟩ := TypedNibble.mem_triEdges_iff.mp hTuv
    obtain ⟨c, huc, hvc, rfl⟩ := TypedNibble.exists_third_of_card_three hT3 hu hv huv
    refine ⟨c, ?_, rfl⟩
    simp only [thirdsT, mem_filter, mem_univ, true_and]
    refine ⟨Ne.symm huc, Ne.symm hvc,
      hTG (TypedNibble.mem_triEdges_iff.mpr ⟨by simp, by simp, huc⟩),
      hTG (TypedNibble.mem_triEdges_iff.mpr ⟨by simp, by simp, hvc⟩), ?_⟩
    rw [← map_val_triple p huv huc hvc]; exact hTp

open Classical in
/-- **Load of the split weights.** -/
theorem sum_split_eq (m : ℕ) (p : V → Fin t) (G : Finset (Sym2 V)) {u v : V} (huv : u ≠ v)
    (hG : s(u, v) ∈ G) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) (yR : Finset V → ℝ)
    (hN : ∀ T : Finset V, T.val.map p = τ → T.card = 3 → 0 < embCount m p τ T) :
    ∑ φ ∈ univ.filter (fun φ => ValidCopyT m p G τ φ ∧ s(u, v) ∈ triEdges (copyTriT m τ φ)),
        yR (copyTriT m τ φ) / embCount m p τ (copyTriT m τ φ) =
      ∑ w ∈ thirdsT p G u v τ, yR {u, v, w} := by
  classical
  rw [← sum_tset_eq_thirds p G huv hG τ yR]
  rw [← sum_fiberwise_of_maps_to (g := copyTriT m τ)
    (t := univ.filter (fun T : Finset V => T.card = 3 ∧ T.val.map p = τ ∧ triEdges T ⊆ G ∧
      s(u, v) ∈ triEdges T)) (fun φ hφ => by
      obtain ⟨⟨hemb, hsub⟩, he⟩ := (mem_filter.mp hφ).2
      exact mem_filter.mpr ⟨mem_univ _, copyTriT_card hτ hemb, copyTriT_map hτ hemb, hsub, he⟩)]
  refine sum_congr rfl fun T hT => ?_
  obtain ⟨hT3, hTp, hTG, hTuv⟩ := (mem_filter.mp hT).2
  have hfib : ((univ.filter (fun φ => ValidCopyT m p G τ φ ∧ s(u, v) ∈ triEdges (copyTriT m τ φ))).filter
      fun φ => copyTriT m τ φ = T) =
      univ.filter fun φ : PosT t m → V => IsEmbT m p φ ∧ copyTriT m τ φ = T := by
    ext φ
    rw [mem_filter, mem_filter, mem_filter]
    constructor
    · rintro ⟨⟨-, hv, -⟩, h2⟩; exact ⟨mem_univ _, hv.1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨⟨mem_univ _, ⟨h1, h2 ▸ hTG⟩, h2 ▸ hTuv⟩, h2⟩
  rw [hfib, sum_congr rfl fun φ hφ => by rw [(mem_filter.mp hφ).2.2], sum_const, nsmul_eq_mul]
  have hc : ((univ.filter fun φ : PosT t m → V => IsEmbT m p φ ∧ copyTriT m τ φ = T).card : ℝ) =
      embCount m p τ T := by
    unfold embCount; congr 1
  rw [hc]
  have := hN T hTp hT3
  field_simp

/-- **Splitting triangle weights over padded embeddings.** -/
theorem paddedRegularT_of_triRegular (m : ℕ) {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : Finset (Sym2 V)} {ω c γ : ℝ} (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hω : 0 < ω)
    (hγ : 0 < γ) (hG : ∀ e ∈ G, ¬ e.IsDiag)
    (hcls : ∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ))
    (hnq : 2 * (qT t m : ℝ) ≤ γ * Fintype.card V) (hR : TriRegular p F G ω c) :
    PaddedRegularT m p F G (ω * min (1 / 27) ((γ / 2) ^ (qT t m - 3))) c := by
  classical
  obtain ⟨yR, hyb, hyl⟩ := hR
  -- the embedding counts of typed triangles
  have hbounds : ∀ τ ∈ F, ∀ T : Finset V, T.val.map p = τ → T.card = 3 →
      3 ≤ qT t m ∧ 0 < (Fintype.card V : ℝ) ∧
      (γ * Fintype.card V / 2) ^ (qT t m - 3) ≤ (embCount m p τ T : ℝ) ∧
      (embCount m p τ T : ℝ) ≤ 27 * (Fintype.card V : ℝ) ^ (qT t m - 3) := by
    intro τ hτ T hTp hT3
    have hτ3 := hcard τ hτ
    obtain ⟨x, -⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hτ3]; norm_num : 0 < Multiset.card τ)
    have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr fun h0 => by subst h0; exact x.elim0
    have hq3 : 3 ≤ qT t m := le_trans (by omega) (Nat.le_mul_of_pos_left (m + 3) ht)
    have hn : (0 : ℝ) < Fintype.card V := by
      have : 3 ≤ Fintype.card V := hT3 ▸ card_le_univ T
      exact_mod_cast (by omega : 0 < Fintype.card V)
    have hq3R : (3 : ℝ) ≤ qT t m := by exact_mod_cast hq3
    refine ⟨hq3, hn, ?_, embCount_upper m p hτ3 hT3⟩
    have hs : 0 ≤ γ * Fintype.card V - qT t m := by linarith
    refine le_trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (embCount_lower m p hτ3 hTp hT3 hs fun i => by linarith [hcls i])
  refine ⟨fun τ φ => yR (copyTriT m τ φ) / embCount m p τ (copyTriT m τ φ), ?_, ?_⟩
  · intro τ hτ φ hφ
    have hτ3 := hcard τ hτ
    obtain ⟨hemb, hsub⟩ := hφ
    have hT3 := copyTriT_card hτ3 hemb
    have hTp := copyTriT_map hτ3 hemb
    obtain ⟨hq3, hn, hL, hU⟩ := hbounds τ hτ _ hTp hT3
    obtain ⟨hy1, hy2⟩ := hyb (copyTriT m τ φ) ⟨hT3, by rw [hTp]; exact hτ⟩ hsub
    set N : ℝ := (embCount m p τ (copyTriT m τ φ) : ℝ) with hNdef
    set yT := yR (copyTriT m τ φ) with hyT
    set n : ℝ := (Fintype.card V : ℝ) with hndef
    have hLpos : 0 < (γ * n / 2) ^ (qT t m - 3) := by positivity
    have hN : 0 < N := lt_of_lt_of_le hLpos hL
    have hyT0 : 0 ≤ yT := le_trans (by positivity) hy1
    have hpow : n ^ (qT t m - 2) = n ^ (qT t m - 3) * n := by
      rw [show qT t m - 2 = (qT t m - 3) + 1 by omega, pow_succ]
    have hpos3 : 0 < n ^ (qT t m - 3) := by positivity
    have hm1 : ω * min (1 / 27) ((γ / 2) ^ (qT t m - 3)) ≤ ω / 27 := by
      have := min_le_left (1 / 27 : ℝ) ((γ / 2) ^ (qT t m - 3))
      nlinarith
    have hm2 : ω * min (1 / 27) ((γ / 2) ^ (qT t m - 3)) ≤ ω * (γ / 2) ^ (qT t m - 3) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hω.le
    have hω' : 0 < ω * min (1 / 27) ((γ / 2) ^ (qT t m - 3)) :=
      mul_pos hω (lt_min (by norm_num) (by positivity))
    constructor
    · -- lower bound
      calc ω * min (1 / 27) ((γ / 2) ^ (qT t m - 3)) / n ^ (qT t m - 2)
          ≤ ω / 27 / n ^ (qT t m - 2) := div_le_div_of_nonneg_right hm1 (by positivity)
        _ = (ω / n) / (27 * n ^ (qT t m - 3)) := by rw [hpow]; field_simp
        _ ≤ yT / (27 * n ^ (qT t m - 3)) := div_le_div_of_nonneg_right hy1 (by positivity)
        _ ≤ yT / N := div_le_div_of_nonneg_left hyT0 hN hU
    · -- upper bound
      have hLeq : (γ * n / 2) ^ (qT t m - 3) = (γ / 2) ^ (qT t m - 3) * n ^ (qT t m - 3) := by
        rw [← mul_pow]; ring_nf
      calc yT / N ≤ yT / (γ * n / 2) ^ (qT t m - 3) := div_le_div_of_nonneg_left hyT0 hLpos hL
        _ ≤ (1 / (ω * n)) / (γ * n / 2) ^ (qT t m - 3) :=
            div_le_div_of_nonneg_right hy2 hLpos.le
        _ = 1 / (ω * (γ / 2) ^ (qT t m - 3) * n ^ (qT t m - 2)) := by
            rw [hLeq, hpow]; field_simp
        _ ≤ 1 / (ω * min (1 / 27) ((γ / 2) ^ (qT t m - 3)) * n ^ (qT t m - 2)) :=
            one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_right hm2 (by positivity))
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := fun h => hG _ he (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)
      have hN : ∀ τ ∈ F, ∀ T : Finset V, T.val.map p = τ → T.card = 3 →
          0 < embCount m p τ T := by
        intro τ hτ T hTp hT3
        obtain ⟨-, hn, hL, -⟩ := hbounds τ hτ T hTp hT3
        have : (0 : ℝ) < embCount m p τ T := lt_of_lt_of_le (by positivity) hL
        exact_mod_cast this
      have hsum := sum_congr rfl fun τ hτ =>
        sum_split_eq m p G huv he (hcard τ hτ) yR (hN τ hτ)
      beta_reduce
      rw [hsum]
      exact hyl u v he

end Split

/-- **The padded interface implies the typed interface.** -/
theorem keevashTypedSpec_of_padded {F : Finset (Multiset (Fin t))}
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hP : KeevashPaddedSpec F) : KeevashTypedSpec F := by
  intro γ hγ
  set m : ℕ := ⌈1 / γ⌉₊ with hm
  obtain ⟨ω0, hω0, n0, hP'⟩ := hP m
  set q : ℕ := qT t m with hq
  set K : ℕ := q * hKT t m with hK
  refine ⟨K, min (ω0 / 2) 1, lt_min (by positivity) one_pos, fun ω hω hωle => ?_⟩
  have hω1 : ω ≤ 1 := hωle.trans (min_le_right _ _)
  have hωh : ω ≤ ω0 / 2 := hωle.trans (min_le_left _ _)
  set ω' : ℝ := ω ^ (K + 1) * min (1 / 27) ((γ / 2) ^ (q - 3)) with hω'def
  have hmin0 : 0 < min (1 / 27 : ℝ) ((γ / 2) ^ (q - 3)) := lt_min (by norm_num) (by positivity)
  have hmin1 : min (1 / 27 : ℝ) ((γ / 2) ^ (q - 3)) ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  have hω'0 : 0 < ω' := mul_pos (pow_pos hω _) hmin0
  have hpowK1 : ω ^ (K + 1) ≤ ω ^ K := pow_le_pow_of_le_one hω.le hω1 (by omega)
  have hpowK1' : ω ^ (K + 1) ≤ ω := by
    calc ω ^ (K + 1) = ω ^ K * ω := pow_succ _ _
      _ ≤ 1 * ω := mul_le_mul_of_nonneg_right (pow_le_one₀ hω.le hω1) hω.le
      _ = ω := one_mul ω
  have hω'K : ω' ≤ ω ^ K :=
    (mul_le_of_le_one_right (pow_nonneg hω.le _) hmin1).trans hpowK1
  have hω'W : ω' ≤ ω * min (1 / 27) ((γ / 2) ^ (q - 3)) :=
    mul_le_mul_of_nonneg_right hpowK1' hmin0.le
  have hω'lt : ω' < ω0 := by
    have : ω' ≤ ω := (mul_le_of_le_one_right (pow_nonneg hω.le _) hmin1).trans hpowK1'
    linarith
  refine ⟨ω' ^ (hKT t m ^ 20), by positivity, ?_⟩
  have hδ : 0 < δKT t m := by unfold δKT; positivity
  set X : ℝ := ω' ^ (-(1 / δKT t m)) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hω'0 _
  refine ⟨max (n0 + 1) (max ⌈2 * (q : ℝ) / γ⌉₊ (⌈X⌉₊ + 1)), ?_⟩
  intro V _ _ p G hN hcls hnd hal hR hC hdiv
  have hn0 : n0 < Fintype.card V := lt_of_lt_of_le (Nat.lt_succ_self n0) (le_trans (le_max_left _ _) hN)
  have hN2 : ⌈2 * (q : ℝ) / γ⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : ⌈X⌉₊ + 1 ≤ Fintype.card V :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hnq : 2 * (qT t m : ℝ) ≤ γ * Fintype.card V := by
    have h1 : 2 * (q : ℝ) / γ ≤ Fintype.card V := (Nat.le_ceil _).trans (by exact_mod_cast hN2)
    have := (div_le_iff₀ hγ).mp h1
    linarith
  have hnX : X < Fintype.card V := by
    have h1 : X ≤ ⌈X⌉₊ := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast hN3
    linarith
  have hrpow : (Fintype.card V : ℝ) ^ (-δKT t m) < ω' := by
    have h1 := Real.rpow_lt_rpow_of_neg hX0 hnX (by linarith : -δKT t m < 0)
    have h2 : X ^ (-δKT t m) = ω' := by
      rw [hX, ← Real.rpow_mul hω'0.le]
      have : -(1 / δKT t m) * -δKT t m = 1 := by field_simp
      rw [this, Real.rpow_one]
    rwa [h2] at h1
  refine hP' hn0 ω' hrpow hω'lt p G hnd hal ?_ hdiv ?_ ?_
  · intro i
    have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr fun h0 => by subst h0; exact i.elim0
    have hq1 : m + 3 ≤ q := Nat.le_mul_of_pos_left (m + 3) ht
    have hK1 : q < hKT t m := by
      have h1 : 50 * q ^ 3 < 2 ^ (50 * q ^ 3) := Nat.lt_two_pow_self
      have h2 : q ≤ 50 * q ^ 3 := by
        have : q ≤ q ^ 3 := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
        exact this.trans (Nat.le_mul_of_pos_left (q ^ 3) (by norm_num))
      exact lt_of_le_of_lt h2 (by unfold hKT; exact h1)
    have hγK : 1 / γ ≤ (hKT t m : ℝ) := by
      have h1 : 1 / γ ≤ (m : ℝ) := Nat.le_ceil _
      have h2 : (m : ℝ) + 3 ≤ q := by exact_mod_cast hq1
      have h3 : (q : ℝ) < hKT t m := by exact_mod_cast hK1
      linarith
    have hKpos : (0 : ℝ) < hKT t m := lt_of_lt_of_le (by positivity) hγK
    have h4 : (Fintype.card V : ℝ) / hKT t m ≤ γ * Fintype.card V := by
      rw [div_le_iff₀ hKpos]
      have := mul_le_mul_of_nonneg_left hγK (by positivity : (0 : ℝ) ≤ γ * Fintype.card V)
      have e : γ * Fintype.card V * (1 / γ) = Fintype.card V := by field_simp
      nlinarith
    exact h4.trans (hcls i)
  · exact (paddedRegularT_of_triRegular m hcard hω hγ hnd hcls hnq hR).mono hω'0 hω'W
  · exact (extendableT_of_cnExt hω hω1 hC).mono hω'K

end PartitionedTriangleAbsorption.BlowupB
