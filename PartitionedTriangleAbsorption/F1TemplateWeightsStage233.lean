/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1TemplateBalanceStage233
public import PartitionedTriangleAbsorption.L3F0LocalInverse

/-!
# Exact positive F1 weights on a lightly damaged balanced template

Let `H ≤ templateGraph t` be a spanning subgraph of the complete F1 template with four classes of
size `t`. Restricting `Bᵀ R` to the actual F1 triangles of `H` gives a correction operator `CH`.
If every non-isolated vertex of `H` misses at most `d` template edges, every edge of `H` loses
at most `2d` template triangles, so (`damaged_residual`, `damaged_correction_bound`)

    ‖x - B_H (CH x)‖ ≤ (120 d / t) ‖x‖,   ‖CH x‖ ≤ (60 / t) ‖x‖

on zero-charge edge vectors supported on `H`. The generic `L3F0.local_inverse` then gives an
exact bounded inverse (`damaged_local_inverse`), and `f1_template_exact_weights` corrects the
uniform weights `1/(2t)` to loads exactly one with every weight in `[1/(4t), 3/(4t)]`, for
`t ≥ 640`, `d ≤ t/640` and zero charge `balance H = 0`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1TemplateStage233

open Finset TypedApplicationLinks F1BalanceGateStage228 TypedNibble

variable {t : ℕ}

/-! ### Subspaces and operators -/

/-- Edge vectors supported on `H` with zero signed charge. -/
def KH (H : SimpleGraph (Fin 4 × Fin t)) [DecidableRel H.Adj] :
    Submodule ℝ (Sym2 (Fin 4 × Fin t) → ℝ) where
  carrier := {d | (∀ e ∉ H.edgeFinset, d e = 0) ∧
    ∑ e ∈ H.edgeFinset, charge Prod.fst e * d e = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun e he => by simp [ha1 e he, hb1 e he], ?_⟩
    simp only [Pi.add_apply, mul_add, sum_add_distrib, ha2, hb2, add_zero]
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro r a ⟨ha1, ha2⟩
    refine ⟨fun e he => by simp [ha1 e he], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ e ∈ H.edgeFinset, charge Prod.fst e * (r * a e) =
      r * ∑ e ∈ H.edgeFinset, charge Prod.fst e * a e by
        rw [mul_sum]; exact sum_congr rfl fun e _ => by ring, ha2, mul_zero]

/-- Triangle weight vectors supported on a family `S`. -/
def suppT (S : Finset (Finset (Fin 4 × Fin t))) : Submodule ℝ (Finset (Fin 4 × Fin t) → ℝ) where
  carrier := {w | ∀ s ∉ S, w s = 0}
  add_mem' ha hb s hs := by simp [ha s hs, hb s hs]
  zero_mem' _ _ := rfl
  smul_mem' r _ ha s hs := by simp [ha s hs]

/-- The load operator `B_H` of the actual F1 triangles of `H` (zero off `H`). -/
noncomputable def LamH (H : SimpleGraph (Fin 4 × Fin t)) [DecidableRel H.Adj] :
    (Finset (Fin 4 × Fin t) → ℝ) →ₗ[ℝ] (Sym2 (Fin 4 × Fin t) → ℝ) where
  toFun w e := if e ∈ H.edgeFinset then load (copies Prod.fst F1 H) w e else 0
  map_add' a b := by
    funext e; simp only [load, Pi.add_apply, sum_add_distrib]; split_ifs <;> simp
  map_smul' r a := by
    funext e; simp only [load, Pi.smul_apply, smul_eq_mul, ← mul_sum, RingHom.id_apply]
    split_ifs <;> simp

/-- The correction operator: `Bᵀ R` restricted to the actual F1 triangles of `H`. -/
noncomputable def CH (H : SimpleGraph (Fin 4 × Fin t)) [DecidableRel H.Adj] :
    (Sym2 (Fin 4 × Fin t) → ℝ) →ₗ[ℝ] (Finset (Fin 4 × Fin t) → ℝ) where
  toFun x s := if s ∈ copies Prod.fst F1 H then ∑ f ∈ triEdges s, Rv x f else 0
  map_add' a b := by
    funext s
    simp only [Pi.add_apply]
    split_ifs
    · rw [← sum_add_distrib]
      exact sum_congr rfl fun f _ => by simpa using Rv_lin a b 1 1 f
    · simp
  map_smul' r a := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rw [mul_sum]
      exact sum_congr rfl fun f _ => by simpa using Rv_lin a 0 r 0 f
    · simp

variable (H : SimpleGraph (Fin 4 × Fin t)) [DecidableRel H.Adj]

omit [DecidableRel H.Adj] in
theorem copies_sub_tstar {s : Finset (Fin 4 × Fin t)} (hs : s ∈ copies Prod.fst F1 H) :
    s ∈ tstar t :=
  mem_tstar.mpr (isTypedTri_of_isCopy (mem_copies_iff.mp hs))

omit [DecidableRel H.Adj] in
theorem mem_copies_of_ok {u v w : Fin 4 × Fin t} (huv : H.Adj u v) (hok : Ok u v w)
    (huw : H.Adj u w) (hvw : H.Adj v w) : ({u, v, w} : Finset _) ∈ copies Prod.fst F1 H := by
  refine mem_copies_iff.mpr ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩, ?_⟩
  rw [map_three Prod.fst (H.ne_of_adj huv) hok.1.symm hok.2.1.symm]
  exact hok.2.2

/-- **Each surviving edge loses at most `2d` template triangles.** -/
theorem missing_card {d : ℝ}
    (hdmg : ∀ u, (∃ v, H.Adj u v) →
      ((univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w).card : ℝ) ≤ d)
    {u v : Fin 4 × Fin t} (huv : H.Adj u v) :
    ((univ.filter fun w => Ok u v w ∧ ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H).card : ℝ)
      ≤ 2 * d := by
  have hsub : (univ.filter fun w => Ok u v w ∧ ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H) ⊆
      (univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w) ∪
      (univ.filter fun w => (templateGraph t).Adj v w ∧ ¬ H.Adj v w) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨hok, hnot⟩ := hw
    obtain ⟨hu, hv⟩ := ok_template_adj hok
    simp only [mem_union, mem_filter, mem_univ, true_and]
    by_contra hc
    push_neg at hc
    exact hnot (mem_copies_of_ok H huv hok (hc.1 hu) (hc.2 hv))
  have h1 := card_le_card hsub
  have h2 := card_union_le (univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w)
    (univ.filter fun w => (templateGraph t).Adj v w ∧ ¬ H.Adj v w)
  have hu := hdmg u ⟨v, huv⟩
  have hv := hdmg v ⟨u, huv.symm⟩
  have : ((univ.filter fun w => Ok u v w ∧ ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H).card
      : ℝ) ≤ (univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w).card +
        (univ.filter fun w => (templateGraph t).Adj v w ∧ ¬ H.Adj v w).card := by
    exact_mod_cast h1.trans h2
  linarith

omit [DecidableRel H.Adj] in
/-- The template load minus the load of the actual triangles of `H`, through `uv`. -/
theorem load_tstar_sub_copies {u v : Fin 4 × Fin t} (huv : u ≠ v)
    (g : Finset (Fin 4 × Fin t) → ℝ) :
    load (tstar t) g s(u, v) - load (copies Prod.fst F1 H) g s(u, v) =
      ∑ w, if Ok u v w then
        (if ({u, v, w} : Finset _) ∈ copies Prod.fst F1 H then 0 else g {u, v, w}) else 0 := by
  classical
  rw [← sum_tstar_edge u v huv (fun s => if s ∈ copies Prod.fst F1 H then 0 else g s)]
  unfold load
  have hsplit : (∑ s ∈ tstar t with s(u, v) ∈ triEdges s, g s) =
      (∑ s ∈ tstar t with s(u, v) ∈ triEdges s,
        if s ∈ copies Prod.fst F1 H then g s else 0) +
      ∑ s ∈ tstar t with s(u, v) ∈ triEdges s,
        if s ∈ copies Prod.fst F1 H then 0 else g s := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun s _ => by split_ifs <;> simp
  have hcop : (∑ s ∈ tstar t with s(u, v) ∈ triEdges s,
      if s ∈ copies Prod.fst F1 H then g s else 0) =
      ∑ s ∈ copies Prod.fst F1 H with s(u, v) ∈ triEdges s, g s := by
    rw [← sum_filter]
    congr 1
    ext s
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨⟨copies_sub_tstar H h2, h1⟩, h2⟩
  rw [hsplit, hcop]; ring

/-- Bound on a triangle coordinate of `Bᵀ R x`. -/
theorem abs_triSum_Rv (ht : 4 ≤ t) (x : Sym2 (Fin 4 × Fin t) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hx : ∀ e, |x e| ≤ ε) {s : Finset (Fin 4 × Fin t)} (hs : s.card = 3) :
    |∑ f ∈ triEdges s, Rv x f| ≤ 60 * ε / t := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs
  rw [sum_triEdges_three _ hab hac hbc]
  have h1 := abs_Rv x hε hx ht s(a, b)
  have h2 := abs_Rv x hε hx ht s(a, c)
  have h3 := abs_Rv x hε hx ht s(b, c)
  calc _ ≤ |Rv x s(a, b) + Rv x s(a, c)| + |Rv x s(b, c)| := abs_add_le _ _
    _ ≤ |Rv x s(a, b)| + |Rv x s(a, c)| + |Rv x s(b, c)| := by gcongr; exact abs_add_le _ _
    _ ≤ 60 * ε / t := by
        have : 60 * ε / t = 3 * (20 * ε / t) := by ring
        linarith

/-- `R` inverts the real Gram operator on every template edge. -/
theorem gram_Rv_adj (ht : 4 ≤ t) (x : Sym2 (Fin 4 × Fin t) → ℝ) (hb : (blocksOf x).Balanced)
    {u v : Fin 4 × Fin t} (h : (templateGraph t).Adj u v) : gram (Rv x) s(u, v) = x s(u, v) := by
  obtain ⟨i, a⟩ := u
  obtain ⟨j, b⟩ := v
  obtain ⟨hne, h1 | h1⟩ := h
  · simp (config := { failIfUnchanged := false }) only at h1
    subst h1
    exact gram_Rv_internal x ht hb i a b (fun e => hne (by rw [e]))
  · exact gram_Rv_cross x ht hb i a j b h1

theorem balanced_of_KH (ht : 4 ≤ t) (hH : H ≤ templateGraph t) {x : Sym2 (Fin 4 × Fin t) → ℝ}
    (hx : x ∈ KH H) : (blocksOf x).Balanced := by
  apply blocksOf_balanced ht
  rw [← hx.2]
  symm
  apply sum_subset (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hH)
  intro e _ he
  rw [hx.1 e he, mul_zero]

/-! ### The two perturbation estimates -/

/-- **Residual estimate** `‖x - B_H (CH x)‖ ≤ (120 d / t) ‖x‖` on `KH`. -/
theorem damaged_residual (ht : 4 ≤ t) (hH : H ≤ templateGraph t) {d : ℝ}
    (hd : 0 ≤ d)
    (hdmg : ∀ u, (∃ v, H.Adj u v) →
      ((univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w).card : ℝ) ≤ d)
    (x : Sym2 (Fin 4 × Fin t) → ℝ) (hx : x ∈ KH H) :
    ‖x - LamH H (CH H x)‖ ≤ 120 * d / t * ‖x‖ := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hε : 0 ≤ ‖x‖ := norm_nonneg _
  have hxe : ∀ e, |x e| ≤ ‖x‖ := fun e => by
    have := norm_le_pi_norm x e; rwa [Real.norm_eq_abs] at this
  have hb := balanced_of_KH H ht hH hx
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  by_cases he : e ∈ H.edgeFinset
  · induction e using Sym2.ind with
    | _ u v =>
      have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have hne : u ≠ v := H.ne_of_adj huv
      have hgram := gram_Rv_adj ht x hb (hH huv)
      have hL : LamH H (CH H x) s(u, v) =
          load (copies Prod.fst F1 H) (fun s => ∑ f ∈ triEdges s, Rv x f) s(u, v) := by
        change (if s(u, v) ∈ H.edgeFinset then load (copies Prod.fst F1 H) (CH H x) s(u, v)
          else 0) = _
        rw [if_pos he]
        unfold load
        refine sum_congr rfl fun s hs => ?_
        change (if s ∈ copies Prod.fst F1 H then _ else _) = _
        rw [if_pos (mem_filter.mp hs).1]
      rw [hL, ← hgram]
      unfold gram
      rw [load_tstar_sub_copies H hne]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ w, |if Ok u v w then (if ({u, v, w} : Finset _) ∈ copies Prod.fst F1 H
          then 0 else ∑ f ∈ triEdges {u, v, w}, Rv x f) else 0| ≤
          if Ok u v w ∧ ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H then 60 * ‖x‖ / t
          else 0 := by
        intro w
        by_cases hok : Ok u v w
        · by_cases hc : ({u, v, w} : Finset _) ∈ copies Prod.fst F1 H
          · simp [hok, hc]
          · rw [if_pos hok, if_neg hc, if_pos ⟨hok, hc⟩]
            have hcard : ({u, v, w} : Finset (Fin 4 × Fin t)).card = 3 :=
              card_eq_three.mpr ⟨u, v, w, hne, hok.1.symm, hok.2.1.symm, rfl⟩
            exact abs_triSum_Rv ht x hε hxe hcard
        · simp [hok]
      refine (sum_le_sum fun w _ => hterm w).trans ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have hm := missing_card H hdmg huv
      have hpos : 0 ≤ 60 * ‖x‖ / t := by positivity
      calc _ ≤ 2 * d * (60 * ‖x‖ / t) := mul_le_mul_of_nonneg_right hm hpos
        _ = 120 * d / t * ‖x‖ := by ring
  · have h1 : x e = 0 := hx.1 e he
    have h2 : LamH H (CH H x) e = 0 := by
      change (if e ∈ H.edgeFinset then _ else _) = 0; rw [if_neg he]
    rw [h1, h2]; simp; positivity

/-- **Correction estimate** `‖CH x‖ ≤ (60 / t) ‖x‖`. -/
theorem damaged_correction_bound (ht : 4 ≤ t) (x : Sym2 (Fin 4 × Fin t) → ℝ) :
    ‖CH H x‖ ≤ 60 / t * ‖x‖ := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hε : 0 ≤ ‖x‖ := norm_nonneg _
  have hxe : ∀ e, |x e| ≤ ‖x‖ := fun e => by
    have := norm_le_pi_norm x e; rwa [Real.norm_eq_abs] at this
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
  rw [Real.norm_eq_abs]
  change |if s ∈ copies Prod.fst F1 H then _ else _| ≤ _
  split_ifs with hs
  · have hcard := (isTypedTri_of_isCopy (mem_copies_iff.mp hs)).1
    have := abs_triSum_Rv ht x hε hxe hcard
    calc _ ≤ 60 * ‖x‖ / t := this
      _ = 60 / t * ‖x‖ := by ring
  · simp; positivity

/-- **Exact bounded inverse of the damaged load operator** (application of `L3F0.local_inverse`
with the actual operators `LamH`, `CH`, subspaces `KH`, `suppT` and the two estimates). -/
theorem damaged_local_inverse (ht : 4 ≤ t) (hH : H ≤ templateGraph t) {d : ℝ} (hd : 0 ≤ d)
    (hκ : 120 * d / t < 1)
    (hdmg : ∀ u, (∃ v, H.Adj u v) →
      ((univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w).card : ℝ) ≤ d) :
    ∀ z ∈ KH H, ∃ y ∈ suppT (copies Prod.fst F1 H), LamH H y = z ∧
      ‖y‖ ≤ (60 / t) / (1 - 120 * d / t) * ‖z‖ := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hLK : ∀ w, LamH H w ∈ KH H := by
    intro w
    refine ⟨fun e he => by change (if e ∈ H.edgeFinset then _ else _) = 0; rw [if_neg he], ?_⟩
    have h := weighted_balance_zero Prod.fst H.edgeFinset (copies Prod.fst F1 H) w
      (fun s hs => triEdges_subset_of_isCopy (mem_copies_iff.mp hs))
      (fun s hs => isTypedTri_of_isCopy (mem_copies_iff.mp hs))
    rw [← h]
    refine sum_congr rfl fun e he => ?_
    change charge Prod.fst e * (if e ∈ H.edgeFinset then _ else _) = _
    rw [if_pos he]
  exact PartitionedTriangleAbsorption.L3F0.local_inverse (LamH H) (CH H) (KH H)
    (suppT (copies Prod.fst F1 H))
    (fun x hx => (KH H).sub_mem hx (hLK _))
    (fun x _ s hs => by change (if s ∈ copies Prod.fst F1 H then _ else _) = 0; rw [if_neg hs])
    hκ (by positivity) (fun x hx => damaged_residual H ht hH hd hdmg x hx)
    (fun x _ => damaged_correction_bound H ht x)

/-! ### Counting the template triangles through an edge -/

/-- The off-diagonal indicator. -/
noncomputable def Yc (t : ℕ) : Sym2 (Fin 4 × Fin t) → ℝ := fun e => if e.IsDiag then 0 else 1

theorem Yc_mk (a b : Fin 4 × Fin t) : Yc t s(a, b) = if a = b then 0 else 1 := by
  simp [Yc]

theorem rowF_Yc_other {u : Fin 4 × Fin t} {c : Fin 4} (hc : c ≠ u.1) : rowF (Yc t) u c = t := by
  unfold rowF
  have : ∀ k : Fin t, Yc t s(u, (c, k)) = 1 := by
    intro k; rw [Yc_mk, if_neg]; intro h; exact hc (by rw [h])
  simp [this]

theorem rowF_Yc_own (u : Fin 4 × Fin t) : rowF (Yc t) u u.1 = t - 1 := by
  unfold rowF
  have : ∀ k : Fin t, Yc t s(u, (u.1, k)) = if k = u.2 then 0 else 1 := by
    intro k; rw [Yc_mk]
    by_cases hk : k = u.2
    · rw [if_pos hk, if_pos (by rw [hk])]
    · rw [if_neg hk, if_neg]; intro h; exact hk (by rw [h])
  simp_rw [this]
  rw [sum_ne_index (fun _ => (1 : ℝ))]
  simp

theorem gram_Yc (u v : Fin 4 × Fin t) (huv : u ≠ v) :
    gram (Yc t) s(u, v) = 3 * ((univ.filter fun w => Ok u v w).card : ℝ) := by
  rw [gram_mk _ u v huv]
  have : ∀ w, (if Ok u v w then Yc t s(u, v) + Yc t s(u, w) + Yc t s(v, w) else 0) =
      if Ok u v w then 3 else 0 := by
    intro w
    split_ifs with h
    · rw [Yc_mk, Yc_mk, Yc_mk, if_neg huv, if_neg (Ne.symm h.1), if_neg (Ne.symm h.2.1)]; norm_num
    · rfl
  rw [sum_congr rfl fun w _ => this w, ← sum_filter, sum_const, nsmul_eq_mul]; ring

/-- Number of template triangles through a template edge: `2t` (internal) or `2t-2` (cross). -/
theorem ok_count_bounds {u v : Fin 4 × Fin t} (h : (templateGraph t).Adj u v) :
    2 * (t : ℝ) - 2 ≤ (univ.filter fun w => Ok u v w).card ∧
      ((univ.filter fun w => Ok u v w).card : ℝ) ≤ 2 * t := by
  have hg := gram_Yc u v h.1
  rcases h.2 with h1 | h1
  · have a1 : first1 u.1 ≠ u.1 := (opp_ne (opp_first1 u.1)).symm
    have a2 : second1 u.1 ≠ u.1 := (opp_ne (opp_second1 u.1)).symm
    have a3 : first1 u.1 ≠ v.1 := h1 ▸ a1
    have a4 : second1 u.1 ≠ v.1 := h1 ▸ a2
    rw [gram_internal _ u v h.1 h1, rowF_Yc_other a1, rowF_Yc_other a3, rowF_Yc_other a2,
      rowF_Yc_other a4, Yc_mk, if_neg h.1] at hg
    constructor <;> linarith
  · have hd : ∀ a, Yc t s(a, a) = 0 := fun a => by simp [Yc]
    rw [gram_cross _ hd u v h1, rowF_Yc_own, rowF_Yc_own, rowF_Yc_other (opp_ne h1).symm,
      rowF_Yc_other (opp_ne h1), Yc_mk, if_neg h.1] at hg
    constructor <;> linarith

/-! ### Exact positive weights -/

/-- **Exact positive F1 weights on a lightly damaged balanced template.** Four classes of size
`t ≥ 640`; `H` is a subgraph of the complete F1 template; every vertex of `H` that has an edge
misses at most `d ≤ t/640` template edges (no condition at isolated vertices); and `H` has zero
signed charge. Then the actual F1 triangles of `H` carry weights in `[1/(4t), 3/(4t)]` with load
exactly one on every edge of `H`. -/
theorem f1_template_exact_weights (ht : 640 ≤ t) (hH : H ≤ templateGraph t) {d : ℝ}
    (hd : d ≤ t / 640)
    (hdmg : ∀ u, (∃ v, H.Adj u v) →
      ((univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w).card : ℝ) ≤ d)
    (hbal : balance Prod.fst H.edgeFinset = 0) :
    ∃ w : Finset (Fin 4 × Fin t) → ℝ,
      (∀ e ∈ H.edgeFinset, load (copies Prod.fst F1 H) w e = 1) ∧
      (∀ s ∈ copies Prod.fst F1 H, 1 / (4 * t) ≤ w s ∧ w s ≤ 3 / (4 * t)) ∧
      (∀ s ∉ copies Prod.fst F1 H, w s = 0) := by
  have ht4 : 4 ≤ t := by omega
  have ht' : (640 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  set d' := max d 0 with hd'
  have hd'0 : 0 ≤ d' := le_max_right _ _
  have hd't : d' ≤ t / 640 := max_le hd (by positivity)
  have hdmg' : ∀ u, (∃ v, H.Adj u v) →
      ((univ.filter fun w => (templateGraph t).Adj u w ∧ ¬ H.Adj u w).card : ℝ) ≤ d' :=
    fun u hu => (hdmg u hu).trans (le_max_left _ _)
  have hκ' : 120 * d' / t ≤ 3 / 16 := by
    rw [div_le_iff₀ ht0]; linarith
  have hκ : 120 * d' / t < 1 := by linarith
  set c : ℝ := 1 / (2 * t) with hc
  let w0 : Finset (Fin 4 × Fin t) → ℝ := fun s => if s ∈ copies Prod.fst F1 H then c else 0
  let z : Sym2 (Fin 4 × Fin t) → ℝ := fun e =>
    if e ∈ H.edgeFinset then 1 - load (copies Prod.fst F1 H) w0 e else 0
  -- `z` has zero charge
  have hzK : z ∈ KH H := by
    refine ⟨fun e he => by simp only [z]; rw [if_neg he], ?_⟩
    have h0 := weighted_balance_zero Prod.fst H.edgeFinset (copies Prod.fst F1 H) w0
      (fun s hs => triEdges_subset_of_isCopy (mem_copies_iff.mp hs))
      (fun s hs => isTypedTri_of_isCopy (mem_copies_iff.mp hs))
    have : ∑ e ∈ H.edgeFinset, charge Prod.fst e * z e =
        balance Prod.fst H.edgeFinset -
          ∑ e ∈ H.edgeFinset, charge Prod.fst e * load (copies Prod.fst F1 H) w0 e := by
      unfold balance
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun e he => ?_
      simp only [z, if_pos he]; ring
    rw [this, hbal, h0, sub_zero]
  -- `z` is small
  have hzb : ∀ e, |z e| ≤ (1 + d') / t := by
    intro e
    by_cases he : e ∈ H.edgeFinset
    · induction e using Sym2.ind with
      | _ u v =>
        have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        have hne : u ≠ v := H.ne_of_adj huv
        have hw0 : load (copies Prod.fst F1 H) w0 s(u, v) =
            load (copies Prod.fst F1 H) (fun _ => c) s(u, v) := by
          unfold load
          exact sum_congr rfl fun s hs => by simp [w0, (mem_filter.mp hs).1]
        have hdiff := load_tstar_sub_copies H hne (fun _ => c)
        have htN : load (tstar t) (fun _ => c) s(u, v) =
            c * ((univ.filter fun w => Ok u v w).card : ℝ) := by
          unfold load
          rw [sum_tstar_edge u v hne (fun _ => c), ← sum_filter, sum_const, nsmul_eq_mul]; ring
        have hM : (∑ w, if Ok u v w then
            (if ({u, v, w} : Finset _) ∈ copies Prod.fst F1 H then 0 else c) else 0) =
            c * ((univ.filter fun w => Ok u v w ∧
              ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H).card : ℝ) := by
          rw [card_filter]; push_cast; rw [mul_sum]
          refine sum_congr rfl fun w _ => ?_
          by_cases h1 : Ok u v w <;> by_cases h2 : ({u, v, w} : Finset _) ∈ copies Prod.fst F1 H <;>
            simp [h1, h2]
        have hm := missing_card H hdmg' huv
        have hm0 : (0 : ℝ) ≤ ((univ.filter fun w => Ok u v w ∧
            ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H).card : ℝ) := Nat.cast_nonneg _
        obtain ⟨hN1, hN2⟩ := ok_count_bounds (hH huv)
        have hzval : z s(u, v) = 1 - c * ((univ.filter fun w => Ok u v w).card : ℝ) +
            c * ((univ.filter fun w => Ok u v w ∧
              ({u, v, w} : Finset _) ∉ copies Prod.fst F1 H).card : ℝ) := by
          simp only [z, if_pos he]
          rw [hw0]; linarith
        rw [hzval, abs_le]
        have hc2 : c * (2 * t) = 1 := by rw [hc]; field_simp
        have hcpos : 0 < c := by positivity
        have e1 : (1 + d') / t = c * 2 + c * (2 * d') := by rw [hc]; field_simp
        rw [e1]
        constructor <;> nlinarith
    · simp only [z, if_neg he, abs_zero]; positivity
  have hzn : ‖z‖ ≤ (1 + d') / t :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun e => by
      rw [Real.norm_eq_abs]; exact hzb e
  obtain ⟨y, hyS, hyz, hyn⟩ := damaged_local_inverse H ht4 hH hd'0 hκ hdmg' z hzK
  -- numerical margin
  have hfac : (60 / t) / (1 - 120 * d' / t) ≤ 80 / t := by
    rw [div_le_iff₀ (by linarith)]
    have : 80 / t * (1 - 120 * d' / t) ≥ 80 / t * (13 / 16) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have : 80 / (t : ℝ) * (13 / 16) = 65 / t := by ring
    have : (60 : ℝ) / t ≤ 65 / t := by gcongr; norm_num
    linarith
  have hz' : (1 + d') / t ≤ 1 / 320 := by
    rw [div_le_iff₀ ht0]; linarith
  have hyb : ‖y‖ ≤ 1 / (4 * t) := by
    calc ‖y‖ ≤ (60 / t) / (1 - 120 * d' / t) * ‖z‖ := hyn
      _ ≤ 80 / t * (1 / 320) := by
          apply mul_le_mul hfac (hzn.trans hz') (norm_nonneg _) (by positivity)
      _ = 1 / (4 * t) := by field_simp; ring
  have hys : ∀ s, |y s| ≤ 1 / (4 * t) := fun s => by
    have := norm_le_pi_norm y s; rw [Real.norm_eq_abs] at this; linarith
  refine ⟨w0 + y, ?_, ?_, ?_⟩
  · intro e he
    have h1 : load (copies Prod.fst F1 H) (w0 + y) e =
        load (copies Prod.fst F1 H) w0 e + load (copies Prod.fst F1 H) y e := by
      unfold load; rw [← sum_add_distrib]; rfl
    have h2 : load (copies Prod.fst F1 H) y e = z e := by
      rw [← hyz]; change _ = if e ∈ H.edgeFinset then _ else _; rw [if_pos he]
    rw [h1, h2]
    simp only [z, if_pos he]; ring
  · intro s hs
    have := abs_le.mp (hys s)
    simp only [Pi.add_apply, w0, if_pos hs]
    have e1 : c = 1 / (4 * t) + 1 / (4 * t) := by rw [hc]; field_simp; ring
    have e2 : (3 : ℝ) / (4 * t) = 3 * (1 / (4 * t)) := by ring
    constructor <;> linarith
  · intro s hs
    simp only [Pi.add_apply, w0, if_neg hs, hyS s hs, add_zero]

end PartitionedTriangleAbsorption.F1TemplateStage233
