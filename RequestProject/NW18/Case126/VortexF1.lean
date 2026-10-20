/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.ProtectedIterationF1
import RequestProject.NW18.Case126.VortexSamplingF1
import RequestProject.NW18.Case126.TerminalAbsorberF1
import RequestProject.NW18.Case126.NearQuarterF1

/-!
# Constructing the `F₁` vortex and closing `Theorem147F1Statement`

* `sf m = m^{-1/4}` is the level-dependent sampling tolerance.
* `exists_vortex_from` (proved, strong induction on `|W|`): from a level `W` whose invariant is
  `VInv … W (ε + (2/(3β)) sf |W|)` there is a full vortex `Ws` starting at `W`, every
  nonterminal level of size `≥ X⁴`, terminal level of size `< X⁴`, with all six fields of
  `F1Vortex`.  The error schedule is the potential `ε + (2/(3β)) |W_i|^{-1/4}`: one sampling
  step costs `6 s/β` with `s = |W_i|^{-1/4}`, and since `|W_{i+1}| ≤ 10⁻⁴ |W_i|` the potential
  grows by a factor `10` going down, which pays exactly for that cost.  So the accumulated
  error at every nonterminal level is at most `ε + (2/(3β)) X⁻¹`, never a per-step `ξ` or `κ`.
  The last step (from `W_{L-1}` to `W_L`) only needs the parent-unit bounds of the sampling
  lemma; there is no lower bound and no invariant required at `W_L`, and `W_{L+1} = ∅`.
* `theorem_14_7_F1_of_vortex` (proved): `Theorem147F1Statement`, with `ε = 10⁻⁸¹`, from
  `F1_close_from_vortex_concrete` (`γ = 1/8`), `compatibleSupply_F1_of_idealized`, the integral
  divisibility hypothesis of the statement, and the vortex built above.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The sampling tolerance `m^{-1/4}`. -/
noncomputable def sf (m : ℕ) : ℝ := 1 / Real.sqrt (Real.sqrt m)

/-- Prepend a level to a sequence of levels. -/
def consSeq (W : Finset V) (Ws : ℕ → Finset V) : ℕ → Finset V
  | 0 => W
  | k + 1 => Ws k

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consSeq_zero (W : Finset V) (Ws : ℕ → Finset V) : consSeq W Ws 0 = W := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consSeq_succ (W : Finset V) (Ws : ℕ → Finset V) (k : ℕ) :
    consSeq W Ws (k + 1) = Ws k := rfl

theorem sqrt_sqrt_pow_four (X : ℕ) : Real.sqrt (Real.sqrt ((X ^ 4 : ℕ) : ℝ)) = X := by
  push_cast
  have h1 : ((X : ℝ) ^ 4) = ((X : ℝ) ^ 2) ^ 2 := by ring
  rw [h1, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]

theorem sqrt_sqrt_mono {a b : ℝ} (h : a ≤ b) : Real.sqrt (Real.sqrt a) ≤ Real.sqrt (Real.sqrt b) :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem sqrt_sqrt_ge_of_ge (X m : ℕ) (h : X ^ 4 ≤ m) : (X : ℝ) ≤ Real.sqrt (Real.sqrt m) := by
  rw [← sqrt_sqrt_pow_four X]
  exact sqrt_sqrt_mono (by exact_mod_cast h)

/-- Shrinking by a factor `10⁻⁴` multiplies `m^{-1/4}` by at least `10`. -/
theorem sf_shrink {m k : ℕ} (hk : 0 < k) (hkm : (k : ℝ) ≤ m / 10 ^ 4) : 10 * sf m ≤ sf k := by
  unfold sf
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt (Real.sqrt k) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hk0)
  have h1 : Real.sqrt (Real.sqrt k) ≤ Real.sqrt (Real.sqrt m) / 10 := by
    calc Real.sqrt (Real.sqrt k) ≤ Real.sqrt (Real.sqrt (m / 10 ^ 4)) := sqrt_sqrt_mono hkm
      _ = Real.sqrt (Real.sqrt m) / 10 := by
        rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 10 ^ 4),
          Real.sqrt_div' _ (Real.sqrt_nonneg _)]
        congr 1
        rw [show (10 : ℝ) ^ 4 = (10 ^ 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
          show (10 : ℝ) ^ 2 = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsm : 0 < Real.sqrt (Real.sqrt m) := by linarith
  rw [mul_one_div, div_le_div_iff₀ hsm hsk]
  linarith

omit [Fintype V] in
/-- Class split of `W \ U` for `U ⊆ W`. -/
theorem card_filter_sdiff (p : V → Fin 4) (W U : Finset V) (hUW : U ⊆ W) (j : Fin 4) :
    (((W \ U).filter fun z => p z = j).card : ℝ) =
      ((W.filter fun z => p z = j).card : ℝ) - ((U.filter fun z => p z = j).card : ℝ) := by
  have hsub : U.filter (fun z => p z = j) ⊆ W.filter (fun z => p z = j) :=
    filter_subset_filter _ hUW
  have heq : (W \ U).filter (fun z => p z = j) =
      W.filter (fun z => p z = j) \ U.filter (fun z => p z = j) := by
    ext z; simp only [mem_filter, mem_sdiff]; tauto
  rw [heq, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]

/-- **The vortex from a level** (proved).  All constants (`β ≤ 10⁻⁴`, `κ`, `ξ`, `ε`, the cutoff
`X`) are fixed before the graph; the induction is on the size of the current level. -/
theorem exists_vortex_from (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    {β κ ξ ε : ℝ} (X : ℕ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 10 ^ 4) (hε : 0 ≤ ε) (hX3 : 3 ≤ X)
    (hXs : 1 / (X : ℝ) ≤ β / 8) (hξ : ε + 2 / (3 * β) * (1 / X) ≤ ξ)
    (hκ : 2 * (ε + 2 / (3 * β) * (1 / X)) + 2 * (1 / X) ≤ κ)
    (h1 : ε + 2 / (3 * β) * (1 / X) ≤ 1) :
    ∀ (m : ℕ) (W : Finset V), W.card = m →
      VInv p G (AllowedT F1) W (ε + 2 / (3 * β) * sf W.card) →
      ∃ (Ws : ℕ → Finset V) (L : ℕ), Ws 0 = W ∧ F1Vortex p G Ws L β κ ξ ∧
        (∀ i < L, X ^ 4 ≤ (Ws i).card) ∧ (Ws L).card < X ^ 4 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W hWm hinv
  by_cases hsmallW : m < X ^ 4
  · -- terminal: `L = 0`, `W 1 = ∅`
    refine ⟨consSeq W fun _ => ∅, 0, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun i hi => absurd hi
      (Nat.not_lt_zero _), by simpa [hWm] using hsmallW⟩
    · intro i hi; obtain rfl : i = 0 := by omega
      simp
    · intro i hi; obtain rfl : i = 0 := by omega
      simp only [consSeq_succ, card_empty, Nat.cast_zero, consSeq_zero]; positivity
    all_goals intro i hi; exact absurd hi (Nat.not_lt_zero _)
  push_neg at hsmallW
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hsmallW
  have hW0 : 0 < W.card := hWm ▸ hm0
  set s := sf W.card with hsdef
  have hsX : (X : ℝ) ≤ Real.sqrt (Real.sqrt W.card) := sqrt_sqrt_ge_of_ge X W.card (hWm ▸ hsmallW)
  have hs0 : 0 < s := by
    rw [hsdef, sf]; exact div_pos one_pos (by linarith)
  have hsle : s ≤ 1 / X := by
    rw [hsdef, sf]; exact one_div_le_one_div_of_le hX0 hsX
  set c : ℝ := 2 / (3 * β) with hc
  have hc0 : 0 < c := by positivity
  set a := ε + c * s with ha
  have ha0 : 0 ≤ a := by positivity
  have haX : a ≤ ε + c * (1 / X) := by have := mul_le_mul_of_nonneg_left hsle hc0.le; linarith
  have hbud := sampling_union_bound (W.card : ℝ) (le_trans (by exact_mod_cast hX3) hsX)
  obtain ⟨U, hUW, hlo, hhi, hdev, hUinv⟩ := vortex_sampling_step p G (AllowedT F1) hβ0
    (by linarith) ha0 (by linarith) hs0 (by linarith) W hW0 hbud hinv
  have hmR : (0 : ℝ) < W.card := by exact_mod_cast hW0
  have hU0 : 0 < U.card := by
    have : (0 : ℝ) < U.card := lt_of_lt_of_le (by positivity) hlo
    exact_mod_cast this
  have hUm : U.card < m := by
    have : (U.card : ℝ) < W.card := lt_of_le_of_lt hhi (by nlinarith)
    rw [← hWm]; exact_mod_cast this
  have hshr : 10 * s ≤ sf U.card := sf_shrink hU0 (by
    calc (U.card : ℝ) ≤ β * W.card := hhi
      _ ≤ 1 / 10 ^ 4 * W.card := by nlinarith
      _ = W.card / 10 ^ 4 := by ring)
  have hUinv' : VInv p G (AllowedT F1) U (ε + c * sf U.card) := by
    refine hUinv.mono ?_
    have h6 : 6 * s / β = 9 * c * s := by rw [hc]; field_simp; ring
    rw [ha, h6]
    nlinarith
  obtain ⟨Ws, L, hWs0, hV, hbig, hterm⟩ := ih U.card hUm U rfl hUinv'
  refine ⟨consSeq W Ws, L + 1, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    rcases i with _ | k
    · simpa [hWs0] using hUW
    · exact hV.sub k (by omega)
  · intro i hi
    rcases i with _ | k
    · simpa [hWs0] using hhi
    · exact hV.hi k (by omega)
  · intro i hi
    rcases i with _ | k
    · simpa [hWs0] using hlo
    · exact hV.lo k (by omega)
  · intro i hi j
    rcases i with _ | k
    · simp only [consSeq_zero, consSeq_succ, hWs0]
      rw [card_filter_sdiff p W U hUW j, tOf]
      have hw := abs_le.mp (hinv.1 j)
      have hu := abs_le.mp (hdev j)
      have hba : β * a ≤ a := by nlinarith
      have hk1 : (a + (β * a + 2 * s)) * (W.card : ℝ) ≤ κ * W.card :=
        mul_le_mul_of_nonneg_right (by linarith) hmR.le
      have hk2 : a * (W.card : ℝ) + (β * a + 2 * s) * W.card =
        (a + (β * a + 2 * s)) * W.card := by ring
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2, hu.1, hu.2]
    · exact hV.out k (by omega) j
  · intro i hi j
    rcases i with _ | k
    · simp only [consSeq_zero, consSeq_succ, hWs0]
      rw [uOf]
      refine (hdev j).trans ?_
      have hba : β * a ≤ a := by nlinarith
      exact mul_le_mul_of_nonneg_right (by linarith) hmR.le
    · exact hV.inn k (by omega) j
  · intro i hi v hv j hj
    rcases i with _ | k
    · simp only [consSeq_zero] at hv ⊢
      refine (hinv.2 v hv j hj).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hmR.le
    · exact hV.typ k (by omega) v hv j hj
  · intro i hi
    rcases i with _ | k
    · simpa [hWm] using hsmallW
    · exact hbig k (by omega)
  · simpa using hterm

omit [DecidableEq V] in
/-- The initial level: an idealized `F₁`-host satisfies the invariant with error `ε` on `univ`. -/
theorem vInv_univ_of_idealized (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 ≤ ε) (hid : IsIdealizedT F1 ε G p) :
    VInv p G (AllowedT F1) (univ : Finset V) ε := by
  have hn : (0 : ℝ) ≤ (univ : Finset V).card := Nat.cast_nonneg _
  refine ⟨fun j => (nearQuarter_of_idealized hid j).trans
    (mul_le_mul_of_nonneg_right (by linarith) hn), fun v _ j hj => ?_⟩
  have h1 := hid.2.2 v j hj
  have h2 := card_nonNbr_add_degT G p v j
  have h2' : ((univ.filter fun y => p y = j ∧ ¬ G.Adj v y).card : ℝ) +
      (degT G p v j : ℝ) = ((clsT p j).card : ℝ) := by exact_mod_cast h2
  rw [card_univ]
  linarith

/-- **The vortex exists on every idealized `F₁`-host** (proved), for the concrete constants
`β = 10⁻⁶`, `κ = ξ = 10⁻⁸⁰`, host error `ε = 10⁻⁸¹` and any cutoff `X ≥ 10⁹⁰`: `W 0 = univ`,
nonterminal levels have size `≥ X⁴`, the terminal level has size `< X⁴`. -/
theorem exists_F1Vortex_concrete (X : ℕ) (hX : 10 ^ 90 ≤ X) (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hid : IsIdealizedT F1 (1 / 10 ^ 81) G p) :
    ∃ (W : ℕ → Finset V) (L : ℕ), W 0 = univ ∧
      F1Vortex p G W L (1 / 10 ^ 6) (1 / 10 ^ 80) (1 / 10 ^ 80) ∧
      (∀ i < L, X ^ 4 ≤ (W i).card) ∧ (W L).card < X ^ 4 := by
  have hXR : (10 : ℝ) ^ 90 ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hXR
  have hinv1 : 1 / (X : ℝ) ≤ 1 / 10 ^ 90 := one_div_le_one_div_of_le (by positivity) hXR
  have hinv0 : 0 ≤ 1 / (X : ℝ) := by positivity
  have hinv1' : (X : ℝ)⁻¹ ≤ 1 / 10 ^ 90 := by rw [← one_div]; exact hinv1
  have hinv0' : 0 ≤ (X : ℝ)⁻¹ := by positivity
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hv := exists_vortex_from p G (β := 1 / 10 ^ 6) (κ := 1 / 10 ^ 80) (ξ := 1 / 10 ^ 80)
    (ε := 1 / 10 ^ 81) X (by norm_num) (by norm_num) (by norm_num) hX3
    (by linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    _ univ rfl
  have hsf : 0 ≤ sf (univ : Finset V).card := by unfold sf; positivity
  exact hv ((vInv_univ_of_idealized p G (by norm_num) hid).mono
    (by have : (0 : ℝ) ≤ 2 / (3 * (1 / 10 ^ 6)) * sf (univ : Finset V).card := by positivity
        linarith))

end NashWilliams18.SpreadF1

namespace NashWilliams18

open Finset SpreadF1
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- **Theorem 14.7 for `F₁`** (proved, without `Theorem1316Statement`).  Constants first:
`ε = 10⁻⁸¹`, the level constants of `exists_level_constants`, `Nlev`, the cutoff
`X = max 10⁹⁰ Nlev` and terminal size `M = X⁴`, then the host threshold `N`.  On every host,
`compatibleSupply_F1_of_idealized` gives compatible supply with `γ = 1/8 ≥ 5β`, integral
divisibility is the hypothesis of the statement, and `exists_F1Vortex_concrete` builds the
vortex; `F1_close_from_vortex_concrete` decomposes the host. -/
theorem theorem_14_7_F1_of_vortex : Theorem147F1Statement := by
  obtain ⟨Nlev, hNlev, hclose⟩ := F1_close_from_vortex_concrete (1 / 8) (by norm_num)
  set X : ℕ := max (10 ^ 90) Nlev with hXdef
  obtain ⟨N, hN⟩ := hclose (X ^ 4)
  refine ⟨1 / 10 ^ 81, by norm_num, N, fun V _ _ p G _ hn hint hid => ?_⟩
  obtain ⟨W, L, hW0, hV, hbig, hterm⟩ := exists_F1Vortex_concrete X (le_max_left _ _) p G hid
  have hNX : Nlev ≤ X ^ 4 := by
    have h1 : Nlev ≤ X := le_max_right _ _
    have h2 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
    omega
  exact hN G p W L hn (compatibleSupply_F1_of_idealized p G (by norm_num) (by norm_num) hid)
    hint hid.2.1 hW0 hV (fun i hi => le_trans hNX (hbig i hi)) hterm.le

end NashWilliams18
