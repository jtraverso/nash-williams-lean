/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.L3F0VertexSample
public import PartitionedTriangleAbsorption.F1BalanceGateStage228

/-!
# A physical, degree-controlled correction of the F1 reserve balance

We first choose an exact number of available edges with controlled vertex
degrees, using the proved simultaneous discrepancy theorem. We then correct
an integer charge using disjoint pools of charge +1 and -2 edges. The pools
are actual edge sets; their availability and the sampling inequalities are
explicit inputs, rather than a supplied correction or absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1ReserveCorrectionStage231

open Finset F1BalanceGateStage228
open scoped NNReal

variable {V : Type*} [Finite V] [DecidableEq V]

/-- An exact-size sparse subset of a supplied pool of available edges. -/
theorem exists_exact_sparse_subset (W : Finset V) (E : Finset (Sym2 V)) (k : ℕ)
    (r : ℝ≥0) (hr : r ≤ 1) (a b D : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < D) (hE : 0 < E.card)
    (hsupport : ∀ e ∈ E, ∀ v ∈ e, v ∈ W)
    (hdeg : ∀ v, ((E.filter fun e => v ∈ e).card : ℝ) ≤ D)
    (hsize : (k : ℝ) ≤ r * E.card - a)
    (htail : 2 * Real.exp (-2 * a ^ 2 / E.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / D)) < 1) :
    ∃ F ⊆ E, F.card = k ∧
      ∀ v, ((F.filter fun e => v ∈ e).card : ℝ) ≤ r * D + b := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let tests : Option {v // v ∈ W} → Finset (Sym2 V) := fun v =>
    match v with
    | none => univ
    | some v => univ.filter fun e => v.val ∈ e
  let tol : Option {v // v ∈ W} → ℝ := fun v => match v with | none => a | some _ => b
  let cap : Option {v // v ∈ W} → ℝ := fun v => match v with | none => E.card | some _ => D
  have hstar (S : Finset (Sym2 V)) (v : V) :
      (univ.filter fun e => v ∈ e) ∩ S = S.filter fun e => v ∈ e := by
    ext e
    simp [and_comm]
  obtain ⟨S, hSE, hS⟩ := L3F0.exists_subset_discrepancy' E r hr tests univ tol cap
    (by intro v _; cases v <;> simp [tol, ha, hb])
    (by intro v _; cases v <;> simp [cap, hD, hE])
    (by
      intro v _
      cases v with
      | none => simp [tests, cap]
      | some v => simpa only [tests, cap, hstar] using hdeg v.val)
    (by simpa [tol, cap, Fintype.sum_option] using htail)
  have hScard := hS none (mem_univ _)
  simp only [tests, tol, univ_inter] at hScard
  have hkS : k ≤ S.card := by
    have := (abs_lt.mp hScard).1
    have : (k : ℝ) ≤ S.card := by linarith
    exact_mod_cast this
  obtain ⟨F, hFS, hFk⟩ := exists_subset_card_eq hkS
  refine ⟨F, hFS.trans hSE, hFk, fun v => ?_⟩
  by_cases hvW : v ∈ W
  · have hv := hS (some ⟨v, hvW⟩) (mem_univ _)
    simp only [tests, tol, hstar] at hv
    have hmono : ((F.filter fun e => v ∈ e).card : ℝ) ≤
        (S.filter fun e => v ∈ e).card := by
      exact_mod_cast card_le_card (filter_subset_filter _ hFS)
    have hrD := mul_le_mul_of_nonneg_left (hdeg v) (NNReal.coe_nonneg r)
    have := (abs_lt.mp hv).2
    linarith
  · have he : (F.filter fun e => v ∈ e) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro e he hv
      exact hvW (hsupport e (hSE (hFS he)) v hv)
    rw [he, card_empty, Nat.cast_zero]
    positivity

/-- Integer charge correction with nonnegative numbers of +1 and -2 edges. -/
theorem integer_charge_counts (q : ℤ) :
    ∃ p m : ℕ, (p : ℤ) - 2 * m = q ∧ p ≤ q.natAbs + 1 ∧ m ≤ q.natAbs + 1 := by
  cases q with
  | ofNat n => exact ⟨n, 0, by simp, by simp, by simp⟩
  | negSucc n =>
    refine ⟨(n + 1) % 2, (n + 2) / 2, ?_, ?_, ?_⟩
    · omega
    · simp only [Int.natAbs_negSucc]
      omega
    · simp only [Int.natAbs_negSucc]
      omega

/-- The selected edges correct the charge with a uniform degree budget. -/
theorem exists_charge_correction (label : V → Fin 4) (W : Finset V)
    (P M : Finset (Sym2 V)) (q : ℤ) (r : ℝ≥0) (hr : r ≤ 1)
    (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hP : 0 < P.card) (hM : 0 < M.card)
    (hPM : Disjoint P M)
    (hchargeP : ∀ e ∈ P, charge label e = 1)
    (hchargeM : ∀ e ∈ M, charge label e = -2)
    (hsupportP : ∀ e ∈ P, ∀ v ∈ e, v ∈ W)
    (hsupportM : ∀ e ∈ M, ∀ v ∈ e, v ∈ W)
    (hdegP : ∀ v, ((P.filter fun e => v ∈ e).card : ℝ) ≤ D)
    (hdegM : ∀ v, ((M.filter fun e => v ∈ e).card : ℝ) ≤ D)
    (hsizeP : ((q.natAbs + 1 : ℕ) : ℝ) ≤ r * P.card - a)
    (hsizeM : ((q.natAbs + 1 : ℕ) : ℝ) ≤ r * M.card - a)
    (htailP : 2 * Real.exp (-2 * a ^ 2 / P.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / D)) < 1)
    (htailM : 2 * Real.exp (-2 * a ^ 2 / M.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / D)) < 1) :
    ∃ C ⊆ P ∪ M, balance label C = q ∧ C.card ≤ 2 * (q.natAbs + 1) ∧
      ∀ v, ((C.filter fun e => v ∈ e).card : ℝ) ≤ 2 * (r * D + b) := by
  obtain ⟨p, m, hq, hp, hm⟩ := integer_charge_counts q
  obtain ⟨Cp, hCp, hpcard, hpdeg⟩ := exists_exact_sparse_subset W P p r hr a b D
    ha hb hD hP hsupportP hdegP
    ((by exact_mod_cast hp : (p : ℝ) ≤ ((q.natAbs + 1 : ℕ) : ℝ)).trans hsizeP)
    htailP
  obtain ⟨Cm, hCm, hmcard, hmdeg⟩ := exists_exact_sparse_subset W M m r hr a b D
    ha hb hD hM hsupportM hdegM
    ((by exact_mod_cast hm : (m : ℝ) ≤ ((q.natAbs + 1 : ℕ) : ℝ)).trans hsizeM)
    htailM
  have hd : Disjoint Cp Cm := hPM.mono hCp hCm
  refine ⟨Cp ∪ Cm, union_subset_union hCp hCm, ?_, ?_, fun v => ?_⟩
  · unfold balance
    rw [sum_union hd]
    have h1 : (∑ e ∈ Cp, charge label e) = (p : ℝ) := by
      rw [sum_congr rfl (fun e he => hchargeP e (hCp he))]
      simp [hpcard]
    have h2 : (∑ e ∈ Cm, charge label e) = -2 * (m : ℝ) := by
      rw [sum_congr rfl (fun e he => hchargeM e (hCm he))]
      simp [hmcard, mul_comm]
    rw [h1, h2]
    have : (p : ℝ) - 2 * m = q := by exact_mod_cast hq
    linarith
  · rw [card_union_of_disjoint hd, hpcard, hmcard]
    omega
  · rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hd), Nat.cast_add]
    linarith [hpdeg v, hmdeg v]

/-- The charge is integral even though the load API uses real numbers. -/
def integerBalance (label : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  ∑ e ∈ E, Sym2.lift ⟨fun x y => pairCharge (label x) (label y),
    fun x y => pairCharge_symm (label x) (label y)⟩ e

omit [Finite V] [DecidableEq V] in
theorem cast_integerBalance (label : V → Fin 4) (E : Finset (Sym2 V)) :
    (integerBalance label E : ℝ) = balance label E := by
  simp [integerBalance, balance, charge]

/-- Repair the reserve itself, not merely a detached charge vector. The input
pools lie outside both the protected core and the existing reserve. The output
keeps the core protected and makes the graph available to the nibble balanced. -/
theorem exists_balanced_reserve_extension (label : V → Fin 4) (W : Finset V)
    (E I R P M : Finset (Sym2 V)) (r : ℝ≥0) (hr : r ≤ 1)
    (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hI : I ⊆ E) (hR : R ⊆ E \ I) (hE : balance label E = 0)
    (hsupport : ∀ e ∈ E, ∀ v ∈ e, v ∈ W)
    (hpools : P ∪ M ⊆ (E \ I) \ R)
    (hP : 0 < P.card) (hM : 0 < M.card) (hPM : Disjoint P M)
    (hchargeP : ∀ e ∈ P, charge label e = 1)
    (hchargeM : ∀ e ∈ M, charge label e = -2)
    (hdegP : ∀ v, ((P.filter fun e => v ∈ e).card : ℝ) ≤ D)
    (hdegM : ∀ v, ((M.filter fun e => v ∈ e).card : ℝ) ≤ D)
    (hsizeP : (((-integerBalance label I - integerBalance label R).natAbs + 1 : ℕ) : ℝ)
      ≤ r * P.card - a)
    (hsizeM : (((-integerBalance label I - integerBalance label R).natAbs + 1 : ℕ) : ℝ)
      ≤ r * M.card - a)
    (htailP : 2 * Real.exp (-2 * a ^ 2 / P.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / D)) < 1)
    (htailM : 2 * Real.exp (-2 * a ^ 2 / M.card) +
      W.card * (2 * Real.exp (-2 * b ^ 2 / D)) < 1) :
    ∃ R', R ⊆ R' ∧ R' ⊆ E \ I ∧ R' \ R ⊆ P ∪ M ∧
      balance label ((E \ I) \ R') = 0 ∧
      (R' \ R).card ≤ 2 * ((-integerBalance label I - integerBalance label R).natAbs + 1) ∧
      (∀ v, (((R' \ R).filter fun e => v ∈ e).card : ℝ) ≤ 2 * (r * D + b)) ∧
      (∀ v, ((R'.filter fun e => v ∈ e).card : ℝ) ≤
        (R.filter fun e => v ∈ e).card + 2 * (r * D + b)) := by
  have hp : P ⊆ E := (subset_union_left.trans hpools).trans
    (sdiff_subset.trans sdiff_subset)
  have hm : M ⊆ E := (subset_union_right.trans hpools).trans
    (sdiff_subset.trans sdiff_subset)
  obtain ⟨C, hC, hbalC, hcardC, hdegC⟩ := exists_charge_correction label W P M
    (-integerBalance label I - integerBalance label R) r hr a b D ha hb hD
    hP hM hPM hchargeP hchargeM
    (fun e he => hsupport e (hp he)) (fun e he => hsupport e (hm he))
    hdegP hdegM hsizeP hsizeM htailP htailM
  have hCsub : C ⊆ (E \ I) \ R := hC.trans hpools
  have hdis : Disjoint R C := by
    rw [disjoint_left]
    intro e heR heC
    exact (mem_sdiff.mp (hCsub heC)).2 heR
  have hnew : (R ∪ C) \ R = C := by
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact (hn h).elim
      · exact h
    · intro he
      exact ⟨Or.inr he, (mem_sdiff.mp (hCsub he)).2⟩
  have hsub : R ∪ C ⊆ E \ I := union_subset hR
    (hCsub.trans sdiff_subset)
  refine ⟨R ∪ C, subset_union_left, hsub, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hnew] using hC
  · rw [balanced_puncture_reserve_ledger label E I (R ∪ C) hI hsub hE]
    have hu : balance label (R ∪ C) = balance label R + balance label C := by
      exact sum_union hdis
    rw [hu, hbalC]
    simp only [Int.cast_sub, Int.cast_neg, cast_integerBalance]
    ring
  · simpa only [hnew] using hcardC
  · simpa only [hnew] using hdegC
  · intro v
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hdis), Nat.cast_add]
    linarith [hdegC v]

omit [Finite V] in
/-- Adding a degree-bounded correction changes every restricted neighbourhood
by at most that degree. This applies to each fine class in the reserve tests. -/
theorem corrected_target_growth (U : Finset V) (R C : Finset (Sym2 V))
    (v : V) (test : V → Prop) [DecidablePred test] :
    ((U.filter fun u => test u ∧ s(v, u) ∈ R ∪ C) \
      (U.filter fun u => test u ∧ s(v, u) ∈ R)).card ≤
      (C.filter fun e => v ∈ e).card := by
  apply card_le_card_of_injOn (fun u => s(v, u))
  · intro u hu
    simp only [mem_coe, mem_sdiff, mem_filter, mem_union] at hu
    have hc : s(v, u) ∈ C := by tauto
    exact mem_filter.mpr ⟨hc, Sym2.mem_mk_left _ _⟩
  · intro u _ w _ he
    exact Sym2.congr_right.mp he

omit [Finite V] in
/-- Every two-root reserve test is stable under a degree-bounded correction.
The event can require either reserved or unreserved edges. This covers the
common-neighbour tests, including pairwise overlaps, without independence
assumptions on the correcting edges. -/
theorem corrected_pair_test (U : Finset V) (R C : Finset (Sym2 V)) (v w : V)
    (event : V → Bool → Bool → Prop) [∀ u x y, Decidable (event u x y)] :
    |((U.filter fun u => event u (decide (s(v, u) ∈ R ∪ C))
        (decide (s(w, u) ∈ R ∪ C))).card : ℝ) -
      (U.filter fun u => event u (decide (s(v, u) ∈ R))
        (decide (s(w, u) ∈ R))).card| ≤
      (C.filter fun e => v ∈ e).card + (C.filter fun e => w ∈ e).card := by
  let A := U.filter fun u => event u (decide (s(v, u) ∈ R ∪ C))
    (decide (s(w, u) ∈ R ∪ C))
  let B := U.filter fun u => event u (decide (s(v, u) ∈ R))
    (decide (s(w, u) ∈ R))
  let S := U.filter fun u => s(v, u) ∈ C ∨ s(w, u) ∈ C
  have hs (u : V) (hu : u ∈ U) (hn : u ∉ S) :
      s(v, u) ∉ C ∧ s(w, u) ∉ C := by
    simpa only [S, mem_filter, hu, true_and, not_or] using hn
  have hAB : A ⊆ B ∪ S := by
    intro u hu
    by_cases hn : u ∈ S
    · exact mem_union_right _ hn
    · obtain ⟨huU, he⟩ := mem_filter.mp hu
      obtain ⟨hv, hw⟩ := hs u huU hn
      apply mem_union_left
      exact mem_filter.mpr ⟨huU, by simpa [hv, hw] using he⟩
  have hBA : B ⊆ A ∪ S := by
    intro u hu
    by_cases hn : u ∈ S
    · exact mem_union_right _ hn
    · obtain ⟨huU, he⟩ := mem_filter.mp hu
      obtain ⟨hv, hw⟩ := hs u huU hn
      apply mem_union_left
      exact mem_filter.mpr ⟨huU, by simpa [hv, hw] using he⟩
  have hS : S.card ≤ (C.filter fun e => v ∈ e).card +
      (C.filter fun e => w ∈ e).card := by
    have hsplit : S = (U.filter fun u => s(v, u) ∈ C) ∪
        (U.filter fun u => s(w, u) ∈ C) := by
      ext u
      simp only [S, mem_filter, mem_union]
      tauto
    have hv : (U.filter fun u => s(v, u) ∈ C).card ≤
        (C.filter fun e => v ∈ e).card := by
      simpa using corrected_target_growth U ∅ C v (fun _ => True)
    have hw : (U.filter fun u => s(w, u) ∈ C).card ≤
        (C.filter fun e => w ∈ e).card := by
      simpa using corrected_target_growth U ∅ C w (fun _ => True)
    rw [hsplit]
    exact (card_union_le _ _).trans (Nat.add_le_add hv hw)
  have h1 : A.card ≤ B.card + S.card := (card_le_card hAB).trans (card_union_le _ _)
  have h2 : B.card ≤ A.card + S.card := (card_le_card hBA).trans (card_union_le _ _)
  have h1R : (A.card : ℝ) ≤ B.card + S.card := by exact_mod_cast h1
  have h2R : (B.card : ℝ) ≤ A.card + S.card := by exact_mod_cast h2
  have hSR : (S.card : ℝ) ≤ (C.filter fun e => v ∈ e).card +
      (C.filter fun e => w ∈ e).card := by exact_mod_cast hS
  change |(A.card : ℝ) - B.card| ≤ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The four numerical inequalities of `SpreadF1.MarginsSlack` survive:
allow a further defect `d` and growth of at most `d` in the root's own class.
The partner classes need only grow. The initial extra margin is explicit. -/
theorem reserve_margin_stability (a b c a' b' c' Γ γ d : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (ha' : a' ≤ a + d)
    (h1 : 4 * (Γ + 2 * d) + 1 + γ ≤ a)
    (h2 : 6 * (Γ + 2 * d) + 1 + γ ≤ b)
    (h3 : 6 * (Γ + 2 * d) + 1 + γ ≤ c)
    (h4 : a + 8 * (Γ + 2 * d) + 1 + 2 * γ ≤ b + c) :
    4 * (Γ + d) + 1 + γ ≤ a' ∧
    6 * (Γ + d) + 1 + γ ≤ b' ∧
    6 * (Γ + d) + 1 + γ ≤ c' ∧
    a' + 8 * (Γ + d) + 1 + 2 * γ ≤ b' + c' := by
  omega

end PartitionedTriangleAbsorption.F1ReserveCorrectionStage231
