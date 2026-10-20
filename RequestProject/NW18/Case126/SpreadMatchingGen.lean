/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib

/-!
# Spread choice of pairings at many roots (deterministic potential argument), generic form

**Attribution.**  The potential argument of this file is *adapted* from the L3 F0 project
(`L3_F0_reference/L3F0/SpreadMatching.lean`, `spread_link_matching_of_family`,
`perRootFamily_of_single`), which is stated there for the two-class family `F0` and the typed
predicate `IsLinkMatching p T g R`.  Here the same argument is stated for an **arbitrary** pair
predicate `ok t : V → V → Prop` per root `t`, so that it can be instantiated with the `F₁` link
pair types (`SpreadPairingF1.lean`).  The mathematics is unchanged; only the predicate is
abstracted, so that no `F0`-specific fact is used.

**Why it is needed for `F₁`.**  Charging the consumption of earlier roots in the worst case
forces `load ≤ degree into the target`; `CrossingCover.crossing_cover_regime` proves that this
forbids a vortex level with a small child set.  Here each root `t` has a *family* of `K` pairwise
edge-disjoint pairings of its target `T t`, and we choose among them one minimising the
exponential potential
`Φ_t = ∑_{i ≥ t} ∑_{u ∈ T i} exp (c_t(u,i) - μ ℓ_t(u))`
(`c_t(u,i)`: consumed edges from `u` into `T i`; `ℓ_t(u)`: processed targets through `u`).
Since the `K` partners of `u` are distinct, at most `|T t ∩ T i| ≤ ω` of them lie in `T i`, so the
requirement becomes the SECOND ORDER condition `(e-1) ω L / K + log ∑ |T i| ≤ B`.
-/

namespace NashWilliams18.SpreadGen

open Finset

variable {V : Type*} [DecidableEq V]

/-- Degree of `v` in an edge set. -/
def deg (E : Finset (Sym2 V)) (v : V) : ℕ := (E.filter (fun e => v ∈ e)).card

/-- `f` is a perfect matching of `T` (a fixed-point-free involution of `T`) by edges of `R`, every
pair satisfying `ok`. -/
def IsOkMatching (ok : V → V → Prop) (T : Finset V) (R : Finset (Sym2 V)) (f : V → V) : Prop :=
  ∀ v ∈ T, f v ∈ T ∧ f v ≠ v ∧ f (f v) = v ∧ s(v, f v) ∈ R ∧ ok v (f v)

/-- The edges of a matching. -/
def matchEdges (T : Finset V) (f : V → V) : Finset (Sym2 V) := T.image (fun v => s(v, f v))

theorem mem_matchEdges {ok : V → V → Prop} {T : Finset V} {R : Finset (Sym2 V)}
    {f : V → V} (hf : IsOkMatching ok T R f) {e : Sym2 V} (he : e ∈ matchEdges T f) {v : V}
    (hv : v ∈ e) : v ∈ T ∧ e = s(v, f v) := by
  simp only [matchEdges, Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact ⟨ha, rfl⟩
  · obtain ⟨h1, -, h3, -⟩ := hf a ha
    exact ⟨h1, by rw [h3, Sym2.eq_swap]⟩

theorem matchEdges_subset {ok : V → V → Prop} {T : Finset V} {R : Finset (Sym2 V)}
    {f : V → V} (hf : IsOkMatching ok T R f) : matchEdges T f ⊆ R := by
  intro e he
  simp only [matchEdges, Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact (hf a ha).2.2.2.1

theorem deg_matchEdges_le {ok : V → V → Prop} {T : Finset V} {R : Finset (Sym2 V)}
    {f : V → V} (hf : IsOkMatching ok T R f) (v : V) :
    deg (matchEdges T f) v ≤ if v ∈ T then 1 else 0 := by
  unfold deg
  split_ifs with hv
  · rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    rw [(mem_matchEdges hf ha.1 ha.2).2, (mem_matchEdges hf hb.1 hb.2).2]
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hve
    exact hv (mem_matchEdges hf he hve).1

theorem card_filter_pair_le (X : Finset V) (F : Finset (Sym2 V)) (v : V) :
    (X.filter (fun w => s(v, w) ∈ F)).card ≤ deg F v := by
  unfold deg
  apply Finset.card_le_card_of_injOn (fun w => s(v, w))
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw ⊢
    exact ⟨hw.2, Sym2.mem_mk_left v w⟩
  · intro a _ b _ hab
    exact Sym2.congr_right.mp hab

omit [DecidableEq V] in
theorem isOkMatching_mono {ok : V → V → Prop} {T : Finset V} {R R' : Finset (Sym2 V)}
    {f : V → V} (h : IsOkMatching ok T R f) (hR : R ⊆ R') : IsOkMatching ok T R' f := by
  intro v hv
  obtain ⟨a1, a2, a3, a4, a5⟩ := h v hv
  exact ⟨a1, a2, a3, hR a4, a5⟩

/-- The edges consumed by the matchings of the roots `< t`. -/
def consumed (T : ℕ → Finset V) (f : ℕ → V → V) (t : ℕ) : Finset (Sym2 V) :=
  (range t).biUnion (fun i => matchEdges (T i) (f i))

/-- Consumed edges from `u` into the target `T i`. -/
def inLoad (T : ℕ → Finset V) (F : Finset (Sym2 V)) (u : V) (i : ℕ) : ℕ :=
  ((T i).filter (fun w => s(u, w) ∈ F)).card

/-- Number of targets `T j`, `j < t`, through `u`. -/
def visits (T : ℕ → Finset V) (t : ℕ) (u : V) : ℕ :=
  ((range t).filter (fun j => u ∈ T j)).card

/-- The exponential potential of the not-yet-processed roots `t ≤ i < k`. -/
noncomputable def potential (T : ℕ → Finset V) (k t : ℕ) (F : Finset (Sym2 V)) (μ : ℝ) : ℝ :=
  ∑ i ∈ Ico t k, ∑ u ∈ T i, Real.exp ((inLoad T F u i : ℝ) - μ * visits T t u)

/-- A family of `K` pairwise edge-disjoint `ok`-matchings of `T` in `R`. -/
def PerRootFamily (ok : V → V → Prop) (T : Finset V) (R : Finset (Sym2 V)) (K : ℕ)
    (fs : ℕ → V → V) : Prop :=
  (∀ j < K, IsOkMatching ok T R (fs j)) ∧
    ∀ j < K, ∀ j' < K, j ≠ j' → Disjoint (matchEdges T (fs j)) (matchEdges T (fs j'))

theorem visits_succ (T : ℕ → Finset V) (t : ℕ) (u : V) :
    visits T (t + 1) u = visits T t u + if u ∈ T t then 1 else 0 := by
  unfold visits
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem visits_le (T : ℕ → Finset V) {t k : ℕ} (htk : t ≤ k) (u : V) :
    visits T t u ≤ visits T k u := by
  unfold visits
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr htk))

theorem inLoad_union_le {ok : V → V → Prop} {T : ℕ → Finset V} {R F : Finset (Sym2 V)}
    {t : ℕ} {h : V → V} (hh : IsOkMatching ok (T t) R h) (u : V) (i : ℕ) :
    inLoad T (F ∪ matchEdges (T t) h) u i ≤
      inLoad T F u i + if u ∈ T t ∧ h u ∈ T i then 1 else 0 := by
  unfold inLoad
  have hsplit : (T i).filter (fun w => s(u, w) ∈ F ∪ matchEdges (T t) h) ⊆
      (T i).filter (fun w => s(u, w) ∈ F) ∪
        (T i).filter (fun w => s(u, w) ∈ matchEdges (T t) h) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_union] at hw ⊢
    rcases hw.2 with h1 | h1
    · exact Or.inl ⟨hw.1, h1⟩
    · exact Or.inr ⟨hw.1, h1⟩
  have hM : ((T i).filter (fun w => s(u, w) ∈ matchEdges (T t) h)).card ≤
      if u ∈ T t ∧ h u ∈ T i then 1 else 0 := by
    have hsub : (T i).filter (fun w => s(u, w) ∈ matchEdges (T t) h) ⊆ {h u} := by
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨-, he⟩ := mem_matchEdges hh hw.2 (Sym2.mem_mk_left u w)
      exact Finset.mem_singleton.mpr (Sym2.congr_right.mp he)
    split_ifs with hc
    · exact (Finset.card_le_card hsub).trans (by simp)
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw hwM
      obtain ⟨hu, he⟩ := mem_matchEdges hh hwM (Sym2.mem_mk_left u w)
      have := Sym2.congr_right.mp he
      subst this
      exact hc ⟨hu, hw⟩
  exact (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans (by omega))

theorem card_partners_le {ok : V → V → Prop} {T : Finset V} {R : Finset (Sym2 V)}
    {K : ℕ} {fs : ℕ → V → V} (hfam : PerRootFamily ok T R K fs) {u : V} (hu : u ∈ T)
    (T' : Finset V) :
    ((range K).filter (fun j => fs j u ∈ T')).card ≤ (T ∩ T').card := by
  apply Finset.card_le_card_of_injOn (fun j => fs j u)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe]
    exact ⟨(hfam.1 j hj.1 u hu).1, hj.2⟩
  · intro j hj j' hj' hjj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj hj'
    by_contra hne
    have h1 : s(u, fs j u) ∈ matchEdges T (fs j) := Finset.mem_image_of_mem _ hu
    have h2 : s(u, fs j u) ∈ matchEdges T (fs j') := by
      rw [show fs j u = fs j' u from hjj]; exact Finset.mem_image_of_mem _ hu
    exact Finset.disjoint_left.mp (hfam.2 j hj.1 j' hj'.1 hne) h1 h2

theorem consumed_succ (T : ℕ → Finset V) (f : ℕ → V → V) (t : ℕ) (h : V → V) :
    consumed T (fun i => if i = t then h else f i) (t + 1) =
      consumed T f t ∪ matchEdges (T t) h := by
  unfold consumed
  rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  congr 1
  · apply Finset.biUnion_congr rfl
    intro i hi
    simp [Nat.ne_of_lt (Finset.mem_range.mp hi)]
  · simp

/-! ### The potential step -/

theorem exp_neg_mu_mul (K ω : ℕ) (hK : 0 < K) :
    Real.exp (-Real.log (1 + (Real.exp 1 - 1) * ω / K)) * (K + (Real.exp 1 - 1) * ω) = K := by
  have he : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1; linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < 1 + (Real.exp 1 - 1) * ω / K := by positivity
  rw [Real.exp_neg, Real.exp_log hpos]
  field_simp

theorem mu_nonneg (K ω : ℕ) : 0 ≤ Real.log (1 + (Real.exp 1 - 1) * ω / K) := by
  have he : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1; linarith
  apply Real.log_nonneg
  have : 0 ≤ (Real.exp 1 - 1) * ω / K := by positivity
  linarith

theorem mu_le (K ω : ℕ) (hK : 0 < K) :
    Real.log (1 + (Real.exp 1 - 1) * ω / K) ≤ (Real.exp 1 - 1) * ω / K := by
  have he : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1; linarith
  have : 0 ≤ (Real.exp 1 - 1) * ω / K := by positivity
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (Real.exp 1 - 1) * ω / K by linarith)
  linarith

theorem exp_add_ite_le (x : ℝ) (P : Prop) [Decidable P] :
    Real.exp (x + ((if P then 1 else 0 : ℕ) : ℝ)) ≤
      Real.exp x * (1 + (Real.exp 1 - 1) * ((if P then 1 else 0 : ℕ) : ℝ)) := by
  split_ifs
  · rw [Real.exp_add]; simp
  · simp

/-- One `(u,i)` term, `u` in the current target: the average over the family is controlled. -/
theorem sum_term_le_in (c : ℕ → ℕ) (c0 ℓ K ω : ℕ) (hK : 0 < K) (P : ℕ → Prop)
    [DecidablePred P] (hc : ∀ j < K, c j ≤ c0 + if P j then 1 else 0)
    (hP : ((range K).filter P).card ≤ ω) :
    ∑ j ∈ range K, Real.exp ((c j : ℝ) -
        Real.log (1 + (Real.exp 1 - 1) * ω / K) * ((ℓ + 1 : ℕ) : ℝ)) ≤
      K * Real.exp ((c0 : ℝ) - Real.log (1 + (Real.exp 1 - 1) * ω / K) * ℓ) := by
  set μ := Real.log (1 + (Real.exp 1 - 1) * ω / K) with hμ
  have he : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1; linarith
  set A := Real.exp ((c0 : ℝ) - μ * ℓ) with hA
  have hterm : ∀ j ∈ range K, Real.exp ((c j : ℝ) - μ * ((ℓ + 1 : ℕ) : ℝ)) ≤
      A * Real.exp (-μ) * (1 + (Real.exp 1 - 1) * ((if P j then 1 else 0 : ℕ) : ℝ)) := by
    intro j hj
    have hcj := hc j (Finset.mem_range.mp hj)
    have h1 : Real.exp ((c j : ℝ) - μ * ((ℓ + 1 : ℕ) : ℝ)) ≤
        Real.exp (((c0 : ℝ) - μ * ℓ - μ) + ((if P j then 1 else 0 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (c j : ℝ) ≤ c0 + ((if P j then 1 else 0 : ℕ) : ℝ) := by exact_mod_cast hcj
      have hl : ((ℓ + 1 : ℕ) : ℝ) = ℓ + 1 := by push_cast; ring
      rw [hl]
      linarith
    refine h1.trans ((exp_add_ite_le _ _).trans (le_of_eq ?_))
    rw [hA, ← Real.exp_add]
    ring_nf
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcount : ∑ j ∈ range K, ((if P j then 1 else 0 : ℕ) : ℝ) ≤ ω := by
    have : ∑ j ∈ range K, ((if P j then 1 else 0 : ℕ) : ℝ) = (((range K).filter P).card : ℝ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [this]; exact_mod_cast hP
  have hA0 : 0 ≤ A * Real.exp (-μ) := by positivity
  calc A * Real.exp (-μ) * (∑ _j ∈ range K, (1 : ℝ) +
        (Real.exp 1 - 1) * ∑ j ∈ range K, ((if P j then 1 else 0 : ℕ) : ℝ))
      ≤ A * Real.exp (-μ) * (K + (Real.exp 1 - 1) * ω) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have := mul_le_mul_of_nonneg_left hcount he
        linarith
    _ = K * A := by
        rw [mul_assoc, hμ, exp_neg_mu_mul K ω hK]; ring

/-- **Potential step.** Some member of the family does not increase the potential. -/
theorem potential_step {ok : V → V → Prop} {R F : Finset (Sym2 V)} {T : ℕ → Finset V}
    {k t K ω : ℕ} (hK : 0 < K) {fs : ℕ → V → V}
    (hfam : PerRootFamily ok (T t) (R \ F) K fs)
    (hover : ∀ i ∈ Ico (t + 1) k, ((T t) ∩ (T i)).card ≤ ω) :
    ∃ j < K, potential T k (t + 1) (F ∪ matchEdges (T t) (fs j))
        (Real.log (1 + (Real.exp 1 - 1) * ω / K)) ≤
      potential T k t F (Real.log (1 + (Real.exp 1 - 1) * ω / K)) := by
  set μ := Real.log (1 + (Real.exp 1 - 1) * ω / K) with hμ
  have hsum : ∑ j ∈ range K, potential T k (t + 1) (F ∪ matchEdges (T t) (fs j)) μ ≤
      ∑ _j ∈ range K, potential T k t F μ := by
    unfold potential
    rw [Finset.sum_comm]
    have hstep : ∀ i ∈ Ico (t + 1) k, ∑ j ∈ range K, ∑ u ∈ T i,
        Real.exp ((inLoad T (F ∪ matchEdges (T t) (fs j)) u i : ℝ) - μ * visits T (t + 1) u) ≤
        K * ∑ u ∈ T i, Real.exp ((inLoad T F u i : ℝ) - μ * visits T t u) := by
      intro i hi
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u ∈ T t
      · have hv : visits T (t + 1) u = visits T t u + 1 := by simp [visits_succ, hu]
        simp only [hv]
        apply sum_term_le_in _ _ _ K ω hK (fun j => fs j u ∈ T i)
        · intro j hj
          have := inLoad_union_le (F := F) ((hfam.1 j hj)) u i
          simp only [hu, true_and] at this
          exact this
        · exact card_partners_le hfam hu (T i) |>.trans (hover i hi)
      · have hv : visits T (t + 1) u = visits T t u := by simp [visits_succ, hu]
        simp only [hv]
        have hle : ∀ j ∈ range K, Real.exp ((inLoad T (F ∪ matchEdges (T t) (fs j)) u i : ℝ) -
            μ * visits T t u) ≤ Real.exp ((inLoad T F u i : ℝ) - μ * visits T t u) := by
          intro j hj
          apply Real.exp_le_exp.mpr
          have := inLoad_union_le (F := F) ((hfam.1 j (Finset.mem_range.mp hj))) u i
          simp only [hu, false_and, ite_false, add_zero] at this
          have : (inLoad T (F ∪ matchEdges (T t) (fs j)) u i : ℝ) ≤ inLoad T F u i := by
            exact_mod_cast this
          linarith
        refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
        simp
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases htk : t < k
    · rw [Finset.sum_eq_sum_Ico_succ_bot htk]
      have : 0 ≤ ∑ u ∈ T t, Real.exp ((inLoad T F u t : ℝ) - μ * visits T t u) :=
        Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      linarith
    · rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (by omega)) hsum
  exact ⟨j, Finset.mem_range.mp hj, hle⟩

/-- The potential controls the in-target consumption of the current root. -/
theorem inLoad_le_of_potential {T : ℕ → Finset V} {k t : ℕ} (htk : t < k) {F : Finset (Sym2 V)}
    {μ P : ℝ} (hΦ : potential T k t F μ ≤ P) {v : V} (hv : v ∈ T t) :
    (inLoad T F v t : ℝ) ≤ μ * visits T t v + Real.log P := by
  have hterm : Real.exp ((inLoad T F v t : ℝ) - μ * visits T t v) ≤ potential T k t F μ := by
    unfold potential
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ u ∈ T i,
      Real.exp ((inLoad T F u i : ℝ) - μ * visits T t u))
      (fun i _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
      (Finset.mem_Ico.mpr ⟨le_rfl, htk⟩))
    exact Finset.single_le_sum (f := fun u => Real.exp ((inLoad T F u t : ℝ) - μ * visits T t u))
      (fun _ _ => (Real.exp_pos _).le) hv
  have hP : 0 < P := lt_of_lt_of_le (Real.exp_pos _) (hterm.trans hΦ)
  have := (Real.le_log_iff_exp_le hP).mpr (hterm.trans hΦ)
  linarith

theorem potential_zero (T : ℕ → Finset V) (k : ℕ) (μ : ℝ) :
    potential T k 0 ∅ μ = ∑ i ∈ range k, ((T i).card : ℝ) := by
  unfold potential inLoad visits
  simp

/-! ### The spread choice -/

/-- **Spread choice of matchings** (generic form of the `F0` lemma
`spread_link_matching_of_family`).  Suppose every root `t` has, against ANY consumed graph whose
trace inside `T t` is pointwise `≤ B`, a family of `K` pairwise edge-disjoint `ok t`-matchings
avoiding it.  If distinct targets overlap in `≤ ω` vertices, every vertex lies in `≤ L` targets,
and `(e-1) ω L / K + log ∑ |T i| ≤ B`, then ALL roots have `ok`-matchings in `R` that are pairwise
edge-disjoint. -/
theorem spread_matching_of_family (ok : ℕ → V → V → Prop) (R : Finset (Sym2 V)) (k : ℕ)
    (T : ℕ → Finset V) (K B ω L : ℕ) (hK : 0 < K)
    (hfam : ∀ t < k, ∀ F : Finset (Sym2 V), (∀ v ∈ T t, inLoad T F v t ≤ B) →
      ∃ fs : ℕ → V → V, PerRootFamily (ok t) (T t) (R \ F) K fs)
    (hover : ∀ i < k, ∀ j < k, i ≠ j → ((T i) ∩ (T j)).card ≤ ω)
    (hload : ∀ v, visits T k v ≤ L)
    (hB : (Real.exp 1 - 1) * ω * L / K + Real.log (∑ i ∈ range k, ((T i).card : ℝ)) ≤ B) :
    ∃ f : ℕ → V → V, (∀ i < k, IsOkMatching (ok i) (T i) R (f i)) ∧
      ∀ i < k, ∀ j < k, i ≠ j → Disjoint (matchEdges (T i) (f i)) (matchEdges (T j) (f j)) := by
  set μ := Real.log (1 + (Real.exp 1 - 1) * ω / K) with hμ
  set P := ∑ i ∈ range k, ((T i).card : ℝ) with hPdef
  have hμ0 : 0 ≤ μ := mu_nonneg K ω
  have hμle : μ ≤ (Real.exp 1 - 1) * ω / K := mu_le K ω hK
  suffices H : ∀ t ≤ k, ∃ f : ℕ → V → V, (∀ i < t, IsOkMatching (ok i) (T i) R (f i)) ∧
      (∀ i < t, ∀ j < t, i ≠ j → Disjoint (matchEdges (T i) (f i)) (matchEdges (T j) (f j))) ∧
      potential T k t (consumed T f t) μ ≤ P by
    obtain ⟨f, h1, h2, -⟩ := H k le_rfl
    exact ⟨f, h1, h2⟩
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun _ => id, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    have : consumed T (fun _ => id) 0 = ∅ := by simp [consumed]
    rw [this, potential_zero]
  | succ t ih =>
    intro hm
    have htk : t < k := hm
    obtain ⟨f, hf, hdisj, hΦ⟩ := ih (Nat.le_of_succ_le hm)
    set F := consumed T f t with hF
    have hbound : ∀ v ∈ T t, inLoad T F v t ≤ B := by
      intro v hv
      have h1 := inLoad_le_of_potential htk hΦ hv
      have hvis : (visits T t v : ℝ) ≤ L := by
        exact_mod_cast (visits_le T htk.le v).trans (hload v)
      have h2 : μ * visits T t v ≤ (Real.exp 1 - 1) * ω * L / K := by
        calc μ * visits T t v ≤ ((Real.exp 1 - 1) * ω / K) * L :=
              mul_le_mul hμle hvis (by positivity) (le_trans hμ0 hμle)
          _ = (Real.exp 1 - 1) * ω * L / K := by ring
      have : (inLoad T F v t : ℝ) ≤ B := by linarith
      exact_mod_cast this
    obtain ⟨fs, hfs⟩ := hfam t htk F hbound
    obtain ⟨j, hj, hΦj⟩ := potential_step (R := R) (F := F) (k := k) hK hfs
      (fun i hi => hover t htk i (Finset.mem_Ico.mp hi).2 (by
        have := (Finset.mem_Ico.mp hi).1; omega))
    set h := fs j with hh
    have hhR : IsOkMatching (ok t) (T t) (R \ F) h := hfs.1 j hj
    let f' : ℕ → V → V := fun i => if i = t then h else f i
    have hf't : f' t = h := by simp [f']
    have hf'i : ∀ i < t, f' i = f i := fun i hi => by simp [f', Nat.ne_of_lt hi]
    have hnew : ∀ i < t, Disjoint (matchEdges (T i) (f i)) (matchEdges (T t) h) := by
      intro i hi
      rw [Finset.disjoint_left]
      intro e he he'
      have hsub := matchEdges_subset hhR he'
      exact (Finset.mem_sdiff.mp hsub).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, he⟩)
    refine ⟨f', fun i hi => ?_, fun i hi i' hi' hii => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hf'i i hi]; exact hf i hi
      · rw [hf't]; exact isOkMatching_mono hhR Finset.sdiff_subset
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hf'i i hi, hf'i i' hi']; exact hdisj i hi i' hi' hii
      · rw [hf'i i hi, hf't]; exact hnew i hi
      · rw [hf'i i' hi', hf't]; exact (hnew i' hi').symm
      · exact absurd rfl hii
    · have hc : consumed T f' (t + 1) = F ∪ matchEdges (T t) h := consumed_succ T f t h
      rw [hc]
      exact hΦj.trans hΦ

/-! ### Per-root families from a single-matching producer -/

theorem card_filter_union_le (X : Finset V) (F G : Finset (Sym2 V)) (v : V) :
    (X.filter (fun w => s(v, w) ∈ F ∪ G)).card ≤
      (X.filter (fun w => s(v, w) ∈ F)).card + (X.filter (fun w => s(v, w) ∈ G)).card := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_union] at hw ⊢
  rcases hw.2 with h | h
  · exact Or.inl ⟨hw.1, h⟩
  · exact Or.inr ⟨hw.1, h⟩

/-- `K` pairwise edge-disjoint `ok`-matchings of ONE target avoiding a consumed graph `F` whose
trace inside `T` is pointwise `≤ B`, from a single-matching producer that tolerates any consumed
graph of trace `≤ B + K` (generic form of the `F0` lemma `perRootFamily_of_single`). -/
theorem perRootFamily_of_single (ok : V → V → Prop) (T : Finset V)
    (R F : Finset (Sym2 V)) (K B : ℕ)
    (hF : ∀ v ∈ T, (T.filter (fun w => s(v, w) ∈ F)).card ≤ B)
    (hsingle : ∀ G : Finset (Sym2 V), (∀ v ∈ T, (T.filter (fun w => s(v, w) ∈ G)).card ≤ B + K) →
      ∃ h : V → V, IsOkMatching ok T (R \ G) h) :
    ∃ fs : ℕ → V → V, PerRootFamily ok T (R \ F) K fs := by
  suffices H : ∀ m ≤ K, ∃ fs : ℕ → V → V, (∀ j < m, IsOkMatching ok T (R \ F) (fs j)) ∧
      ∀ j < m, ∀ j' < m, j ≠ j' → Disjoint (matchEdges T (fs j)) (matchEdges T (fs j')) by
    obtain ⟨fs, h1, h2⟩ := H K le_rfl
    exact ⟨fs, h1, h2⟩
  intro m
  induction m with
  | zero => intro _; exact ⟨fun _ => id, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨fs, hfs, hdisj⟩ := ih (Nat.le_of_succ_le hm)
    set G := F ∪ (range m).biUnion (fun j => matchEdges T (fs j)) with hG
    have hGdeg : ∀ v ∈ T, (T.filter (fun w => s(v, w) ∈ G)).card ≤ B + K := by
      intro v hv
      refine (card_filter_union_le T F _ v).trans ?_
      have h2 : (T.filter
          (fun w => s(v, w) ∈ (range m).biUnion (fun j => matchEdges T (fs j)))).card ≤ m := by
        refine (card_filter_pair_le T _ v).trans ?_
        have h1 : deg ((range m).biUnion (fun j => matchEdges T (fs j))) v ≤
            ∑ j ∈ range m, deg (matchEdges T (fs j)) v := by
          unfold deg
          rw [Finset.filter_biUnion]
          exact Finset.card_biUnion_le
        refine h1.trans ?_
        calc ∑ j ∈ range m, deg (matchEdges T (fs j)) v ≤ ∑ _j ∈ range m, 1 := by
              apply Finset.sum_le_sum
              intro j hj
              have := deg_matchEdges_le (hfs j (Finset.mem_range.mp hj)) v
              split_ifs at this; omega
          _ = m := by simp
      have := hF v hv
      have hmK : m < K := hm
      omega
    obtain ⟨h, hh⟩ := hsingle G hGdeg
    have hGsub : R \ G ⊆ R \ F := by
      intro e he
      simp only [Finset.mem_sdiff, hG, Finset.mem_union, not_or] at he ⊢
      exact ⟨he.1, he.2.1⟩
    let fs' : ℕ → V → V := fun j => if j = m then h else fs j
    have hfm : fs' m = h := by simp [fs']
    have hfj : ∀ j < m, fs' j = fs j := fun j hj => by simp [fs', Nat.ne_of_lt hj]
    have hnew : ∀ j < m, Disjoint (matchEdges T (fs j)) (matchEdges T h) := by
      intro j hj
      rw [Finset.disjoint_left]
      intro e he he'
      have hsub := matchEdges_subset hh he'
      simp only [Finset.mem_sdiff, hG, Finset.mem_union, not_or] at hsub
      exact hsub.2.2 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, he⟩)
    refine ⟨fs', fun j hj => ?_, fun j hj j' hj' hjj => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hfj j hj]; exact hfs j hj
      · rw [hfm]; exact isOkMatching_mono hh hGsub
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · rw [hfj j hj, hfj j' hj']; exact hdisj j hj j' hj' hjj
      · rw [hfj j hj, hfm]; exact hnew j hj
      · rw [hfj j' hj', hfm]; exact (hnew j' hj').symm
      · exact absurd rfl hjj

/-! ### Why a degree budget alone cannot suffice (new) -/

/-- **Overlap is a necessary invariant (proved, new).**  If `k` roots have the SAME target `T`
and pairwise edge-disjoint perfect matchings of `T`, then `k * |T| ≤ |T| * (|T| - 1)`: a target
supports at most `|T| - 1` edge-disjoint perfect matchings.  So no terminal pairing lemma can be
stated with degree (load) budgets alone: `k = |T|` roots sharing one target of size `4` have load
`4` at every vertex — negligible against any linear budget — yet admit no edge-disjoint pairings.
The overlap parameter `ω` of `spread_matching_of_family` is exactly the missing invariant. -/
theorem same_target_bound (ok : ℕ → V → V → Prop) (R : Finset (Sym2 V)) (T : Finset V)
    (k : ℕ) (f : ℕ → V → V) (hf : ∀ i < k, IsOkMatching (ok i) T R (f i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (matchEdges T (f i)) (matchEdges T (f j))) :
    k * T.card ≤ T.card * (T.card - 1) := by
  classical
  -- every matching has exactly `|T| / 2` edges, i.e. `2 |M_i| = |T|`
  have hcard : ∀ i < k, 2 * (matchEdges T (f i)).card = T.card := by
    intro i hi
    -- double count incidences: each vertex of `T` lies in exactly one edge, each edge has 2 ends
    have hinc : ∑ e ∈ matchEdges T (f i), (T.filter (fun v => v ∈ e)).card = T.card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨_, _, hv, _⟩; exact hv
        · intro hv
          exact ⟨s(v, f i v), Finset.mem_image_of_mem _ hv, hv, Sym2.mem_mk_left _ _⟩
      · intro e he e' he' hne
        rw [Function.onFun, Finset.disjoint_left]
        intro v hv hv'
        simp only [Finset.mem_filter] at hv hv'
        exact hne ((mem_matchEdges (hf i hi) he hv.2).2.trans
          (mem_matchEdges (hf i hi) he' hv'.2).2.symm)
    have htwo : ∀ e ∈ matchEdges T (f i), (T.filter (fun v => v ∈ e)).card = 2 := by
      intro e he
      simp only [matchEdges, Finset.mem_image] at he
      obtain ⟨a, ha, rfl⟩ := he
      obtain ⟨h1, h2, -⟩ := hf i hi a ha
      have : T.filter (fun v => v ∈ s(a, f i a)) = {a, f i a} := by
        ext v
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; exact h
        · rintro (rfl | rfl)
          · exact ⟨ha, Or.inl rfl⟩
          · exact ⟨h1, Or.inr rfl⟩
      rw [this, Finset.card_pair (Ne.symm h2)]
    rw [Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul] at hinc
    omega
  -- all matching edges are non-diagonal 2-subsets of `T`
  set U := (range k).biUnion (fun i => matchEdges T (f i)) with hU
  have hsub : U ⊆ T.sym2.filter (fun e => ¬ e.IsDiag) := by
    intro e he
    obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    simp only [matchEdges, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨h1, h2, -⟩ := hf i (Finset.mem_range.mp hi) a ha
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    exact ⟨⟨ha, h1⟩, fun h => h2 h.symm⟩
  have hUcard : U.card = ∑ i ∈ range k, (matchEdges T (f i)).card := by
    rw [hU, Finset.card_biUnion]
    intro i hi j hj hij
    exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have hoff : 2 * (T.sym2.filter (fun e => ¬ e.IsDiag)).card = T.card * (T.card - 1) := by
    have := Finset.card_sym2 T
    have hdiag : (T.sym2.filter (fun e => e.IsDiag)).card = T.card := by
      rw [show T.sym2.filter (fun e => e.IsDiag) = T.image (fun v => s(v, v)) from ?_]
      · exact Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      · ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
            Finset.mem_image, Sym2.eq_iff]
          constructor
          · rintro ⟨⟨ha, -⟩, rfl⟩; exact ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩
          · rintro ⟨c, hc, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> exact ⟨⟨hc, hc⟩, rfl⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := T.sym2) (fun e : Sym2 V => e.IsDiag)
    rw [this, hdiag, Nat.choose_two_right] at hsplit
    set n := T.card
    set off := (T.sym2.filter (fun e => ¬ e.IsDiag)).card
    have hev : 2 ∣ (n + 1) * (n + 1 - 1) := by
      rw [show n + 1 - 1 = n by omega]
      exact (Nat.even_mul_pred_self (n + 1)).two_dvd.trans (by rw [show n + 1 - 1 = n by omega])
    have h1 : 2 * (n + off) = (n + 1) * (n + 1 - 1) := by
      rw [hsplit]; exact Nat.mul_div_cancel' hev
    rw [show n + 1 - 1 = n by omega] at h1
    rcases n with _ | m
    · simp at h1 ⊢; omega
    · rw [show m + 1 - 1 = m by omega]
      nlinarith
  have hle := Finset.card_le_card hsub
  rw [hUcard] at hle
  have hsum : 2 * ∑ i ∈ range k, (matchEdges T (f i)).card = k * T.card := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i hi => hcard i (Finset.mem_range.mp hi))]
    simp
  omega

end NashWilliams18.SpreadGen
