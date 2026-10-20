/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.L3F0Hoeffding
import RequestProject.NW18.Case124.EGJTriangle
import RequestProject.NW18.Case124.ProtectedSeed

/-!
# Random thinning of REAL triangles from an exact regular fractional seed (branch 12.4, F1)

* `exists_weighted_subset_discrepancy`: a random subset of a finite index type, each index `i`
  kept independently with probability `p i`, meets every test set `Q k` (`k ∈ I`) in
  `∑_{i ∈ Q k} p i ± t k` simultaneously, provided `∑_k 2 exp(-2 t_k² / m_k) < 1`.
* `regular_thinning`: if `J` has an exact `C`-regular fractional triangle decomposition `w`,
  keeping each real triangle `T` of `J` with probability `w(T) n / (2C) ∈ (0, 1/2]` produces a
  family `𝒯 ⊆ K₃(J)` (a subfamily of the real triangles, no parallel copies) whose physical
  triangle hypergraph has every edge degree of `J` in `((1-ζ) n/(2C), (1+ζ) n/(2C))`.
* `regular_seed_nibble`: feeding that family to the existing `egj_nibble_leftover`, for every
  `η > 0` and every polynomial monitor budget `n^B` there is `N` (depending only on `C, η, B`)
  such that every `J` on `n ≥ N` vertices with a `C`-regular fractional decomposition has ONE
  edge-disjoint packing of real triangles of `J` leaving at most `η |S_k|` uncovered edges of
  every monitored edge set `S_k ⊆ E(J)` with `|S_k| ≥ 6 n^{1/4}`.
* `protected_nibble`: composition with `protected_seed_of_reserves`: the same packing on the
  reserved graph `J = G - (A ∪ R₀ ∪ R₁ ∪ W.sym2)` of a non-`β`-extremal `G` with
  `δ(G) ≥ (3/4-θ) n` under the budget `Δ(A)+Δ(R₀)+Δ(R₁)+|W| ≤ θ n`.  One scale only.
-/

namespace NashWilliams18.Case124

open Finset MeasureTheory ProbabilityTheory PartitionedTriangleAbsorption.L3F0
open scoped NNReal

/-! ### Weighted simultaneous discrepancy -/

theorem exists_weighted_subset_discrepancy {ι K : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ≥0) (hp : ∀ i, p i ≤ 1) (Q : K → Finset ι) (I : Finset K) (t m : K → ℝ)
    (ht : ∀ k ∈ I, 0 < t k) (hm : ∀ k ∈ I, 0 < m k) (hQm : ∀ k ∈ I, ((Q k).card : ℝ) ≤ m k)
    (hsmall : ∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k) < 1) :
    ∃ S : Finset ι, ∀ k ∈ I, |((Q k ∩ S).card : ℝ) - ∑ i ∈ Q k, (p i : ℝ)| < t k := by
  classical
  set μ := bernPi p hp
  set bad : K → Set (ι → Bool) := fun k =>
    {ω | t k ≤ |∑ y ∈ Q k, blockInd {y} ω - ∑ y ∈ Q k, ∏ i ∈ ({y} : Finset ι), (p i : ℝ)|}
    with hbad
  have hb : ∀ k ∈ I, μ.real (bad k) ≤ 2 * Real.exp (-2 * t k ^ 2 / m k) := by
    intro k hk
    refine tail_blocks p hp (fun y => {y}) (Q k) ?_ (ht k hk) (hm k hk) (hQm k hk)
    intro y _ y' _ hyy'
    exact disjoint_singleton.mpr hyy'
  have hsum : μ.real (⋃ k ∈ I, bad k) < 1 := by
    calc μ.real (⋃ k ∈ I, bad k) ≤ ∑ k ∈ I, μ.real (bad k) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k) := sum_le_sum hb
      _ < 1 := hsmall
  have hne : (⋃ k ∈ I, bad k) ≠ Set.univ := by
    intro h; rw [h, measureReal_def, measure_univ, ENNReal.toReal_one] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨univ.filter fun v => ω v = true, fun k hk => ?_⟩
  have hnot : ¬ t k ≤ |∑ y ∈ Q k, blockInd {y} ω -
      ∑ y ∈ Q k, ∏ i ∈ ({y} : Finset ι), (p i : ℝ)| := fun h =>
    hω (Set.mem_biUnion hk (by simpa only [hbad, Set.mem_setOf_eq] using h))
  have h1 : ∑ y ∈ Q k, blockInd {y} ω = ((Q k ∩ univ.filter fun v => ω v = true).card : ℝ) := by
    have : Q k ∩ univ.filter (fun v => ω v = true) = (Q k).filter fun v => ω v = true := by
      ext v; simp
    rw [this, card_filter, Nat.cast_sum]
    refine sum_congr rfl fun y _ => ?_
    unfold blockInd
    simp only [mem_singleton, forall_eq]
    split_ifs <;> simp
  have h2 : ∑ y ∈ Q k, ∏ i ∈ ({y} : Finset ι), (p i : ℝ) = ∑ i ∈ Q k, (p i : ℝ) := by
    refine sum_congr rfl fun y _ => ?_
    rw [prod_singleton]
  rw [h1, h2] at hnot
  exact lt_of_not_ge hnot

/-! ### Triangle hypergraph degrees of subfamilies of real triangles -/

section Degrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of members of `𝒯` containing the edge `e`. -/
def triDeg (𝒯 : Finset (Finset V)) (e : Sym2 V) : ℕ :=
  (𝒯.filter (fun t => e ∈ BKLOIface.triEdges t)).card

open EGJTriangle

omit [Fintype V] in
/-- The degree of an edge in the physical triangle hypergraph of a family of 3-sets is the number
of members containing it. -/
lemma degree_triHyp_eq (𝒯 : Finset (Finset V)) (h3 : ∀ t ∈ 𝒯, t.card = 3) (e : Sym2 V) :
    Pseudorandom.degree (triHyp 𝒯) e = triDeg 𝒯 e := by
  unfold Pseudorandom.degree triHyp triDeg
  rw [filter_image, card_image_of_injOn]
  intro a ha b hb hab
  exact triEdges_injOn (by simp [h3 a (mem_filter.mp ha).1])
    (by simp [h3 b (mem_filter.mp hb).1]) hab

omit [Fintype V] in
/-- An edge `s(u,v)` of `J` lies in the triangle `t` of `J` iff `u, v ∈ t`. -/
lemma mk_mem_triEdges_iff_of_adj (J : SimpleGraph V) {u v : V} (huv : J.Adj u v) (t : Finset V) :
    s(u, v) ∈ BKLOIface.triEdges t ↔ u ∈ t ∧ v ∈ t := by
  rw [EGJTriangle.mk_mem_triEdges]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, huv.ne⟩⟩

/-- A real triangle of `J` only contains edges of `J`. -/
lemma mem_edgeFinset_of_mem_triEdges (J : SimpleGraph V) [DecidableRel J.Adj] {t : Finset V}
    (ht : t ∈ J.cliqueFinset 3) {e : Sym2 V} (he : e ∈ BKLOIface.triEdges t) :
    e ∈ J.edgeFinset := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [EGJTriangle.mk_mem_triEdges] at he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ((SimpleGraph.mem_cliqueFinset_iff.mp ht).1 he.1 he.2.1 he.2.2)

/-- At most `n` real triangles contain a given edge. -/
lemma card_triangles_containing_le (J : SimpleGraph V) [DecidableRel J.Adj] (e : Sym2 V) :
    ((J.cliqueFinset 3).filter (fun t => e ∈ BKLOIface.triEdges t)).card ≤ Fintype.card V := by
  induction e using Sym2.ind with
  | _ a b =>
  have hsub : (J.cliqueFinset 3).filter (fun t => s(a, b) ∈ BKLOIface.triEdges t) ⊆
      univ.image (fun x => ({a, b, x} : Finset V)) := by
    intro t ht
    rw [mem_filter, EGJTriangle.mk_mem_triEdges] at ht
    obtain ⟨ht3, ha, hb, hab⟩ := ht
    have hcard : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht3).2
    have h2 : ({a, b} : Finset V).card = 2 := card_pair hab
    obtain ⟨x, hx⟩ : ∃ x, x ∈ t \ {a, b} := by
      apply Finset.Nonempty.exists_mem
      rw [← card_pos, card_sdiff_of_subset (by
        intro y hy; simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption)]
      omega
    rw [mem_sdiff] at hx
    refine mem_image.mpr ⟨x, mem_univ _, ?_⟩
    refine eq_of_subset_of_card_le ?_ ?_
    · intro y hy; simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hx.1
    · rw [hcard]
      have : x ∉ ({a, b} : Finset V) := hx.2
      rw [show ({a, b, x} : Finset V) = insert x {a, b} by ext; simp; tauto,
        card_insert_of_notMem this, h2]
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

end Degrees

/-! ### The thinning -/

/-- **Regular thinning of real triangles.**  From an exact `C`-regular fractional decomposition,
one subfamily `𝒯` of the real triangles of `J` has every edge degree of `J` within
`ζ n/(2C)` of `n/(2C)`, provided the union bound `n² · 2 exp(-ζ² n / (2C²)) < 1` holds. -/
theorem regular_thinning {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (C : ℝ) (hC : 1 ≤ C) (w : Finset V → ℝ)
    (hw : IsRegularFracDecomp J C w) (ζ : ℝ) (hζ : 0 < ζ) (hn : 0 < Fintype.card V)
    (hsmall : ((Fintype.card V : ℝ) ^ 2) *
      (2 * Real.exp (-(ζ ^ 2 * Fintype.card V / (2 * C ^ 2)))) < 1) :
    ∃ 𝒯 ⊆ J.cliqueFinset 3, ∀ e ∈ J.edgeFinset,
      |(triDeg 𝒯 e : ℝ) - Fintype.card V / (2 * C)| < ζ * (Fintype.card V / (2 * C)) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hnpos : (0 : ℝ) < n := by rw [hn_def]; exact_mod_cast hn
  have hCpos : (0 : ℝ) < C := by linarith
  set c : ℝ := n / (2 * C) with hc_def
  have hcpos : 0 < c := by positivity
  obtain ⟨hfrac, hreg⟩ := hw
  set K3 := J.cliqueFinset 3
  let p : Finset V → ℝ≥0 := fun t => if t ∈ K3 then Real.toNNReal (w t * c) else 0
  have hp : ∀ t, p t ≤ 1 := by
    intro t
    by_cases ht : t ∈ K3
    · simp only [p, if_pos ht]
      rw [Real.toNNReal_le_one]
      have h1 := (hreg t ht).2
      calc w t * c ≤ C / n * c := mul_le_mul_of_nonneg_right h1 hcpos.le
        _ = 1 / 2 := by rw [hc_def]; field_simp
        _ ≤ 1 := by norm_num
    · simp [p, if_neg ht]
  let Q : Sym2 V → Finset (Finset V) := fun e => K3.filter (fun t => e ∈ BKLOIface.triEdges t)
  obtain ⟨S, hS⟩ := exists_weighted_subset_discrepancy p hp Q J.edgeFinset
    (fun _ => ζ * c) (fun _ => n) (fun _ _ => by positivity) (fun _ _ => hnpos)
    (fun e _ => by
      show ((Q e).card : ℝ) ≤ n
      rw [hn_def]; exact_mod_cast card_triangles_containing_le J e) (by
      rw [sum_const, nsmul_eq_mul]
      have hE : (J.edgeFinset.card : ℝ) ≤ n ^ 2 := by
        rw [hn_def]
        exact_mod_cast SimpleGraph.card_edgeFinset_le_card_choose_two.trans
          (Nat.choose_le_pow _ _)
      have hexp : -2 * (ζ * c) ^ 2 / n = -(ζ ^ 2 * n / (2 * C ^ 2)) := by
        rw [hc_def]; field_simp
      rw [hexp]
      calc (J.edgeFinset.card : ℝ) * (2 * Real.exp (-(ζ ^ 2 * n / (2 * C ^ 2))))
          ≤ n ^ 2 * (2 * Real.exp (-(ζ ^ 2 * n / (2 * C ^ 2)))) :=
            mul_le_mul_of_nonneg_right hE (by positivity)
        _ < 1 := hsmall)
  refine ⟨K3.filter (fun t => t ∈ S), filter_subset _ _, fun e he => ?_⟩
  have hdeg : triDeg (K3.filter (fun t => t ∈ S)) e = (Q e ∩ S).card := by
    unfold triDeg
    congr 1
    ext t; simp only [Q, mem_filter, mem_inter]; tauto
  have hsum : ∑ t ∈ Q e, (p t : ℝ) = c := by
    induction e using Sym2.ind with
    | _ u v =>
    have hadj : J.Adj u v := by simpa using he
    have h1 : ∑ t ∈ Q s(u, v), (p t : ℝ) = ∑ t ∈ Q s(u, v), w t * c := by
      refine sum_congr rfl fun t ht => ?_
      have htK : t ∈ K3 := (mem_filter.mp ht).1
      simp only [p, if_pos htK]
      exact Real.coe_toNNReal _ (mul_nonneg (hfrac.1 t) hcpos.le)
    have h2 : Q s(u, v) = K3.filter (fun t => u ∈ t ∧ v ∈ t) := by
      ext t; simp only [Q, mem_filter, mk_mem_triEdges_iff_of_adj J hadj]
    rw [h1, ← sum_mul, h2, hfrac.2 u v hadj, one_mul]
  have := hS e he
  rw [hsum] at this
  rw [hdeg]
  exact this

/-! ### Asymptotic side conditions -/

section Asymptotics

open Filter

lemma ev_pow_le_exp_rpow (c a : ℝ) (hc : 0 < c) (ha : 0 < a) (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, x ^ K ≤ Real.exp ((c * x) ^ a) := by
  have hb : 0 < c ^ a / (K + 1) := by positivity
  have h1 := (isLittleO_log_rpow_atTop ha).bound hb
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ c ^ a / (K + 1) * x ^ a := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    exact (le_abs_self _).trans hx
  rw [← Real.exp_log (pow_pos hx0 K), Real.log_pow, Real.mul_rpow hc.le hx0.le]
  apply Real.exp_le_exp.mpr
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
  have hca : 0 ≤ c ^ a := Real.rpow_nonneg hc.le _
  calc (K : ℝ) * Real.log x ≤ K * (c ^ a / (K + 1) * x ^ a) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ = (K / (K + 1)) * (c ^ a * x ^ a) := by ring
    _ ≤ 1 * (c ^ a * x ^ a) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hca hxa)
        rw [div_le_one (by positivity)]; linarith
    _ = c ^ a * x ^ a := one_mul _

lemma ev_sq_exp_lt (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, x ^ 2 * (2 * Real.exp (-(κ * x))) < 1 := by
  have h1 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < κ / 4 by positivity)
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ), eventually_gt_atTop (4 * Real.log 2 / κ)]
    with x hx hx1 hx2
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ κ / 4 * x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx0] at hx
    exact (le_abs_self _).trans hx
  have hl2 : Real.log 2 < κ / 4 * x := by
    rw [div_lt_iff₀ hκ] at hx2; linarith
  have : x ^ 2 * (2 * Real.exp (-(κ * x))) = Real.exp (2 * Real.log x + Real.log 2 - κ * x) := by
    rw [Real.exp_sub, Real.exp_add, show (2:ℝ) * Real.log x = ((2:ℕ):ℝ) * Real.log x by norm_num,
      ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (by norm_num), Real.exp_neg]
    field_simp
  rw [this, Real.exp_lt_one_iff]
  nlinarith [mul_pos hκ hx0]

lemma ev_rpow_neg_lt (c ε η : ℝ) (hc : 0 < c) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, (c * x) ^ (-ε) < η := by
  have h := (tendsto_rpow_neg_atTop hε).comp (tendsto_id.const_mul_atTop hc)
  exact h.eventually (gt_mem_nhds hη)

end Asymptotics

lemma card_cliqueFinset_three_le {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] :
    (J.cliqueFinset 3).card ≤ Fintype.card V ^ 3 := by
  have hsub : J.cliqueFinset 3 ⊆ powersetCard 3 univ := by
    intro t ht
    rw [mem_powersetCard]
    exact ⟨subset_univ _, (SimpleGraph.mem_cliqueFinset_iff.mp ht).2⟩
  calc (J.cliqueFinset 3).card ≤ (powersetCard 3 (univ : Finset V)).card := card_le_card hsub
    _ = (Fintype.card V).choose 3 := by rw [card_powersetCard, card_univ]
    _ ≤ Fintype.card V ^ 3 := Nat.choose_le_pow _ _

/-! ### One-scale nibble from a regular seed -/

/-- **Nibble from an exact regular seed.**  For fixed `C ≥ 1`, `η > 0` and monitor budget `n^B`,
there is `N` such that every graph `J` on `n ≥ N` vertices with a `C`-regular fractional
triangle decomposition has ONE edge-disjoint packing `P` of real triangles of `J` such that every
monitored edge set `S_k ⊆ E(J)` with `|S_k| ≥ 6 n^{1/4}` has at most `η |S_k|` edges not covered
by `P`. -/
theorem regular_seed_nibble (C : ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) (B : ℕ) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
      (w : Finset V → ℝ), N ≤ Fintype.card V → IsRegularFracDecomp J C w →
      ∀ (ι : Type) [Fintype ι] (S : ι → Finset (Sym2 V)),
        (Fintype.card ι : ℝ) ≤ (Fintype.card V : ℝ) ^ B → (∀ k, S k ⊆ J.edgeFinset) →
        ∃ P ⊆ J.cliqueFinset 3,
          (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' →
            Disjoint (BKLOIface.triEdges t) (BKLOIface.triEdges t')) ∧
          ∀ k, 6 * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ ((S k).card : ℝ) →
            (((S k) \ P.biUnion BKLOIface.triEdges).card : ℝ) ≤ η * (S k).card := by
  classical
  set ζ : ℝ := min (η / 4) (1 / 4) with hζ_def
  have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζη : ζ ≤ η / 4 := min_le_left _ _
  have hζ4 : ζ ≤ 1 / 4 := min_le_right _ _
  have hCpos : (0 : ℝ) < C := by linarith
  set c₀ : ℝ := (1 + ζ) / (2 * C) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hc₀1 : c₀ ≤ 1 := by rw [hc₀, div_le_one (by positivity)]; linarith
  set a : ℝ := ((1 / 4 : ℝ) / 450) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set κ : ℝ := ζ ^ 2 / (2 * C ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨Δ₀, hEGJ⟩ := EGJTriangle.egj_nibble_leftover (1 / 4) (by norm_num) (by norm_num)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Δ₀ ≤ c₀ * x ∧ (c₀ * x) ^ (-((1 / 4 : ℝ) / 450)) < η / 2 ∧
      x ^ (max 3 B) ≤ Real.exp ((c₀ * x) ^ a) ∧ x ^ 2 * (2 * Real.exp (-(κ * x))) < 1 ∧
      1 ≤ x := by
    refine ((((Filter.tendsto_id.const_mul_atTop hc₀pos).eventually_ge_atTop Δ₀).and
      (ev_rpow_neg_lt c₀ ((1 / 4 : ℝ) / 450) (η / 2) hc₀pos (by norm_num) (by positivity))).and
      ((ev_pow_le_exp_rpow c₀ a hc₀pos ha0 (max 3 B)).and
      ((ev_sq_exp_lt κ hκ0).and (Filter.eventually_ge_atTop 1)))).mono ?_
    rintro x ⟨⟨h1, h2⟩, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨N, ?_⟩
  intro V _ _ J _ w hNV hw ι _ S hι hS
  obtain ⟨hΔ₀, hεη, hpoly, hunion, hx1⟩ := hN _ hNV
  set x : ℝ := (Fintype.card V : ℝ) with hx_def
  have hx0 : 0 < x := by linarith
  have hcardpos : 0 < Fintype.card V := Nat.cast_pos.mp hx0
  -- the thinning
  obtain ⟨𝒯, h𝒯K, h𝒯deg⟩ := regular_thinning J C hC w hw ζ hζ0 hcardpos (by
    have : ζ ^ 2 * x / (2 * C ^ 2) = κ * x := by rw [hκ]; ring
    rw [this]; exact hunion)
  have h3 : ∀ t ∈ 𝒯, t.card = 3 := fun t ht =>
    (SimpleGraph.mem_cliqueFinset_iff.mp (h𝒯K ht)).2
  set Δ : ℝ := c₀ * x with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔx : Δ ≤ x := by rw [hΔ]; nlinarith
  have hdegE : ∀ e ∈ J.edgeFinset, (1 - 2 * ζ) * Δ ≤ (triDeg 𝒯 e : ℝ) ∧ (triDeg 𝒯 e : ℝ) ≤ Δ := by
    intro e he
    have h := abs_lt.mp (h𝒯deg e he)
    have hc : 0 ≤ x / (2 * C) := by positivity
    have hΔ' : Δ = (1 + ζ) * (x / (2 * C)) := by rw [hΔ, hc₀]; ring
    constructor
    · rw [hΔ']; nlinarith [mul_nonneg (sq_nonneg ζ) hc]
    · rw [hΔ']; linarith
  have hdeg0 : ∀ e ∉ J.edgeFinset, triDeg 𝒯 e = 0 := by
    intro e he
    unfold triDeg
    rw [card_eq_zero, filter_eq_empty_iff]
    intro t ht hte
    exact he (mem_edgeFinset_of_mem_triEdges J (h𝒯K ht) hte)
  have hpow3 : x ^ 3 ≤ Real.exp (Δ ^ a) :=
    (pow_le_pow_right₀ hx1 (le_max_left 3 B)).trans hpoly
  have hpowB : x ^ B ≤ Real.exp (Δ ^ a) :=
    (pow_le_pow_right₀ hx1 (le_max_right 3 B)).trans hpoly
  obtain ⟨Pk, hPk, hdisj, hleft⟩ := hEGJ Δ hΔ₀ V 𝒯 (2 * ζ) (by positivity) (by linarith) h3
    (fun e => by
      rw [degree_triHyp_eq 𝒯 h3]
      by_cases he : e ∈ J.edgeFinset
      · exact (hdegE e he).2
      · rw [hdeg0 e he]; simpa using hΔpos.le)
    (by
      calc (𝒯.card : ℝ) ≤ ((J.cliqueFinset 3).card : ℝ) := by exact_mod_cast card_le_card h𝒯K
        _ ≤ x ^ 3 := by rw [hx_def]; exact_mod_cast card_cliqueFinset_three_le J
        _ ≤ _ := hpow3)
    ι S (hι.trans hpowB)
    (fun k e he => by
      rw [degree_triHyp_eq 𝒯 h3]
      exact (hdegE e (hS k he)).1)
  refine ⟨Pk, hPk.trans h𝒯K, hdisj, fun k hk => ?_⟩
  have hsz : 6 * Δ ^ (1 / 4 : ℝ) ≤ ((S k).card : ℝ) := by
    refine le_trans ?_ hk
    have := Real.rpow_le_rpow hΔpos.le hΔx (show (0:ℝ) ≤ 1 / 4 by norm_num)
    linarith
  refine (hleft k hsz).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

/-- **Protected one-scale nibble.**  For every sufficiently small `β > 0` there is `θ > 0`
such that for every `η > 0` and monitor budget `n^B` there is `N`, all chosen before the graph
and the reserves, with: if `n ≥ N`, `δ(G) ≥ (3/4-θ)n`, `G` is not `β`-extremal and
`Δ(A)+Δ(R₀)+Δ(R₁)+|W| ≤ θ n`, then the reserved graph `J = G - (A ∪ R₀ ∪ R₁ ∪ W.sym2)` has one
edge-disjoint packing of its real triangles leaving at most `η|S_k|` edges of every monitored
`S_k ⊆ E(J)` with `|S_k| ≥ 6 n^{1/4}` (at most `n^B` monitors). -/
theorem protected_nibble :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ →
      ∃ θ : ℝ, 0 < θ ∧ ∀ η : ℝ, 0 < η → ∀ B : ℕ, ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (A R₀ R₁ : Finset (Sym2 V)) (W : Finset V) (dA d₀ d₁ : ℕ),
        N ≤ Fintype.card V →
        (3 / 4 - θ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal β G →
        (∀ v, (A.filter (fun e => v ∈ e)).card ≤ dA) →
        (∀ v, (R₀.filter (fun e => v ∈ e)).card ≤ d₀) →
        (∀ v, (R₁.filter (fun e => v ∈ e)).card ≤ d₁) →
        ((dA + d₀ + d₁ + W.card : ℕ) : ℝ) ≤ θ * Fintype.card V →
        ∀ (ι : Type) [Fintype ι] (S : ι → Finset (Sym2 V)),
        (Fintype.card ι : ℝ) ≤ (Fintype.card V : ℝ) ^ B →
        (∀ k, S k ⊆ (del G (A ∪ R₀ ∪ R₁ ∪ W.sym2)).edgeFinset) →
        ∃ P ⊆ (del G (A ∪ R₀ ∪ R₁ ∪ W.sym2)).cliqueFinset 3,
          (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' →
            Disjoint (BKLOIface.triEdges t) (BKLOIface.triEdges t')) ∧
          ∀ k, 6 * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ ((S k).card : ℝ) →
            (((S k) \ P.biUnion BKLOIface.triEdges).card : ℝ) ≤ η * (S k).card := by
  obtain ⟨β₀, hβ₀, hseed⟩ := protected_seed_of_reserves
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
  obtain ⟨θ, hθ, C, hC, N₁, hs⟩ := hseed β hβ hββ₀
  refine ⟨θ, hθ, fun η hη B => ?_⟩
  obtain ⟨N₂, hnib⟩ := regular_seed_nibble C hC η hη B
  refine ⟨max N₁ N₂, ?_⟩
  intro V _ _ G _ A R₀ R₁ W dA d₀ d₁ hN hdeg hnx hA h₀ h₁ hb ι _ S hι hS
  obtain ⟨w, hw⟩ := hs V G A R₀ R₁ W dA d₀ d₁ (le_trans (le_max_left _ _) hN) hdeg hnx hA h₀ h₁ hb
  exact hnib V _ w (le_trans (le_max_right _ _) hN) hw ι S hι hS

end NashWilliams18.Case124
