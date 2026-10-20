/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassReserveStage65.Count
public import PartitionedTriangleAbsorption.ClassReserveStage65.Threshold

/-! # One sparse class-aware hinge reserve, selected before all roots and residues

Main result: `exists_class_aware_hinge_reserve`. For fixed `γ > 0` and `0 < ρ ≤ 1` there is
`N`, chosen before the vertex type, the four structural classes, the host and the roots, such
that every complete four-class host on `n ≥ N` vertices whose structural fibres have size at
least `γ n` contains **one** edge reserve `X ⊆ E(G)` with maximum degree at most `2 ρ n` such
that, for every labelling `p` constant on the fibres, every triangle family `F` and every two
original `F`-copies `S, S'` of `G` sharing exactly one edge, `X` contains at least
`γ² ρ⁷ n² / 32` distinct six-vertex `F`-hinges for `S, S'` (counted as edge sets).

Proof (one measure, union bound):

1. Sample every coordinate of `Sym2 V` independently with probability `ρ`; the reserve is the
   set of sampled graph edges.
2. Bad events, all for the same outcome `ω`:
   * `n` degree upper tails (`PhysicalStarTail.sampled_star_degree_tail`);
   * for each ordered tuple `(a, b, w, z)` whose roots `{b, w, z}` avoid the class of `a`: the
     number of `x ∈ fibre(a) \ {a}` with `bx, wx, zx` sampled is at most `γ ρ³ n / 4`
     (`marker_lower_tail`; the three-edge blocks are disjoint);
   * for each pair of disjoint vertex sets `A, B` both larger than `γ ρ³ n / 4`: at most
     `ρ |A| |B| / 2` cross pairs are sampled (`cross_lower_tail`). This family is indexed by
     all `(2ⁿ)²` pairs of sets, which handles the random marked sets without conditioning.
3. `failureBudget γ ρ n < 1` for `n ≥ N` (`exists_uniform_threshold`), so one outcome avoids
   every bad event (`PhysicalReserveTails.exists_simultaneous_outcome`).
4. For roots `u v w`, `u v z`, the two marked sets have more than `γ ρ³ n / 4` elements, so more
   than `ρ (γ ρ³ n / 4)² / 2 = γ² ρ⁷ n² / 32` sampled connectors join them; each gives a
   distinct physical hinge inside the reserve (`hinge_count_of_marked`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks ClassAwareHingesStage64
  PhysicalHingeSupply SignedHinge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Index set of the bad events. -/
abbrev BadIndex (V : Type*) := V ⊕ (V × V × V × V) ⊕ (Finset V × Finset V)

/-- The marker query condition for `(a, b, w, z)`. -/
def MarkerOK (cls : V → Fin 4) (γ : ℝ) (q : V × V × V × V) : Prop :=
  Disjoint (xCand cls q.1) {q.2.1, q.2.2.1, q.2.2.2} ∧
    γ * Fintype.card V / 2 ≤ ((xCand cls q.1).card : ℝ)

/-- The cross query condition for `(A, B)`. -/
def CrossOK (γ ρ : ℝ) (q : Finset V × Finset V) : Prop :=
  Disjoint q.1 q.2 ∧ markBound γ ρ (Fintype.card V) < (q.1.card : ℝ) ∧
    markBound γ ρ (Fintype.card V) < (q.2.card : ℝ)

/-- All bad events, on the single sampling space. -/
def badEvent (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4) (γ ρ : ℝ) :
    BadIndex V → Set (Sym2 V → Bool)
  | Sum.inl v => {ω | 2 * ρ * Fintype.card V ≤
      (((sampledEdges G ω).filter (fun e => v ∈ e)).card : ℝ)}
  | Sum.inr (Sum.inl q) => {ω | MarkerOK cls γ q ∧
      ((marked (xCand cls q.1) {q.2.1, q.2.2.1, q.2.2.2} ω).card : ℝ) ≤
        markBound γ ρ (Fintype.card V)}
  | Sum.inr (Sum.inr q) => {ω | CrossOK γ ρ q ∧
      ((crossSampled q.1 q.2 ω).card : ℝ) ≤ ρ * (q.1.card * q.2.card) / 2}

/-- Their probability bounds. -/
noncomputable def badBound (γ ρ : ℝ) (n : ℕ) : BadIndex V → ℝ
  | Sum.inl _ => Real.exp (-(2 * ρ ^ 2 * n))
  | Sum.inr (Sum.inl _) => Real.exp (-(ρ ^ 3) ^ 2 * (γ * n / 2) / 2)
  | Sum.inr (Sum.inr _) => Real.exp (-ρ ^ 2 * (markBound γ ρ n * markBound γ ρ n) / 2)

omit [DecidableEq V] in
theorem sum_badBound (γ ρ : ℝ) :
    ∑ i, badBound (V := V) γ ρ (Fintype.card V) i = failureBudget γ ρ (Fintype.card V) := by
  simp only [Fintype.sum_sum_type, badBound, sum_const, card_univ, nsmul_eq_mul,
    Fintype.card_prod, Fintype.card_finset, failureBudget]
  push_cast
  ring

theorem markBound_pos {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) {n : ℕ} (hn : 0 < n) :
    0 < markBound γ ρ n := by
  unfold markBound
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem badEvent_tail (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4)
    {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 0 < Fintype.card V)
    (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ) (i : BadIndex V) :
    μ.real (badEvent G cls γ ρ i) ≤ badBound γ ρ (Fintype.card V) i := by
  classical
  rcases i with v | q | q
  · exact PhysicalStarTail.sampled_star_degree_tail μ hind ρ hρ hmarg G v
  · by_cases hc : MarkerOK cls γ q
    · obtain ⟨hdis, hcard⟩ := hc
      set C := xCand cls q.1
      set R : Finset V := {q.2.1, q.2.2.1, q.2.2.2}
      have hγn : 0 < γ * Fintype.card V / 2 := by
        have : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
        positivity
      have hCpos : (0 : ℝ) < C.card := hγn.trans_le hcard
      have hC : C.Nonempty := card_pos.mp (by exact_mod_cast hCpos)
      have hR : R.card ≤ 3 := card_le_three
      have hpow : ρ ^ 3 ≤ ρ ^ R.card := pow_le_pow_of_le_one hρ.le hρ1 hR
      have h3 : 0 ≤ ρ ^ 3 := by positivity
      have htail := marker_lower_tail μ hind ρ hρ hmarg C R hdis hC
      refine le_trans (measureReal_mono ?_) (htail.trans (Real.exp_le_exp.mpr ?_))
      · intro ω hω
        simp only [badEvent, Set.mem_ofPred_eq] at hω ⊢
        refine hω.2.trans ?_
        unfold markBound
        have := mul_le_mul hpow hcard hγn.le (h3.trans hpow)
        linarith
      · have hsq : (ρ ^ 3) ^ 2 ≤ (ρ ^ R.card) ^ 2 := pow_le_pow_left₀ h3 hpow 2
        have := mul_le_mul hsq hcard hγn.le (sq_nonneg _)
        linarith
    · have hempty : badEvent G cls γ ρ (Sum.inr (Sum.inl q)) = ∅ := by
        ext ω
        simp [badEvent, hc]
      rw [hempty, measureReal_empty]
      exact (Real.exp_pos _).le
  · by_cases hc : CrossOK γ ρ q
    · obtain ⟨hdis, hA, hB⟩ := hc
      have hm := markBound_pos hγ hρ hn (γ := γ)
      have hA0 : q.1.Nonempty := card_pos.mp (by exact_mod_cast hm.trans hA)
      have hB0 : q.2.Nonempty := card_pos.mp (by exact_mod_cast hm.trans hB)
      have htail := cross_lower_tail μ hind ρ hρ hmarg q.1 q.2 hdis hA0 hB0
      refine le_trans (measureReal_mono ?_) (htail.trans (Real.exp_le_exp.mpr ?_))
      · intro ω hω
        simp only [badEvent, Set.mem_ofPred_eq] at hω ⊢
        exact hω.2
      · have := mul_le_mul hA.le hB.le hm.le (hm.trans hA).le
        have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
        nlinarith
    · have hempty : badEvent G cls γ ρ (Sum.inr (Sum.inr q)) = ∅ := by
        ext ω
        simp [badEvent, hc]
      rw [hempty, measureReal_empty]
      exact (Real.exp_pos _).le

/-- There is one sampled outcome avoiding every bad event. -/
theorem exists_good_outcome (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4)
    {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 0 < Fintype.card V)
    (hbudget : failureBudget γ ρ (Fintype.card V) < 1) :
    ∃ ω : Sym2 V → Bool, ∀ i, ω ∉ badEvent G cls γ ρ i := by
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Sym2 V) ρ hρ.le hρ1
  have := hμ
  exact PhysicalReserveTails.exists_simultaneous_outcome μ (badEvent G cls γ ρ)
    (badBound γ ρ (Fintype.card V)) (badEvent_tail G cls hγ hρ hρ1 hn μ hind hmarg)
    (by rw [sum_badBound]; exact hbudget)

/-- **Many sampled connectors between the two marked sets** in a good outcome, for every
rooted pair `u v w`, `u v z` of the original class graph. -/
theorem cross_count_of_good (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {γ ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v, γ * Fintype.card V ≤ ((fibre cls v).card : ℝ))
    (h2 : 2 ≤ γ * Fintype.card V) (ω : Sym2 V → Bool)
    (hω : ∀ i, ω ∉ badEvent G cls γ ρ i) {u v w z : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (huz : G.Adj u z) (hvw : G.Adj v w) (hvz : G.Adj v z) :
    γ ^ 2 * ρ ^ 7 * (Fintype.card V : ℝ) ^ 2 / 32 ≤
      ((crossSampled (marked (xCand cls u) {v, w, z} ω)
        (marked (xCand cls v) {u, w, z} ω) ω).card : ℝ) := by
  set n := Fintype.card V
  set Mx := marked (xCand cls u) {v, w, z} ω
  set My := marked (xCand cls v) {u, w, z} ω
  have cuv := (hG _ _).mp huv
  have hcand : ∀ a, γ * n / 2 ≤ ((xCand cls a).card : ℝ) := by
    intro a
    have := xCand_card_ge a (hsize a)
    linarith
  have hMx : markBound γ ρ n < (Mx.card : ℝ) := by
    have h := hω (Sum.inr (Sum.inl (u, v, w, z)))
    simp only [badEvent, Set.mem_ofPred_eq, not_and, not_le] at h
    exact h ⟨xCand_disjoint_roots (Ne.symm cuv) (Ne.symm ((hG _ _).mp huw))
      (Ne.symm ((hG _ _).mp huz)), hcand u⟩
  have hMy : markBound γ ρ n < (My.card : ℝ) := by
    have h := hω (Sum.inr (Sum.inl (v, u, w, z)))
    simp only [badEvent, Set.mem_ofPred_eq, not_and, not_le] at h
    exact h ⟨xCand_disjoint_roots cuv (Ne.symm ((hG _ _).mp hvw))
      (Ne.symm ((hG _ _).mp hvz)), hcand v⟩
  have hdis : Disjoint Mx My :=
    (xCand_disjoint_cross cuv).mono (filter_subset _ _) (filter_subset _ _)
  have hcross : ρ * (Mx.card * My.card) / 2 < ((crossSampled Mx My ω).card : ℝ) := by
    have h := hω (Sum.inr (Sum.inr (Mx, My)))
    simp only [badEvent, Set.mem_ofPred_eq, not_and, not_le] at h
    exact h ⟨hdis, hMx, hMy⟩
  have hm : 0 ≤ markBound γ ρ n := by unfold markBound; positivity
  have hprod := mul_le_mul hMx.le hMy.le hm (hm.trans hMx.le)
  have hval : γ ^ 2 * ρ ^ 7 * (n : ℝ) ^ 2 / 32 =
      ρ * (markBound γ ρ n * markBound γ ρ n) / 2 := by
    unfold markBound; ring
  rw [hval]
  nlinarith

open Classical in
/-- **Physical supply in a good reserve.** -/
theorem hinge_supply_of_good (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {γ ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v, γ * Fintype.card V ≤ ((fibre cls v).card : ℝ))
    (h2 : 2 ≤ γ * Fintype.card V) (ω : Sym2 V → Bool)
    (hω : ∀ i, ω ∉ badEvent G cls γ ρ i)
    {t : ℕ} (p : V → Fin t) (hp : ∀ a b, cls a = cls b → p a = p b)
    (F : Finset (Multiset (Fin t))) (S S' : Finset V)
    (hS : IsCopy p F G S) (hS' : IsCopy p F G S') (h1 : (triEdges S ∩ triEdges S').card = 1) :
    γ ^ 2 * ρ ^ 7 * (Fintype.card V : ℝ) ^ 2 / 32 ≤
      (((sampledEdges G ω).powerset.filter
        (fun H => IsHinge p F S S' H ∧ (vertSet H).card = 6)).card : ℝ) := by
  obtain ⟨u, v, w, z, -, -, -, -, -, hwz, rfl, rfl⟩ :=
    roots_of_shared_edge hS.1.card_eq hS'.1.card_eq h1
  obtain ⟨huv, huw, hvw⟩ := SimpleGraph.is3Clique_triple_iff.mp hS.1
  obtain ⟨-, huz, hvz⟩ := SimpleGraph.is3Clique_triple_iff.mp hS'.1
  have hcount := hinge_count_of_marked (p := p) (F := F) cls hG hp huv huw huz hvw hvz hwz
    hS.2 hS'.2 ω
  refine (cross_count_of_good G cls hG hρ hsize h2 ω hω huv huw huz hvw hvz).trans ?_
  exact_mod_cast hcount

/-- **Reserve with original-root physical hinge supply, for one host.** The scalar
conditions `2 ≤ γ n` and `failureBudget γ ρ n < 1` are discharged uniformly by
`exists_uniform_threshold`. The reserve depends only on `G`, `cls`, `γ`, `ρ`; the labelling,
the triangle family and the roots are quantified afterwards. -/
theorem exists_reserve_of_budget (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hsize : ∀ v, γ * Fintype.card V ≤ ((fibre cls v).card : ℝ))
    (h2 : 2 ≤ γ * Fintype.card V) (hbudget : failureBudget γ ρ (Fintype.card V) < 1) :
    ∃ X : Finset (Sym2 V), X ⊆ G.edgeFinset ∧ DegBounded X (2 * ρ * Fintype.card V) ∧
      ∀ {t : ℕ} (p : V → Fin t), (∀ a b, cls a = cls b → p a = p b) →
        ∀ (F : Finset (Multiset (Fin t))) (S S' : Finset V),
          IsCopy p F G S → IsCopy p F G S' → (triEdges S ∩ triEdges S').card = 1 →
          open Classical in
          γ ^ 2 * ρ ^ 7 * (Fintype.card V : ℝ) ^ 2 / 32 ≤
            ((X.powerset.filter
              (fun H => IsHinge p F S S' H ∧ (vertSet H).card = 6)).card : ℝ) := by
  have hn : 0 < Fintype.card V := by
    by_contra h
    have : Fintype.card V = 0 := by omega
    rw [this] at h2
    norm_num at h2
  obtain ⟨ω, hω⟩ := exists_good_outcome G cls hγ hρ hρ1 hn hbudget
  refine ⟨sampledEdges G ω, sampledEdges_subset G ω, ?_, ?_⟩
  · intro v
    have h := hω (Sum.inl v)
    simp only [badEvent, Set.mem_ofPred_eq, not_le] at h
    exact h.le
  · intro t p hp F S S' hS hS' h1
    exact hinge_supply_of_good G cls hG hρ hsize h2 ω hω p hp F S S' hS hS' h1

universe u

/-- **One sparse class-aware hinge reserve, selected before all roots and residues.**
For fixed `γ > 0` and `0 < ρ ≤ 1`, a single `N` (depending only on `γ, ρ`) works for every
finite vertex type, every structural four-class map, every host and every root pair. -/
theorem exists_class_aware_hinge_reserve (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (cls : W → Fin 4)
      (G : SimpleGraph W) [DecidableRel G.Adj], N ≤ Fintype.card W →
      (∀ v, γ * Fintype.card W ≤ ((fibre cls v).card : ℝ)) →
      (∀ a b, G.Adj a b ↔ cls a ≠ cls b) →
      ∃ X : Finset (Sym2 W), X ⊆ G.edgeFinset ∧ DegBounded X (2 * ρ * Fintype.card W) ∧
        ∀ {t : ℕ} (p : W → Fin t), (∀ a b, cls a = cls b → p a = p b) →
          ∀ (F : Finset (Multiset (Fin t))) (S S' : Finset W),
            IsCopy p F G S → IsCopy p F G S' → (triEdges S ∩ triEdges S').card = 1 →
            open Classical in
            γ ^ 2 * ρ ^ 7 * (Fintype.card W : ℝ) ^ 2 / 32 ≤
              ((X.powerset.filter
                (fun H => IsHinge p F S S' H ∧ (vertSet H).card = 6)).card : ℝ) := by
  obtain ⟨N, hN⟩ := exists_uniform_threshold γ ρ hγ hρ
  refine ⟨N, ?_⟩
  intro W _ _ cls G _ hn hsize hG
  obtain ⟨h2, hb⟩ := hN (Fintype.card W) hn
  exact exists_reserve_of_budget G cls hG hγ hρ hρ1 hsize h2 hb

/-- The statement with the parameter ranges `0 < γ ≤ 1/4`, `0 < ρ ≤ 1/2` exactly as posed.
The upper bound on `γ` is not needed by the proof, and `ρ ≤ 1/2` is only used through
`ρ ≤ 1`; both are kept here only to match the requested form. -/
theorem exists_class_aware_hinge_reserve_stated (γ ρ : ℝ) (hγ : 0 < γ) (_hγ4 : γ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (cls : W → Fin 4)
      (G : SimpleGraph W) [DecidableRel G.Adj], N ≤ Fintype.card W →
      (∀ v, γ * Fintype.card W ≤ ((fibre cls v).card : ℝ)) →
      (∀ a b, G.Adj a b ↔ cls a ≠ cls b) →
      ∃ X : Finset (Sym2 W), X ⊆ G.edgeFinset ∧ DegBounded X (2 * ρ * Fintype.card W) ∧
        ∀ {t : ℕ} (p : W → Fin t), (∀ a b, cls a = cls b → p a = p b) →
          ∀ (F : Finset (Multiset (Fin t))) (S S' : Finset W),
            IsCopy p F G S → IsCopy p F G S' → (triEdges S ∩ triEdges S').card = 1 →
            open Classical in
            γ ^ 2 * ρ ^ 7 * (Fintype.card W : ℝ) ^ 2 / 32 ≤
              ((X.powerset.filter
                (fun H => IsHinge p F S S' H ∧ (vertSet H).card = 6)).card : ℝ) :=
  exists_class_aware_hinge_reserve γ ρ hγ hρ (by linarith)

end PartitionedTriangleAbsorption.ClassReserveStage65
