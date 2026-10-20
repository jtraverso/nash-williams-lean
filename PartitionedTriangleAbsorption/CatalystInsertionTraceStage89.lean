/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystInsertionStepStage89

/-! # Catalyst insertion by actual exchanges

Each active vertex `y` is processed by the Stage87 exchange with roots
`(x₁, x₂, a₀, b₀, c₀, d₀) = (y, co y, a₀, b₀, cs y, ct y)`, selected by
`PairExchangeTraceStage87.exists_framed_exchange` (three physical moves); its
two carriers `z, z'` have label `p y` and avoid the full forbidden vertex set,
which contains every vertex of the current configuration. The Stage88 terminal
ledger of the three moves becomes the next history, so freshness is always
checked against the whole cumulative history. The token bookkeeping
`config_step` identifies the resulting configuration exactly.

Per step the forbidden vertex set grows by two and the history by at most 27
edges; with the step requirement `14 + |Z| + 4(d + |U|) < a`, the explicit
budget `|Z| + 4(d + |U|) + 124 · #(remaining) < a` is propagated.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}

omit [DecidableEq V] in
theorem link_of_sym2_eq {F : Finset (Multiset (Fin t))} {p : V → Fin t} {u v x w : V}
    (h : s(u, v) = s(x, w)) (hl : ∃ k, Link F (p x) (p w) k) :
    ∃ k, Link F (p u) (p v) k := by
  obtain ⟨k, hk⟩ := hl
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨k, hk⟩
  · exact ⟨k, (link_root_swap F _ _ k).mp hk⟩

variable [Fintype V]

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V}

/-- **One insertion step.** Process `y ∉ P` by one selected, framed exchange.
Returns the carriers `z, z'`, the next history (the exact terminal ledger of
the three moves), the next invariant, and the continuation property. -/
theorem insert_step (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a) (hB : DegBounded B d)
    (hd : 0 ≤ d) (fr : Frame p F G B S Z₀) {cz cz' : V → V} {P : Finset V}
    {U : Finset (Sym2 V)} {Z : Finset V} (inv : Inv p F G B S Z₀ cz cz' P U Z) {y : V}
    (hy : y ∈ S.A) (hyP : y ∉ P) (hb : 14 + (Z.card : ℝ) + 4 * (d + U.card) < a) :
    ∃ (z z' : V) (U' : Finset (Sym2 V)),
      Inv p F G B S Z₀ (Function.update cz y z) (Function.update cz' y z') (insert y P) U'
        (insert z (insert z' Z)) ∧ U'.card ≤ U.card + 27 ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U'
          (S.config (Function.update cz y z) (Function.update cz' y z') (insert y P)) W k →
        PhysicalMoves p F G.edgeFinset B U (S.config cz cz' P) W (3 + k) := by
  set a0 := S.a₀ cz cz' P y with ha0
  set b0 := S.b₀ cz cz' P y with hb0
  have hsplit := config_split (cz := cz) (cz' := cz') fr hy hyP
  have hsrc : S.srcEdges cz cz' P y ⊆ S.config cz cz' P := by
    rw [hsplit]; exact subset_union_right
  have hm1 : s(y, a0) ∈ S.config cz cz' P := hsrc (by simp [Data.srcEdges, ha0])
  have hm2 : s(y, b0) ∈ S.config cz cz' P := hsrc (by simp [Data.srcEdges, hb0])
  have hm3 : s(S.co y, S.cs y) ∈ S.config cz cz' P := hsrc (by simp [Data.srcEdges])
  have hm4 : s(S.co y, S.ct y) ∈ S.config cz cz' P := hsrc (by simp [Data.srcEdges])
  have nodiag : ∀ {u v : V}, s(u, v) ∈ S.config cz cz' P → u ≠ v := by
    intro u v huv
    have h := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (inv.real huv))
    simpa using h
  obtain ⟨n1, n2, n3⟩ := fr.cat_notA hy
  obtain ⟨d1, d2, d3⟩ := fr.distinct y hy
  obtain ⟨hnmA, hnpA⟩ := fr.nm_A hy
  have hc := inv.carriers
  have hco : S.co y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
  have hcs : S.cs y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
  have hct : S.ct y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
  have hsd : PhysicalHingeSupply.SixDistinct y (S.co y) a0 b0 (S.cs y) (S.ct y) :=
    ⟨fun h => n1 (h ▸ hy), nodiag hm1, nodiag hm2, fun h => n2 (h ▸ hy),
      fun h => n3 (h ▸ hy), Ne.symm (rep_not_cat fr hc hnmA _ hy hco),
      Ne.symm (rep_not_cat fr hc hnpA _ hy hco), d1, d2,
      rep_ne_of_ne fr hc hnmA hnpA (fr.nm_ne_np y hy) _ _,
      rep_not_cat fr hc hnmA _ hy hcs, rep_not_cat fr hc hnmA _ hy hct,
      rep_not_cat fr hc hnpA _ hy hcs, rep_not_cat fr hc hnpA _ hy hct, d3⟩
  set r := PhysicalHingeSupply.sixEmb hsd with hr
  have hsrc_eq : PairExchangeProducerStage87.sourceEdges r = S.srcEdges cz cz' P y := rfl
  have hroot : ∀ i, r i ∈ Z := by
    intro i
    fin_cases i
    · exact inv.supp _ hm1 _ (Sym2.mem_mk_left _ _)
    · exact inv.supp _ hm3 _ (Sym2.mem_mk_left _ _)
    · exact inv.supp _ hm1 _ (Sym2.mem_mk_right _ _)
    · exact inv.supp _ hm2 _ (Sym2.mem_mk_right _ _)
    · exact inv.supp _ hm3 _ (Sym2.mem_mk_right _ _)
    · exact inv.supp _ hm4 _ (Sym2.mem_mk_right _ _)
  have hdata : PairExchangeProducerStage87.ExchangeData p F G a d B U Z
      (S.config cz cz' P) r :=
    { threeStep := hF
      supply := hs
      d_nonneg := hd
      forbidden := hB
      budget := by linarith
      roots_mem := hroot
      label_eq := fr.label y hy
      source_real := hsrc_eq ▸ hsrc.trans inv.real
      active := ⟨inv.links _ _ hm1, inv.links _ _ hm2, inv.links _ _ hm3, inv.links _ _ hm4⟩
      source_sub := hsrc_eq ▸ hsrc
      config_history := inv.hist
      config_real := inv.real
      config_forbidden := inv.forb
      support := inv.supp }
  obtain ⟨f, hf, htr, hreal, hforb⟩ := PairExchangeTraceStage87.exists_framed_exchange hdata
  have hfin_eq : PairExchangeTraceStage87.finalEdges r f = S.newEdges cz cz' P y (f 6) (f 7) :=
    rfl
  have hcfg : (S.config cz cz' P \ PairExchangeProducerStage87.sourceEdges r) ∪
      PairExchangeTraceStage87.finalEdges r f =
      S.config (Function.update cz y (f 6)) (Function.update cz' y (f 7)) (insert y P) := by
    rw [hsrc_eq, hfin_eq, config_step fr hc hy hyP]
  rw [hcfg] at htr hreal hforb
  obtain ⟨L, hUL, hYL, hLc, -, hcont⟩ := MoveLedgerStage88.terminal_ledger htr inv.hist
  have hz : f 6 ∉ Z := hf.fresh_vertices 6 (by decide)
  have hz' : f 7 ∉ Z := hf.fresh_vertices 7 (by decide)
  have hzz : f 6 ≠ f 7 := f.injective.ne (by decide)
  have hlz : p (f 6) = p y := hf.carrier_labels.1
  have hlz' : p (f 7) = p y := hf.carrier_labels.2
  have hrest : S.rest cz cz' P y ⊆ S.config cz cz' P := by
    rw [hsplit]; exact subset_union_left
  have hnext := config_split_next (cz := cz) (cz' := cz') (P := P) fr hy (f 6) (f 7)
  have hZsub : Z ⊆ insert (f 6) (insert (f 7) Z) := fun v hv =>
    mem_insert_of_mem (mem_insert_of_mem hv)
  refine ⟨f 6, f 7, L, ?_, by omega, fun W k h => hcont W k h⟩
  refine ⟨insert_subset hy inv.sub, hYL, hreal, hforb, ?_, inv.base.trans hZsub, ?_, ?_, ?_, ?_⟩
  · intro e he v hv
    rw [hnext] at he
    rcases mem_union.mp he with he | he
    · exact hZsub (inv.supp e (hrest he) v hv)
    · simp only [Data.newEdges, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact mem_insert_self _ _
      · exact hZsub (hroot 2)
      · exact mem_insert_self _ _
      · exact hZsub (hroot 4)
      · exact mem_insert_of_mem (mem_insert_self _ _)
      · exact hZsub (hroot 3)
      · exact mem_insert_of_mem (mem_insert_self _ _)
      · exact hZsub (hroot 5)
  · intro u v huv
    rw [hnext] at huv
    rcases mem_union.mp huv with huv | huv
    · exact inv.links u v (hrest huv)
    · obtain ⟨k1, hk1⟩ := inv.links _ _ hm1
      obtain ⟨k2, hk2⟩ := inv.links _ _ hm2
      have hl := fr.link y hy
      simp only [Data.newEdges, mem_insert, mem_singleton] at huv
      rcases huv with h | h | h | h
      · exact link_of_sym2_eq h ⟨k1, by rw [hlz]; exact hk1⟩
      · exact link_of_sym2_eq h ⟨_, by rw [hlz]; exact hl⟩
      · exact link_of_sym2_eq h ⟨k2, by rw [hlz']; exact hk2⟩
      · exact link_of_sym2_eq h ⟨_, by rw [hlz']; exact (link_swap F _ _ _).mp hl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro y' hy'
      by_cases h : y' = y
      · subst h
        simp only [Function.update_self]
        exact ⟨fun h0 => hz (inv.base h0), fun h0 => hz' (inv.base h0)⟩
      · have hy'P := (mem_insert.mp hy').resolve_left h
        simp only [Function.update_of_ne h]
        exact hc.fresh y' hy'P
    · intro y' hy'
      by_cases h : y' = y
      · subst h
        simp only [Function.update_self]
        exact hzz
      · have hy'P := (mem_insert.mp hy').resolve_left h
        simp only [Function.update_of_ne h]
        exact hc.ne y' hy'P
    · intro y₁ hy₁ y₂ hy₂ hne
      by_cases h₁ : y₁ = y <;> by_cases h₂ : y₂ = y
      · exact absurd (h₁.trans h₂.symm) hne
      · subst h₁
        have hy₂P := (mem_insert.mp hy₂).resolve_left h₂
        obtain ⟨m1, m2⟩ := inv.carrier_mem y₂ hy₂P
        simp only [Function.update_self, Function.update_of_ne h₂]
        exact ⟨fun h => hz (h ▸ m1), fun h => hz (h ▸ m2), fun h => hz' (h ▸ m2)⟩
      · subst h₂
        have hy₁P := (mem_insert.mp hy₁).resolve_left h₁
        obtain ⟨m1, m2⟩ := inv.carrier_mem y₁ hy₁P
        simp only [Function.update_self, Function.update_of_ne h₁]
        exact ⟨fun h => hz (h ▸ m1), fun h => hz' (h ▸ m1), fun h => hz' (h ▸ m2)⟩
      · have hy₁P := (mem_insert.mp hy₁).resolve_left h₁
        have hy₂P := (mem_insert.mp hy₂).resolve_left h₂
        simp only [Function.update_of_ne h₁, Function.update_of_ne h₂]
        exact hc.inj y₁ hy₁P y₂ hy₂P hne
  · intro y' hy'
    by_cases h : y' = y
    · subst h
      simp
    · have hy'P := (mem_insert.mp hy').resolve_left h
      simp only [Function.update_of_ne h]
      exact ⟨hZsub (inv.carrier_mem y' hy'P).1, hZsub (inv.carrier_mem y' hy'P).2⟩
  · intro y' hy'
    by_cases h : y' = y
    · subst h
      simp only [Function.update_self]
      exact ⟨hlz, hlz'⟩
    · have hy'P := (mem_insert.mp hy').resolve_left h
      simp only [Function.update_of_ne h]
      exact inv.carrier_label y' hy'P

/-- **The insertion induction.** Process every vertex of `R` (disjoint from
the processed set `P`). The final state processes `R ∪ P`; the history grows
by at most `27` edges and the forbidden vertex set by `2` per vertex, and the
trace of `3 |R|` moves can be continued from the final history. -/
theorem insert_all (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a) (hB : DegBounded B d)
    (hd : 0 ≤ d) (fr : Frame p F G B S Z₀) :
    ∀ (R : Finset V) (cz cz' : V → V) (P : Finset V) (U : Finset (Sym2 V)) (Z : Finset V),
      Inv p F G B S Z₀ cz cz' P U Z → R ⊆ S.A → Disjoint R P →
      (Z.card : ℝ) + 4 * (d + U.card) + 124 * R.card < a →
      ∃ (cz₂ cz₂' : V → V) (U₂ : Finset (Sym2 V)) (Z₂ : Finset V),
        Inv p F G B S Z₀ cz₂ cz₂' (R ∪ P) U₂ Z₂ ∧
        U₂.card ≤ U.card + 27 * R.card ∧ Z₂.card ≤ Z.card + 2 * R.card ∧
        ∀ W k, PhysicalMoves p F G.edgeFinset B U₂ (S.config cz₂ cz₂' (R ∪ P)) W k →
          PhysicalMoves p F G.edgeFinset B U (S.config cz cz' P) W (3 * R.card + k) := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro cz cz' P U Z inv _ _ _
    refine ⟨cz, cz', U, Z, by simpa using inv, by simp, by simp, ?_⟩
    intro W k h
    simpa using h
  | @insert y R hyR ih =>
    intro cz cz' P U Z inv hRA hRP hb
    have hy : y ∈ S.A := hRA (mem_insert_self y R)
    have hyP : y ∉ P := disjoint_left.mp hRP (mem_insert_self y R)
    have hcard : ((insert y R).card : ℝ) = R.card + 1 := by
      rw [card_insert_of_notMem hyR]; push_cast; ring
    have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
    obtain ⟨z, z', U', inv', hU', hcont'⟩ := insert_step a d hF hs hB hd fr inv hy hyP
      (by rw [hcard] at hb; linarith)
    have hZ' : ((insert z (insert z' Z)).card : ℝ) ≤ Z.card + 2 := by
      have h1 := card_insert_le z (insert z' Z)
      have h2 := card_insert_le z' Z
      exact_mod_cast (show (insert z (insert z' Z)).card ≤ Z.card + 2 by omega)
    have hU'r : (U'.card : ℝ) ≤ U.card + 27 := by exact_mod_cast hU'
    obtain ⟨cz₂, cz₂', U₂, Z₂, inv₂, hU₂, hZ₂, hcont₂⟩ :=
      ih (Function.update cz y z) (Function.update cz' y z') (insert y P) U'
        (insert z (insert z' Z)) inv' ((subset_insert y R).trans hRA)
        (by
          rw [disjoint_insert_right]
          exact ⟨hyR, hRP.mono_left (subset_insert y R)⟩)
        (by rw [hcard] at hb; linarith)
    have hRP' : R ∪ insert y P = insert y R ∪ P := by
      ext v; simp only [mem_union, mem_insert]; tauto
    rw [hRP'] at inv₂ hcont₂
    refine ⟨cz₂, cz₂', U₂, Z₂, inv₂, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem hyR]; omega
    · have h1 := card_insert_le z (insert z' Z)
      have h2 := card_insert_le z' Z
      rw [card_insert_of_notMem hyR]; omega
    · intro W k h
      have h' := hcont' W _ (hcont₂ W k h)
      have he : 3 + (3 * R.card + k) = 3 * (insert y R).card + k := by
        rw [card_insert_of_notMem hyR]; ring
      rwa [he] at h'

/-- The initial invariant: nothing processed, configuration `Y ∪ D`. -/
theorem initial_inv (fr : Frame p F G B S Z₀) (cz cz' : V → V) {U : Finset (Sym2 V)}
    (hU : S.Y ∪ S.cats ⊆ U) : Inv p F G B S Z₀ cz cz' ∅ U Z₀ := by
  have hcat : ∀ e ∈ S.cats, ∃ y ∈ S.A, e ∈ catEdges (S.co y) (S.cs y) (S.ct y) := by
    intro e he
    exact mem_biUnion.mp he
  refine ⟨empty_subset _, ?_, ?_, ?_, ?_, Subset.refl _, ?_, ⟨by simp, by simp, by simp⟩,
    by simp, by simp⟩ <;> rw [S.config_empty cz cz']
  · exact hU
  · intro e he
    rcases mem_union.mp he with he | he
    · exact fr.Y_real he
    · obtain ⟨y, hy, he⟩ := hcat e he
      exact fr.cat_real y hy he
  · rw [disjoint_union_left]
    refine ⟨fr.Y_forb, ?_⟩
    rw [disjoint_left]
    intro e he
    obtain ⟨y, hy, he⟩ := hcat e he
    exact disjoint_left.mp (fr.cat_forb y hy) he
  · intro e he v hv
    rcases mem_union.mp he with he | he
    · exact fr.ZA (fr.supp e he v hv)
    · obtain ⟨y, hy, he⟩ := hcat e he
      exact fr.Zcat y hy (mem_catVerts_of_mem he hv)
  · intro u v huv
    rcases mem_union.mp huv with huv | huv
    · exact fr.Y_link u v huv
    · obtain ⟨y, hy, he⟩ := hcat _ huv
      have hl : Link F (p (S.co y)) (p (S.cs y)) (p (S.ct y)) := by
        rw [fr.label y hy]; exact fr.link y hy
      obtain ⟨-, -, h1, -, h2, -⟩ := PairExchangeProducerStage87.link_exists_all hl
      simp only [catEdges, mem_insert, mem_singleton] at he
      rcases he with h | h | h
      · exact link_of_sym2_eq h ⟨_, hl⟩
      · exact link_of_sym2_eq h h1
      · exact link_of_sym2_eq h h2

/-- **Token-tracked catalyst insertion (all active vertices).** Starting from
the configuration `Y ∪ D` with history `U₀ ⊇ Y ∪ D` and forbidden vertex set
`Z₀` (containing all active and all catalyst vertices), every active vertex is
processed by one exchange. The result is an actual physical trace of exactly
`3 |A|` moves from `Y ∪ D` to the explicitly token-tracked configuration
`S.config cz cz' S.A`, the final invariant (carriers fresh, distinct, with label
`p y`), and the continuation property from the final history. Budget:
`|Z₀| + 4(d + |U₀|) + 124 |A| < a`. -/
theorem insert_catalysts (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a) (hB : DegBounded B d)
    (hd : 0 ≤ d) (fr : Frame p F G B S Z₀) (U₀ : Finset (Sym2 V)) (hU₀ : S.Y ∪ S.cats ⊆ U₀)
    (hb : (Z₀.card : ℝ) + 4 * (d + U₀.card) + 124 * S.A.card < a) :
    ∃ (cz cz' : V → V) (U₂ : Finset (Sym2 V)) (Z₂ : Finset V),
      Inv p F G B S Z₀ cz cz' S.A U₂ Z₂ ∧
      U₂.card ≤ U₀.card + 27 * S.A.card ∧ Z₂.card ≤ Z₀.card + 2 * S.A.card ∧
      PhysicalMoves p F G.edgeFinset B U₀ (S.Y ∪ S.cats) (S.config cz cz' S.A) (3 * S.A.card) ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U₂ (S.config cz cz' S.A) W k →
        PhysicalMoves p F G.edgeFinset B U₀ (S.Y ∪ S.cats) W (3 * S.A.card + k) := by
  obtain ⟨cz, cz', U₂, Z₂, inv, hU, hZ, hcont⟩ :=
    insert_all a d hF hs hB hd fr S.A id id ∅ U₀ Z₀ (initial_inv fr id id hU₀)
      (Subset.refl _) (disjoint_empty_right _) hb
  rw [union_empty] at inv hcont
  rw [S.config_empty id id] at hcont
  exact ⟨cz, cz', U₂, Z₂, inv, hU, hZ, by simpa using hcont _ 0 (.stop _ _), hcont⟩

end

end PartitionedTriangleAbsorption.CatalystInsertionStage89
