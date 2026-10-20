/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.MoveLedgerStage88
public import PartitionedTriangleAbsorption.PairExchangeTraceStage87

/-! # Token-tracked physical exchanges in an arbitrary configuration

A *physical token state* is a finite token set `toks` with current positions
`pos`, injective on the tokens, whose image (the current configuration) is
real, avoids `B`, lies in the cumulative ledger `U`, is supported inside the
active vertex set `Z`, and whose edges have active label types.

`token_exchange` applies one Stage87 exchange
(`PairExchangeTraceStage87.exists_framed_exchange`) to four tokens sitting at
the four source edges `r₀r₂, r₀r₃, r₁r₄, r₁r₅`. Exactly these four tokens move,
to `z r₂, z' r₃, z r₄, z' r₅`; every other token keeps its position. The new
carriers `z, z'` avoid all of `Z` and carry the label `p r₀`; the next ledger
is the actual Stage88 terminal ledger of the three moves (at most `27` new
edges), and the trace can be continued from it.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer PhysicalMovesStage86
  PairExchangeProducerStage87 PairExchangeTraceStage87

variable {V : Type*} [DecidableEq V] {t : ℕ} {τ : Type*} [DecidableEq τ]

/-- Move exactly four tokens to four prescribed positions. -/
def move4 (pos : τ → Sym2 V) (q₁ q₂ q₃ q₄ : τ) (e₁ e₂ e₃ e₄ : Sym2 V) : τ → Sym2 V :=
  fun q => if q = q₁ then e₁ else if q = q₂ then e₂ else if q = q₃ then e₃ else
    if q = q₄ then e₄ else pos q

omit [DecidableEq V] in
theorem move4_of_ne {pos : τ → Sym2 V} {q₁ q₂ q₃ q₄ q : τ} {e₁ e₂ e₃ e₄ : Sym2 V}
    (h₁ : q ≠ q₁) (h₂ : q ≠ q₂) (h₃ : q ≠ q₃) (h₄ : q ≠ q₄) :
    move4 pos q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄ q = pos q := by
  simp [move4, h₁, h₂, h₃, h₄]

omit [DecidableEq V] in
/-- The four moved tokens arrive at their prescribed positions. -/
theorem move4_vals {pos : τ → Sym2 V} {q₁ q₂ q₃ q₄ : τ} {e₁ e₂ e₃ e₄ : Sym2 V}
    (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h14 : q₁ ≠ q₄) (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄)
    (h34 : q₃ ≠ q₄) :
    move4 pos q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄ q₁ = e₁ ∧ move4 pos q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄ q₂ = e₂ ∧
      move4 pos q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄ q₃ = e₃ ∧ move4 pos q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄ q₄ = e₄ := by
  simp [move4, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm]

/-- The configuration after a four-token move. -/
theorem image_move4 {toks : Finset τ} {pos : τ → Sym2 V} (hinj : Set.InjOn pos toks)
    {q₁ q₂ q₃ q₄ : τ} (m₁ : q₁ ∈ toks) (m₂ : q₂ ∈ toks) (m₃ : q₃ ∈ toks) (m₄ : q₄ ∈ toks)
    (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h14 : q₁ ≠ q₄) (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄)
    (h34 : q₃ ≠ q₄) (e₁ e₂ e₃ e₄ : Sym2 V) :
    toks.image (move4 pos q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄) =
      (toks.image pos \ {pos q₁, pos q₂, pos q₃, pos q₄}) ∪ {e₁, e₂, e₃, e₄} := by
  obtain ⟨v₁, v₂, v₃, v₄⟩ := move4_vals (pos := pos) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
    (e₄ := e₄) h12 h13 h14 h23 h24 h34
  have key : ∀ q ∈ toks, ∀ q' ∈ toks, pos q = pos q' → q = q' := fun q hq q' hq' h =>
    hinj hq hq' h
  ext e
  simp only [mem_image, mem_union, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨q, hq, rfl⟩
    by_cases c₁ : q = q₁
    · subst c₁; right; left; exact v₁
    by_cases c₂ : q = q₂
    · subst c₂; right; right; left; exact v₂
    by_cases c₃ : q = q₃
    · subst c₃; right; right; right; left; exact v₃
    by_cases c₄ : q = q₄
    · subst c₄; right; right; right; right; exact v₄
    left
    rw [move4_of_ne c₁ c₂ c₃ c₄]
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rintro (h | h | h | h)
    · exact c₁ (key q hq q₁ m₁ h)
    · exact c₂ (key q hq q₂ m₂ h)
    · exact c₃ (key q hq q₃ m₃ h)
    · exact c₄ (key q hq q₄ m₄ h)
  · rintro (⟨⟨q, hq, rfl⟩, hn⟩ | rfl | rfl | rfl | rfl)
    · have c₁ : q ≠ q₁ := fun h => hn (Or.inl (h ▸ rfl))
      have c₂ : q ≠ q₂ := fun h => hn (Or.inr (Or.inl (h ▸ rfl)))
      have c₃ : q ≠ q₃ := fun h => hn (Or.inr (Or.inr (Or.inl (h ▸ rfl))))
      have c₄ : q ≠ q₄ := fun h => hn (Or.inr (Or.inr (Or.inr (h ▸ rfl))))
      exact ⟨q, hq, move4_of_ne c₁ c₂ c₃ c₄⟩
    · exact ⟨q₁, m₁, v₁⟩
    · exact ⟨q₂, m₂, v₂⟩
    · exact ⟨q₃, m₃, v₃⟩
    · exact ⟨q₄, m₄, v₄⟩

omit [DecidableEq V] in
theorem link_of_eq {F : Finset (Multiset (Fin t))} {p : V → Fin t} {u v x w : V}
    (h : s(u, v) = s(x, w)) (hl : ∃ k, Link F (p x) (p w) k) :
    ∃ k, Link F (p u) (p v) k := by
  obtain ⟨k, hk⟩ := hl
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨k, hk⟩
  · exact ⟨k, (link_root_swap F _ _ k).mp hk⟩

variable [Fintype V]

/-- A physical token-tracked state with ledger `U` and active vertex set `Z`. -/
structure Phys (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset (Sym2 V)) (toks : Finset τ) (pos : τ → Sym2 V)
    (U : Finset (Sym2 V)) (Z : Finset V) : Prop where
  inj : Set.InjOn pos toks
  hist : toks.image pos ⊆ U
  real : toks.image pos ⊆ G.edgeFinset
  forb : Disjoint (toks.image pos) B
  supp : ∀ q ∈ toks, ∀ v ∈ pos q, v ∈ Z
  links : ∀ q ∈ toks, ∀ u v, pos q = s(u, v) → ∃ k, Link F (p u) (p v) k

/-- **One token-tracked exchange.** Four tokens at the source edges
`r₀r₂, r₀r₃, r₁r₄, r₁r₅` of six distinct roots (with `p r₁ = p r₀`) are moved
by one selected, framed Stage87 exchange to `z r₂, z' r₃, z r₄, z' r₅`.
All other tokens stay where they are. The new carriers are fresh for the
whole active set `Z`, distinct and labelled `p r₀`; the next ledger is the
exact terminal ledger of the three moves. -/
theorem token_exchange {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    {toks : Finset τ} {pos : τ → Sym2 V} {U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B toks pos U Z)
    {r₀ r₁ r₂ r₃ r₄ r₅ : V} (hr : PhysicalHingeSupply.SixDistinct r₀ r₁ r₂ r₃ r₄ r₅)
    (hlab : p r₁ = p r₀) {q₁ q₂ q₃ q₄ : τ}
    (m₁ : q₁ ∈ toks) (m₂ : q₂ ∈ toks) (m₃ : q₃ ∈ toks) (m₄ : q₄ ∈ toks)
    (p₁ : pos q₁ = s(r₀, r₂)) (p₂ : pos q₂ = s(r₀, r₃)) (p₃ : pos q₃ = s(r₁, r₄))
    (p₄ : pos q₄ = s(r₁, r₅))
    (hb : 14 + (Z.card : ℝ) + 4 * (d + U.card) < a) :
    ∃ (z z' : V) (U' : Finset (Sym2 V)),
      z ∉ Z ∧ z' ∉ Z ∧ z ≠ z' ∧ p z = p r₀ ∧ p z' = p r₀ ∧
      Phys p F G B toks (move4 pos q₁ q₂ q₃ q₄ s(z, r₂) s(z', r₃) s(z, r₄) s(z', r₅)) U'
        (insert z (insert z' Z)) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 27 ∧
      PhysicalMoves p F G.edgeFinset B U (toks.image pos)
        (toks.image (move4 pos q₁ q₂ q₃ q₄ s(z, r₂) s(z', r₃) s(z, r₄) s(z', r₅))) 3 ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U'
          (toks.image (move4 pos q₁ q₂ q₃ q₄ s(z, r₂) s(z', r₃) s(z, r₄) s(z', r₅))) W k →
        PhysicalMoves p F G.edgeFinset B U (toks.image pos) W (3 + k) := by
  obtain ⟨d01, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ := id hr
  set r := PhysicalHingeSupply.sixEmb hr with hrdef
  have hsrc : sourceEdges r = {s(r₀, r₂), s(r₀, r₃), s(r₁, r₄), s(r₁, r₅)} := by
    simp [sourceEdges, hrdef, PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap]
  -- the four tokens are distinct, since their positions are
  have hne : ∀ {q q' : τ} {e e' : Sym2 V}, pos q = e → pos q' = e' → e ≠ e' → q ≠ q' := by
    rintro q q' e e' rfl rfl h rfl
    exact h rfl
  have h12 : q₁ ≠ q₂ := hne p₁ p₂ (by rw [Ne, Sym2.eq_iff]; tauto)
  have h13 : q₁ ≠ q₃ := hne p₁ p₃ (by rw [Ne, Sym2.eq_iff]; tauto)
  have h14 : q₁ ≠ q₄ := hne p₁ p₄ (by rw [Ne, Sym2.eq_iff]; tauto)
  have h23 : q₂ ≠ q₃ := hne p₂ p₃ (by rw [Ne, Sym2.eq_iff]; tauto)
  have h24 : q₂ ≠ q₄ := hne p₂ p₄ (by rw [Ne, Sym2.eq_iff]; tauto)
  have h34 : q₃ ≠ q₄ := hne p₃ p₄ (by rw [Ne, Sym2.eq_iff]; tauto)
  have inZ : ∀ {q : τ}, q ∈ toks → ∀ {u v : V}, pos q = s(u, v) → u ∈ Z ∧ v ∈ Z :=
    fun hq _ _ h => ⟨ph.supp _ hq _ (h ▸ Sym2.mem_mk_left _ _),
      ph.supp _ hq _ (h ▸ Sym2.mem_mk_right _ _)⟩
  have z0 := (inZ m₁ p₁).1
  have z1 := (inZ m₃ p₃).1
  have z2 := (inZ m₁ p₁).2
  have z3 := (inZ m₂ p₂).2
  have z4 := (inZ m₃ p₃).2
  have z5 := (inZ m₄ p₄).2
  have hsub : sourceEdges r ⊆ toks.image pos := by
    rw [hsrc]
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact mem_image.mpr ⟨q₁, m₁, p₁⟩
    · exact mem_image.mpr ⟨q₂, m₂, p₂⟩
    · exact mem_image.mpr ⟨q₃, m₃, p₃⟩
    · exact mem_image.mpr ⟨q₄, m₄, p₄⟩
  have hsupp : ∀ e ∈ toks.image pos, ∀ v ∈ e, v ∈ Z := by
    intro e he v hv
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    exact ph.supp q hq v hv
  have hdata : ExchangeData p F G a d B U Z (toks.image pos) r :=
    { threeStep := hF
      supply := hs
      d_nonneg := hd
      forbidden := hB
      budget := by linarith
      roots_mem := by
        intro i
        fin_cases i
        · exact z0
        · exact z1
        · exact z2
        · exact z3
        · exact z4
        · exact z5
      label_eq := hlab
      source_real := hsub.trans ph.real
      active := ⟨ph.links q₁ m₁ _ _ p₁, ph.links q₂ m₂ _ _ p₂, ph.links q₃ m₃ _ _ p₃,
        ph.links q₄ m₄ _ _ p₄⟩
      source_sub := hsub
      config_history := ph.hist
      config_real := ph.real
      config_forbidden := ph.forb
      support := hsupp }
  obtain ⟨f, hf, htr, hreal, hforb⟩ := exists_framed_exchange hdata
  set z := f 6 with hzdef
  set z' := f 7 with hz'def
  have hz : z ∉ Z := hf.fresh_vertices 6 (by decide)
  have hz' : z' ∉ Z := hf.fresh_vertices 7 (by decide)
  have hzz : z ≠ z' := f.injective.ne (by decide)
  have hfin : finalEdges r f = {s(z, r₂), s(z', r₃), s(z, r₄), s(z', r₅)} := by
    simp only [finalEdges, hrdef, PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap]
    ext e
    simp only [Function.Embedding.coeFn_mk, Matrix.cons_val, mem_insert, mem_singleton]
    tauto
  set pos' := move4 pos q₁ q₂ q₃ q₄ s(z, r₂) s(z', r₃) s(z, r₄) s(z', r₅) with hpos'
  have hcfg : (toks.image pos \ sourceEdges r) ∪ finalEdges r f = toks.image pos' := by
    rw [hpos', image_move4 ph.inj m₁ m₂ m₃ m₄ h12 h13 h14 h23 h24 h34, hsrc, hfin, p₁, p₂, p₃,
      p₄]
  rw [hcfg] at htr hreal hforb
  obtain ⟨L, hUL, hYL, hLc, -, hcont⟩ := MoveLedgerStage88.terminal_ledger htr ph.hist
  have hv := move4_vals (pos := pos) (e₁ := s(z, r₂)) (e₂ := s(z', r₃))
    (e₃ := s(z, r₄)) (e₄ := s(z', r₅)) h12 h13 h14 h23 h24 h34
  have v₁ : pos' q₁ = s(z, r₂) := hv.1
  have v₂ : pos' q₂ = s(z', r₃) := hv.2.1
  have v₃ : pos' q₃ = s(z, r₄) := hv.2.2.1
  have v₄ : pos' q₄ = s(z', r₅) := hv.2.2.2
  have hZsub : Z ⊆ insert z (insert z' Z) := fun v hv =>
    mem_insert_of_mem (mem_insert_of_mem hv)
  have nz : ∀ v, v ∈ Z → v ≠ z ∧ v ≠ z' := fun v hv =>
    ⟨fun h => hz (h ▸ hv), fun h => hz' (h ▸ hv)⟩
  have untouched : ∀ q, q₁ ≠ q → q₂ ≠ q → q₃ ≠ q → q₄ ≠ q → pos' q = pos q :=
    fun _ c₁ c₂ c₃ c₄ => move4_of_ne (Ne.symm c₁) (Ne.symm c₂) (Ne.symm c₃) (Ne.symm c₄)
  have freshEnd : ∀ q ∈ toks, z ∉ pos q ∧ z' ∉ pos q := fun q hq =>
    ⟨fun h => hz (ph.supp q hq z h), fun h => hz' (ph.supp q hq z' h)⟩
  have hl₁ := ph.links q₁ m₁ _ _ p₁
  have hl₂ := ph.links q₂ m₂ _ _ p₂
  have hl₃ := ph.links q₃ m₃ _ _ p₃
  have hl₄ := ph.links q₄ m₄ _ _ p₄
  have lz : p z = p r₀ := hf.carrier_labels.1
  have lz' : p z' = p r₀ := hf.carrier_labels.2
  refine ⟨z, z', L, hz, hz', hzz, lz, lz', ?_, hUL, by omega, ?_, fun W k h => hcont W k h⟩
  · refine ⟨?_, hYL, hreal, hforb, ?_, ?_⟩
    · -- injectivity of the new positions
      obtain ⟨n2, n2'⟩ := nz _ z2
      obtain ⟨n3, n3'⟩ := nz _ z3
      obtain ⟨n4, n4'⟩ := nz _ z4
      obtain ⟨n5, n5'⟩ := nz _ z5
      have touchedFresh : ∀ q, (q₁ = q ∨ q₂ = q ∨ q₃ = q ∨ q₄ = q) →
          z ∈ pos' q ∨ z' ∈ pos' q := by
        rintro q (rfl | rfl | rfl | rfl)
        · rw [v₁]; exact Or.inl (Sym2.mem_mk_left _ _)
        · rw [v₂]; exact Or.inr (Sym2.mem_mk_left _ _)
        · rw [v₃]; exact Or.inl (Sym2.mem_mk_left _ _)
        · rw [v₄]; exact Or.inr (Sym2.mem_mk_left _ _)
      intro q hq q' hq' (heq : pos' q = pos' q')
      by_cases hT : q₁ = q ∨ q₂ = q ∨ q₃ = q ∨ q₄ = q <;>
        by_cases hT' : q₁ = q' ∨ q₂ = q' ∨ q₃ = q' ∨ q₄ = q'
      · rcases hT with rfl | rfl | rfl | rfl <;> rcases hT' with rfl | rfl | rfl | rfl <;>
          first
          | rfl
          | (exfalso
             simp only [v₁, v₂, v₃, v₄, Sym2.eq_iff] at heq
             rcases heq with ⟨h, h'⟩ | ⟨h, h'⟩
             all_goals first
               | exact hzz h | exact hzz h.symm | exact d24 h' | exact d35 h'
               | exact d24 h'.symm | exact d35 h'.symm
               | exact n2 h.symm | exact n2' h.symm | exact n3 h.symm | exact n3' h.symm
               | exact n4 h.symm | exact n4' h.symm | exact n5 h.symm | exact n5' h.symm)
      · simp only [not_or] at hT'
        rw [untouched q' hT'.1 hT'.2.1 hT'.2.2.1 hT'.2.2.2] at heq
        have hf' := freshEnd q' hq'
        rcases touchedFresh q hT with h | h
        · exact absurd (heq ▸ h) hf'.1
        · exact absurd (heq ▸ h) hf'.2
      · simp only [not_or] at hT
        rw [untouched q hT.1 hT.2.1 hT.2.2.1 hT.2.2.2] at heq
        have hf' := freshEnd q hq
        rcases touchedFresh q' hT' with h | h
        · exact absurd (heq ▸ h) hf'.1
        · exact absurd (heq ▸ h) hf'.2
      · simp only [not_or] at hT hT'
        rw [untouched q hT.1 hT.2.1 hT.2.2.1 hT.2.2.2,
          untouched q' hT'.1 hT'.2.1 hT'.2.2.1 hT'.2.2.2] at heq
        exact ph.inj hq hq' heq
    · intro q hq v (hv : v ∈ pos' q)
      by_cases c₁ : q₁ = q
      · rw [← c₁, v₁] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact mem_insert_self _ _
        · exact hZsub z2
      by_cases c₂ : q₂ = q
      · rw [← c₂, v₂] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact mem_insert_of_mem (mem_insert_self _ _)
        · exact hZsub z3
      by_cases c₃ : q₃ = q
      · rw [← c₃, v₃] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact mem_insert_self _ _
        · exact hZsub z4
      by_cases c₄ : q₄ = q
      · rw [← c₄, v₄] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact mem_insert_of_mem (mem_insert_self _ _)
        · exact hZsub z5
      rw [untouched q c₁ c₂ c₃ c₄] at hv
      exact hZsub (ph.supp q hq v hv)
    · intro q hq u v (huv : pos' q = s(u, v))
      by_cases c₁ : q₁ = q
      · rw [← c₁, v₁] at huv
        obtain ⟨k, hk⟩ := hl₁
        exact link_of_eq huv.symm ⟨k, by rw [lz]; exact hk⟩
      by_cases c₂ : q₂ = q
      · rw [← c₂, v₂] at huv
        obtain ⟨k, hk⟩ := hl₂
        exact link_of_eq huv.symm ⟨k, by rw [lz']; exact hk⟩
      by_cases c₃ : q₃ = q
      · rw [← c₃, v₃] at huv
        obtain ⟨k, hk⟩ := hl₃
        exact link_of_eq huv.symm ⟨k, by rw [lz, ← hlab]; exact hk⟩
      by_cases c₄ : q₄ = q
      · rw [← c₄, v₄] at huv
        obtain ⟨k, hk⟩ := hl₄
        exact link_of_eq huv.symm ⟨k, by rw [lz', ← hlab]; exact hk⟩
      rw [untouched q c₁ c₂ c₃ c₄] at huv
      exact ph.links q hq u v huv
  · simpa using hcont _ 0 (.stop _ _)

end PartitionedTriangleAbsorption.TripleCutStage94
