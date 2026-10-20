/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SelectedTripleCutStage98
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # Geometry of the catalytic residue after all original triples are cut

These lemmas derive the companion of a catalytic handle from the actual
physical state and boundary invariant. No new supply or decomposition of
the catalytic residue is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalyticCleanupStage99

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 TripleCutStage94

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))}
  {G : SimpleGraph V} [DecidableRel G.Adj] {B U : Finset (Sym2 V)}
  {Z : Finset V} {S : Data V} {pos : Tok V → Sym2 V}

theorem edge_ne (ph : Phys p F G B S.tokens pos U Z)
    {q : Tok V} (hq : q ∈ S.tokens) {u v : V} (hp : pos q = s(u, v)) : u ≠ v := by
  have he := ph.real (mem_image.mpr ⟨q, hq, rfl⟩)
  rw [SimpleGraph.mem_edgeFinset, hp, SimpleGraph.mem_edgeSet] at he
  exact G.ne_of_adj he

/-- A mobile handle never lies at any of the fixed catalytic vertices. -/
theorem handle_ne_cat (ph : Phys p F G B S.tokens pos U Z)
    (bd : Bdry p F S pos ∅) {y : V} (hy : y ∈ S.A) {i : Fin 3} (hi : i ≠ 2)
    {h : V} (hp : pos (.inr (y, i)) = s(h, catV S y i))
    {y' : V} (hy' : y' ∈ S.A) (j : Fin 3) : h ≠ catV S y' j := by
  intro hh
  have hm : (.inr (y, i) : Tok V) ∈ tokAtP S pos h :=
    mem_tokAtP.mpr ⟨(mem_tokens_inr y i).mpr hy, hp ▸ Sym2.mem_mk_left _ _⟩
  have hn := edge_ne ph ((mem_tokens_inr y i).mpr hy) hp
  unfold catV at hh
  split_ifs at hh
  · rw [hh, bd.at_cs y' hy'] at hm
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨-, he⟩
    · exact hn (by simpa [catV] using hh)
    · exact hi he
  · rw [hh, bd.at_ct y' hy'] at hm
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨-, he⟩
    · exact hn (by simpa [catV] using hh)
    · exact hi he

/-- The second token at a mobile handle is another mobile catalytic handle,
not a fixed middle edge and not an original token. -/
theorem handle_companion (ph : Phys p F G B S.tokens pos U Z)
    (bd : Bdry p F S pos ∅) {y : V} (hy : y ∈ S.A) {i : Fin 3} (hi : i ≠ 2)
    {h : V} (hp : pos (.inr (y, i)) = s(h, catV S y i)) :
    ∃ y' ∈ S.A, ∃ i' : Fin 3, i' ≠ 2 ∧ (y', i') ≠ (y, i) ∧
      tokAtP S pos h = {.inr (y, i), .inr (y', i')} ∧
      pos (.inr (y', i')) = s(h, catV S y' i') ∧ p h = p y' := by
  have hm : (.inr (y, i) : Tok V) ∈ tokAtP S pos h :=
    mem_tokAtP.mpr ⟨(mem_tokens_inr y i).mpr hy, hp ▸ Sym2.mem_mk_left _ _⟩
  rcases bd.other h (by simp) with he | ⟨κ, κ', hne, hat⟩ | ⟨e, e', -, -, -, hat⟩
  · rw [he] at hm
    simp at hm
  · have hm' := hm
    rw [hat] at hm'
    simp only [mem_insert, mem_singleton, Sum.inr.injEq] at hm'
    obtain ⟨κ', hne', hat'⟩ : ∃ κ' : V × Fin 3, κ' ≠ (y, i) ∧
        tokAtP S pos h = {.inr (y, i), .inr κ'} := by
      rcases hm' with h | h
      · subst κ
        exact ⟨κ', hne.symm, hat⟩
      · subst κ'
        exact ⟨κ, hne, by rw [hat, pair_comm]⟩
    have hκ : (.inr κ' : Tok V) ∈ tokAtP S pos h := by simp [hat']
    obtain ⟨htok, hv⟩ := mem_tokAtP.mp hκ
    have hy' := (mem_tokens_inr κ'.1 κ'.2).mp htok
    have hi' : κ'.2 ≠ 2 := by
      intro h2
      have hmid : pos (.inr κ') = s(S.cs κ'.1, S.ct κ'.1) := by
        convert bd.handle₂ κ'.1 hy' using 1
        exact congrArg (fun i => pos (.inr (κ'.1, i))) h2
      rw [hmid, Sym2.mem_iff] at hv
      rcases hv with hh | hh
      · exact handle_ne_cat ph bd hy hi hp hy' 0 (by simpa [catV] using hh)
      · exact handle_ne_cat ph bd hy hi hp hy' 1 (by simpa [catV] using hh)
    obtain ⟨h', he', hl⟩ := bd.handle κ'.1 hy' κ'.2 hi'
    have hh' : h = h' := by
      rw [he', Sym2.mem_iff] at hv
      rcases hv with hh | hh
      · exact hh
      · exact False.elim (handle_ne_cat ph bd hy hi hp hy' κ'.2 hh)
    subst h'
    exact ⟨κ'.1, hy', κ'.2, hi', hne', hat', he', hl⟩
  · rw [hat] at hm
    simp at hm

/-- The four moving handles of an unclosed block have six distinct roots.
This is derived from injectivity and the boundary invariant, rather than
supplied as an additional geometric premise. -/
theorem open_block_roots (ph : Phys p F G B S.tokens pos U Z)
    (bd : Bdry p F S pos ∅) {y : V} (hy : y ∈ S.A) {a b : V}
    (h0 : pos (.inr (y, 0)) = s(a, S.cs y))
    (h1 : pos (.inr (y, 1)) = s(b, S.ct y)) (hab : a ≠ b) :
    ∃ y₀ ∈ S.A, ∃ i₀ : Fin 3, ∃ y₁ ∈ S.A, ∃ i₁ : Fin 3,
      i₀ ≠ 2 ∧ i₁ ≠ 2 ∧ (y₀, i₀) ≠ (y, 0) ∧ (y₁, i₁) ≠ (y, 1) ∧
      tokAtP S pos a = {.inr (y, 0), .inr (y₀, i₀)} ∧
      tokAtP S pos b = {.inr (y, 1), .inr (y₁, i₁)} ∧
      pos (.inr (y₀, i₀)) = s(a, catV S y₀ i₀) ∧
      pos (.inr (y₁, i₁)) = s(b, catV S y₁ i₁) ∧
      PhysicalHingeSupply.SixDistinct a b (S.cs y) (catV S y₀ i₀)
        (S.ct y) (catV S y₁ i₁) := by
  have hp0 : pos (.inr (y, 0)) = s(a, catV S y 0) := by simpa [catV] using h0
  have hp1 : pos (.inr (y, 1)) = s(b, catV S y 1) := by simpa [catV] using h1
  obtain ⟨y₀, hy₀, i₀, hi₀, hn₀, at₀, hp₀, -⟩ := handle_companion ph bd hy (by decide) hp0
  obtain ⟨y₁, hy₁, i₁, hi₁, hn₁, at₁, hp₁, -⟩ := handle_companion ph bd hy (by decide) hp1
  have d02 : a ≠ S.cs y := by simpa [catV] using handle_ne_cat ph bd hy (by decide) hp0 hy 0
  have d03 := handle_ne_cat ph bd hy (by decide) hp0 hy₀ i₀
  have d04 : a ≠ S.ct y := by simpa [catV] using handle_ne_cat ph bd hy (by decide) hp0 hy 1
  have d05 := handle_ne_cat ph bd hy (by decide) hp0 hy₁ i₁
  have d12 : b ≠ S.cs y := by simpa [catV] using handle_ne_cat ph bd hy (by decide) hp1 hy 0
  have d13 := handle_ne_cat ph bd hy (by decide) hp1 hy₀ i₀
  have d14 : b ≠ S.ct y := by simpa [catV] using handle_ne_cat ph bd hy (by decide) hp1 hy 1
  have d15 := handle_ne_cat ph bd hy (by decide) hp1 hy₁ i₁
  have d23 : S.cs y ≠ catV S y₀ i₀ := by
    intro he
    have hq := ph.inj ((mem_tokens_inr y₀ i₀).mpr hy₀)
      ((mem_tokens_inr y 0).mpr hy) (by rw [hp₀, h0, he])
    exact hn₀ (Sum.inr.inj hq)
  have d24 := edge_ne ph ((mem_tokens_inr y 2).mpr hy) (bd.handle₂ y hy)
  have d25 : S.cs y ≠ catV S y₁ i₁ := by
    simpa [catV] using bd.catV_ne hy₁ hi₁ hy (by decide) hp0 hp₁ hab
  have d34 : catV S y₀ i₀ ≠ S.ct y := by
    simpa [catV] using bd.catV_ne hy (by decide) hy₀ hi₀ hp₀ hp1 hab
  have d35 := bd.catV_ne hy₁ hi₁ hy₀ hi₀ hp₀ hp₁ hab
  have d45 : S.ct y ≠ catV S y₁ i₁ := by
    intro he
    have hq := ph.inj ((mem_tokens_inr y₁ i₁).mpr hy₁)
      ((mem_tokens_inr y 1).mpr hy) (by rw [hp₁, h1, he])
    exact hn₁ (Sum.inr.inj hq)
  exact ⟨y₀, hy₀, i₀, y₁, hy₁, i₁, hi₀, hi₁, hn₀, hn₁, at₀, at₁, hp₀, hp₁,
    hab, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩

/-- Close one unclosed catalytic block by an actual physical exchange.
The other original tokens and all middle edges remain fixed. This theorem
does not yet claim restoration of the full boundary invariant. -/
theorem close_open_block (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos ∅)
    {y : V} (hy : y ∈ S.A) (hl : Link F (p y) (p (S.cs y)) (p (S.ct y)))
    {h₀ h₁ : V} (h0 : pos (.inr (y, 0)) = s(h₀, S.cs y))
    (h1 : pos (.inr (y, 1)) = s(h₁, S.ct y)) (hh : h₀ ≠ h₁)
    (hb : 14 + (Z.card : ℝ) + 4 * (d + U.card) < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (z z' : V),
      Phys p F G B S.tokens pos' U' (insert z (insert z' Z)) ∧
      pos' (.inr (y, 0)) = s(z, S.cs y) ∧
      pos' (.inr (y, 1)) = s(z, S.ct y) ∧ p z = p y ∧
      HasDecomp p F (CatalystSelectionStage89.catEdges z (S.cs y) (S.ct y)) ∧
      (∀ e, pos' (.inl e) = pos (.inl e)) ∧
      (∀ y', pos' (.inr (y', 2)) = pos (.inr (y', 2))) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 27 ∧
      PhysicalMovesStage86.PhysicalMoves p F G.edgeFinset B U
        (S.tokens.image pos) (S.tokens.image pos') 3 ∧
      ∀ W k, PhysicalMovesStage86.PhysicalMoves p F G.edgeFinset B U'
          (S.tokens.image pos') W k →
        PhysicalMovesStage86.PhysicalMoves p F G.edgeFinset B U
          (S.tokens.image pos) W (3 + k) := by
  obtain ⟨y₀, hy₀, i₀, y₁, hy₁, i₁, hi₀, hi₁, hn₀, hn₁, -, -, hp₀, hp₁, hr⟩ :=
    open_block_roots ph bd hy h0 h1 hh
  obtain ⟨h, hp, lh⟩ := bd.handle y hy 0 (by decide)
  have l0 : p h₀ = p y := by
    rw [catV_zero, h0] at hp
    have he : h = h₀ := Sym2.congr_left.mp hp.symm
    simpa [he] using lh
  obtain ⟨h, hp, lh⟩ := bd.handle y hy 1 (by decide)
  have l1 : p h₁ = p y := by
    rw [catV_one, h1] at hp
    have he : h = h₁ := Sym2.congr_left.mp hp.symm
    simpa [he] using lh
  obtain ⟨z, z', U', hz, hz', hzz', lz, -, ph', hU, hc, tr, cont⟩ :=
    token_exchange a d hF hs hB hd ph hr (l1.trans l0.symm)
      ((mem_tokens_inr y 0).mpr hy) ((mem_tokens_inr y₀ i₀).mpr hy₀)
      ((mem_tokens_inr y 1).mpr hy) ((mem_tokens_inr y₁ i₁).mpr hy₁)
      h0 hp₀ h1 hp₁ hb
  let pos' := move4 pos (.inr (y, 0)) (.inr (y₀, i₀)) (.inr (y, 1)) (.inr (y₁, i₁))
    s(z, S.cs y) s(z', catV S y₀ i₀) s(z, S.ct y) s(z', catV S y₁ i₁)
  have q12 : (.inr (y, 0) : Tok V) ≠ .inr (y₀, i₀) := by simpa using hn₀.symm
  have q13 : (.inr (y, 0) : Tok V) ≠ .inr (y, 1) := by simp
  have hp0 : pos (.inr (y, 0)) = s(h₀, catV S y 0) := by simpa [catV] using h0
  have hp1 : pos (.inr (y, 1)) = s(h₁, catV S y 1) := by simpa [catV] using h1
  have q14 := tok_ne_of hp0 hp₁ hh
  have q23 := tok_ne_of hp₀ hp1 hh
  have q24 := tok_ne_of hp₀ hp₁ hh
  have q34 : (.inr (y, 1) : Tok V) ≠ .inr (y₁, i₁) := by simpa using hn₁.symm
  obtain ⟨v0, -, v1, -⟩ := move4_vals (pos := pos) (e₁ := s(z, S.cs y))
    (e₂ := s(z', catV S y₀ i₀)) (e₃ := s(z, S.ct y)) (e₄ := s(z', catV S y₁ i₁))
    q12 q13 q14 q23 q24 q34
  have vz0 : pos' (.inr (y, 0)) = s(z, S.cs y) := v0
  have vz1 : pos' (.inr (y, 1)) = s(z, S.ct y) := v1
  have hncs := edge_ne ph' ((mem_tokens_inr y 0).mpr hy) vz0
  have hnct := edge_ne ph' ((mem_tokens_inr y 1).mpr hy) vz1
  have hct := edge_ne ph ((mem_tokens_inr y 2).mpr hy) (bd.handle₂ y hy)
  refine ⟨pos', U', z, z', ph', vz0, vz1, lz.trans l0, ?_, ?_, ?_, hU, hc, tr, cont⟩
  · exact CatalystSelectionStage89.catalyst_decomp hncs hnct hct (by rw [lz, l0]; exact hl)
  · intro e
    exact move4_of_ne (by simp) (by simp) (by simp) (by simp)
  · intro y'
    exact move4_of_ne (by simp) (by simp [Ne.symm hi₀]) (by simp) (by simp [Ne.symm hi₁])

/-- The three current edges belonging to one catalytic block. -/
def blockEdges (pos : Tok V → Sym2 V) (y : V) : Finset (Sym2 V) :=
  (univ : Finset (Fin 3)).image fun i => pos (.inr (y, i))

/-- Current blocks are edge-disjoint even when their vertices are not. -/
theorem blocks_disjoint (ph : Phys p F G B S.tokens pos U Z)
    {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A) (hne : y ≠ y') :
    Disjoint (blockEdges pos y) (blockEdges pos y') := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨i, -, hi⟩ := mem_image.mp he
  obtain ⟨i', -, hi'⟩ := mem_image.mp he'
  have hq := ph.inj ((mem_tokens_inr y i).mpr hy) ((mem_tokens_inr y' i').mpr hy')
    (hi.trans hi'.symm)
  exact hne (congrArg Prod.fst (Sum.inr.inj hq))

omit [Fintype V] in
theorem blockEdges_closed {y h : V}
    (h0 : pos (.inr (y, 0)) = s(h, S.cs y))
    (h1 : pos (.inr (y, 1)) = s(h, S.ct y))
    (h2 : pos (.inr (y, 2)) = s(S.cs y, S.ct y)) :
    blockEdges pos y = CatalystSelectionStage89.catEdges h (S.cs y) (S.ct y) := by
  ext e
  simp only [blockEdges, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [h0, h1, h2, CatalystSelectionStage89.catEdges]
  · simp only [CatalystSelectionStage89.catEdges, mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩

/-- Once every block is closed, the catalytic residue has an actual
edge-disjoint decomposition, using the types of the retained frame. -/
theorem catalytic_decomp_of_closed (ph : Phys p F G B S.tokens pos U Z)
    (bd : Bdry p F S pos ∅)
    (hl : ∀ y ∈ S.A, Link F (p y) (p (S.cs y)) (p (S.ct y)))
    (hc : ∀ y ∈ S.A, ∃ h, pos (.inr (y, 0)) = s(h, S.cs y) ∧
      pos (.inr (y, 1)) = s(h, S.ct y)) :
    HasDecomp p F (S.A.biUnion (blockEdges pos)) := by
  apply RefinerAssembly.hasDecomp_biUnion
  · intro y hy
    obtain ⟨h, h0, h1⟩ := hc y hy
    obtain ⟨h', hh', lp⟩ := bd.handle y hy 0 (by decide)
    rw [catV_zero, h0] at hh'
    have he : h = h' := Sym2.congr_left.mp hh'
    have hlabel : p h = p y := by simpa [← he] using lp
    rw [blockEdges_closed h0 h1 (bd.handle₂ y hy)]
    exact CatalystSelectionStage89.catalyst_decomp
      (edge_ne ph ((mem_tokens_inr y 0).mpr hy) h0)
      (edge_ne ph ((mem_tokens_inr y 1).mpr hy) h1)
      (edge_ne ph ((mem_tokens_inr y 2).mpr hy) (bd.handle₂ y hy))
      (by rw [hlabel]; exact hl y hy)
  · intro y hy y' hy' hne
    exact blocks_disjoint ph hy hy' hne

/-- The exact current configuration splits into original and catalytic
token images, without an overlap. -/
theorem token_image_split (ph : Phys p F G B S.tokens pos U Z) :
    S.tokens.image pos = S.Y.image (fun e => pos (.inl e)) ∪
      S.A.biUnion (blockEdges pos) ∧
    Disjoint (S.Y.image (fun e => pos (.inl e))) (S.A.biUnion (blockEdges pos)) := by
  constructor
  · ext e
    simp only [mem_image, mem_union, mem_biUnion, blockEdges, mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with e | ⟨y, i⟩
      · exact Or.inl ⟨e, (mem_tokens_inl e).mp hq, rfl⟩
      · exact Or.inr ⟨y, (mem_tokens_inr y i).mp hq, i, rfl⟩
    · rintro (⟨e, he, rfl⟩ | ⟨y, hy, i, rfl⟩)
      · exact ⟨.inl e, (mem_tokens_inl e).mpr he, rfl⟩
      · exact ⟨.inr (y, i), (mem_tokens_inr y i).mpr hy, rfl⟩
  · rw [disjoint_left]
    intro e he he'
    obtain ⟨f, hf, hfpos⟩ := mem_image.mp he
    obtain ⟨y, hy, he'⟩ := mem_biUnion.mp he'
    obtain ⟨i, -, hipos⟩ := mem_image.mp he'
    have hq := ph.inj ((mem_tokens_inl f).mpr hf) ((mem_tokens_inr y i).mpr hy)
      (hfpos.trans hipos.symm)
    cases hq

/-- The final assembly consumer. Closure of every catalytic block is still
an explicit premise here; its production by induction is a separate gate. -/
theorem full_decomp_of_closed (ph : Phys p F G B S.tokens pos U Z)
    (bd : Bdry p F S pos ∅)
    (hl : ∀ y ∈ S.A, Link F (p y) (p (S.cs y)) (p (S.ct y)))
    (hc : ∀ y ∈ S.A, ∃ h, pos (.inr (y, 0)) = s(h, S.cs y) ∧
      pos (.inr (y, 1)) = s(h, S.ct y)) : HasDecomp p F (S.tokens.image pos) := by
  obtain ⟨hsplit, hd⟩ := token_image_split ph
  rw [hsplit]
  have hy : HasDecomp p F (S.Y.image fun e => pos (.inl e)) := by
    simpa using bd.done_decomp
  exact hy.union (catalytic_decomp_of_closed ph bd hl hc) hd

omit [DecidableEq V] [Fintype V] in
/-- Scalar budget consumed by one proved three-move exchange. This is a
ledger calculation, not the missing induction that produces all closures. -/
theorem cleanup_budget_step (z u z' u' r d a : ℝ)
    (hr : 1 ≤ r) (hz : z' ≤ z + 2) (hu : u' ≤ u + 27)
    (hb : z + 110 * r + 4 * (d + u) < a) :
    14 + z + 4 * (d + u) < a ∧
      z' + 110 * (r - 1) + 4 * (d + u') < a := by
  constructor <;> linarith

end PartitionedTriangleAbsorption.CatalyticCleanupStage99
