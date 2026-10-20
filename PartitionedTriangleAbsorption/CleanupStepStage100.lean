/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupIncidenceStage100

/-! # Invariant-preserving closure of one catalytic block -/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupStage100

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89
  TripleCutStage94 CatalyticCleanupStage99 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- Both mobile handles of the block share one carrier. -/
def Closed (S : Data V) (pos : Tok V → Sym2 V) (y : V) : Prop :=
  ∃ h, pos (.inr (y, 0)) = s(h, S.cs y) ∧ pos (.inr (y, 1)) = s(h, S.ct y)

variable [Fintype V] {p : V → Fin t} {F : Finset (Multiset (Fin t))}
  {G : SimpleGraph V} [DecidableRel G.Adj] {B U : Finset (Sym2 V)}
  {Z : Finset V} {S : Data V} {pos : Tok V → Sym2 V}

omit [Fintype V] in
theorem handle_label (bd : Bdry p F S pos ∅) {y : V} (hy : y ∈ S.A)
    {i : Fin 3} (hi : i ≠ 2) {h : V}
    (hp : pos (.inr (y, i)) = s(h, catV S y i)) : p h = p y := by
  obtain ⟨h', hp', hl⟩ := bd.handle y hy i hi
  rw [hp] at hp'
  have hh : h = h' := Sym2.congr_left.mp hp'
  simpa [← hh] using hl

omit [Fintype V] in
theorem closed_incidence (bd : Bdry p F S pos ∅) {y : V} (hy : y ∈ S.A)
    {h : V} (h0 : pos (.inr (y, 0)) = s(h, S.cs y))
    (h1 : pos (.inr (y, 1)) = s(h, S.ct y)) :
    tokAtP S pos h = {.inr (y, 0), .inr (y, 1)} := by
  have hsub : ({.inr (y, 0), .inr (y, 1)} : Finset (Tok V)) ⊆ tokAtP S pos h := by
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact mem_tokAtP.mpr ⟨(mem_tokens_inr y 0).mpr hy, h0 ▸ Sym2.mem_mk_left _ _⟩
    · exact mem_tokAtP.mpr ⟨(mem_tokens_inr y 1).mpr hy, h1 ▸ Sym2.mem_mk_left _ _⟩
  have hcard : (tokAtP S pos h).card ≤ 2 := by
    rcases bd.other h (by simp) with he | ⟨κ, κ', -, he⟩ | ⟨e, e', -, -, -, he⟩
    · simp [he]
    · rw [he]; exact (card_insert_le _ _).trans (by simp)
    · rw [he]; exact (card_insert_le _ _).trans (by simp)
  have hpair : ({.inr (y, 0), .inr (y, 1)} : Finset (Tok V)).card = 2 := by simp
  exact (eq_of_subset_of_card_le hsub (by rw [hpair]; exact hcard)).symm

omit [Fintype V] in
/-- A closed block cannot occupy a carrier of an open block. -/
theorem closed_carrier_ne (bd : Bdry p F S pos ∅) {y y' : V}
    (hy' : y' ∈ S.A) {a b h : V}
    (h0 : pos (.inr (y, 0)) = s(a, S.cs y))
    (h1 : pos (.inr (y, 1)) = s(b, S.ct y)) (hab : a ≠ b)
    (at0 : (.inr (y, 0) : Tok V) ∈ tokAtP S pos a)
    (at1 : (.inr (y, 1) : Tok V) ∈ tokAtP S pos b)
    (hc0 : pos (.inr (y', 0)) = s(h, S.cs y'))
    (hc1 : pos (.inr (y', 1)) = s(h, S.ct y')) : h ≠ a ∧ h ≠ b := by
  have hat := closed_incidence bd hy' hc0 hc1
  constructor
  · intro ha
    rw [← ha, hat] at at0
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at at0
    rcases at0 with ⟨rfl, -⟩ | ⟨-, hi⟩
    · rw [h1] at hc1
      exact hab (ha.symm.trans (Sym2.congr_left.mp hc1).symm)
    · exact (by decide : (0 : Fin 3) ≠ 1) hi
  · intro hb
    rw [← hb, hat] at at1
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at at1
    rcases at1 with ⟨-, hi⟩ | ⟨rfl, -⟩
    · exact (by decide : (1 : Fin 3) ≠ 0) hi
    · rw [h0] at hc0
      exact hab ((Sym2.congr_left.mp hc0).trans hb)

/-- Close one open block, restore the boundary invariant, and preserve all
closed blocks. The three moves carry the actual terminal ledger. -/
theorem close_step (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos ∅)
    {y : V} (hy : y ∈ S.A) (hop : ¬ Closed S pos y)
    (hb : 14 + (Z.card : ℝ) + 4 * (d + U.card) < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V),
      Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' ∅ ∧ Closed S pos' y ∧
      (∀ y' ∈ S.A, Closed S pos y' → Closed S pos' y') ∧
      (∀ e, pos' (.inl e) = pos (.inl e)) ∧
      (∀ y', pos' (.inr (y', 2)) = pos (.inr (y', 2))) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 27 ∧ Z ⊆ Z' ∧ Z'.card ≤ Z.card + 2 ∧
      PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos') 3 ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W k →
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (3 + k) := by
  obtain ⟨a₀, hp0, lp0⟩ := bd.handle y hy 0 (by decide)
  obtain ⟨a₁, hp1, lp1⟩ := bd.handle y hy 1 (by decide)
  rw [catV_zero] at hp0
  rw [catV_one] at hp1
  have hab : a₀ ≠ a₁ := by rintro rfl; exact hop ⟨a₀, hp0, hp1⟩
  obtain ⟨y₀, hy₀, i₀, y₁, hy₁, i₁, hi₀, hi₁, hn₀, hn₁, at₀, at₁, hp₀, hp₁, hr⟩ :=
    open_block_roots ph bd hy hp0 hp1 hab
  have p0 : pos (.inr (y, 0)) = s(a₀, catV S y 0) := by simpa [catV] using hp0
  have p1 : pos (.inr (y, 1)) = s(a₁, catV S y 1) := by simpa [catV] using hp1
  have lc0 := handle_label bd hy₀ hi₀ hp₀
  have lc1 := handle_label bd hy₁ hi₁ hp₁
  have q12 : (.inr (y, 0) : Tok V) ≠ .inr (y₀, i₀) := by simpa using hn₀.symm
  have q13 : (.inr (y, 0) : Tok V) ≠ .inr (y, 1) := by simp
  have q14 := tok_ne_of p0 hp₁ hab
  have q23 := tok_ne_of hp₀ p1 hab
  have q24 := tok_ne_of hp₀ hp₁ hab
  have q34 : (.inr (y, 1) : Tok V) ≠ .inr (y₁, i₁) := by simpa using hn₁.symm
  have m0 := (mem_tokens_inr y 0).mpr hy
  have m1 := (mem_tokens_inr y 1).mpr hy
  have mc0 := (mem_tokens_inr y₀ i₀).mpr hy₀
  have mc1 := (mem_tokens_inr y₁ i₁).mpr hy₁
  obtain ⟨z, z', U', hz, hz', hzz', lz, lz', ph', hUU, hUc, tr, cont⟩ :=
    token_exchange a d hF hs hB hd ph hr (lp1.trans lp0.symm)
      m0 mc0 m1 mc1 hp0 hp₀ hp1 hp₁ hb
  let pos' := move4 pos (.inr (y, 0)) (.inr (y₀, i₀)) (.inr (y, 1)) (.inr (y₁, i₁))
    s(z, S.cs y) s(z', catV S y₀ i₀) s(z, S.ct y) s(z', catV S y₁ i₁)
  obtain ⟨v0, vc0, v1, vc1⟩ := move4_vals (pos := pos) (e₁ := s(z, S.cs y))
    (e₂ := s(z', catV S y₀ i₀)) (e₃ := s(z, S.ct y)) (e₄ := s(z', catV S y₁ i₁))
    q12 q13 q14 q23 q24 q34
  have unO : ∀ e, pos' (.inl e) = pos (.inl e) :=
    fun _ => move4_of_ne (by simp) (by simp) (by simp) (by simp)
  have un2 : ∀ y', pos' (.inr (y', 2)) = pos (.inr (y', 2)) :=
    fun _ => move4_of_ne (by simp) (by simp [Ne.symm hi₀]) (by simp) (by simp [Ne.symm hi₁])
  have unK : ∀ q, q ≠ .inr (y, 0) → q ≠ .inr (y₀, i₀) → q ≠ .inr (y, 1) →
      q ≠ .inr (y₁, i₁) → pos' q = pos q := fun _ => move4_of_ne
  have fixZ : ∀ y' ∈ S.A, S.cs y' ∈ Z ∧ S.ct y' ∈ Z := fun y' hy' =>
    ⟨ph.supp _ ((mem_tokens_inr y' 2).mpr hy') _
      (by rw [bd.handle₂ y' hy']; exact Sym2.mem_mk_left _ _),
     ph.supp _ ((mem_tokens_inr y' 2).mpr hy') _
      (by rw [bd.handle₂ y' hy']; exact Sym2.mem_mk_right _ _)⟩
  have c0Z := ph.supp _ mc0 _ (hp₀ ▸ Sym2.mem_mk_right _ _)
  have c1Z := ph.supp _ mc1 _ (hp₁ ▸ Sym2.mem_mk_right _ _)
  have old0Z := ph.supp _ m0 _ (hp0 ▸ Sym2.mem_mk_left _ _)
  have old1Z := ph.supp _ m1 _ (hp1 ▸ Sym2.mem_mk_left _ _)
  have loc : ∀ v, v ≠ a₀ → v ≠ a₁ → v ≠ z → v ≠ z' → tokAtP S pos' v = tokAtP S pos v :=
    fun _ => exchange_other hp0 hp₀ hp1 hp₁ q12 q13 q14 q23 q24 q34
  have na : tokAtP S pos' a₀ = ∅ := by
    apply exchange_empty q12 q13 q14 q23 q24 q34
    · rw [at₀]; intro q hq; simp only [mem_insert, mem_singleton] at hq ⊢; tauto
    · exact hr.2.1
    · exact hr.2.2.1
    · exact hr.2.2.2.1
    · exact hr.2.2.2.2.1
    · exact ne_of_notMem' old0Z hz
    · exact ne_of_notMem' old0Z hz'
  have nb : tokAtP S pos' a₁ = ∅ := by
    apply exchange_empty q12 q13 q14 q23 q24 q34
    · rw [at₁]; intro q hq; simp only [mem_insert, mem_singleton] at hq ⊢; tauto
    · exact hr.2.2.2.2.2.1
    · exact hr.2.2.2.2.2.2.1
    · exact hr.2.2.2.2.2.2.2.1
    · exact hr.2.2.2.2.2.2.2.2.1
    · exact ne_of_notMem' old1Z hz
    · exact ne_of_notMem' old1Z hz'
  have nz : tokAtP S pos' z = {.inr (y, 0), .inr (y, 1)} :=
    exchange_at_new ph.supp m0 m1 q12 q13 q14 q23 q24 q34 hz hzz' c0Z c1Z
  have nz' : tokAtP S pos' z' = {.inr (y₀, i₀), .inr (y₁, i₁)} :=
    exchange_at_new' ph.supp mc0 mc1 q12 q13 q14 q23 q24 q34 hz' hzz'
      (fixZ y hy).1 (fixZ y hy).2
  have bd' : Bdry p F S pos' ∅ := by
    refine ⟨by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y' hy'
      rw [loc _ (by simpa [catV] using (handle_ne_cat ph bd hy (by decide) p0 hy' 0).symm)
        (by simpa [catV] using (handle_ne_cat ph bd hy (by decide) p1 hy' 0).symm)
        (ne_of_notMem' (fixZ y' hy').1 hz) (ne_of_notMem' (fixZ y' hy').1 hz')]
      exact bd.at_cs y' hy'
    · intro y' hy'
      rw [loc _ (by simpa [catV] using (handle_ne_cat ph bd hy (by decide) p0 hy' 1).symm)
        (by simpa [catV] using (handle_ne_cat ph bd hy (by decide) p1 hy' 1).symm)
        (ne_of_notMem' (fixZ y' hy').2 hz) (ne_of_notMem' (fixZ y' hy').2 hz')]
      exact bd.at_ct y' hy'
    · intro y' hy' i hi
      by_cases h0 : (y', i) = (y, 0)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
        exact ⟨z, v0, lz.trans lp0⟩
      by_cases hc0 : (y', i) = (y₀, i₀)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc0
        exact ⟨z', vc0, lz'.trans lc0⟩
      by_cases h1 : (y', i) = (y, 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
        exact ⟨z, v1, lz.trans lp0⟩
      by_cases hc1 : (y', i) = (y₁, i₁)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc1
        exact ⟨z', vc1, lz'.trans ((lp0.trans lp1.symm).trans lc1)⟩
      obtain ⟨h, hp, hl⟩ := bd.handle y' hy' i hi
      exact ⟨h, by rw [unK _ (by simpa using h0) (by simpa using hc0)
        (by simpa using h1) (by simpa using hc1)]; exact hp, hl⟩
    · intro y' hy'; rw [un2]; exact bd.handle₂ y' hy'
    · intro v _
      by_cases ha : v = a₀
      · subst v; exact Or.inl na
      by_cases hb : v = a₁
      · subst v; exact Or.inl nb
      by_cases hvz : v = z
      · subst v; exact Or.inr (Or.inl ⟨(y, 0), (y, 1), by simp, nz⟩)
      by_cases hvz' : v = z'
      · subst v; exact Or.inr (Or.inl ⟨(y₀, i₀), (y₁, i₁), by simpa using q24, nz'⟩)
      rw [loc v ha hb hvz hvz']; exact bd.other v (by simp)
    · intro e he v hv
      rw [unO] at hv
      obtain ⟨e', he', hne, hat⟩ := bd.done_iso e he v hv
      have hm : (.inl e : Tok V) ∈ tokAtP S pos v :=
        mem_tokAtP.mpr ⟨(mem_tokens_inl e).mpr (mem_sdiff.mp he).1, hv⟩
      have hna : v ≠ a₀ := by intro hv'; rw [hv', at₀] at hm; simp at hm
      have hnb : v ≠ a₁ := by intro hv'; rw [hv', at₁] at hm; simp at hm
      have hvZ := ph.supp _ ((mem_tokens_inl e).mpr (mem_sdiff.mp he).1) _ hv
      exact ⟨e', he', hne, by rw [loc v hna hnb (ne_of_notMem' hvZ hz)
        (ne_of_notMem' hvZ hz')]; exact hat⟩
    · have heq : (S.Y \ ∅).image (fun e => pos' (.inl e)) =
          (S.Y \ ∅).image (fun e => pos (.inl e)) := image_congr fun e _ => unO e
      rw [heq]; exact bd.done_decomp
  have persist : ∀ y' ∈ S.A, Closed S pos y' → Closed S pos' y' := by
    intro y' hy' hc
    obtain ⟨h, hc0, hc1⟩ := hc
    have ma : (.inr (y, 0) : Tok V) ∈ tokAtP S pos a₀ := by simp [at₀]
    have mb : (.inr (y, 1) : Tok V) ∈ tokAtP S pos a₁ := by simp [at₁]
    obtain ⟨hna, hnb⟩ := closed_carrier_ne bd hy' hp0 hp1 hab ma mb hc0 hc1
    have pc0 : pos (.inr (y', 0)) = s(h, catV S y' 0) := by simpa [catV] using hc0
    have pc1 : pos (.inr (y', 1)) = s(h, catV S y' 1) := by simpa [catV] using hc1
    refine ⟨h, ?_, ?_⟩
    · rw [unK _ (tok_ne_of pc0 p0 hna) (tok_ne_of pc0 hp₀ hna)
        (tok_ne_of pc0 p1 hnb) (tok_ne_of pc0 hp₁ hnb)]; exact hc0
    · rw [unK _ (tok_ne_of pc1 p0 hna) (tok_ne_of pc1 hp₀ hna)
        (tok_ne_of pc1 p1 hnb) (tok_ne_of pc1 hp₁ hnb)]; exact hc1
  refine ⟨pos', U', insert z (insert z' Z), ph', bd', ⟨z, v0, v1⟩, persist, unO, un2,
    hUU, hUc, ?_, ?_, tr, cont⟩
  · exact subset_insert _ _ |>.trans (subset_insert _ _)
  · have h1 := card_insert_le z (insert z' Z)
    have h2 := card_insert_le z' Z
    omega

end PartitionedTriangleAbsorption.CleanupStage100
