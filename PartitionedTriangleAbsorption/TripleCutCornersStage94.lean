/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutExchangeStage94

/-! # Three corner exchanges cutting one triple of tokens

Nine tokens of an arbitrary physical token state are given: three edge tokens
`E₁ = A₁B₁`, `E₂ = B₂C₂`, `E₃ = C₃A₃` and, at each of the six endpoints `X`,
one further token `K_X = X w_X`. The twelve vertices are distinct and the
corner labels agree, `p B₂ = p B₁`, `p C₃ = p C₂`, `p A₁ = p A₃`.

Three token-tracked exchanges (`token_exchange`) are applied:

* at `B`, roots `(B₁, B₂, A₁, w_B₁, C₂, w_B₂)`: the new vertex `z_B` receives
  the `B`-ends of `E₁, E₂`, the new vertex `z'_B` those of `K_B₁, K_B₂`;
* at `C`, roots `(C₂, C₃, z_B, w_C₂, A₃, w_C₃)`;
* at `A`, roots `(A₃, A₁, z_C, w_A₃, z_B, w_A₁)`.

Afterwards `E₁ = z_A z_B`, `E₂ = z_C z_B`, `E₃ = z_A z_C` form a triangle on
three new vertices, the six side tokens hang at `z'_X w_X`, and every other
token is where it was. The intermediate vertex `z_B` (after the first
exchange) carries two edge tokens; distinctness of all roots at the second
and third exchanges is derived from the freshness of `z_B, z'_B, z_C, z'_C`
for the full active set.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer PhysicalMovesStage86

/-- Close a disequality from distinctness and freshness facts in context. -/
local macro "dst" : tactic =>
  `(tactic| first
    | assumption
    | exact Ne.symm ‹_›
    | exact ne_of_mem_of_not_mem ‹_› ‹_›
    | exact (ne_of_mem_of_not_mem ‹_› ‹_›).symm)

/-- Two unordered pairs differ, by distinctness facts in context. -/
local macro "sym2ne" : tactic =>
  `(tactic| (rw [Ne, Sym2.eq_iff]; rintro (⟨h, h'⟩ | ⟨h, h'⟩) <;> first
      | exact absurd h ‹_› | exact absurd h' ‹_› | exact absurd h.symm ‹_›
      | exact absurd h'.symm ‹_›))

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ} {τ : Type*} [DecidableEq τ]

omit [DecidableEq τ] in
/-- **The three corner exchanges of one triple.** -/
theorem three_exchanges {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    {toks : Finset τ} {pos : τ → Sym2 V} {U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B toks pos U Z)
    {E₁ E₂ E₃ KA₁ KB₁ KB₂ KC₂ KC₃ KA₃ : τ}
    (mE₁ : E₁ ∈ toks) (mE₂ : E₂ ∈ toks) (mE₃ : E₃ ∈ toks) (mA₁ : KA₁ ∈ toks)
    (mB₁ : KB₁ ∈ toks) (mB₂ : KB₂ ∈ toks) (mC₂ : KC₂ ∈ toks) (mC₃ : KC₃ ∈ toks)
    (mA₃ : KA₃ ∈ toks)
    {A₁ B₁ B₂ C₂ C₃ A₃ wA₁ wB₁ wB₂ wC₂ wC₃ wA₃ : V}
    (nd : [A₁, B₁, B₂, C₂, C₃, A₃, wA₁, wB₁, wB₂, wC₂, wC₃, wA₃].Nodup)
    (pE₁ : pos E₁ = s(A₁, B₁)) (pE₂ : pos E₂ = s(B₂, C₂)) (pE₃ : pos E₃ = s(C₃, A₃))
    (pA₁ : pos KA₁ = s(A₁, wA₁)) (pB₁ : pos KB₁ = s(B₁, wB₁)) (pB₂ : pos KB₂ = s(B₂, wB₂))
    (pC₂ : pos KC₂ = s(C₂, wC₂)) (pC₃ : pos KC₃ = s(C₃, wC₃)) (pA₃ : pos KA₃ = s(A₃, wA₃))
    (lB : p B₂ = p B₁) (lC : p C₃ = p C₂) (lA : p A₁ = p A₃)
    (hb : 234 + (Z.card : ℝ) + 4 * (d + U.card) < a) :
    ∃ (zA zB zC z'A z'B z'C : V) (pos' : τ → Sym2 V) (U' : Finset (Sym2 V)),
      (zA ∉ Z ∧ zB ∉ Z ∧ zC ∉ Z ∧ z'A ∉ Z ∧ z'B ∉ Z ∧ z'C ∉ Z) ∧
      [zA, zB, zC, z'A, z'B, z'C].Nodup ∧
      (p zA = p A₃ ∧ p z'A = p A₃ ∧ p zB = p B₁ ∧ p z'B = p B₁ ∧ p zC = p C₂ ∧
        p z'C = p C₂) ∧
      (pos' E₁ = s(zA, zB) ∧ pos' E₂ = s(zC, zB) ∧ pos' E₃ = s(zA, zC)) ∧
      (pos' KA₁ = s(z'A, wA₁) ∧ pos' KB₁ = s(z'B, wB₁) ∧ pos' KB₂ = s(z'B, wB₂) ∧
        pos' KC₂ = s(z'C, wC₂) ∧ pos' KC₃ = s(z'C, wC₃) ∧ pos' KA₃ = s(z'A, wA₃)) ∧
      (∀ q, q ≠ E₁ → q ≠ E₂ → q ≠ E₃ → q ≠ KA₁ → q ≠ KB₁ → q ≠ KB₂ → q ≠ KC₂ →
        q ≠ KC₃ → q ≠ KA₃ → pos' q = pos q) ∧
      Phys p F G B toks pos' U'
        (insert zA (insert z'A (insert zC (insert z'C (insert zB (insert z'B Z)))))) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 81 ∧
      PhysicalMoves p F G.edgeFinset B U (toks.image pos) (toks.image pos') 9 ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U' (toks.image pos') W k →
        PhysicalMoves p F G.edgeFinset B U (toks.image pos) W (9 + k) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at nd
  casesm* _ ∧ _
  have tne : ∀ {q q' : τ}, pos q ≠ pos q' → q ≠ q' := by
    rintro q q' h rfl
    exact h rfl
  have t_E1_E2 : E₁ ≠ E₂ := tne (by rw [pE₁, pE₂]; sym2ne)
  have t_E1_E3 : E₁ ≠ E₃ := tne (by rw [pE₁, pE₃]; sym2ne)
  have t_E1_KA1 : E₁ ≠ KA₁ := tne (by rw [pE₁, pA₁]; sym2ne)
  have t_E1_KB1 : E₁ ≠ KB₁ := tne (by rw [pE₁, pB₁]; sym2ne)
  have t_E1_KB2 : E₁ ≠ KB₂ := tne (by rw [pE₁, pB₂]; sym2ne)
  have t_E1_KC2 : E₁ ≠ KC₂ := tne (by rw [pE₁, pC₂]; sym2ne)
  have t_E1_KC3 : E₁ ≠ KC₃ := tne (by rw [pE₁, pC₃]; sym2ne)
  have t_E1_KA3 : E₁ ≠ KA₃ := tne (by rw [pE₁, pA₃]; sym2ne)
  have t_E2_E3 : E₂ ≠ E₃ := tne (by rw [pE₂, pE₃]; sym2ne)
  have t_E2_KA1 : E₂ ≠ KA₁ := tne (by rw [pE₂, pA₁]; sym2ne)
  have t_E2_KB1 : E₂ ≠ KB₁ := tne (by rw [pE₂, pB₁]; sym2ne)
  have t_E2_KB2 : E₂ ≠ KB₂ := tne (by rw [pE₂, pB₂]; sym2ne)
  have t_E2_KC2 : E₂ ≠ KC₂ := tne (by rw [pE₂, pC₂]; sym2ne)
  have t_E2_KC3 : E₂ ≠ KC₃ := tne (by rw [pE₂, pC₃]; sym2ne)
  have t_E2_KA3 : E₂ ≠ KA₃ := tne (by rw [pE₂, pA₃]; sym2ne)
  have t_E3_KA1 : E₃ ≠ KA₁ := tne (by rw [pE₃, pA₁]; sym2ne)
  have t_E3_KB1 : E₃ ≠ KB₁ := tne (by rw [pE₃, pB₁]; sym2ne)
  have t_E3_KB2 : E₃ ≠ KB₂ := tne (by rw [pE₃, pB₂]; sym2ne)
  have t_E3_KC2 : E₃ ≠ KC₂ := tne (by rw [pE₃, pC₂]; sym2ne)
  have t_E3_KC3 : E₃ ≠ KC₃ := tne (by rw [pE₃, pC₃]; sym2ne)
  have t_E3_KA3 : E₃ ≠ KA₃ := tne (by rw [pE₃, pA₃]; sym2ne)
  have t_KA1_KB1 : KA₁ ≠ KB₁ := tne (by rw [pA₁, pB₁]; sym2ne)
  have t_KA1_KB2 : KA₁ ≠ KB₂ := tne (by rw [pA₁, pB₂]; sym2ne)
  have t_KA1_KC2 : KA₁ ≠ KC₂ := tne (by rw [pA₁, pC₂]; sym2ne)
  have t_KA1_KC3 : KA₁ ≠ KC₃ := tne (by rw [pA₁, pC₃]; sym2ne)
  have t_KA1_KA3 : KA₁ ≠ KA₃ := tne (by rw [pA₁, pA₃]; sym2ne)
  have t_KB1_KB2 : KB₁ ≠ KB₂ := tne (by rw [pB₁, pB₂]; sym2ne)
  have t_KB1_KC2 : KB₁ ≠ KC₂ := tne (by rw [pB₁, pC₂]; sym2ne)
  have t_KB1_KC3 : KB₁ ≠ KC₃ := tne (by rw [pB₁, pC₃]; sym2ne)
  have t_KB1_KA3 : KB₁ ≠ KA₃ := tne (by rw [pB₁, pA₃]; sym2ne)
  have t_KB2_KC2 : KB₂ ≠ KC₂ := tne (by rw [pB₂, pC₂]; sym2ne)
  have t_KB2_KC3 : KB₂ ≠ KC₃ := tne (by rw [pB₂, pC₃]; sym2ne)
  have t_KB2_KA3 : KB₂ ≠ KA₃ := tne (by rw [pB₂, pA₃]; sym2ne)
  have t_KC2_KC3 : KC₂ ≠ KC₃ := tne (by rw [pC₂, pC₃]; sym2ne)
  have t_KC2_KA3 : KC₂ ≠ KA₃ := tne (by rw [pC₂, pA₃]; sym2ne)
  have t_KC3_KA3 : KC₃ ≠ KA₃ := tne (by rw [pC₃, pA₃]; sym2ne)
  have inZ : ∀ {q : τ}, q ∈ toks → ∀ {u v : V}, pos q = s(u, v) → u ∈ Z ∧ v ∈ Z :=
    fun hq _ _ h => ⟨ph.supp _ hq _ (h ▸ Sym2.mem_mk_left _ _),
      ph.supp _ hq _ (h ▸ Sym2.mem_mk_right _ _)⟩
  have zA₁ := (inZ mE₁ pE₁).1
  have zB₁ := (inZ mE₁ pE₁).2
  have zB₂ := (inZ mE₂ pE₂).1
  have zC₂ := (inZ mE₂ pE₂).2
  have zC₃ := (inZ mE₃ pE₃).1
  have zA₃ := (inZ mE₃ pE₃).2
  have zwA₁ := (inZ mA₁ pA₁).2
  have zwB₁ := (inZ mB₁ pB₁).2
  have zwB₂ := (inZ mB₂ pB₂).2
  have zwC₂ := (inZ mC₂ pC₂).2
  have zwC₃ := (inZ mC₃ pC₃).2
  have zwA₃ := (inZ mA₃ pA₃).2
  have hZ0 : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
  -- exchange at the corner B
  obtain ⟨zB, z'B, U₁, hzB, hz'B, hzzB, lzB, lz'B, ph₁, hUU₁, hU₁, htr₁, hc₁⟩ :=
    token_exchange a d hF hs hB hd ph (r₀ := B₁) (r₁ := B₂) (r₂ := A₁) (r₃ := wB₁)
      (r₄ := C₂) (r₅ := wB₂)
      (by
        unfold PhysicalHingeSupply.SixDistinct
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dst)
      lB mE₁ mB₁ mE₂ mB₂ (by rw [pE₁, Sym2.eq_swap]) pB₁ pE₂ pB₂ (by linarith)
  set pos₁ := move4 pos E₁ KB₁ E₂ KB₂ s(zB, A₁) s(z'B, wB₁) s(zB, C₂) s(z'B, wB₂) with hpos₁
  have hv₁ : pos₁ E₁ = s(zB, A₁) ∧ pos₁ KB₁ = s(z'B, wB₁) ∧ pos₁ E₂ = s(zB, C₂) ∧
      pos₁ KB₂ = s(z'B, wB₂) :=
    move4_vals (pos := pos) (e₁ := s(zB, A₁)) (e₂ := s(z'B, wB₁)) (e₃ := s(zB, C₂))
    (e₄ := s(z'B, wB₂)) (q₁ := E₁) (q₂ := KB₁) (q₃ := E₂) (q₄ := KB₂)
    (by dst) (by dst) (by dst) (by dst) (by dst) (by dst)
  have k1 : ∀ q, q ≠ E₁ → q ≠ KB₁ → q ≠ E₂ → q ≠ KB₂ → pos₁ q = pos q :=
    fun _ h₁ h₂ h₃ h₄ => move4_of_ne h₁ h₂ h₃ h₄
  have hU₁r : (U₁.card : ℝ) ≤ U.card + 27 := by exact_mod_cast hU₁
  have hZ₁r : ((insert zB (insert z'B Z)).card : ℝ) ≤ Z.card + 2 := by
    have h1 := card_insert_le zB (insert z'B Z)
    have h2 := card_insert_le z'B Z
    exact_mod_cast (show (insert zB (insert z'B Z)).card ≤ Z.card + 2 by omega)
  -- exchange at the corner C
  obtain ⟨zC, z'C, U₂, hzC, hz'C, hzzC, lzC, lz'C, ph₂, hUU₂, hU₂, htr₂, hc₂⟩ :=
    token_exchange a d hF hs hB hd ph₁ (r₀ := C₂) (r₁ := C₃) (r₂ := zB) (r₃ := wC₂)
      (r₄ := A₃) (r₅ := wC₃)
      (by
        unfold PhysicalHingeSupply.SixDistinct
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dst)
      lC mE₂ mC₂ mE₃ mC₃ (by rw [hv₁.2.2.1, Sym2.eq_swap])
      (by rw [k1 _ (by dst) (by dst) (by dst) (by dst), pC₂])
      (by rw [k1 _ (by dst) (by dst) (by dst) (by dst), pE₃])
      (by rw [k1 _ (by dst) (by dst) (by dst) (by dst), pC₃]) (by linarith)
  simp only [mem_insert, not_or] at hzC hz'C
  obtain ⟨hzCB, hzCB', hzC⟩ := hzC
  obtain ⟨hz'CB, hz'CB', hz'C⟩ := hz'C
  set pos₂ := move4 pos₁ E₂ KC₂ E₃ KC₃ s(zC, zB) s(z'C, wC₂) s(zC, A₃) s(z'C, wC₃) with hpos₂
  have hv₂ : pos₂ E₂ = s(zC, zB) ∧ pos₂ KC₂ = s(z'C, wC₂) ∧ pos₂ E₃ = s(zC, A₃) ∧
      pos₂ KC₃ = s(z'C, wC₃) := move4_vals (pos := pos₁) (e₁ := s(zC, zB)) (e₂ := s(z'C, wC₂))
    (e₃ := s(zC, A₃)) (e₄ := s(z'C, wC₃)) (q₁ := E₂) (q₂ := KC₂) (q₃ := E₃) (q₄ := KC₃)
    (by dst) (by dst) (by dst) (by dst) (by dst) (by dst)
  have k2 : ∀ q, q ≠ E₂ → q ≠ KC₂ → q ≠ E₃ → q ≠ KC₃ → pos₂ q = pos₁ q :=
    fun _ h₁ h₂ h₃ h₄ => move4_of_ne h₁ h₂ h₃ h₄
  have hU₂r : (U₂.card : ℝ) ≤ U.card + 54 := by
    have : (U₂.card : ℝ) ≤ U₁.card + 27 := by exact_mod_cast hU₂
    linarith
  have hZ₂r : ((insert zC (insert z'C (insert zB (insert z'B Z)))).card : ℝ) ≤ Z.card + 4 := by
    have h1 := card_insert_le zC (insert z'C (insert zB (insert z'B Z)))
    have h2 := card_insert_le z'C (insert zB (insert z'B Z))
    have h3 := card_insert_le zB (insert z'B Z)
    have h4 := card_insert_le z'B Z
    exact_mod_cast (show (insert zC (insert z'C (insert zB (insert z'B Z)))).card ≤ Z.card + 4
      by omega)
  -- exchange at the corner A
  obtain ⟨zA, z'A, U₃, hzA, hz'A, hzzA, lzA, lz'A, ph₃, hUU₃, hU₃, htr₃, hc₃⟩ :=
    token_exchange a d hF hs hB hd ph₂ (r₀ := A₃) (r₁ := A₁) (r₂ := zC) (r₃ := wA₃)
      (r₄ := zB) (r₅ := wA₁)
      (by
        unfold PhysicalHingeSupply.SixDistinct
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dst)
      lA mE₃ mA₃ mE₁ mA₁ (by rw [hv₂.2.2.1, Sym2.eq_swap])
      (by rw [k2 _ (by dst) (by dst) (by dst) (by dst), k1 _ (by dst) (by dst) (by dst) (by dst),
        pA₃])
      (by rw [k2 _ (by dst) (by dst) (by dst) (by dst), hv₁.1, Sym2.eq_swap])
      (by rw [k2 _ (by dst) (by dst) (by dst) (by dst), k1 _ (by dst) (by dst) (by dst) (by dst),
        pA₁]) (by linarith)
  simp only [mem_insert, not_or] at hzA hz'A
  obtain ⟨hzAC, hzAC', hzAB, hzAB', hzA⟩ := hzA
  obtain ⟨hz'AC, hz'AC', hz'AB, hz'AB', hz'A⟩ := hz'A
  set pos₃ := move4 pos₂ E₃ KA₃ E₁ KA₁ s(zA, zC) s(z'A, wA₃) s(zA, zB) s(z'A, wA₁) with hpos₃
  have hv₃ : pos₃ E₃ = s(zA, zC) ∧ pos₃ KA₃ = s(z'A, wA₃) ∧ pos₃ E₁ = s(zA, zB) ∧
      pos₃ KA₁ = s(z'A, wA₁) := move4_vals (pos := pos₂) (e₁ := s(zA, zC)) (e₂ := s(z'A, wA₃))
    (e₃ := s(zA, zB)) (e₄ := s(z'A, wA₁)) (q₁ := E₃) (q₂ := KA₃) (q₃ := E₁) (q₄ := KA₁)
    (by dst) (by dst) (by dst) (by dst) (by dst) (by dst)
  have k3 : ∀ q, q ≠ E₃ → q ≠ KA₃ → q ≠ E₁ → q ≠ KA₁ → pos₃ q = pos₂ q :=
    fun _ h₁ h₂ h₃ h₄ => move4_of_ne h₁ h₂ h₃ h₄
  refine ⟨zA, zB, zC, z'A, z'B, z'C, pos₃, U₃, ⟨hzA, hzB, hzC, hz'A, hz'B, hz'C⟩, ?_,
    ⟨lzA, lz'A, lzB, lz'B, lzC, lz'C⟩, ⟨hv₃.2.2.1, ?_, hv₃.1⟩, ⟨hv₃.2.2.2, ?_, ?_, ?_, ?_,
      hv₃.2.1⟩, ?_, ph₃, hUU₁.trans (hUU₂.trans hUU₃), by omega, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> dst
  · rw [k3 _ (by dst) (by dst) (by dst) (by dst), hv₂.1]
  · rw [k3 _ (by dst) (by dst) (by dst) (by dst), k2 _ (by dst) (by dst) (by dst) (by dst),
      hv₁.2.1]
  · rw [k3 _ (by dst) (by dst) (by dst) (by dst), k2 _ (by dst) (by dst) (by dst) (by dst),
      hv₁.2.2.2]
  · rw [k3 _ (by dst) (by dst) (by dst) (by dst), hv₂.2.1]
  · rw [k3 _ (by dst) (by dst) (by dst) (by dst), hv₂.2.2.2]
  · intro q c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉
    rw [k3 q c₃ c₉ c₁ c₄, k2 q c₂ c₇ c₃ c₈, k1 q c₁ c₅ c₂ c₆]
  · exact hc₁ _ _ (hc₂ _ _ htr₃)
  · intro W k h
    have h' := hc₁ _ _ (hc₂ _ _ (hc₃ W k h))
    rwa [show 3 + (3 + (3 + k)) = 9 + k by omega] at h'

end PartitionedTriangleAbsorption.TripleCutStage94
