/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutLocalStage94
public import PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

/-! # The boundary invariant between complete triple cuts

Tokens are those of the accepted insertion return,
`S.tokens = Y.disjSum (A × univ)`: original tokens `inl e` and catalytic
tokens `inr (y, i)`. A *token state* is an arbitrary position map
`pos : Tok V → Sym2 V`; `R ⊆ Y` is the set of original tokens not yet cut.

`Bdry p F S pos R` is the invariant at complete-triple boundaries:

* every endpoint `v` of a remaining original token `e` is a *carrier*: exactly
  `e` and one catalytic token `(y, i)`, `i ≠ 2`, sit at `v`, and that token is
  `v – catV S y i` (where `catV S y 0 = cs y`, `catV S y 1 = ct y`);
* the old catalytic vertices `cs y`, `ct y` carry exactly `(y,0),(y,2)` and
  `(y,1),(y,2)`; the catalytic handle tokens are `h – cs y`, `h' – ct y`,
  `cs y – ct y` with `p h = p h' = p y`;
* every other vertex carries nothing, exactly two catalytic tokens, or exactly
  two finished original tokens;
* finished original tokens sit at vertices carrying exactly two finished
  original tokens, and the finished original edges decompose into allowed
  triangles.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- Original tokens `inl e` and catalytic tokens `inr (y, i)`. -/
abbrev Tok (V : Type*) := Sym2 V ⊕ (V × Fin 3)

/-- The tokens sitting at `v` under the position map `pos`. -/
def tokAtP (S : Data V) (pos : Tok V → Sym2 V) (v : V) : Finset (Tok V) :=
  S.tokens.filter fun q => v ∈ pos q

/-- The catalytic endpoint of the catalytic token `(y, i)`, `i ≠ 2`. -/
def catV (S : Data V) (y : V) (i : Fin 3) : V := if i = 0 then S.cs y else S.ct y

/-- **The boundary invariant** after a number of complete triple cuts;
`R` is the set of original tokens still to be cut. -/
structure Bdry (p : V → Fin t) (F : Finset (Multiset (Fin t))) (S : Data V)
    (pos : Tok V → Sym2 V) (R : Finset (Sym2 V)) : Prop where
  rem : R ⊆ S.Y
  /-- A remaining original token keeps its endpoint-label type. -/
  type : ∀ e ∈ R, Sym2.map p (pos (.inl e)) = Sym2.map p e
  /-- Carriers: exactly one remaining original and one catalytic token. -/
  carrier : ∀ e ∈ R, ∀ v ∈ pos (.inl e), ∃ y ∈ S.A, ∃ i : Fin 3, i ≠ 2 ∧
    pos (.inr (y, i)) = s(v, catV S y i) ∧ tokAtP S pos v = {.inl e, .inr (y, i)}
  at_cs : ∀ y ∈ S.A, tokAtP S pos (S.cs y) = {.inr (y, 0), .inr (y, 2)}
  at_ct : ∀ y ∈ S.A, tokAtP S pos (S.ct y) = {.inr (y, 1), .inr (y, 2)}
  /-- Catalytic handles keep their catalytic endpoint, and the other endpoint
  has the label of the old active vertex. -/
  handle : ∀ y ∈ S.A, ∀ i : Fin 3, i ≠ 2 →
    ∃ h, pos (.inr (y, i)) = s(h, catV S y i) ∧ p h = p y
  handle₂ : ∀ y ∈ S.A, pos (.inr (y, 2)) = s(S.cs y, S.ct y)
  /-- Every non-carrier vertex is empty, catalytic, or a finished-triangle vertex. -/
  other : ∀ v, (∀ e ∈ R, v ∉ pos (.inl e)) →
    tokAtP S pos v = ∅ ∨
    (∃ κ κ' : V × Fin 3, κ ≠ κ' ∧ tokAtP S pos v = {.inr κ, .inr κ'}) ∨
    (∃ e e', e ∈ S.Y \ R ∧ e' ∈ S.Y \ R ∧ e ≠ e' ∧ tokAtP S pos v = {.inl e, .inl e'})
  /-- Finished original tokens are isolated from everything else. -/
  done_iso : ∀ e ∈ S.Y \ R, ∀ v ∈ pos (.inl e), ∃ e', e' ∈ S.Y \ R ∧ e' ≠ e ∧
    tokAtP S pos v = {.inl e, .inl e'}
  /-- The finished original edges decompose into allowed triangles. -/
  done_decomp : HasDecomp p F ((S.Y \ R).image fun e => pos (.inl e))

section basic

variable {S : Data V} {pos : Tok V → Sym2 V}

theorem mem_tokAtP {v : V} {q : Tok V} :
    q ∈ tokAtP S pos v ↔ q ∈ S.tokens ∧ v ∈ pos q := mem_filter

omit [DecidableEq V] in
theorem catV_zero (y : V) : catV S y 0 = S.cs y := by simp [catV]

omit [DecidableEq V] in
theorem catV_one (y : V) : catV S y 1 = S.ct y := by simp [catV]

omit [DecidableEq V] in
/-- Orientation of an unordered pair with prescribed label type. -/
theorem orient {p : V → Fin t} {x : Sym2 V} {i j : Fin t} (h : Sym2.map p x = s(i, j)) :
    ∃ u v, x = s(u, v) ∧ p u = i ∧ p v = j := by
  induction x using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, b, rfl, h1, h2⟩
    · exact ⟨b, a, Sym2.eq_swap, h2, h1⟩

end basic

section derived

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {S : Data V}
  {pos : Tok V → Sym2 V} {R : Finset (Sym2 V)}

/-- A carrier is never an old catalytic vertex. -/
theorem Bdry.carrier_ne_catV (bd : Bdry p F S pos R) {e : Sym2 V} (he : e ∈ R) {v : V}
    (hv : v ∈ pos (.inl e)) {y : V} (hy : y ∈ S.A) (i : Fin 3) : v ≠ catV S y i := by
  intro h
  have hm : (.inl e : Tok V) ∈ tokAtP S pos v :=
    mem_tokAtP.mpr ⟨(mem_tokens_inl e).mpr (bd.rem he), hv⟩
  unfold catV at h
  split_ifs at h
  · rw [h, bd.at_cs y hy] at hm
    simp at hm
  · rw [h, bd.at_ct y hy] at hm
    simp at hm

/-- Carriers of different remaining original tokens are different vertices. -/
theorem Bdry.carrier_ne (bd : Bdry p F S pos R) {e e' : Sym2 V} (he : e ∈ R) (he' : e' ∈ R)
    (hne : e ≠ e') {v v' : V} (hv : v ∈ pos (.inl e)) (hv' : v' ∈ pos (.inl e')) : v ≠ v' := by
  rintro rfl
  obtain ⟨y, -, i, -, -, hat⟩ := bd.carrier e he v hv
  have hm : (.inl e' : Tok V) ∈ tokAtP S pos v :=
    mem_tokAtP.mpr ⟨(mem_tokens_inl e').mpr (bd.rem he'), hv'⟩
  rw [hat] at hm
  simp only [mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false] at hm
  exact hne hm.symm

/-- The catalytic endpoints at two different carriers are different. -/
theorem Bdry.catV_ne (bd : Bdry p F S pos R) {v v' y y' : V} {i i' : Fin 3}
    (hy' : y' ∈ S.A) (hi' : i' ≠ 2) (hy : y ∈ S.A) (hi : i ≠ 2)
    (hp : pos (.inr (y, i)) = s(v, catV S y i)) (hp' : pos (.inr (y', i')) = s(v', catV S y' i'))
    (hvv : v ≠ v') : catV S y i ≠ catV S y' i' := by
  intro h
  have hm : (.inr (y', i') : Tok V) ∈ tokAtP S pos (catV S y i) :=
    mem_tokAtP.mpr ⟨(mem_tokens_inr y' i').mpr hy', by rw [hp', ← h]; exact Sym2.mem_mk_right _ _⟩
  have key : (y', i') = (y, i) → False := by
    intro hyi
    simp only [Prod.mk.injEq] at hyi
    obtain ⟨rfl, rfl⟩ := hyi
    rw [hp] at hp'
    exact hvv (Sym2.congr_left.mp hp')
  unfold catV at hm
  split_ifs at hm with hi0
  · rw [bd.at_cs y hy] at hm
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
    · exact key (by rw [hi0])
    · exact hi' rfl
  · rw [bd.at_ct y hy] at hm
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, hi1⟩ | ⟨-, rfl⟩
    · have : i = 1 := by fin_cases i <;> simp_all
      exact key (by rw [hi1, this])
    · exact hi' rfl

/-- **Separation (i).** Every catalytic token has an old catalytic endpoint. -/
theorem Bdry.catalytic_endpoint (bd : Bdry p F S pos R) {y : V} (hy : y ∈ S.A) (i : Fin 3) :
    S.cs y ∈ pos (.inr (y, i)) ∨ S.ct y ∈ pos (.inr (y, i)) := by
  by_cases hi : i = 2
  · subst hi
    rw [bd.handle₂ y hy]
    exact Or.inl (Sym2.mem_mk_left _ _)
  · obtain ⟨h, hp, -⟩ := bd.handle y hy i hi
    unfold catV at hp
    split_ifs at hp
    · exact Or.inl (hp ▸ Sym2.mem_mk_right _ _)
    · exact Or.inr (hp ▸ Sym2.mem_mk_right _ _)

/-- **Separation (ii).** An old catalytic vertex `catV S y i` is joined by a
token to at most one carrier of a remaining original token. -/
theorem Bdry.one_carrier (bd : Bdry p F S pos R) {y : V} (hy : y ∈ S.A) (i : Fin 3)
    {e e' : Sym2 V} (he : e ∈ R) (he' : e' ∈ R) {v v' : V} (hv : v ∈ pos (.inl e))
    (hv' : v' ∈ pos (.inl e')) {q q' : Tok V} (hq : q ∈ S.tokens) (hq' : q' ∈ S.tokens)
    (hpq : pos q = s(catV S y i, v)) (hpq' : pos q' = s(catV S y i, v')) : v = v' := by
  have hm : q ∈ tokAtP S pos (catV S y i) :=
    mem_tokAtP.mpr ⟨hq, by rw [hpq]; exact Sym2.mem_mk_left _ _⟩
  have hm' : q' ∈ tokAtP S pos (catV S y i) :=
    mem_tokAtP.mpr ⟨hq', by rw [hpq']; exact Sym2.mem_mk_left _ _⟩
  have nv := bd.carrier_ne_catV he hv hy
  have nv' := bd.carrier_ne_catV he' hv' hy
  unfold catV at hm hm' hpq hpq' nv nv'
  split_ifs at hm hm' hpq hpq' nv nv' with hi
  · rw [bd.at_cs y hy] at hm hm'
    simp only [mem_insert, mem_singleton] at hm hm'
    have h2 : pos (.inr (y, 2)) = s(S.cs y, S.ct y) := bd.handle₂ y hy
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
    · rw [hpq] at hpq'
      exact Sym2.congr_right.mp hpq'
    · rw [hpq', Sym2.congr_right] at h2
      exact absurd h2 (nv' 1)
    · rw [hpq, Sym2.congr_right] at h2
      exact absurd h2 (nv 1)
    · rw [hpq] at hpq'
      exact Sym2.congr_right.mp hpq'
  · rw [bd.at_ct y hy] at hm hm'
    simp only [mem_insert, mem_singleton] at hm hm'
    have h2 : pos (.inr (y, 2)) = s(S.ct y, S.cs y) := by rw [bd.handle₂ y hy, Sym2.eq_swap]
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
    · rw [hpq] at hpq'
      exact Sym2.congr_right.mp hpq'
    · rw [hpq', Sym2.congr_right] at h2
      exact absurd h2 (nv' 0)
    · rw [hpq, Sym2.congr_right] at h2
      exact absurd h2 (nv 0)
    · rw [hpq] at hpq'
      exact Sym2.congr_right.mp hpq'

end derived

end PartitionedTriangleAbsorption.TripleCutStage94
