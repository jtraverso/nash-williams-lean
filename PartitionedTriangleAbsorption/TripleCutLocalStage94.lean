/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutCornersStage94

/-! # Local effect of the three corner exchanges on token incidences

For an arbitrary token type, the tokens sitting at a vertex `v` are
`toks.filter (v ∈ pos ·)`. After the three corner exchanges of one triple
(`three_exchanges`):

* at a vertex that is neither one of the six old endpoints nor one of the six
  new vertices, exactly the same tokens sit as before;
* at each old endpoint `X` (where exactly `E_X` and `K_X` sat) no token sits;
* at `z_A, z_B, z_C` sit exactly two of the three edge tokens, and at
  `z'_A, z'_B, z'_C` exactly the two side tokens of that corner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset

variable {V : Type*} {τ : Type*}

theorem ne_of_notMem {a b : V} {s : Finset V} (ha : a ∉ s) (hb : b ∈ s) : a ≠ b :=
  fun h => ha (h ▸ hb)

theorem ne_of_notMem' {a b : V} {s : Finset V} (ha : a ∈ s) (hb : b ∉ s) : a ≠ b :=
  fun h => hb (h ▸ ha)

/-- Refute an equation `h` from distinctness and freshness facts in context. -/
local macro "kill " h:ident : tactic => `(tactic| first
  | exact absurd $h ‹_›
  | exact absurd ($h).symm ‹_›
  | exact absurd $h (ne_of_notMem ‹_› ‹_›)
  | exact absurd $h (ne_of_notMem' ‹_› ‹_›))

/-- Use or refute an equation `h`. -/
local macro "keep " h:ident : tactic => `(tactic| first
  | exact Or.inl $h
  | exact Or.inr $h
  | kill $h)

variable [DecidableEq V] [DecidableEq τ]

/-- **Token incidences after cutting one triple.** -/
theorem after_cut_local {toks : Finset τ} {pos pos' : τ → Sym2 V} {Z : Finset V}
    (hZ : ∀ q ∈ toks, ∀ v ∈ pos q, v ∈ Z)
    {E₁ E₂ E₃ KA₁ KB₁ KB₂ KC₂ KC₃ KA₃ : τ}
    (mE₁ : E₁ ∈ toks) (mE₂ : E₂ ∈ toks) (mE₃ : E₃ ∈ toks) (mA₁ : KA₁ ∈ toks)
    (mB₁ : KB₁ ∈ toks) (mB₂ : KB₂ ∈ toks) (mC₂ : KC₂ ∈ toks) (mC₃ : KC₃ ∈ toks)
    (mA₃ : KA₃ ∈ toks)
    {A₁ B₁ B₂ C₂ C₃ A₃ wA₁ wB₁ wB₂ wC₂ wC₃ wA₃ : V}
    (nd : [A₁, B₁, B₂, C₂, C₃, A₃, wA₁, wB₁, wB₂, wC₂, wC₃, wA₃].Nodup)
    (pE₁ : pos E₁ = s(A₁, B₁)) (pE₂ : pos E₂ = s(B₂, C₂)) (pE₃ : pos E₃ = s(C₃, A₃))
    (pA₁ : pos KA₁ = s(A₁, wA₁)) (pB₁ : pos KB₁ = s(B₁, wB₁)) (pB₂ : pos KB₂ = s(B₂, wB₂))
    (pC₂ : pos KC₂ = s(C₂, wC₂)) (pC₃ : pos KC₃ = s(C₃, wC₃)) (pA₃ : pos KA₃ = s(A₃, wA₃))
    {zA zB zC z'A z'B z'C : V}
    (hzA : zA ∉ Z) (hzB : zB ∉ Z) (hzC : zC ∉ Z) (hz'A : z'A ∉ Z) (hz'B : z'B ∉ Z)
    (hz'C : z'C ∉ Z) (nd' : [zA, zB, zC, z'A, z'B, z'C].Nodup)
    (vE₁ : pos' E₁ = s(zA, zB)) (vE₂ : pos' E₂ = s(zC, zB)) (vE₃ : pos' E₃ = s(zA, zC))
    (vA₁ : pos' KA₁ = s(z'A, wA₁)) (vB₁ : pos' KB₁ = s(z'B, wB₁))
    (vB₂ : pos' KB₂ = s(z'B, wB₂)) (vC₂ : pos' KC₂ = s(z'C, wC₂))
    (vC₃ : pos' KC₃ = s(z'C, wC₃)) (vA₃ : pos' KA₃ = s(z'A, wA₃))
    (untouched : ∀ q, q ≠ E₁ → q ≠ E₂ → q ≠ E₃ → q ≠ KA₁ → q ≠ KB₁ → q ≠ KB₂ → q ≠ KC₂ →
      q ≠ KC₃ → q ≠ KA₃ → pos' q = pos q)
    (atA₁ : toks.filter (fun q => A₁ ∈ pos q) = {E₁, KA₁})
    (atB₁ : toks.filter (fun q => B₁ ∈ pos q) = {E₁, KB₁})
    (atB₂ : toks.filter (fun q => B₂ ∈ pos q) = {E₂, KB₂})
    (atC₂ : toks.filter (fun q => C₂ ∈ pos q) = {E₂, KC₂})
    (atC₃ : toks.filter (fun q => C₃ ∈ pos q) = {E₃, KC₃})
    (atA₃ : toks.filter (fun q => A₃ ∈ pos q) = {E₃, KA₃}) :
    (∀ v, v ∉ [A₁, B₁, B₂, C₂, C₃, A₃] → v ∉ [zA, zB, zC, z'A, z'B, z'C] →
      toks.filter (fun q => v ∈ pos' q) = toks.filter (fun q => v ∈ pos q)) ∧
    (toks.filter (fun q => A₁ ∈ pos' q) = ∅ ∧ toks.filter (fun q => B₁ ∈ pos' q) = ∅ ∧
      toks.filter (fun q => B₂ ∈ pos' q) = ∅ ∧ toks.filter (fun q => C₂ ∈ pos' q) = ∅ ∧
      toks.filter (fun q => C₃ ∈ pos' q) = ∅ ∧ toks.filter (fun q => A₃ ∈ pos' q) = ∅) ∧
    (toks.filter (fun q => zA ∈ pos' q) = {E₃, E₁} ∧
      toks.filter (fun q => zB ∈ pos' q) = {E₁, E₂} ∧
      toks.filter (fun q => zC ∈ pos' q) = {E₂, E₃} ∧
      toks.filter (fun q => z'A ∈ pos' q) = {KA₃, KA₁} ∧
      toks.filter (fun q => z'B ∈ pos' q) = {KB₁, KB₂} ∧
      toks.filter (fun q => z'C ∈ pos' q) = {KC₂, KC₃}) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at nd nd'
  casesm* _ ∧ _
  have zA₁ : A₁ ∈ Z := hZ _ mE₁ _ (by rw [pE₁]; exact Sym2.mem_mk_left _ _)
  have zB₁ : B₁ ∈ Z := hZ _ mE₁ _ (by rw [pE₁]; exact Sym2.mem_mk_right _ _)
  have zB₂ : B₂ ∈ Z := hZ _ mE₂ _ (by rw [pE₂]; exact Sym2.mem_mk_left _ _)
  have zC₂ : C₂ ∈ Z := hZ _ mE₂ _ (by rw [pE₂]; exact Sym2.mem_mk_right _ _)
  have zC₃ : C₃ ∈ Z := hZ _ mE₃ _ (by rw [pE₃]; exact Sym2.mem_mk_left _ _)
  have zA₃ : A₃ ∈ Z := hZ _ mE₃ _ (by rw [pE₃]; exact Sym2.mem_mk_right _ _)
  have zwA₁ : wA₁ ∈ Z := hZ _ mA₁ _ (by rw [pA₁]; exact Sym2.mem_mk_right _ _)
  have zwB₁ : wB₁ ∈ Z := hZ _ mB₁ _ (by rw [pB₁]; exact Sym2.mem_mk_right _ _)
  have zwB₂ : wB₂ ∈ Z := hZ _ mB₂ _ (by rw [pB₂]; exact Sym2.mem_mk_right _ _)
  have zwC₂ : wC₂ ∈ Z := hZ _ mC₂ _ (by rw [pC₂]; exact Sym2.mem_mk_right _ _)
  have zwC₃ : wC₃ ∈ Z := hZ _ mC₃ _ (by rw [pC₃]; exact Sym2.mem_mk_right _ _)
  have zwA₃ : wA₃ ∈ Z := hZ _ mA₃ _ (by rw [pA₃]; exact Sym2.mem_mk_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hv'
    simp only [List.mem_cons, List.not_mem_nil, not_or, or_false] at hv hv'
    casesm* _ ∧ _
    ext q
    simp only [mem_filter]
    refine and_congr_right fun _ => ?_
    by_cases c1 : q = E₁
    · subst c1
      rw [vE₁, pE₁, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c2 : q = E₂
    · subst c2
      rw [vE₂, pE₂, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c3 : q = E₃
    · subst c3
      rw [vE₃, pE₃, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c4 : q = KA₁
    · subst c4
      rw [vA₁, pA₁, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c5 : q = KB₁
    · subst c5
      rw [vB₁, pB₁, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c6 : q = KB₂
    · subst c6
      rw [vB₂, pB₂, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c7 : q = KC₂
    · subst c7
      rw [vC₂, pC₂, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c8 : q = KC₃
    · subst c8
      rw [vC₃, pC₃, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    by_cases c9 : q = KA₃
    · subst c9
      rw [vA₃, pA₃, Sym2.mem_iff, Sym2.mem_iff]
      constructor <;> rintro (h | h) <;> keep h
    rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext q
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hq hX
      by_cases c1 : q = E₁
      · subst c1
        rw [vE₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c2 : q = E₂
      · subst c2
        rw [vE₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c3 : q = E₃
      · subst c3
        rw [vE₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c4 : q = KA₁
      · subst c4
        rw [vA₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c5 : q = KB₁
      · subst c5
        rw [vB₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c6 : q = KB₂
      · subst c6
        rw [vB₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c7 : q = KC₂
      · subst c7
        rw [vC₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c8 : q = KC₃
      · subst c8
        rw [vC₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c9 : q = KA₃
      · subst c9
        rw [vA₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hX
      have hm : q ∈ toks.filter (fun q => A₁ ∈ pos q) := mem_filter.mpr ⟨hq, hX⟩
      rw [atA₁, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm <;> contradiction
    · ext q
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hq hX
      by_cases c1 : q = E₁
      · subst c1
        rw [vE₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c2 : q = E₂
      · subst c2
        rw [vE₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c3 : q = E₃
      · subst c3
        rw [vE₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c4 : q = KA₁
      · subst c4
        rw [vA₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c5 : q = KB₁
      · subst c5
        rw [vB₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c6 : q = KB₂
      · subst c6
        rw [vB₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c7 : q = KC₂
      · subst c7
        rw [vC₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c8 : q = KC₃
      · subst c8
        rw [vC₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c9 : q = KA₃
      · subst c9
        rw [vA₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hX
      have hm : q ∈ toks.filter (fun q => B₁ ∈ pos q) := mem_filter.mpr ⟨hq, hX⟩
      rw [atB₁, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm <;> contradiction
    · ext q
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hq hX
      by_cases c1 : q = E₁
      · subst c1
        rw [vE₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c2 : q = E₂
      · subst c2
        rw [vE₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c3 : q = E₃
      · subst c3
        rw [vE₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c4 : q = KA₁
      · subst c4
        rw [vA₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c5 : q = KB₁
      · subst c5
        rw [vB₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c6 : q = KB₂
      · subst c6
        rw [vB₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c7 : q = KC₂
      · subst c7
        rw [vC₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c8 : q = KC₃
      · subst c8
        rw [vC₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c9 : q = KA₃
      · subst c9
        rw [vA₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hX
      have hm : q ∈ toks.filter (fun q => B₂ ∈ pos q) := mem_filter.mpr ⟨hq, hX⟩
      rw [atB₂, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm <;> contradiction
    · ext q
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hq hX
      by_cases c1 : q = E₁
      · subst c1
        rw [vE₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c2 : q = E₂
      · subst c2
        rw [vE₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c3 : q = E₃
      · subst c3
        rw [vE₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c4 : q = KA₁
      · subst c4
        rw [vA₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c5 : q = KB₁
      · subst c5
        rw [vB₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c6 : q = KB₂
      · subst c6
        rw [vB₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c7 : q = KC₂
      · subst c7
        rw [vC₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c8 : q = KC₃
      · subst c8
        rw [vC₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c9 : q = KA₃
      · subst c9
        rw [vA₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hX
      have hm : q ∈ toks.filter (fun q => C₂ ∈ pos q) := mem_filter.mpr ⟨hq, hX⟩
      rw [atC₂, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm <;> contradiction
    · ext q
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hq hX
      by_cases c1 : q = E₁
      · subst c1
        rw [vE₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c2 : q = E₂
      · subst c2
        rw [vE₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c3 : q = E₃
      · subst c3
        rw [vE₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c4 : q = KA₁
      · subst c4
        rw [vA₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c5 : q = KB₁
      · subst c5
        rw [vB₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c6 : q = KB₂
      · subst c6
        rw [vB₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c7 : q = KC₂
      · subst c7
        rw [vC₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c8 : q = KC₃
      · subst c8
        rw [vC₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c9 : q = KA₃
      · subst c9
        rw [vA₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hX
      have hm : q ∈ toks.filter (fun q => C₃ ∈ pos q) := mem_filter.mpr ⟨hq, hX⟩
      rw [atC₃, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm <;> contradiction
    · ext q
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hq hX
      by_cases c1 : q = E₁
      · subst c1
        rw [vE₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c2 : q = E₂
      · subst c2
        rw [vE₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c3 : q = E₃
      · subst c3
        rw [vE₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c4 : q = KA₁
      · subst c4
        rw [vA₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c5 : q = KB₁
      · subst c5
        rw [vB₁, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c6 : q = KB₂
      · subst c6
        rw [vB₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c7 : q = KC₂
      · subst c7
        rw [vC₂, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c8 : q = KC₃
      · subst c8
        rw [vC₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      by_cases c9 : q = KA₃
      · subst c9
        rw [vA₃, Sym2.mem_iff] at hX
        rcases hX with h | h <;> kill h
      rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hX
      have hm : q ∈ toks.filter (fun q => A₃ ∈ pos q) := mem_filter.mpr ⟨hq, hX⟩
      rw [atA₃, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm <;> contradiction
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext q
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hz⟩
        by_cases c1 : q = E₁
        · subst c1
          exact Or.inr rfl
        by_cases c2 : q = E₂
        · subst c2
          rw [vE₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c3 : q = E₃
        · subst c3
          exact Or.inl rfl
        by_cases c4 : q = KA₁
        · subst c4
          rw [vA₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c5 : q = KB₁
        · subst c5
          rw [vB₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c6 : q = KB₂
        · subst c6
          rw [vB₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c7 : q = KC₂
        · subst c7
          rw [vC₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c8 : q = KC₃
        · subst c8
          rw [vC₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c9 : q = KA₃
        · subst c9
          rw [vA₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hz
        exact absurd (hZ q hq _ hz) ‹_›
      · rintro (rfl | rfl)
        · exact ⟨‹_›, by rw [vE₃]; simp⟩
        · exact ⟨‹_›, by rw [vE₁]; simp⟩
    · ext q
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hz⟩
        by_cases c1 : q = E₁
        · subst c1
          exact Or.inl rfl
        by_cases c2 : q = E₂
        · subst c2
          exact Or.inr rfl
        by_cases c3 : q = E₃
        · subst c3
          rw [vE₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c4 : q = KA₁
        · subst c4
          rw [vA₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c5 : q = KB₁
        · subst c5
          rw [vB₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c6 : q = KB₂
        · subst c6
          rw [vB₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c7 : q = KC₂
        · subst c7
          rw [vC₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c8 : q = KC₃
        · subst c8
          rw [vC₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c9 : q = KA₃
        · subst c9
          rw [vA₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hz
        exact absurd (hZ q hq _ hz) ‹_›
      · rintro (rfl | rfl)
        · exact ⟨‹_›, by rw [vE₁]; simp⟩
        · exact ⟨‹_›, by rw [vE₂]; simp⟩
    · ext q
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hz⟩
        by_cases c1 : q = E₁
        · subst c1
          rw [vE₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c2 : q = E₂
        · subst c2
          exact Or.inl rfl
        by_cases c3 : q = E₃
        · subst c3
          exact Or.inr rfl
        by_cases c4 : q = KA₁
        · subst c4
          rw [vA₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c5 : q = KB₁
        · subst c5
          rw [vB₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c6 : q = KB₂
        · subst c6
          rw [vB₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c7 : q = KC₂
        · subst c7
          rw [vC₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c8 : q = KC₃
        · subst c8
          rw [vC₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c9 : q = KA₃
        · subst c9
          rw [vA₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hz
        exact absurd (hZ q hq _ hz) ‹_›
      · rintro (rfl | rfl)
        · exact ⟨‹_›, by rw [vE₂]; simp⟩
        · exact ⟨‹_›, by rw [vE₃]; simp⟩
    · ext q
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hz⟩
        by_cases c1 : q = E₁
        · subst c1
          rw [vE₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c2 : q = E₂
        · subst c2
          rw [vE₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c3 : q = E₃
        · subst c3
          rw [vE₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c4 : q = KA₁
        · subst c4
          exact Or.inr rfl
        by_cases c5 : q = KB₁
        · subst c5
          rw [vB₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c6 : q = KB₂
        · subst c6
          rw [vB₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c7 : q = KC₂
        · subst c7
          rw [vC₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c8 : q = KC₃
        · subst c8
          rw [vC₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c9 : q = KA₃
        · subst c9
          exact Or.inl rfl
        rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hz
        exact absurd (hZ q hq _ hz) ‹_›
      · rintro (rfl | rfl)
        · exact ⟨‹_›, by rw [vA₃]; simp⟩
        · exact ⟨‹_›, by rw [vA₁]; simp⟩
    · ext q
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hz⟩
        by_cases c1 : q = E₁
        · subst c1
          rw [vE₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c2 : q = E₂
        · subst c2
          rw [vE₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c3 : q = E₃
        · subst c3
          rw [vE₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c4 : q = KA₁
        · subst c4
          rw [vA₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c5 : q = KB₁
        · subst c5
          exact Or.inl rfl
        by_cases c6 : q = KB₂
        · subst c6
          exact Or.inr rfl
        by_cases c7 : q = KC₂
        · subst c7
          rw [vC₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c8 : q = KC₃
        · subst c8
          rw [vC₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c9 : q = KA₃
        · subst c9
          rw [vA₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hz
        exact absurd (hZ q hq _ hz) ‹_›
      · rintro (rfl | rfl)
        · exact ⟨‹_›, by rw [vB₁]; simp⟩
        · exact ⟨‹_›, by rw [vB₂]; simp⟩
    · ext q
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hz⟩
        by_cases c1 : q = E₁
        · subst c1
          rw [vE₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c2 : q = E₂
        · subst c2
          rw [vE₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c3 : q = E₃
        · subst c3
          rw [vE₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c4 : q = KA₁
        · subst c4
          rw [vA₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c5 : q = KB₁
        · subst c5
          rw [vB₁, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c6 : q = KB₂
        · subst c6
          rw [vB₂, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        by_cases c7 : q = KC₂
        · subst c7
          exact Or.inl rfl
        by_cases c8 : q = KC₃
        · subst c8
          exact Or.inr rfl
        by_cases c9 : q = KA₃
        · subst c9
          rw [vA₃, Sym2.mem_iff] at hz
          exfalso; rcases hz with h | h <;> kill h
        rw [untouched q c1 c2 c3 c4 c5 c6 c7 c8 c9] at hz
        exact absurd (hZ q hq _ hz) ‹_›
      · rintro (rfl | rfl)
        · exact ⟨‹_›, by rw [vC₂]; simp⟩
        · exact ⟨‹_›, by rw [vC₃]; simp⟩

end PartitionedTriangleAbsorption.TripleCutStage94
