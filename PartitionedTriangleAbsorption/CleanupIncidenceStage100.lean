/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalyticCleanupStage99

/-! # Exact incidences under one catalytic exchange -/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupStage100

open Finset TripleCutStage94 CatalystInsertionStage89

variable {V : Type*} [DecidableEq V] {S : Data V} {pos : Tok V → Sym2 V}
  {q₁ q₂ q₃ q₄ : Tok V} {a b c d e f z z' : V}

/-- Away from the two old and two new carriers, token incidences are unchanged. -/
theorem exchange_other
    (p₁ : pos q₁ = s(a, c)) (p₂ : pos q₂ = s(a, d))
    (p₃ : pos q₃ = s(b, e)) (p₄ : pos q₄ = s(b, f))
    (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h14 : q₁ ≠ q₄)
    (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄) (h34 : q₃ ≠ q₄)
    {v : V} (ha : v ≠ a) (hb : v ≠ b) (hz : v ≠ z) (hz' : v ≠ z') :
    tokAtP S (move4 pos q₁ q₂ q₃ q₄ s(z, c) s(z', d) s(z, e) s(z', f)) v =
      tokAtP S pos v := by
  obtain ⟨v₁, v₂, v₃, v₄⟩ := move4_vals (pos := pos) (e₁ := s(z, c))
    (e₂ := s(z', d)) (e₃ := s(z, e)) (e₄ := s(z', f)) h12 h13 h14 h23 h24 h34
  ext q
  simp only [mem_tokAtP]
  by_cases h1 : q = q₁
  · subst q; rw [v₁, p₁]; simp [Sym2.mem_iff, ha, hz]
  by_cases h2 : q = q₂
  · subst q; rw [v₂, p₂]; simp [Sym2.mem_iff, ha, hz']
  by_cases h3 : q = q₃
  · subst q; rw [v₃, p₃]; simp [Sym2.mem_iff, hb, hz]
  by_cases h4 : q = q₄
  · subst q; rw [v₄, p₄]; simp [Sym2.mem_iff, hb, hz']
  rw [move4_of_ne h1 h2 h3 h4]

/-- Every incidence at an old carrier is removed. -/
theorem exchange_empty
    (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h14 : q₁ ≠ q₄)
    (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄) (h34 : q₃ ≠ q₄)
    {v : V} (hat : tokAtP S pos v ⊆ {q₁, q₂, q₃, q₄})
    (hc : v ≠ c) (hd : v ≠ d) (he : v ≠ e) (hf : v ≠ f)
    (hz : v ≠ z) (hz' : v ≠ z') :
    tokAtP S (move4 pos q₁ q₂ q₃ q₄ s(z, c) s(z', d) s(z, e) s(z', f)) v = ∅ := by
  obtain ⟨v₁, v₂, v₃, v₄⟩ := move4_vals (pos := pos) (e₁ := s(z, c))
    (e₂ := s(z', d)) (e₃ := s(z, e)) (e₄ := s(z', f)) h12 h13 h14 h23 h24 h34
  rw [eq_empty_iff_forall_notMem]
  intro q hm
  obtain ⟨hq, hv⟩ := mem_tokAtP.mp hm
  by_cases h1 : q = q₁
  · subst q; rw [v₁] at hv; simp [Sym2.mem_iff, hc, hz] at hv
  by_cases h2 : q = q₂
  · subst q; rw [v₂] at hv; simp [Sym2.mem_iff, hd, hz'] at hv
  by_cases h3 : q = q₃
  · subst q; rw [v₃] at hv; simp [Sym2.mem_iff, he, hz] at hv
  by_cases h4 : q = q₄
  · subst q; rw [v₄] at hv; simp [Sym2.mem_iff, hf, hz'] at hv
  rw [move4_of_ne h1 h2 h3 h4] at hv
  have hm' := hat (mem_tokAtP.mpr ⟨hq, hv⟩)
  simp [h1, h2, h3, h4] at hm'

/-- A fresh carrier receives exactly the first and third moved tokens. -/
theorem exchange_at_new {Z : Finset V}
    (supp : ∀ q ∈ S.tokens, ∀ v ∈ pos q, v ∈ Z)
    (m₁ : q₁ ∈ S.tokens) (m₃ : q₃ ∈ S.tokens)
    (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h14 : q₁ ≠ q₄)
    (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄) (h34 : q₃ ≠ q₄)
    (hz : z ∉ Z) (hzz' : z ≠ z') (hd : d ∈ Z) (hf : f ∈ Z) :
    tokAtP S (move4 pos q₁ q₂ q₃ q₄ s(z, c) s(z', d) s(z, e) s(z', f)) z = {q₁, q₃} := by
  obtain ⟨v₁, v₂, v₃, v₄⟩ := move4_vals (pos := pos) (e₁ := s(z, c))
    (e₂ := s(z', d)) (e₃ := s(z, e)) (e₄ := s(z', f)) h12 h13 h14 h23 h24 h34
  have nzd : z ≠ d := ne_of_notMem hz hd
  have nzf : z ≠ f := ne_of_notMem hz hf
  ext q
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hm
    obtain ⟨hq, hv⟩ := mem_tokAtP.mp hm
    by_cases h1 : q = q₁
    · exact Or.inl h1
    by_cases h2 : q = q₂
    · subst q; rw [v₂] at hv; simp [Sym2.mem_iff, hzz', nzd] at hv
    by_cases h3 : q = q₃
    · exact Or.inr h3
    by_cases h4 : q = q₄
    · subst q; rw [v₄] at hv; simp [Sym2.mem_iff, hzz', nzf] at hv
    rw [move4_of_ne h1 h2 h3 h4] at hv
    exact False.elim (hz (supp q hq z hv))
  · rintro (rfl | rfl)
    · exact mem_tokAtP.mpr ⟨m₁, by rw [v₁]; exact Sym2.mem_mk_left _ _⟩
    · exact mem_tokAtP.mpr ⟨m₃, by rw [v₃]; exact Sym2.mem_mk_left _ _⟩

/-- The second fresh carrier receives exactly the companion tokens. -/
theorem exchange_at_new' {Z : Finset V}
    (supp : ∀ q ∈ S.tokens, ∀ v ∈ pos q, v ∈ Z)
    (m₂ : q₂ ∈ S.tokens) (m₄ : q₄ ∈ S.tokens)
    (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h14 : q₁ ≠ q₄)
    (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄) (h34 : q₃ ≠ q₄)
    (hz' : z' ∉ Z) (hzz' : z ≠ z') (hc : c ∈ Z) (he : e ∈ Z) :
    tokAtP S (move4 pos q₁ q₂ q₃ q₄ s(z, c) s(z', d) s(z, e) s(z', f)) z' = {q₂, q₄} := by
  obtain ⟨v₁, v₂, v₃, v₄⟩ := move4_vals (pos := pos) (e₁ := s(z, c))
    (e₂ := s(z', d)) (e₃ := s(z, e)) (e₄ := s(z', f)) h12 h13 h14 h23 h24 h34
  have nzc : z' ≠ c := ne_of_notMem hz' hc
  have nze : z' ≠ e := ne_of_notMem hz' he
  ext q
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hm
    obtain ⟨hq, hv⟩ := mem_tokAtP.mp hm
    by_cases h1 : q = q₁
    · subst q; rw [v₁] at hv; simp [Sym2.mem_iff, hzz'.symm, nzc] at hv
    by_cases h2 : q = q₂
    · exact Or.inl h2
    by_cases h3 : q = q₃
    · subst q; rw [v₃] at hv; simp [Sym2.mem_iff, hzz'.symm, nze] at hv
    by_cases h4 : q = q₄
    · exact Or.inr h4
    rw [move4_of_ne h1 h2 h3 h4] at hv
    exact False.elim (hz' (supp q hq z' hv))
  · rintro (rfl | rfl)
    · exact mem_tokAtP.mpr ⟨m₂, by rw [v₂]; exact Sym2.mem_mk_left _ _⟩
    · exact mem_tokAtP.mpr ⟨m₄, by rw [v₄]; exact Sym2.mem_mk_left _ _⟩

end PartitionedTriangleAbsorption.CleanupStage100
