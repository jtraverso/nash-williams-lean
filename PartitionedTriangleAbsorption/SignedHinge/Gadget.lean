/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups

/-! # The occurrence gadget: one hinge between a certificate triangle and a fresh triangle

Let `t = {a,b,c}` be a typed triangle and `x` a further vertex, and let `H` be a hinge for the
two copies `{a,b,c}` and `{a,b,x}` (sharing exactly the edge `ab`). Fix a decomposition of
`H ∪ {ac, bc}` and let `{a,c,y}`, `{b,c,z}` be its triangles through `ac` and `bc`. Then

* `y, z` are new vertices (`∉ {a,b,c,x}`), `y ≠ z`;
* the *slot wedges* `{ax,bx}`, `{ay,cy}`, `{bz,cz}` close the three edges of `t` with the
  apices `x, y, z` (slot triangles `{a,b,x}`, `{a,c,y}`, `{b,c,z}`);
* `R = H ∪ {ax,bx}` is decomposable (first hinge mode), and
  `Y = H \ {ay,cy,bz,cz}` is decomposable (rest of the second hinge mode);
* `R` is the disjoint union of `Y` and the three slot wedges (the "hexagon").

Hence `Y` is a decomposable absorber for the hexagon `{ax,bx,ay,cy,bz,cz}` which uses **no**
edge of `t`: this is the root-clean local closure used for every certificate occurrence.
Generic in the type family `F`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

omit [DecidableEq V] in
theorem mem_of_mk_mem_triEdges [DecidableEq V] {s : Finset V} {a b : V}
    (h : s(a, b) ∈ triEdges s) : a ∈ s ∧ b ∈ s := by
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff] at h
  exact h.1

/-- The third vertex of a 3-set containing two given vertices. -/
theorem third_vertex {T : Finset V} {a c : V} (h3 : T.card = 3) (ha : a ∈ T) (hc : c ∈ T)
    (hac : a ≠ c) : ∃ y, y ≠ a ∧ y ≠ c ∧ T = {a, c, y} := by
  have hsub : ({a, c} : Finset V) ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : (T \ {a, c}).card = 1 := by
    rw [card_sdiff_of_subset hsub, h3, card_pair hac]
  obtain ⟨y, hy⟩ := card_eq_one.mp hcard
  have hyT : y ∈ T \ {a, c} := by rw [hy]; exact mem_singleton_self y
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hyT
  refine ⟨y, hyT.2.1, hyT.2.2, ?_⟩
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hc
    · exact hyT.1
  · rw [h3, card_insert_of_notMem (by simp [hac, Ne.symm hyT.2.1]),
      card_pair (Ne.symm hyT.2.2)]

/-- **Occurrence gadget from one hinge.** -/
theorem hinge_gadget {a b c x : V} {H : Finset (Sym2 V)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (h : IsHinge p F {a, b, c} {a, b, x} H) :
    ∃ y z : V, y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ y ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ x ∧ y ≠ z ∧
      IsTypedTri p F {a, c, y} ∧ IsTypedTri p F {b, c, z} ∧
      s(a, y) ∈ H ∧ s(c, y) ∈ H ∧ s(b, z) ∈ H ∧ s(c, z) ∈ H ∧
      HasDecomp p F (H \ {s(a, y), s(c, y), s(b, z), s(c, z)}) ∧
      HasDecomp p F (H ∪ {s(a, x), s(b, x)}) := by
  have hE := triEdges_three hab hac hbc
  have hE' := triEdges_three hab (Ne.symm hxa) (Ne.symm hxb)
  have hd1 : triEdges ({a, b, c} : Finset V) \ triEdges {a, b, x} = {s(a, c), s(b, c)} := by
    rw [hE, hE']
    ext e
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩
        simp only [Sym2.eq_iff, not_or, not_and]
        aesop
      · refine ⟨Or.inr (Or.inr rfl), ?_⟩
        simp only [Sym2.eq_iff, not_or, not_and]
        aesop
  have hd2 : triEdges ({a, b, x} : Finset V) \ triEdges {a, b, c} = {s(a, x), s(b, x)} := by
    rw [hE, hE']
    ext e
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩
        simp only [Sym2.eq_iff, not_or, not_and]
        aesop
      · refine ⟨Or.inr (Or.inr rfl), ?_⟩
        simp only [Sym2.eq_iff, not_or, not_and]
        aesop
  have hdisj := h.1
  have hnot : ∀ e, e ∈ triEdges ({a, b, c} : Finset V) ∪ triEdges {a, b, x} → e ∉ H :=
    fun e he hH => disjoint_left.mp hdisj hH he
  have hab_H : s(a, b) ∉ H := hnot _ (by rw [hE]; simp)
  have hac_H : s(a, c) ∉ H := hnot _ (by rw [hE]; simp)
  have hbc_H : s(b, c) ∉ H := hnot _ (by rw [hE]; simp)
  have hax_H : s(a, x) ∉ H := hnot _ (by rw [hE']; simp)
  have hbx_H : s(b, x) ∉ H := hnot _ (by rw [hE']; simp)
  have hmode1 := h.2.1
  rw [hd1] at hmode1
  obtain ⟨D, hDt, hDd, hDu⟩ := hmode1
  have hmemU : ∀ e, e ∈ H ∪ {s(a, c), s(b, c)} ↔ ∃ T ∈ D, e ∈ triEdges T := by
    intro e; rw [← hDu, mem_biUnion]
  obtain ⟨T₁, hT₁D, hacT₁⟩ := (hmemU (s(a, c))).mp (by simp)
  obtain ⟨T₂, hT₂D, hbcT₂⟩ := (hmemU (s(b, c))).mp (by simp)
  obtain ⟨y, hya, hyc, rfl⟩ := third_vertex (hDt T₁ hT₁D).1
    (mem_of_mk_mem_triEdges hacT₁).1 (mem_of_mk_mem_triEdges hacT₁).2 hac
  obtain ⟨z, hzb, hzc, rfl⟩ := third_vertex (hDt T₂ hT₂D).1
    (mem_of_mk_mem_triEdges hbcT₂).1 (mem_of_mk_mem_triEdges hbcT₂).2 hbc
  have hT₁e := triEdges_three hac (Ne.symm hya) (Ne.symm hyc)
  have hT₂e := triEdges_three hbc (Ne.symm hzb) (Ne.symm hzc)
  have hin₁ : ∀ e ∈ triEdges ({a, c, y} : Finset V), e ∈ H ∪ {s(a, c), s(b, c)} :=
    fun e he => (hmemU e).mpr ⟨_, hT₁D, he⟩
  have hin₂ : ∀ e ∈ triEdges ({b, c, z} : Finset V), e ∈ H ∪ {s(a, c), s(b, c)} :=
    fun e he => (hmemU e).mpr ⟨_, hT₂D, he⟩
  have hay : s(a, y) ∈ H ∪ {s(a, c), s(b, c)} := hin₁ _ (by rw [hT₁e]; simp)
  have hcy : s(c, y) ∈ H ∪ {s(a, c), s(b, c)} := hin₁ _ (by rw [hT₁e]; simp)
  have hbz : s(b, z) ∈ H ∪ {s(a, c), s(b, c)} := hin₂ _ (by rw [hT₂e]; simp)
  have hcz : s(c, z) ∈ H ∪ {s(a, c), s(b, c)} := hin₂ _ (by rw [hT₂e]; simp)
  have hab_H' : s(b, a) ∉ H := by rw [Sym2.eq_swap]; exact hab_H
  have hbc_H' : s(c, b) ∉ H := by rw [Sym2.eq_swap]; exact hbc_H
  have hac_H' : s(c, a) ∉ H := by rw [Sym2.eq_swap]; exact hac_H
  have key : ∀ u v : V, s(u, v) ∈ H ∪ {s(a, c), s(b, c)} → s(u, v) ∈ H ∨
      ((u = a ∧ v = c ∨ u = c ∧ v = a) ∨ (u = b ∧ v = c ∨ u = c ∧ v = b)) := by
    intro u v huv
    rcases mem_union.mp huv with h1 | h1
    · exact Or.inl h1
    · right; simpa [Sym2.eq_iff] using h1
  have hyb : y ≠ b := by
    rintro rfl
    rcases key _ _ hay with h1 | (⟨-, h3⟩ | ⟨h2, -⟩) | (⟨h2, -⟩ | ⟨h2, -⟩)
    · exact hab_H h1
    · exact hbc h3
    · exact hac h2
    · exact hab h2
    · exact hac h2
  have hza : z ≠ a := by
    rintro rfl
    rcases key _ _ hbz with h1 | (⟨h2, -⟩ | ⟨h2, -⟩) | (⟨-, h3⟩ | ⟨h2, -⟩)
    · exact hab_H' h1
    · exact hab h2.symm
    · exact hbc h2
    · exact hac h3
    · exact hbc h2
  have hayH : s(a, y) ∈ H := by
    rcases key _ _ hay with h1 | (⟨-, h3⟩ | ⟨h2, -⟩) | (⟨h2, -⟩ | ⟨h2, -⟩)
    · exact h1
    · exact absurd h3 hyc
    · exact absurd h2 hac
    · exact absurd h2 hab
    · exact absurd h2 hac
  have hcyH : s(c, y) ∈ H := by
    rcases key _ _ hcy with h1 | (⟨h2, -⟩ | ⟨-, h3⟩) | (⟨h2, -⟩ | ⟨-, h3⟩)
    · exact h1
    · exact absurd h2.symm hac
    · exact absurd h3 hya
    · exact absurd h2.symm hbc
    · exact absurd h3 hyb
  have hbzH : s(b, z) ∈ H := by
    rcases key _ _ hbz with h1 | (⟨h2, -⟩ | ⟨h2, -⟩) | (⟨-, h3⟩ | ⟨h2, -⟩)
    · exact h1
    · exact absurd h2.symm hab
    · exact absurd h2 hbc
    · exact absurd h3 hzc
    · exact absurd h2 hbc
  have hczH : s(c, z) ∈ H := by
    rcases key _ _ hcz with h1 | (⟨h2, -⟩ | ⟨-, h3⟩) | (⟨h2, -⟩ | ⟨-, h3⟩)
    · exact h1
    · exact absurd h2.symm hac
    · exact absurd h3 hza
    · exact absurd h2.symm hbc
    · exact absurd h3 hzb
  have hyx : y ≠ x := by rintro rfl; exact hax_H hayH
  have hzx : z ≠ x := by rintro rfl; exact hbx_H hbzH
  have hT₁₂ : ({a, c, y} : Finset V) ≠ {b, c, z} := by
    intro heq
    have : b ∈ ({a, c, y} : Finset V) := by rw [heq]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact hab h1.symm
    · exact hbc h1
    · exact hyb h1.symm
  have hdisT := hDd hT₁D hT₂D hT₁₂
  have hyz : y ≠ z := by
    rintro rfl
    have h1 : s(c, y) ∈ triEdges ({a, c, y} : Finset V) := by rw [hT₁e]; simp
    have h2 : s(c, y) ∈ triEdges ({b, c, y} : Finset V) := by rw [hT₂e]; simp
    exact disjoint_left.mp hdisT h1 h2
  refine ⟨y, z, hya, hyb, hyc, hyx, hza, hzb, hzc, hzx, hyz, hDt _ hT₁D, hDt _ hT₂D,
    hayH, hcyH, hbzH, hczH, ?_, ?_⟩
  · refine ⟨(D.erase {a, c, y}).erase {b, c, z}, fun s hs => hDt s
      (mem_of_mem_erase (mem_of_mem_erase hs)), hDd.subset (fun s hs => by
        simp only [coe_erase, Set.mem_sdiff, mem_coe] at hs
        exact hs.1.1), ?_⟩
    ext e
    simp only [mem_biUnion, mem_erase, mem_sdiff]
    constructor
    · rintro ⟨T, ⟨hT2, hT1, hTD⟩, heT⟩
      have heU := (hmemU e).mpr ⟨T, hTD, heT⟩
      have hn1 : e ∉ triEdges ({a, c, y} : Finset V) := fun h' =>
        disjoint_left.mp (hDd hTD hT₁D hT1) heT h'
      have hn2 : e ∉ triEdges ({b, c, z} : Finset V) := fun h' =>
        disjoint_left.mp (hDd hTD hT₂D hT2) heT h'
      rw [hT₁e] at hn1
      rw [hT₂e] at hn2
      simp only [mem_union, mem_insert, mem_singleton, not_or] at heU hn1 hn2 ⊢
      rcases heU with heU | heU | heU
      · exact ⟨heU, hn1.2.1, hn1.2.2, hn2.2.1, hn2.2.2⟩
      · exact absurd heU hn1.1
      · exact absurd heU hn2.1
    · rintro ⟨heH, hne⟩
      obtain ⟨T, hTD, heT⟩ := (hmemU e).mp (mem_union_left _ heH)
      refine ⟨T, ⟨?_, ?_, hTD⟩, heT⟩
      · rintro rfl
        rw [hT₂e] at heT
        simp only [mem_insert, mem_singleton] at heT hne
        rcases heT with rfl | rfl | rfl
        · exact hbc_H heH
        · exact hne (Or.inr (Or.inr (Or.inl rfl)))
        · exact hne (Or.inr (Or.inr (Or.inr rfl)))
      · rintro rfl
        rw [hT₁e] at heT
        simp only [mem_insert, mem_singleton] at heT hne
        rcases heT with rfl | rfl | rfl
        · exact hac_H heH
        · exact hne (Or.inl rfl)
        · exact hne (Or.inr (Or.inl rfl))
  · rw [← hd2]; exact h.2.2

end PartitionedTriangleAbsorption.SignedHinge
