/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Configs

/-!
# Lemma 14.4 from a count of hinge configurations

We reduce Lemma 14.4 (absorber stability) to a purely extremal statement,
`lemma_14_4_configs`: in a graph with `δ(G) ≥ 3n/4` that is not close to the three extremal
graphs, for every two triangles `u₁u₂v₁`, `u₁u₂v₂` there are `Ω(n⁴)` configurations of type 1 or
of type 2 (see `HingeModel.lean`).  Each configuration gives a distinct `K₃`-hinge on eight
vertices; this part is proved here.

**Status:** `lemma_14_4_configs` is proved (in `Configs.lean`, via a stability argument based on
counting 4-walks, which replaces the paper's Lemmas 14.1 and 14.2).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **Configuration count for Lemma 14.4** (proved in `Configs.lean`).  There is `α₀ > 0` such that for
every `α ∈ (0, α₀]` there are `c > 0` and `n₀` such that: if `G` has `n ≥ n₀` vertices,
`δ(G) ≥ 3n/4` and `G` is not `α`-close to any of the three extremal graphs, then for every two
triangles `u₁u₂v₁`, `u₁u₂v₂` (four distinct vertices) there are at least `c n⁴` configurations of
type 1, or of type 2, or of type 2 with the roles of `u₁, u₂` exchanged. -/
theorem lemma_14_4_configs :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 3 * Fintype.card V ≤ 4 * G.minDegree →
        ¬ IsCloseToExtremal α G →
        ∀ u₁ u₂ v₁ v₂ : V, Function.Injective ![u₁, u₂, v₁, v₂] →
          G.Adj u₁ u₂ → G.Adj u₁ v₁ → G.Adj u₂ v₁ → G.Adj u₁ v₂ → G.Adj u₂ v₂ →
          c * (Fintype.card V : ℝ) ^ 4 ≤ cfgCount mH1 G u₁ u₂ v₁ v₂ ∨
          c * (Fintype.card V : ℝ) ^ 4 ≤ cfgCount mH2 G u₁ u₂ v₁ v₂ ∨
          c * (Fintype.card V : ℝ) ^ 4 ≤ cfgCount mH2 G u₂ u₁ v₁ v₂ :=
  lemma_14_4_configs_proof

/-! ### From configurations to hinges -/

omit [Fintype V] in
lemma mem_image_sym2_map {M : Finset (Sym2 (Fin 8))} {g : Fin 8 → V} {z : Sym2 V} :
    z ∈ M.image (Sym2.map g) ↔ ∃ i j, s(i, j) ∈ M ∧ z = s(g i, g j) := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := mem_image.mp h
    induction e using Sym2.ind with
    | _ i j => exact ⟨i, j, he, rfl⟩
  · rintro ⟨i, j, h, rfl⟩
    exact mem_image.mpr ⟨s(i, j), h, rfl⟩

omit [Fintype V] in
/-- Recovering a vertex of a configuration from the hinge: if the only `M`-neighbours of `k`
outside `X` is `m`, and `a ∉ g(X)` is a neighbour of `g k` in `g(M)`, then `a = g m`. -/
lemma eq_of_mem_image {M : Finset (Sym2 (Fin 8))} {g : Fin 8 → V} (hg : Function.Injective g)
    {k m : Fin 8} {X : Finset (Fin 8)} (hM : ∀ j, s(k, j) ∈ M → j ∈ X ∨ j = m) {a : V}
    (ha : ∀ j ∈ X, a ≠ g j) (h : s(g k, a) ∈ M.image (Sym2.map g)) : a = g m := by
  obtain ⟨i, j, hij, he⟩ := mem_image_sym2_map.mp h
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi : k = i := hg h1
    subst hi
    rcases hM j hij with hj | hj
    · exact absurd h2 (ha j hj)
    · rw [h2, hj]
  · have hj : k = j := hg h1
    subst hj
    rw [Sym2.eq_swap] at hij
    rcases hM i hij with hi | hi
    · exact absurd h2 (ha i hi)
    · rw [h2, hi]

omit [Fintype V] in
/-- Injectivity for configurations of type 1, for an abstract `M` with the needed properties of
`mH1` (keeping `M` abstract keeps the proof cheap to check). -/
lemma image_injective_type1 {M : Finset (Sym2 (Fin 8))} {u₁ u₂ v₁ v₂ : V}
    {x y : V × V × V × V}
    (m04 : s(0, 4) ∈ M) (m71 : s(7, 1) ∈ M) (m45 : s(4, 5) ∈ M) (m67 : s(6, 7) ∈ M)
    (n0 : ∀ j, s(0, j) ∈ M → j ∈ (∅ : Finset (Fin 8)) ∨ j = 4)
    (n1 : ∀ j, s(1, j) ∈ M → j ∈ (∅ : Finset (Fin 8)) ∨ j = 7)
    (n4 : ∀ j, s(4, j) ∈ M → j ∈ ({0, 2, 3} : Finset (Fin 8)) ∨ j = 5)
    (n7 : ∀ j, s(7, j) ∈ M → j ∈ ({1, 2, 3} : Finset (Fin 8)) ∨ j = 6)
    (hx : Function.Injective (cfgVec u₁ u₂ v₁ v₂ x))
    (hy : Function.Injective (cfgVec u₁ u₂ v₁ v₂ y))
    (h : M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) =
      M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ y))) : x = y := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  obtain ⟨y1, y2, y3, y4⟩ := y
  have mem : ∀ i j, s(i, j) ∈ M → s(cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) i,
      cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) j) ∈
      M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ (y1, y2, y3, y4))) := by
    intro i j hij; rw [← h]; exact mem_image_sym2_map.mpr ⟨i, j, hij, rfl⟩
  have ne : ∀ i j, i ≠ j → cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) i ≠
      cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) j := fun i j hij hh => hij (hx hh)
  have h50 : x2 ≠ u₁ := ne 5 0 (by decide)
  have h52 : x2 ≠ v₁ := ne 5 2 (by decide)
  have h53 : x2 ≠ v₂ := ne 5 3 (by decide)
  have h61 : x3 ≠ u₂ := ne 6 1 (by decide)
  have h62 : x3 ≠ v₁ := ne 6 2 (by decide)
  have h63 : x3 ≠ v₂ := ne 6 3 (by decide)
  have e1 : x1 = y1 := by
    have := mem 0 4 m04
    rw [cfgVec_0, cfgVec_4] at this
    exact eq_of_mem_image hy n0 (by simp) (by rw [cfgVec_0]; exact this)
  have e4 : x4 = y4 := by
    have := mem 7 1 m71
    rw [cfgVec_7, cfgVec_1, Sym2.eq_swap] at this
    exact eq_of_mem_image hy n1 (by simp) (by rw [cfgVec_1]; exact this)
  have e2 : x2 = y2 := by
    have := mem 4 5 m45
    rw [cfgVec_4, cfgVec_5, e1] at this
    refine eq_of_mem_image hy n4 ?_ (by rw [cfgVec_4]; exact this)
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · rw [cfgVec_0]; exact h50
    · rw [cfgVec_2]; exact h52
    · rw [cfgVec_3]; exact h53
  have e3 : x3 = y3 := by
    have := mem 6 7 m67
    rw [cfgVec_6, cfgVec_7, e4, Sym2.eq_swap] at this
    refine eq_of_mem_image hy n7 ?_ (by rw [cfgVec_7]; exact this)
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · rw [cfgVec_1]; exact h61
    · rw [cfgVec_2]; exact h62
    · rw [cfgVec_3]; exact h63
  rw [e1, e2, e3, e4]

omit [Fintype V] in
/-- Injectivity for configurations of type 2, for an abstract `M` with the needed properties of
`mH2`. -/
lemma image_injective_type2 {M : Finset (Sym2 (Fin 8))} {u₁ u₂ v₁ v₂ : V}
    {x y : V × V × V × V}
    (m40 : s(4, 0) ∈ M) (m25 : s(2, 5) ∈ M) (m73 : s(7, 3) ∈ M) (m16 : s(1, 6) ∈ M)
    (n0 : ∀ j, s(0, j) ∈ M → j ∈ (∅ : Finset (Fin 8)) ∨ j = 4)
    (n2 : ∀ j, s(2, j) ∈ M → j ∈ ({4} : Finset (Fin 8)) ∨ j = 5)
    (n3 : ∀ j, s(3, j) ∈ M → j ∈ ({4} : Finset (Fin 8)) ∨ j = 7)
    (n1 : ∀ j, s(1, j) ∈ M → j ∈ ({5, 7} : Finset (Fin 8)) ∨ j = 6)
    (hx : Function.Injective (cfgVec u₁ u₂ v₁ v₂ x))
    (hy : Function.Injective (cfgVec u₁ u₂ v₁ v₂ y))
    (h : M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) =
      M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ y))) : x = y := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  obtain ⟨y1, y2, y3, y4⟩ := y
  have mem : ∀ i j, s(i, j) ∈ M → s(cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) i,
      cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) j) ∈
      M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ (y1, y2, y3, y4))) := by
    intro i j hij; rw [← h]; exact mem_image_sym2_map.mpr ⟨i, j, hij, rfl⟩
  have ne : ∀ i j, i ≠ j → cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) i ≠
      cfgVec u₁ u₂ v₁ v₂ (x1, x2, x3, x4) j := fun i j hij hh => hij (hx hh)
  have h54 : x2 ≠ x1 := ne 5 4 (by decide)
  have h74 : x4 ≠ x1 := ne 7 4 (by decide)
  have h65 : x3 ≠ x2 := ne 6 5 (by decide)
  have h67 : x3 ≠ x4 := ne 6 7 (by decide)
  have e1 : x1 = y1 := by
    have := mem 4 0 m40
    rw [cfgVec_4, cfgVec_0, Sym2.eq_swap] at this
    exact eq_of_mem_image hy n0 (by simp) (by rw [cfgVec_0]; exact this)
  have e2 : x2 = y2 := by
    have := mem 2 5 m25
    rw [cfgVec_2, cfgVec_5] at this
    refine eq_of_mem_image hy n2 ?_ (by rw [cfgVec_2]; exact this)
    intro j hj
    rw [mem_singleton] at hj
    subst hj
    rw [cfgVec_4, ← e1]; exact h54
  have e4 : x4 = y4 := by
    have := mem 7 3 m73
    rw [cfgVec_7, cfgVec_3, Sym2.eq_swap] at this
    refine eq_of_mem_image hy n3 ?_ (by rw [cfgVec_3]; exact this)
    intro j hj
    rw [mem_singleton] at hj
    subst hj
    rw [cfgVec_4, ← e1]; exact h74
  have e3 : x3 = y3 := by
    have := mem 1 6 m16
    rw [cfgVec_1, cfgVec_6] at this
    refine eq_of_mem_image hy n1 ?_ (by rw [cfgVec_1]; exact this)
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    · rw [cfgVec_5, ← e2]; exact h65
    · rw [cfgVec_7, ← e4]; exact h67
  rw [e1, e2, e3, e4]

omit [Fintype V] in
lemma image_mH1_injective {u₁ u₂ v₁ v₂ : V} {x y : V × V × V × V}
    (hx : Function.Injective (cfgVec u₁ u₂ v₁ v₂ x))
    (hy : Function.Injective (cfgVec u₁ u₂ v₁ v₂ y))
    (h : mH1.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) =
      mH1.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ y))) : x = y :=
  image_injective_type1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hx hy h

omit [Fintype V] in
lemma image_mH2_injective {u₁ u₂ v₁ v₂ : V} {x y : V × V × V × V}
    (hx : Function.Injective (cfgVec u₁ u₂ v₁ v₂ x))
    (hy : Function.Injective (cfgVec u₁ u₂ v₁ v₂ y))
    (h : mH2.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) =
      mH2.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ y))) : x = y :=
  image_injective_type2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hx hy h

/-- Every configuration yields a hinge on eight vertices. -/
lemma isHinge_of_cfg {M : Finset (Sym2 (Fin 8))} (hM : IsHinge onePart K3fam mT1 mT2 M)
    (hMV : vertSet M = univ) {G : SimpleGraph V} [DecidableRel G.Adj] {u₁ u₂ v₁ v₂ : V}
    {x : V × V × V × V} (hx : IsCfg M G u₁ u₂ v₁ v₂ x) :
    M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) ⊆ G.edgeFinset ∧
    IsHinge onePart K3fam {u₁, u₂, v₁} {u₁, u₂, v₂}
      (M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x))) ∧
    (vertSet (M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)))).card = 8 := by
  obtain ⟨hinj, hadj⟩ := hx
  set f : Fin 8 ↪ V := ⟨cfgVec u₁ u₂ v₁ v₂ x, hinj⟩
  have himg : M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) = M.map f.sym2Map := by
    rw [map_eq_image]; rfl
  refine ⟨fun e he => ?_, ?_, ?_⟩
  · obtain ⟨i, j, hij, rfl⟩ := mem_image_sym2_map.mp he
    simpa using hadj i j hij
  · have h1 : mT1.map f = {u₁, u₂, v₁} := by simp [mT1, f, cfgVec]
    have h2 : mT2.map f = {u₁, u₂, v₂} := by simp [mT2, f, cfgVec]
    rw [himg, ← h1, ← h2]
    exact isHinge_map f hM
  · rw [himg, vertSet_map, hMV, card_map, card_univ, Fintype.card_fin]

/-! ### Lemma 14.4 -/

omit [Fintype V] in
/-- Two triangles sharing exactly one edge have the form `u₁u₂v₁`, `u₁u₂v₂`. -/
lemma two_triangles_sharing_edge {S S' : Finset V} (hS : S.card = 3) (hS' : S'.card = 3)
    (h1 : (triEdges S ∩ triEdges S').card = 1) :
    ∃ u₁ u₂ v₁ v₂ : V, u₁ ≠ u₂ ∧ u₁ ≠ v₁ ∧ u₁ ≠ v₂ ∧ u₂ ≠ v₁ ∧ u₂ ≠ v₂ ∧ v₁ ≠ v₂ ∧
      S = {u₁, u₂, v₁} ∧ S' = {u₁, u₂, v₂} := by
  obtain ⟨e, he⟩ := card_eq_one.mp h1
  have hemem : e ∈ triEdges S ∩ triEdges S' := by rw [he]; exact mem_singleton_self e
  induction e using Sym2.ind with
  | _ a b =>
  rw [mem_inter, mk_mem_triEdges, mk_mem_triEdges] at hemem
  obtain ⟨⟨haS, hbS, hab⟩, haS', hbS', -⟩ := hemem
  have third : ∀ T : Finset V, T.card = 3 → a ∈ T → b ∈ T →
      ∃ v, v ≠ a ∧ v ≠ b ∧ T = {a, b, v} := by
    intro T hT ha hb
    have hsub : ({a, b} : Finset V) ⊆ T := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    have hc : (T \ {a, b}).card = 1 := by
      rw [card_sdiff_of_subset hsub, hT, card_pair hab]
    obtain ⟨v, hv⟩ := card_eq_one.mp hc
    have hvT : v ∈ T \ {a, b} := by rw [hv]; exact mem_singleton_self v
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hvT
    refine ⟨v, hvT.2.1, hvT.2.2, ?_⟩
    symm
    apply eq_of_subset_of_card_le
    · intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> first | assumption | exact hvT.1
    · rw [hT, card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨hab, fun h => hvT.2.1 h.symm⟩),
        card_pair (Ne.symm hvT.2.2)]
  obtain ⟨v₁, h1a, h1b, rfl⟩ := third S hS haS hbS
  obtain ⟨v₂, h2a, h2b, rfl⟩ := third S' hS' haS' hbS'
  refine ⟨a, b, v₁, v₂, hab, h1a.symm, h2a.symm, h1b.symm, h2b.symm, ?_, rfl, rfl⟩
  rintro rfl
  have hm : s(a, v₁) ∈ triEdges ({a, b, v₁} : Finset V) ∩ triEdges {a, b, v₁} := by
    rw [mem_inter, and_self, mk_mem_triEdges]; simp [h1a.symm]
  rw [he, mem_singleton, Sym2.eq_iff] at hm
  rcases hm with ⟨-, h⟩ | ⟨h, -⟩
  · exact h1b h
  · exact hab h

open Classical in
/-- Distinct configurations give distinct hinges, so the number of hinges on eight vertices is at
least the number of configurations. -/
lemma cfgCount_le_hingeCount {M : Finset (Sym2 (Fin 8))} (hM : IsHinge onePart K3fam mT1 mT2 M)
    (hMV : vertSet M = univ) (G : SimpleGraph V) [DecidableRel G.Adj] (u₁ u₂ v₁ v₂ : V)
    (hinj : ∀ x y : V × V × V × V, Function.Injective (cfgVec u₁ u₂ v₁ v₂ x) →
      Function.Injective (cfgVec u₁ u₂ v₁ v₂ y) →
      M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) = M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ y)) →
      x = y) :
    (cfgCount M G u₁ u₂ v₁ v₂ : ℝ) ≤
      ((G.edgeFinset.powerset.filter (fun H => IsHinge onePart K3fam {u₁, u₂, v₁} {u₁, u₂, v₂} H ∧
        (vertSet H).card = 8)).card : ℝ) := by
  unfold cfgCount
  exact_mod_cast card_le_card_of_injOn (fun x => M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)))
    (fun x hx => by
      rw [coe_filter] at hx
      obtain ⟨h1, h2, h3⟩ := isHinge_of_cfg hM hMV hx.2
      rw [coe_filter]
      exact ⟨mem_powerset.mpr h1, h2, h3⟩)
    (fun x hx y hy hxy => by
      rw [coe_filter] at hx hy
      exact hinj x y hx.2.1 hy.2.1 hxy)

/-- **Lemma 14.4** (absorber stability). There is `α₀ > 0` such that for every `α ∈ (0, α₀]`
there is `c > 0` such that for all large `n`: every graph `G` on `n` vertices with `δ(G) ≥ 3n/4`
that is not `α`-close to any of `T₂(n/2)+T₂(n/2)`, `T̄₂(n/2)+T₂(n/2)`, `T̄₂(n/2)+T̄₂(n/2)` is
`(c, 8)`-`K₃`-hingeful (hinge counts normalised as `c n^{i-4}`).  The paper gives the explicit
constant `c = α³/10¹⁴`; only positivity is used.  Proved here from `lemma_14_4_configs`. -/
theorem lemma_14_4 :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 3 * Fintype.card V ≤ 4 * G.minDegree →
        ¬ IsCloseToExtremal α G →
        HingefulN onePart K3fam G c 8 := by
  obtain ⟨α₀, hα₀, hcfg⟩ := lemma_14_4_configs
  refine ⟨α₀, hα₀, fun α hα hαα₀ => ?_⟩
  obtain ⟨c, hc, n₀, hn₀⟩ := hcfg α hα hαα₀
  refine ⟨c, hc, n₀, fun V _ _ G _ hn hδ hnc => ?_⟩
  intro S S' hS hS' h1
  obtain ⟨u₁, u₂, v₁, v₂, h12, h13, h14, h23, h24, h34, rfl, rfl⟩ :=
    two_triangles_sharing_edge hS.1.2 hS'.1.2 h1
  have adj : ∀ {T : Finset V} {x y : V}, IsCopy onePart K3fam G T → x ∈ T → y ∈ T → x ≠ y →
      G.Adj x y := fun hT hx hy hxy => hT.1.1 (mem_coe.mpr hx) (mem_coe.mpr hy) hxy
  have inj : Function.Injective ![u₁, u₂, v₁, v₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; first | exact absurd hij ‹_› | exact absurd hij.symm ‹_›)
  have hpow : (Fintype.card V : ℝ) ^ (((8 : ℕ) : ℤ) - 4) = (Fintype.card V : ℝ) ^ 4 := by
    rw [show ((8 : ℕ) : ℤ) - 4 = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
  refine ⟨8, by simp, ?_⟩
  rw [hpow]
  rcases hn₀ V G hn hδ hnc u₁ u₂ v₁ v₂ inj (adj hS (by simp) (by simp) h12)
      (adj hS (by simp) (by simp) h13) (adj hS (by simp) (by simp) h23)
      (adj hS' (by simp) (by simp) h14) (adj hS' (by simp) (by simp) h24) with h | h | h
  · exact h.trans (cfgCount_le_hingeCount model_hinge1 vertSet_mH1 G u₁ u₂ v₁ v₂
      (fun x y hx hy hxy => image_mH1_injective hx hy hxy))
  · exact h.trans (cfgCount_le_hingeCount model_hinge2 vertSet_mH2 G u₁ u₂ v₁ v₂
      (fun x y hx hy hxy => image_mH2_injective hx hy hxy))
  · have := h.trans (cfgCount_le_hingeCount model_hinge2 vertSet_mH2 G u₂ u₁ v₁ v₂
      (fun x y hx hy hxy => image_mH2_injective hx hy hxy))
    rwa [insert_comm u₂ u₁, insert_comm u₂ u₁] at this

end NashWilliams18
