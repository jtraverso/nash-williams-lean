/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystInsertionTraceStage89

/-! # The configuration after all insertions: tokens, carriers, separation

After every active vertex has been processed, the tokens are
`inl e` (`e ∈ Y`, original) and `inr (y, i)` (`y ∈ A`, `i : Fin 3`,
catalytic), with current positions `tokPos`. We prove:

* `tokPos` is injective on the tokens and its image is the configuration;
* at the carrier `cz y` sit exactly the original token `y – nm y` and the
  catalytic token `(y, 0)`; at `cz' y` exactly `y – np y` and `(y, 1)`;
* at the catalytic vertex `cs y` sit exactly `(y, 0)`, `(y, 2)`; at `ct y`
  exactly `(y, 1)`, `(y, 2)`; no token sits at any other vertex;
* hence the configuration is 2-regular on carriers ∪ catalytic vertices and
  every other vertex (all original active vertices and all centres `co y`)
  is isolated;
* separation: every catalytic edge has a catalytic endpoint, and each
  catalytic vertex is adjacent to at most one carrier.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}

namespace Data

variable (S : Data V) (cz cz' : V → V) (P : Finset V)

/-- Tokens: original `inl e` for `e ∈ Y`, catalytic `inr (y, i)` for `y ∈ A`. -/
def tokens : Finset (Sym2 V ⊕ (V × Fin 3)) := S.Y.disjSum (S.A ×ˢ univ)

/-- The current position of a token. -/
def tokPos : Sym2 V ⊕ (V × Fin 3) → Sym2 V
  | .inl e => S.curY cz cz' P e
  | .inr q => S.catTok cz cz' P q.1 q.2

/-- Tokens whose current position contains `v`. -/
def tokAt (v : V) : Finset (Sym2 V ⊕ (V × Fin 3)) :=
  S.tokens.filter fun q => v ∈ S.tokPos cz cz' P q

/-- The carriers. -/
def carriers : Finset V := S.A.image cz ∪ S.A.image cz'

/-- The catalytic vertices. -/
def catalytic : Finset V := S.A.image S.cs ∪ S.A.image S.ct

theorem config_eq_image : S.config cz cz' P = S.tokens.image (S.tokPos cz cz' P) := by
  ext e
  simp only [config, tokens, mem_union, mem_image, mem_biUnion, catCur_eq_image, mem_disjSum,
    mem_univ, true_and, mem_product]
  constructor
  · rintro (⟨e₀, he₀, rfl⟩ | ⟨y, hy, i, rfl⟩)
    · exact ⟨.inl e₀, Or.inl ⟨e₀, he₀, rfl⟩, rfl⟩
    · exact ⟨.inr (y, i), Or.inr ⟨(y, i), ⟨hy, trivial⟩, rfl⟩, rfl⟩
  · rintro ⟨q, (⟨e₀, he₀, rfl⟩ | ⟨⟨y, i⟩, ⟨hy, -⟩, rfl⟩), rfl⟩
    · exact Or.inl ⟨e₀, he₀, rfl⟩
    · exact Or.inr ⟨y, hy, i, rfl⟩

/-- Initially every token is at its original edge. -/
theorem tokPos_empty_inl (e : Sym2 V) : S.tokPos cz cz' ∅ (.inl e) = e := by
  simp [tokPos, curY, rep, Sym2.map_id']

theorem tokPos_empty_inr (y : V) :
    S.tokPos cz cz' ∅ (.inr (y, 0)) = s(S.co y, S.cs y) ∧
      S.tokPos cz cz' ∅ (.inr (y, 1)) = s(S.co y, S.ct y) ∧
      S.tokPos cz cz' ∅ (.inr (y, 2)) = s(S.cs y, S.ct y) := by
  simp [tokPos, catTok]

end Data

section carriers

variable {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}

omit [DecidableEq V] in
theorem cz_eq (hc : Carriers Z₀ cz cz' S.A) {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A)
    (h : cz y = cz y') : y = y' := by
  by_contra hne
  exact (hc.inj y hy y' hy' hne).1 h

omit [DecidableEq V] in
theorem cz'_eq (hc : Carriers Z₀ cz cz' S.A) {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A)
    (h : cz' y = cz' y') : y = y' := by
  by_contra hne
  exact (hc.inj y hy y' hy' hne).2.2 h

omit [DecidableEq V] in
theorem cz_ne_cz' (hc : Carriers Z₀ cz cz' S.A) {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A) :
    cz y ≠ cz' y' := by
  by_cases h : y = y'
  · subst h; exact hc.ne y hy
  · exact (hc.inj y hy y' hy' h).2.1

theorem rep_full {u : V} (hu : u ∈ S.A) (e : Sym2 V) :
    S.rep cz cz' S.A u e = if e = s(u, S.nm u) then cz u else cz' u := by
  simp [Data.rep, hu]

theorem catTok_full {y : V} (hy : y ∈ S.A) :
    S.catTok cz cz' S.A y 0 = s(cz y, S.cs y) ∧ S.catTok cz cz' S.A y 1 = s(cz' y, S.ct y) ∧
      S.catTok cz cz' S.A y 2 = s(S.cs y, S.ct y) := by
  simp [Data.catTok, hy]

theorem mem_catTok_full {y : V} (hy : y ∈ S.A) (i : Fin 3) (v : V) :
    v ∈ S.catTok cz cz' S.A y i ↔
      (i = 0 ∧ (v = cz y ∨ v = S.cs y)) ∨ (i = 1 ∧ (v = cz' y ∨ v = S.ct y)) ∨
        (i = 2 ∧ (v = S.cs y ∨ v = S.ct y)) := by
  fin_cases i <;> simp [Data.catTok, hy]

omit [DecidableEq V] in
theorem mem_tokens_inl (e : Sym2 V) : (.inl e : Sym2 V ⊕ (V × Fin 3)) ∈ S.tokens ↔ e ∈ S.Y := by
  simp [Data.tokens, mem_disjSum]

omit [DecidableEq V] in
theorem mem_tokens_inr (y : V) (i : Fin 3) :
    (.inr (y, i) : Sym2 V ⊕ (V × Fin 3)) ∈ S.tokens ↔ y ∈ S.A := by
  simp [Data.tokens, mem_disjSum]

theorem mem_tokAt_inl (P : Finset V) (v : V) (e : Sym2 V) :
    (.inl e : Sym2 V ⊕ (V × Fin 3)) ∈ S.tokAt cz cz' P v ↔
      e ∈ S.Y ∧ v ∈ S.curY cz cz' P e := by
  rw [Data.tokAt, mem_filter, mem_tokens_inl]
  rfl

theorem mem_tokAt_inr (P : Finset V) (v : V) (y : V) (i : Fin 3) :
    (.inr (y, i) : Sym2 V ⊕ (V × Fin 3)) ∈ S.tokAt cz cz' P v ↔
      y ∈ S.A ∧ v ∈ S.catTok cz cz' P y i := by
  rw [Data.tokAt, mem_filter, mem_tokens_inr]
  rfl

end carriers

variable [Fintype V]

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V}
  {cz cz' : V → V}

theorem cs_eq (fr : Frame p F G B S Z₀) {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A)
    (h : S.cs y = S.cs y') : y = y' := by
  by_contra hne
  have h1 : S.cs y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
  have h2 : S.cs y ∈ catVerts (S.co y') (S.cs y') (S.ct y') := by rw [h]; simp [catVerts]
  exact disjoint_left.mp (fr.vdisj y hy y' hy' hne) h1 h2

theorem ct_eq (fr : Frame p F G B S Z₀) {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A)
    (h : S.ct y = S.ct y') : y = y' := by
  by_contra hne
  have h1 : S.ct y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
  have h2 : S.ct y ∈ catVerts (S.co y') (S.cs y') (S.ct y') := by rw [h]; simp [catVerts]
  exact disjoint_left.mp (fr.vdisj y hy y' hy' hne) h1 h2

theorem cs_ne_ct (fr : Frame p F G B S Z₀) {y y' : V} (hy : y ∈ S.A) (hy' : y' ∈ S.A) :
    S.cs y ≠ S.ct y' := by
  by_cases h : y = y'
  · subst h; exact (fr.distinct y hy).2.2
  · intro heq
    have h1 : S.cs y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
    have h2 : S.cs y ∈ catVerts (S.co y') (S.cs y') (S.ct y') := by rw [heq]; simp [catVerts]
    exact disjoint_left.mp (fr.vdisj y hy y' hy' h) h1 h2

/-- Carriers are distinct from all catalytic vertices. -/
theorem carrier_ne_cat (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y y' : V}
    (hy : y ∈ S.A) (hy' : y' ∈ S.A) :
    cz y ≠ S.cs y' ∧ cz y ≠ S.ct y' ∧ cz' y ≠ S.cs y' ∧ cz' y ≠ S.ct y' := by
  obtain ⟨-, h1, h2⟩ := fr.mem_cat hy'
  obtain ⟨f1, f2⟩ := hc.fresh y hy
  exact ⟨fun h => f1 (h ▸ h1), fun h => f1 (h ▸ h2), fun h => f2 (h ▸ h1),
    fun h => f2 (h ▸ h2)⟩

theorem star_cases (fr : Frame p F G B S Z₀) {u : V} (hu : u ∈ S.A) {e : Sym2 V}
    (he : e ∈ S.Y) (hue : u ∈ e) : e = s(u, S.nm u) ∨ e = s(u, S.np u) := by
  have h : e ∈ S.Y.filter (fun e => u ∈ e) := mem_filter.mpr ⟨he, hue⟩
  rw [fr.star u hu] at h
  simpa using h

theorem np_ne_nm (fr : Frame p F G B S Z₀) {u : V} (hu : u ∈ S.A) :
    s(u, S.np u) ≠ s(u, S.nm u) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
  · exact fr.nm_ne_np u hu h.symm
  · exact (fr.nm_ne hu).1 h.symm

/-- Every vertex of the current position of an original token is a carrier. -/
theorem curY_carrier (fr : Frame p F G B S Z₀) {e : Sym2 V} (he : e ∈ S.Y) {v : V}
    (hv : v ∈ S.curY cz cz' S.A e) : ∃ u ∈ S.A, v = cz u ∨ v = cz' u := by
  obtain ⟨u, hu, hr⟩ := (S.mem_curY cz cz' S.A).mp hv
  have huA := fr.supp e he u hu
  refine ⟨u, huA, ?_⟩
  rw [rep_full huA] at hr
  split_ifs at hr
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm

theorem curY_notZ (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {e : Sym2 V}
    (he : e ∈ S.Y) {v : V} (hv : v ∈ S.curY cz cz' S.A e) : v ∉ Z₀ := by
  obtain ⟨u, hu, h | h⟩ := curY_carrier fr he hv <;> rw [h]
  · exact (hc.fresh u hu).1
  · exact (hc.fresh u hu).2

theorem cz_mem_curY (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) {e : Sym2 V} (he : e ∈ S.Y) :
    cz y ∈ S.curY cz cz' S.A e ↔ e = s(y, S.nm y) := by
  constructor
  · intro hm
    obtain ⟨u, hu, hr⟩ := (S.mem_curY cz cz' S.A).mp hm
    have huA := fr.supp e he u hu
    rw [rep_full huA] at hr
    split_ifs at hr with h
    · rw [cz_eq hc huA hy hr] at h; exact h
    · exact absurd hr.symm (cz_ne_cz' hc hy huA)
  · rintro rfl
    exact (S.mem_curY cz cz' S.A).mpr ⟨y, Sym2.mem_mk_left _ _, by rw [rep_full hy]; simp⟩

theorem cz'_mem_curY (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) {e : Sym2 V} (he : e ∈ S.Y) :
    cz' y ∈ S.curY cz cz' S.A e ↔ e = s(y, S.np y) := by
  constructor
  · intro hm
    obtain ⟨u, hu, hr⟩ := (S.mem_curY cz cz' S.A).mp hm
    have huA := fr.supp e he u hu
    rw [rep_full huA] at hr
    split_ifs at hr with h
    · exact absurd hr (cz_ne_cz' hc huA hy)
    · have hu' := cz'_eq hc huA hy hr
      subst hu'
      exact (star_cases fr huA he hu).resolve_left h
  · rintro rfl
    exact (S.mem_curY cz cz' S.A).mpr ⟨y, Sym2.mem_mk_left _ _, by
      rw [rep_full hy]; simp [np_ne_nm fr hy]⟩

/-- **Carrier `cz y`:** exactly the original token `y – nm y` and the
catalytic token `(y, 0)` sit there. -/
theorem tokAt_cz (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) : S.tokAt cz cz' S.A (cz y) = {.inl s(y, S.nm y), .inr (y, 0)} := by
  ext q
  rcases q with e | ⟨y', i⟩
  · rw [mem_tokAt_inl]
    simp only [mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false]
    constructor
    · rintro ⟨he, hm⟩
      exact (cz_mem_curY fr hc hy he).mp hm
    · rintro rfl
      exact ⟨(fr.nm_mem hy).1, (cz_mem_curY fr hc hy (fr.nm_mem hy).1).mpr rfl⟩
  · rw [mem_tokAt_inr]
    simp only [mem_insert, mem_singleton, reduceCtorEq, false_or, Sum.inr.injEq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hy', hm⟩
      have hn := carrier_ne_cat fr hc hy hy'
      rcases (mem_catTok_full hy' i _).mp hm with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
      · exact ⟨(cz_eq hc hy hy' h).symm, rfl⟩
      · exact absurd h hn.1
      · exact absurd h (cz_ne_cz' hc hy hy')
      · exact absurd h hn.2.1
      · exact absurd h hn.1
      · exact absurd h hn.2.1
    · rintro ⟨rfl, rfl⟩
      exact ⟨hy, (mem_catTok_full hy 0 _).mpr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩

/-- **Carrier `cz' y`:** exactly the original token `y – np y` and the
catalytic token `(y, 1)` sit there. -/
theorem tokAt_cz' (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) : S.tokAt cz cz' S.A (cz' y) = {.inl s(y, S.np y), .inr (y, 1)} := by
  ext q
  rcases q with e | ⟨y', i⟩
  · rw [mem_tokAt_inl]
    simp only [mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false]
    constructor
    · rintro ⟨he, hm⟩
      exact (cz'_mem_curY fr hc hy he).mp hm
    · rintro rfl
      exact ⟨(fr.nm_mem hy).2, (cz'_mem_curY fr hc hy (fr.nm_mem hy).2).mpr rfl⟩
  · rw [mem_tokAt_inr]
    simp only [mem_insert, mem_singleton, reduceCtorEq, false_or, Sum.inr.injEq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hy', hm⟩
      have hn := carrier_ne_cat fr hc hy hy'
      rcases (mem_catTok_full hy' i _).mp hm with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
      · exact absurd h.symm (cz_ne_cz' hc hy' hy)
      · exact absurd h hn.2.2.1
      · exact ⟨(cz'_eq hc hy hy' h).symm, rfl⟩
      · exact absurd h hn.2.2.2
      · exact absurd h hn.2.2.1
      · exact absurd h hn.2.2.2
    · rintro ⟨rfl, rfl⟩
      exact ⟨hy, (mem_catTok_full hy 1 _).mpr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))⟩

/-- **Catalytic vertex `cs y`:** exactly the catalytic tokens `(y, 0)`,
`(y, 2)` sit there; no original token. -/
theorem tokAt_cs (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) : S.tokAt cz cz' S.A (S.cs y) = {.inr (y, 0), .inr (y, 2)} := by
  ext q
  rcases q with e | ⟨y', i⟩
  · rw [mem_tokAt_inl]
    simp only [mem_insert, mem_singleton, reduceCtorEq, or_self, iff_false, not_and]
    intro he hm
    exact curY_notZ fr hc he hm (fr.mem_cat hy).2.1
  · rw [mem_tokAt_inr]
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hy', hm⟩
      have hn := carrier_ne_cat fr hc hy' hy
      rcases (mem_catTok_full hy' i _).mp hm with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
      · exact absurd h.symm hn.1
      · exact Or.inl ⟨(cs_eq fr hy hy' h).symm, rfl⟩
      · exact absurd h.symm hn.2.2.1
      · exact absurd h (cs_ne_ct fr hy hy')
      · exact Or.inr ⟨(cs_eq fr hy hy' h).symm, rfl⟩
      · exact absurd h (cs_ne_ct fr hy hy')
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hy, (mem_catTok_full hy 0 _).mpr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
      · exact ⟨hy, (mem_catTok_full hy 2 _).mpr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))⟩

/-- **Catalytic vertex `ct y`:** exactly the catalytic tokens `(y, 1)`,
`(y, 2)` sit there; no original token. -/
theorem tokAt_ct (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) : S.tokAt cz cz' S.A (S.ct y) = {.inr (y, 1), .inr (y, 2)} := by
  ext q
  rcases q with e | ⟨y', i⟩
  · rw [mem_tokAt_inl]
    simp only [mem_insert, mem_singleton, reduceCtorEq, or_self, iff_false, not_and]
    intro he hm
    exact curY_notZ fr hc he hm (fr.mem_cat hy).2.2
  · rw [mem_tokAt_inr]
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hy', hm⟩
      have hn := carrier_ne_cat fr hc hy' hy
      rcases (mem_catTok_full hy' i _).mp hm with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
      · exact absurd h.symm hn.2.1
      · exact absurd h.symm (cs_ne_ct fr hy' hy)
      · exact absurd h.symm hn.2.2.2
      · exact Or.inl ⟨(ct_eq fr hy hy' h).symm, rfl⟩
      · exact absurd h.symm (cs_ne_ct fr hy' hy)
      · exact Or.inr ⟨(ct_eq fr hy hy' h).symm, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hy, (mem_catTok_full hy 1 _).mpr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))⟩
      · exact ⟨hy, (mem_catTok_full hy 2 _).mpr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))⟩

/-- **No token at any other vertex.** -/
theorem tokAt_other (fr : Frame p F G B S Z₀) {v : V}
    (hv : v ∉ S.carriers cz cz' ∪ S.catalytic) : S.tokAt cz cz' S.A v = ∅ := by
  simp only [Data.carriers, Data.catalytic, mem_union, mem_image, not_or, not_exists,
    not_and] at hv
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  ext q
  simp only [notMem_empty, iff_false]
  rcases q with e | ⟨y', i⟩
  · rw [mem_tokAt_inl]
    rintro ⟨he, hm⟩
    obtain ⟨u, hu, h | h⟩ := curY_carrier fr he hm
    · exact h1 u hu h.symm
    · exact h2 u hu h.symm
  · rw [mem_tokAt_inr]
    rintro ⟨hy', hm⟩
    rcases (mem_catTok_full hy' i _).mp hm with ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h | h⟩
    · exact h1 y' hy' h.symm
    · exact h3 y' hy' h.symm
    · exact h2 y' hy' h.symm
    · exact h4 y' hy' h.symm
    · exact h3 y' hy' h.symm
    · exact h4 y' hy' h.symm

/-- An original token and a catalytic token never share a position. -/
theorem inl_ne_inr (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {e : Sym2 V}
    (he : e ∈ S.Y) {y : V} (hy : y ∈ S.A) (i : Fin 3) :
    S.curY cz cz' S.A e ≠ S.catTok cz cz' S.A y i := by
  intro h
  obtain ⟨-, hcs, hct⟩ := fr.mem_cat hy
  obtain ⟨h0, h1, h2⟩ := catTok_full (cz := cz) (cz' := cz') hy
  fin_cases i
  · exact curY_notZ fr hc he (h ▸ h0 ▸ Sym2.mem_mk_right _ _) hcs
  · exact curY_notZ fr hc he (h ▸ h1 ▸ Sym2.mem_mk_right _ _) hct
  · exact curY_notZ fr hc he (h ▸ h2 ▸ Sym2.mem_mk_left _ _) hcs

/-- **Token correspondence is a bijection onto the configuration.** -/
theorem tokPos_injOn (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) :
    Set.InjOn (S.tokPos cz cz' S.A) S.tokens := by
  intro q hq q' hq' heq
  have key : ∀ v, q ∈ S.tokAt cz cz' S.A v → q' ∈ S.tokAt cz cz' S.A v := by
    intro v h
    rw [Data.tokAt, mem_filter] at h ⊢
    exact ⟨hq', heq ▸ h.2⟩
  rcases q with e | ⟨y, i⟩
  · have he : e ∈ S.Y := (mem_tokens_inl e).mp hq
    induction e using Sym2.ind with
    | _ a b =>
    have haA : a ∈ S.A := fr.supp _ he a (Sym2.mem_mk_left a b)
    have hmem : S.rep cz cz' S.A a s(a, b) ∈ S.tokPos cz cz' S.A (.inl s(a, b)) :=
      (S.mem_curY cz cz' S.A).mpr ⟨a, Sym2.mem_mk_left a b, rfl⟩
    rw [rep_full haA] at hmem
    have hinr : ∀ y' i', q' = .inr (y', i') → False := by
      rintro y' i' rfl
      have hy' : y' ∈ S.A := (mem_tokens_inr y' i').mp hq'
      exact inl_ne_inr fr hc he hy' i' heq
    split_ifs at hmem with h
    · have hq'' := key (cz a) (by rw [Data.tokAt, mem_filter]; exact ⟨hq, hmem⟩)
      rw [tokAt_cz fr hc haA] at hq''
      simp only [mem_insert, mem_singleton] at hq''
      rcases hq'' with rfl | rfl
      · rw [h]
      · exact (hinr _ _ rfl).elim
    · have hq'' := key (cz' a) (by rw [Data.tokAt, mem_filter]; exact ⟨hq, hmem⟩)
      rw [tokAt_cz' fr hc haA] at hq''
      simp only [mem_insert, mem_singleton] at hq''
      rcases hq'' with rfl | rfl
      · rw [(star_cases fr haA he (Sym2.mem_mk_left a b)).resolve_left h]
      · exact (hinr _ _ rfl).elim
  · have hy : y ∈ S.A := (mem_tokens_inr y i).mp hq
    have mk : ∀ v, v ∈ S.catTok cz cz' S.A y i → q' ∈ S.tokAt cz cz' S.A v := fun v hv =>
      key v ((mem_tokAt_inr _ _ _ _).mpr ⟨hy, hv⟩)
    fin_cases i
    · have ha := mk (cz y) (by simp [Data.catTok, hy])
      have hb := mk (S.cs y) (by simp [Data.catTok, hy])
      rw [tokAt_cz fr hc hy] at ha
      rw [tokAt_cs fr hc hy] at hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl
      · simp at hb
      · rfl
    · have ha := mk (cz' y) (by simp [Data.catTok, hy])
      have hb := mk (S.ct y) (by simp [Data.catTok, hy])
      rw [tokAt_cz' fr hc hy] at ha
      rw [tokAt_ct fr hc hy] at hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl
      · simp at hb
      · rfl
    · have ha := mk (S.cs y) (by simp [Data.catTok, hy])
      have hb := mk (S.ct y) (by simp [Data.catTok, hy])
      rw [tokAt_cs fr hc hy] at ha
      rw [tokAt_ct fr hc hy] at hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl
      · simp at hb
      · rfl

/-- The final configuration has exactly `|Y| + 3|A|` edges. -/
theorem config_card (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) :
    (S.config cz cz' S.A).card = S.Y.card + 3 * S.A.card := by
  rw [Data.config_eq_image, card_image_of_injOn (tokPos_injOn fr hc), Data.tokens,
    card_disjSum, card_product, card_univ, Fintype.card_fin, Nat.mul_comm]

/-- The degree of `v` in the final configuration is the number of tokens at `v`. -/
theorem load_eq_tokAt (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) (v : V) :
    incidentLoad (S.config cz cz' S.A) v = (S.tokAt cz cz' S.A v).card := by
  unfold incidentLoad
  rw [Data.config_eq_image, filter_image]
  exact card_image_of_injOn ((tokPos_injOn fr hc).mono (filter_subset _ _))

/-- **2-regularity.** In the final configuration every carrier and every
catalytic vertex has degree exactly two, and every other vertex degree zero. -/
theorem final_degree (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) (v : V) :
    (v ∈ S.carriers cz cz' ∪ S.catalytic → incidentLoad (S.config cz cz' S.A) v = 2) ∧
      (v ∉ S.carriers cz cz' ∪ S.catalytic → incidentLoad (S.config cz cz' S.A) v = 0) := by
  rw [load_eq_tokAt fr hc]
  refine ⟨fun hv => ?_, fun hv => by rw [tokAt_other fr hv, card_empty]⟩
  simp only [Data.carriers, Data.catalytic, mem_union, mem_image] at hv
  rcases hv with (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
  · rw [tokAt_cz fr hc hy, card_pair (by simp)]
  · rw [tokAt_cz' fr hc hy, card_pair (by simp)]
  · rw [tokAt_cs fr hc hy, card_pair (by simp)]
  · rw [tokAt_ct fr hc hy, card_pair (by simp)]

theorem final_two_regular (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) (v : V) :
    incidentLoad (S.config cz cz' S.A) v = 0 ∨ incidentLoad (S.config cz cz' S.A) v = 2 := by
  by_cases hv : v ∈ S.carriers cz cz' ∪ S.catalytic
  · exact Or.inr ((final_degree fr hc v).1 hv)
  · exact Or.inl ((final_degree fr hc v).2 hv)

/-- Carriers and catalytic vertices are disjoint. -/
theorem carriers_disjoint_catalytic (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) :
    Disjoint (S.carriers cz cz') S.catalytic := by
  rw [disjoint_left]
  intro v hv hv'
  simp only [Data.carriers, Data.catalytic, mem_union, mem_image] at hv hv'
  have hZ : v ∈ Z₀ := by
    rcases hv' with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact (fr.mem_cat hy).2.1
    · exact (fr.mem_cat hy).2.2
  rcases hv with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact (hc.fresh y hy).1 hZ
  · exact (hc.fresh y hy).2 hZ

/-- The original active vertices and the catalyst centres are isolated. -/
theorem originals_isolated (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) : incidentLoad (S.config cz cz' S.A) y = 0 ∧
      incidentLoad (S.config cz cz' S.A) (S.co y) = 0 := by
  have hnot : ∀ w ∈ Z₀, (∀ y' ∈ S.A, w ≠ S.cs y' ∧ w ≠ S.ct y') →
      w ∉ S.carriers cz cz' ∪ S.catalytic := by
    intro w hw hcat hmem
    simp only [Data.carriers, Data.catalytic, mem_union, mem_image] at hmem
    rcases hmem with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hc.fresh u hu).1 hw
    · exact (hc.fresh u hu).2 hw
    · exact (hcat u hu).1 rfl
    · exact (hcat u hu).2 rfl
  refine ⟨(final_degree fr hc y).2 (hnot y (fr.ZA hy) ?_),
    (final_degree fr hc _).2 (hnot _ (fr.mem_cat hy).1 ?_)⟩
  · intro y' hy'
    obtain ⟨-, h2, h3⟩ := fr.cat_notA hy'
    exact ⟨fun h => h2 (h ▸ hy), fun h => h3 (h ▸ hy)⟩
  · intro y' hy'
    by_cases h : y = y'
    · subst h
      exact ⟨(fr.distinct y hy).1, (fr.distinct y hy).2.1⟩
    · have hd := fr.vdisj y hy y' hy' h
      have hco : S.co y ∈ catVerts (S.co y) (S.cs y) (S.ct y) := by simp [catVerts]
      refine ⟨fun h' => disjoint_left.mp hd hco (by rw [h']; simp [catVerts]),
        fun h' => disjoint_left.mp hd hco (by rw [h']; simp [catVerts])⟩

omit [Fintype V] in
/-- **Separation (i):** every catalytic token's position has a catalytic endpoint. -/
theorem catalytic_edge_endpoint {y : V} (hy : y ∈ S.A) (i : Fin 3) :
    ∃ w ∈ S.catalytic, w ∈ S.tokPos cz cz' S.A (.inr (y, i)) := by
  have hcs : S.cs y ∈ S.catalytic := mem_union.mpr (Or.inl (mem_image_of_mem _ hy))
  have hct : S.ct y ∈ S.catalytic := mem_union.mpr (Or.inr (mem_image_of_mem _ hy))
  fin_cases i
  · exact ⟨_, hcs, by simp [Data.tokPos, Data.catTok, hy]⟩
  · exact ⟨_, hct, by simp [Data.tokPos, Data.catTok, hy]⟩
  · exact ⟨_, hcs, by simp [Data.tokPos, Data.catTok]⟩

/-- A carrier adjacent to `cs y` in the final configuration is `cz y`. -/
theorem carrier_adj_cs (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) {k : V} (hk : k ∈ S.carriers cz cz')
    (hadj : s(S.cs y, k) ∈ S.config cz cz' S.A) : k = cz y := by
  rw [Data.config_eq_image, mem_image] at hadj
  obtain ⟨q, hq, hpos⟩ := hadj
  have hat : q ∈ S.tokAt cz cz' S.A (S.cs y) := by
    rw [Data.tokAt, mem_filter, hpos]; exact ⟨hq, Sym2.mem_mk_left _ _⟩
  rw [tokAt_cs fr hc hy] at hat
  have hkZ : k ∉ Z₀ := by
    simp only [Data.carriers, mem_union, mem_image] at hk
    rcases hk with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact (hc.fresh u hu).1
    · exact (hc.fresh u hu).2
  obtain ⟨h0, -, h2⟩ := catTok_full (cz := cz) (cz' := cz') hy
  simp only [mem_insert, mem_singleton] at hat
  rcases hat with rfl | rfl
  · simp only [Data.tokPos] at hpos
    rw [h0] at hpos
    rcases Sym2.eq_iff.mp hpos with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (carrier_ne_cat fr hc hy hy).1
    · exact h.symm
  · simp only [Data.tokPos] at hpos
    rw [h2] at hpos
    rcases Sym2.eq_iff.mp hpos with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd (h ▸ (fr.mem_cat hy).2.2) hkZ
    · exact absurd (h ▸ (fr.mem_cat hy).2.1) hkZ

/-- A carrier adjacent to `ct y` in the final configuration is `cz' y`. -/
theorem carrier_adj_ct (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {y : V}
    (hy : y ∈ S.A) {k : V} (hk : k ∈ S.carriers cz cz')
    (hadj : s(S.ct y, k) ∈ S.config cz cz' S.A) : k = cz' y := by
  rw [Data.config_eq_image, mem_image] at hadj
  obtain ⟨q, hq, hpos⟩ := hadj
  have hat : q ∈ S.tokAt cz cz' S.A (S.ct y) := by
    rw [Data.tokAt, mem_filter, hpos]; exact ⟨hq, Sym2.mem_mk_left _ _⟩
  rw [tokAt_ct fr hc hy] at hat
  have hkZ : k ∉ Z₀ := by
    simp only [Data.carriers, mem_union, mem_image] at hk
    rcases hk with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact (hc.fresh u hu).1
    · exact (hc.fresh u hu).2
  obtain ⟨-, h1, h2⟩ := catTok_full (cz := cz) (cz' := cz') hy
  simp only [mem_insert, mem_singleton] at hat
  rcases hat with rfl | rfl
  · simp only [Data.tokPos] at hpos
    rw [h1] at hpos
    rcases Sym2.eq_iff.mp hpos with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (carrier_ne_cat fr hc hy hy).2.2.2
    · exact h.symm
  · simp only [Data.tokPos] at hpos
    rw [h2] at hpos
    rcases Sym2.eq_iff.mp hpos with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (cs_ne_ct fr hy hy)
    · exact (hkZ (h ▸ (fr.mem_cat hy).2.1)).elim

/-- **Separation (ii):** each catalytic vertex is adjacent to at most one carrier. -/
theorem catalytic_one_carrier (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {w : V}
    (hw : w ∈ S.catalytic) :
    ((S.carriers cz cz').filter fun k => s(w, k) ∈ S.config cz cz' S.A).card ≤ 1 := by
  simp only [Data.catalytic, mem_union, mem_image] at hw
  rcases hw with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · refine (card_le_card (t := {cz y}) ?_).trans (by simp)
    intro k hk
    obtain ⟨hk, hadj⟩ := mem_filter.mp hk
    exact mem_singleton.mpr (carrier_adj_cs fr hc hy hk hadj)
  · refine (card_le_card (t := {cz' y}) ?_).trans (by simp)
    intro k hk
    obtain ⟨hk, hadj⟩ := mem_filter.mp hk
    exact mem_singleton.mpr (carrier_adj_ct fr hc hy hk hadj)

end

end PartitionedTriangleAbsorption.CatalystInsertionStage89
