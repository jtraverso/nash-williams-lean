/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Physical perfect pairings in dense typed links

This file is purely combinatorial (no `F₁`-specific content).  It produces **physical**
perfect pairings — not coefficients — in a dense typed link:

* `dense_bipartite_matching`: Hall's theorem for a bipartite relation in which every vertex
  misses at most `γ` vertices of the other side, sides of equal size `k ≥ 2γ`;
* `IsPerfectPairing`: a family of ordered pairs whose 2-sets partition a vertex set `N`, every pair
  satisfying a relation;
* `link_pairing`: for three distinct classes `c, d₁, d₂`, a set `N` of vertices of these classes
  in which every vertex misses at most `γ` vertices of every class it may be paired with (with
  respect to a symmetric relation `ok`), with the parity `|N_c| ≡ |N_{d₁}| + |N_{d₂}| (mod 2)` and the explicit size
  margins `|N_c| ≥ 4γ+1`, `|N_{d₁}|, |N_{d₂}| ≥ 6γ+1`, `|N_{d₁}| + |N_{d₂}| ≥ |N_c| + 8γ + 1`,
  there is a perfect pairing of `N` into pairs of types `c d₁`, `c d₂`, `d₁ d₁`, `d₂ d₂`, all
  satisfying `ok`.

The pairing is used in `CrossingCoverF1.lean` to cover the crossing star of an apex vertex by
edge-disjoint `F₁`-triangles (the cover-down step of an `F₁` vortex level).
-/

namespace NashWilliams18.LinkPairing

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Dense bipartite perfect matching** (Hall).  If `|S| = |T| ≥ 2γ` and every vertex of either
side fails `r` with at most `γ` vertices of the other side, then `r` has a perfect matching
`S → T`. -/
theorem dense_bipartite_matching (S T : Finset V) (r : V → V → Prop)
    [DecidableRel r] (γ : ℕ) (hcard : S.card = T.card) (hk : 2 * γ ≤ S.card)
    (hS : ∀ a ∈ S, (T.filter fun b => ¬ r a b).card ≤ γ)
    (hT : ∀ b ∈ T, (S.filter fun a => ¬ r a b).card ≤ γ) :
    ∃ f : V → V, Set.BijOn f S T ∧ ∀ a ∈ S, r a (f a) := by
  classical
  let t : S → Finset V := fun a => T.filter fun b => r a b
  have hall : ∀ s : Finset S, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
    · simp
    by_cases hsmall : s.card + γ ≤ T.card
    · have h1 : (t a0).card + (T.filter fun b => ¬ r a0 b).card = T.card := by
        simpa [t] using card_filter_add_card_filter_not (s := T) (fun b => r a0 b)
      have h2 := hS a0 a0.2
      have h3 : t a0 ⊆ s.biUnion t := subset_biUnion_of_mem t ha0
      have := card_le_card h3
      omega
    · have hsub : T ⊆ s.biUnion t := by
        intro b hb
        by_contra hnot
        have hall : ∀ a ∈ s, ¬ r a b := by
          intro a ha hr
          exact hnot (mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨hb, hr⟩⟩)
        have hsub2 : s.map (Function.Embedding.subtype _) ⊆ S.filter fun a => ¬ r a b := by
          intro a ha
          obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
          exact mem_filter.mpr ⟨a'.2, hall a' ha'⟩
        have := card_le_card hsub2
        rw [card_map] at this
        have := hT b hb
        omega
      have := card_le_card hsub
      have hsS : s.card ≤ S.card := by
        have := card_le_univ s
        simpa using this
      omega
  obtain ⟨g, hginj, hgmem⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hall
  let f : V → V := fun a => if h : a ∈ S then g ⟨a, h⟩ else a
  have hfS : ∀ a (h : a ∈ S), f a = g ⟨a, h⟩ := fun a h => by simp [f, h]
  have hmaps : Set.MapsTo f S T := by
    intro a ha
    rw [hfS a ha]
    exact (mem_filter.mp (hgmem ⟨a, ha⟩)).1
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    rw [hfS a ha, hfS b hb] at hab
    exact congrArg Subtype.val (hginj hab)
  refine ⟨f, ⟨hmaps, hinj, ?_⟩, fun a ha => ?_⟩
  · have himg : S.image f ⊆ T := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      exact hmaps ha
    have hc : (S.image f).card = T.card := by
      rw [card_image_of_injOn hinj, hcard]
    have heq := eq_of_subset_of_card_le himg hc.ge
    intro b hb
    have : b ∈ S.image f := heq ▸ hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp this
    exact ⟨a, ha, rfl⟩
  · rw [hfS a ha]
    exact (mem_filter.mp (hgmem ⟨a, ha⟩)).2

/-- `P` is a perfect pairing of `N` by `ok`-pairs: the 2-sets `{y, z}` of the pairs `(y, z) ∈ P`
are pairwise disjoint and partition `N`. -/
structure IsPerfectPairing (N : Finset V) (P : Finset (V × V)) (ok : V → V → Prop) : Prop where
  ok : ∀ q ∈ P, ok q.1 q.2
  ne : ∀ q ∈ P, q.1 ≠ q.2
  cover : P.biUnion (fun q => ({q.1, q.2} : Finset V)) = N
  disj : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → Disjoint ({q.1, q.2} : Finset V) {q'.1, q'.2}

lemma IsPerfectPairing.mem_left {N : Finset V} {P : Finset (V × V)} {ok : V → V → Prop}
    (h : IsPerfectPairing N P ok) {q : V × V} (hq : q ∈ P) : q.1 ∈ N := by
  rw [← h.cover]; exact mem_biUnion.mpr ⟨q, hq, by simp⟩

lemma IsPerfectPairing.mem_right {N : Finset V} {P : Finset (V × V)} {ok : V → V → Prop}
    (h : IsPerfectPairing N P ok) {q : V × V} (hq : q ∈ P) : q.2 ∈ N := by
  rw [← h.cover]; exact mem_biUnion.mpr ⟨q, hq, by simp⟩

lemma IsPerfectPairing.union {N N' : Finset V} {P P' : Finset (V × V)} {ok : V → V → Prop}
    (h : IsPerfectPairing N P ok) (h' : IsPerfectPairing N' P' ok) (hNN : Disjoint N N') :
    IsPerfectPairing (N ∪ N') (P ∪ P') ok := by
  have hsub : ∀ q ∈ P, ({q.1, q.2} : Finset V) ⊆ N := fun q hq => by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h.mem_left hq
    · exact h.mem_right hq
  have hsub' : ∀ q ∈ P', ({q.1, q.2} : Finset V) ⊆ N' := fun q hq => by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h'.mem_left hq
    · exact h'.mem_right hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases mem_union.mp hq with hq | hq
    · exact h.ok q hq
    · exact h'.ok q hq
  · intro q hq
    rcases mem_union.mp hq with hq | hq
    · exact h.ne q hq
    · exact h'.ne q hq
  · rw [union_biUnion, h.cover, h'.cover]
  · intro q hq q' hq' hne
    rcases mem_union.mp hq with hq | hq <;> rcases mem_union.mp hq' with hq' | hq'
    · exact h.disj q hq q' hq' hne
    · exact hNN.mono (hsub q hq) (hsub' q' hq')
    · exact (hNN.mono (hsub q' hq') (hsub' q hq)).symm
    · exact h'.disj q hq q' hq' hne

lemma IsPerfectPairing.mono {N : Finset V} {P : Finset (V × V)} {ok ok' : V → V → Prop}
    (h : IsPerfectPairing N P ok) (hok : ∀ y z, ok y z → ok' y z) : IsPerfectPairing N P ok' :=
  ⟨fun q hq => hok _ _ (h.ok q hq), h.ne, h.cover, h.disj⟩

/-- A bijection between disjoint sets gives a perfect pairing of their union. -/
lemma isPerfectPairing_of_bijOn {S T : Finset V} (hST : Disjoint S T) {f : V → V}
    (hf : Set.BijOn f S T) {r : V → V → Prop} (hr : ∀ a ∈ S, r a (f a)) :
    IsPerfectPairing (S ∪ T) (S.image fun a => (a, f a)) r := by
  have hfT : ∀ a ∈ S, f a ∈ T := fun a ha => hf.mapsTo ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact hr a ha
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    intro h
    have h' : a = f a := h
    exact disjoint_left.mp hST ha (by rw [h']; exact hfT a ha)
  · ext v
    simp only [mem_biUnion, mem_image, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨q, ⟨a, ha, rfl⟩, hv | hv⟩
      · exact Or.inl (hv ▸ ha)
      · exact Or.inr (hv ▸ hfT a ha)
    · rintro (hv | hv)
      · exact ⟨(v, f v), ⟨v, hv, rfl⟩, Or.inl rfl⟩
      · obtain ⟨a, ha, rfl⟩ := hf.surjOn hv
        exact ⟨(a, f a), ⟨a, ha, rfl⟩, Or.inr rfl⟩
  · intro q hq q' hq' hne
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hq'
    have hab : a ≠ b := fun h => hne (by rw [h])
    have hfab : f a ≠ f b := fun h => hab (hf.injOn ha hb h)
    have h1 : a ≠ f b := fun h => disjoint_left.mp hST ha (h ▸ hfT b hb)
    have h2 : f a ≠ b := fun h => disjoint_left.mp hST hb (h ▸ hfT a ha)
    rw [disjoint_left]
    intro v hv hv'
    simp only [mem_insert, mem_singleton] at hv hv'
    rcases hv with rfl | rfl <;> rcases hv' with h | h
    · exact hab h
    · exact h1 h
    · exact h2 h
    · exact hfab h

/-- Dense bipartite pairing between two disjoint blocks, read off from `dense_bipartite_matching`
for a symmetric relation. -/
lemma block_pairing (S T : Finset V) (hST : Disjoint S T) (r : V → V → Prop) [DecidableRel r]
    (γ : ℕ) (hcard : S.card = T.card) (hk : 2 * γ ≤ S.card)
    (hS : ∀ a ∈ S, (T.filter fun b => ¬ r a b).card ≤ γ)
    (hT : ∀ b ∈ T, (S.filter fun a => ¬ r a b).card ≤ γ) :
    ∃ P, IsPerfectPairing (S ∪ T) P r := by
  obtain ⟨f, hf, hr⟩ := dense_bipartite_matching S T r γ hcard hk hS hT
  exact ⟨_, isPerfectPairing_of_bijOn hST hf hr⟩

/-- The four admissible pair types in the link of an apex of class `c`, with partner classes
`d₁, d₂`: `c d₁`, `c d₂`, `d₁ d₁`, `d₂ d₂`. -/
def LinkPat (c d1 d2 i j : Fin 4) : Prop :=
  (i = c ∧ j = d1) ∨ (i = c ∧ j = d2) ∨ (i = d1 ∧ j = d1) ∨ (i = d2 ∧ j = d2)

instance (c d1 d2 i j : Fin 4) : Decidable (LinkPat c d1 d2 i j) := by
  unfold LinkPat; infer_instance

/-- Choice of the block sizes. -/
lemma exists_block_sizes (γ a a1 a2 : ℕ) (hc : 4 * γ + 1 ≤ a) (h1 : 6 * γ + 1 ≤ a1)
    (h2 : 6 * γ + 1 ≤ a2) (hsum : a + 8 * γ + 1 ≤ a1 + a2) (hpar : (a + a1 + a2) % 2 = 0) :
    ∃ k m r : ℕ, 2 * γ ≤ k ∧ 2 * γ ≤ a - k ∧ 2 * γ ≤ m ∧ 2 * γ ≤ r ∧ k ≤ a ∧
      k + 2 * m = a1 ∧ (a - k) + 2 * r = a2 := by
  have key : ∃ k, 2 * γ ≤ k ∧ k + 2 * γ ≤ a ∧ k + 4 * γ ≤ a1 ∧ a + 4 * γ ≤ a2 + k ∧
      (a1 - k) % 2 = 0 := by
    by_cases hlo : 2 * γ ≤ a + 4 * γ - a2
    · by_cases hp : (a1 - (a + 4 * γ - a2)) % 2 = 0
      · exact ⟨a + 4 * γ - a2, by omega, by omega, by omega, by omega, hp⟩
      · exact ⟨a + 4 * γ - a2 + 1, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases hp : (a1 - 2 * γ) % 2 = 0
      · exact ⟨2 * γ, le_refl _, by omega, by omega, by omega, hp⟩
      · exact ⟨2 * γ + 1, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ := key
  refine ⟨k, (a1 - k) / 2, (a2 - (a - k)) / 2, hk1, by omega, by omega, by omega, by omega,
    by omega, by omega⟩

/-- Split a block of size `2m` into two halves of size `m`. -/
lemma exists_halves (W : Finset V) (m : ℕ) (hW : W.card = 2 * m) :
    ∃ W1 W2 : Finset V, W1 ⊆ W ∧ W2 ⊆ W ∧ Disjoint W1 W2 ∧ W1 ∪ W2 = W ∧
      W1.card = m ∧ W2.card = m := by
  obtain ⟨W1, hW1, hc⟩ := exists_subset_card_eq (s := W) (n := m) (by omega)
  refine ⟨W1, W \ W1, hW1, sdiff_subset, disjoint_sdiff, union_sdiff_of_subset hW1, hc, ?_⟩
  rw [card_sdiff_of_subset hW1]; omega

/-- **Physical perfect pairing of a dense typed link.**  Let `c, d₁, d₂` be distinct classes and
`N` a set of vertices of these classes.  Suppose that every `y ∈ N` fails the symmetric relation
`ok` with at most `γ` vertices of each class `j` inside `N` such that `(p y, j)` is a link pair
type, that `|N_c| ≡ |N_{d₁}| + |N_{d₂}|
(mod 2)`, and the margins `|N_c| ≥ 4γ+1`, `|N_{d₁}|, |N_{d₂}| ≥ 6γ+1`,
`|N_{d₁}| + |N_{d₂}| ≥ |N_c| + 8γ + 1` hold.  Then `N` has a perfect pairing into `ok`-pairs of
types `c d₁`, `c d₂`, `d₁ d₁`, `d₂ d₂`. -/
theorem link_pairing (p : V → Fin 4) (c d1 d2 : Fin 4) (hc1 : c ≠ d1) (hc2 : c ≠ d2)
    (h12 : d1 ≠ d2) (N : Finset V) (ok : V → V → Prop) [DecidableRel ok]
    (hsymm : ∀ y z, ok y z → ok z y) (γ : ℕ)
    (hN : ∀ y ∈ N, p y = c ∨ p y = d1 ∨ p y = d2)
    (hdense : ∀ y ∈ N, ∀ j : Fin 4, (LinkPat c d1 d2 (p y) j ∨ LinkPat c d1 d2 j (p y)) →
      (N.filter fun z => p z = j ∧ ¬ ok y z).card ≤ γ)
    (hac : 4 * γ + 1 ≤ (N.filter fun y => p y = c).card)
    (ha1 : 6 * γ + 1 ≤ (N.filter fun y => p y = d1).card)
    (ha2 : 6 * γ + 1 ≤ (N.filter fun y => p y = d2).card)
    (hsum : (N.filter fun y => p y = c).card + 8 * γ + 1 ≤
      (N.filter fun y => p y = d1).card + (N.filter fun y => p y = d2).card)
    (hpar : ((N.filter fun y => p y = c).card + (N.filter fun y => p y = d1).card +
      (N.filter fun y => p y = d2).card) % 2 = 0) :
    ∃ P, IsPerfectPairing N P (fun y z => ok y z ∧ LinkPat c d1 d2 (p y) (p z)) := by
  classical
  set Nc := N.filter fun y => p y = c
  set N1 := N.filter fun y => p y = d1
  set N2 := N.filter fun y => p y = d2
  obtain ⟨k, m, r, hk, hl, hm, hr, hka, hk1, hk2⟩ :=
    exists_block_sizes γ Nc.card N1.card N2.card hac ha1 ha2 hsum hpar
  -- blocks
  obtain ⟨K, hK, hKc⟩ := exists_subset_card_eq (s := Nc) (n := k) hka
  obtain ⟨K', hK', hK'c⟩ := exists_subset_card_eq (s := N1) (n := k) (by omega)
  obtain ⟨L', hL', hL'c⟩ := exists_subset_card_eq (s := N2) (n := Nc.card - k) (by omega)
  set L := Nc \ K
  set M := N1 \ K'
  set R := N2 \ L'
  have hLc : L.card = Nc.card - k := by rw [card_sdiff_of_subset hK, hKc]
  have hMc : M.card = 2 * m := by rw [card_sdiff_of_subset hK', hK'c]; omega
  have hRc : R.card = 2 * r := by rw [card_sdiff_of_subset hL', hL'c]; omega
  obtain ⟨M1, M2, hM1, hM2, hM12, hMu, hM1c, hM2c⟩ := exists_halves M m hMc
  obtain ⟨R1, R2, hR1, hR2, hR12, hRu, hR1c, hR2c⟩ := exists_halves R r hRc
  -- class membership
  have mc : ∀ y ∈ Nc, y ∈ N ∧ p y = c := fun y hy => mem_filter.mp hy
  have m1 : ∀ y ∈ N1, y ∈ N ∧ p y = d1 := fun y hy => mem_filter.mp hy
  have m2 : ∀ y ∈ N2, y ∈ N ∧ p y = d2 := fun y hy => mem_filter.mp hy
  have hLsub : L ⊆ Nc := sdiff_subset
  have hMsub : M ⊆ N1 := sdiff_subset
  have hRsub : R ⊆ N2 := sdiff_subset
  -- the relation used in every block
  set rel := fun y z => ok y z ∧ LinkPat c d1 d2 (p y) (p z) with hrel
  -- generic density transfer
  have dens : ∀ (S T : Finset V) (i j : Fin 4), LinkPat c d1 d2 i j →
      (∀ y ∈ S, y ∈ N ∧ p y = i) → (∀ y ∈ T, y ∈ N ∧ p y = j) →
      (∀ a ∈ S, (T.filter fun b => ¬ rel a b).card ≤ γ) ∧
      (∀ b ∈ T, (S.filter fun a => ¬ rel a b).card ≤ γ) := by
    intro S T i j hij hS hT
    constructor
    · intro a ha
      refine le_trans (card_le_card ?_)
        (hdense a (hS a ha).1 j (Or.inl (by rw [(hS a ha).2]; exact hij)))
      intro b hb
      obtain ⟨hbT, hnot⟩ := mem_filter.mp hb
      refine mem_filter.mpr ⟨(hT b hbT).1, (hT b hbT).2, fun hok => hnot ⟨hok, ?_⟩⟩
      rw [(hS a ha).2, (hT b hbT).2]; exact hij
    · intro b hb
      refine le_trans (card_le_card ?_)
        (hdense b (hT b hb).1 i (Or.inr (by rw [(hT b hb).2]; exact hij)))
      intro a ha
      obtain ⟨haS, hnot⟩ := mem_filter.mp ha
      refine mem_filter.mpr ⟨(hS a haS).1, (hS a haS).2, fun hok => hnot ⟨hsymm _ _ hok, ?_⟩⟩
      rw [(hS a haS).2, (hT b hb).2]; exact hij
  have dKK := dens K K' c d1 (Or.inl ⟨rfl, rfl⟩) (fun y hy => mc y (hK hy))
    (fun y hy => m1 y (hK' hy))
  have dLL := dens L L' c d2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (fun y hy => mc y (hLsub hy))
    (fun y hy => m2 y (hL' hy))
  have dMM := dens M1 M2 d1 d1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (fun y hy => m1 y (hMsub (hM1 hy))) (fun y hy => m1 y (hMsub (hM2 hy)))
  have dRR := dens R1 R2 d2 d2 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    (fun y hy => m2 y (hRsub (hR1 hy))) (fun y hy => m2 y (hRsub (hR2 hy)))
  -- disjointness of the classes
  have dcl : ∀ (S T : Finset V) (i j : Fin 4), i ≠ j → (∀ y ∈ S, p y = i) →
      (∀ y ∈ T, p y = j) → Disjoint S T := by
    intro S T i j hij hS hT
    rw [disjoint_left]; intro y hyS hyT; exact hij ((hS y hyS).symm.trans (hT y hyT))
  have hKK'd : Disjoint K K' :=
    dcl K K' c d1 hc1 (fun y hy => (mc y (hK hy)).2) (fun y hy => (m1 y (hK' hy)).2)
  have hLL'd : Disjoint L L' :=
    dcl L L' c d2 hc2 (fun y hy => (mc y (hLsub hy)).2) (fun y hy => (m2 y (hL' hy)).2)
  obtain ⟨P1, hP1⟩ := block_pairing K K' hKK'd rel γ (by rw [hKc, hK'c]) (by omega) dKK.1 dKK.2
  obtain ⟨P2, hP2⟩ := block_pairing L L' hLL'd rel γ (by rw [hLc, hL'c]) (by omega) dLL.1 dLL.2
  obtain ⟨P3, hP3⟩ := block_pairing M1 M2 hM12 rel γ (by rw [hM1c, hM2c]) (by omega)
    dMM.1 dMM.2
  obtain ⟨P4, hP4⟩ := block_pairing R1 R2 hR12 rel γ (by rw [hR1c, hR2c]) (by omega)
    dRR.1 dRR.2
  -- assemble
  have hKL : K ∪ L = Nc := union_sdiff_of_subset hK
  have hK'M : K' ∪ M = N1 := union_sdiff_of_subset hK'
  have hL'R : L' ∪ R = N2 := union_sdiff_of_subset hL'
  have hNsplit : N = Nc ∪ N1 ∪ N2 := by
    ext y
    simp only [Nc, N1, N2, mem_union, mem_filter]
    constructor
    · intro hy
      rcases hN y hy with h | h | h
      · exact Or.inl (Or.inl ⟨hy, h⟩)
      · exact Or.inl (Or.inr ⟨hy, h⟩)
      · exact Or.inr ⟨hy, h⟩
    · rintro ((⟨hy, -⟩ | ⟨hy, -⟩) | ⟨hy, -⟩) <;> exact hy
  have dc1 : Disjoint Nc N1 := dcl Nc N1 c d1 hc1 (fun y hy => (mc y hy).2) (fun y hy => (m1 y hy).2)
  have dc2 : Disjoint Nc N2 := dcl Nc N2 c d2 hc2 (fun y hy => (mc y hy).2) (fun y hy => (m2 y hy).2)
  have d12 : Disjoint N1 N2 := dcl N1 N2 d1 d2 h12 (fun y hy => (m1 y hy).2) (fun y hy => (m2 y hy).2)
  have hKL_d : Disjoint K L := disjoint_sdiff
  have hK'M_d : Disjoint K' M := disjoint_sdiff
  have hL'R_d : Disjoint L' R := disjoint_sdiff
  -- (K ∪ K') ∪ (L ∪ L') ∪ (M1 ∪ M2) ∪ (R1 ∪ R2) = N, pieces pairwise disjoint
  have e12 : Disjoint (K ∪ K') (L ∪ L') := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨hKL_d, dc2.mono hK hL'⟩, ⟨(dc1.mono hLsub hK').symm, d12.mono hK' hL'⟩⟩
  have hP12 := hP1.union hP2 e12
  have hM12u : M1 ∪ M2 = M := hMu
  have hR12u : R1 ∪ R2 = R := hRu
  have e3 : Disjoint (K ∪ K' ∪ (L ∪ L')) (M1 ∪ M2) := by
    rw [hM12u, disjoint_union_left, disjoint_union_left, disjoint_union_left]
    exact ⟨⟨(dc1.mono hK hMsub), hK'M_d⟩, ⟨(dc1.mono hLsub hMsub), (d12.mono hMsub hL').symm⟩⟩
  have hP123 := hP12.union hP3 e3
  have e4 : Disjoint (K ∪ K' ∪ (L ∪ L') ∪ (M1 ∪ M2)) (R1 ∪ R2) := by
    rw [hR12u, hM12u, disjoint_union_left, disjoint_union_left, disjoint_union_left,
      disjoint_union_left]
    exact ⟨⟨⟨dc2.mono hK hRsub, d12.mono hK' hRsub⟩,
      ⟨dc2.mono hLsub hRsub, hL'R_d⟩⟩, d12.mono hMsub hRsub⟩
  have hP1234 := hP123.union hP4 e4
  have hcov : K ∪ K' ∪ (L ∪ L') ∪ (M1 ∪ M2) ∪ (R1 ∪ R2) = N := by
    rw [hM12u, hR12u, hNsplit, ← hKL, ← hK'M, ← hL'R]
    ext y; simp only [mem_union]; tauto
  rw [hcov] at hP1234
  exact ⟨_, hP1234⟩

end NashWilliams18.LinkPairing
