/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Defs

/-!
# Pairings (matchings) given as sets of ordered pairs

Tools for the One Oddball Cleaning Lemma 15.7: a *pairing* of a graph `F` is a finite set of
ordered pairs `(x, y)` of adjacent vertices, any two of which are vertex-disjoint; `verts M` is
the set of matched vertices.

* `IsPairing.union`: pairings on disjoint vertex sets combine;
* `exists_pairing_greedy`: a pairing with `t` pairs inside a set `X` in which every vertex has
  at least `d ≥ 2t` neighbours (greedy);
* `exists_pairing_large`: a pairing with `t` pairs inside `X` as soon as every vertex has at
  least `d ≥ t` neighbours in `X` and `|X| > 2t` (a maximum pairing has no augmenting path of
  length three);
* `exists_pairing_into`: a pairing of `X` with part of `Y` (Hall's theorem) when every vertex of `X`
  has at least `|X|` neighbours in `Y`;
* `pairing_of_equiv`: a bijection `X ≃ Y` along edges is a pairing covering `X ∪ Y`.
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [DecidableEq V]

/-- `M` is a pairing of `F`: pairs of adjacent vertices, pairwise vertex-disjoint. -/
def IsPairing (F : SimpleGraph V) (M : Finset (V × V)) : Prop :=
  (∀ q ∈ M, F.Adj q.1 q.2) ∧
    ∀ q ∈ M, ∀ q' ∈ M, q ≠ q' → q.1 ≠ q'.1 ∧ q.1 ≠ q'.2 ∧ q.2 ≠ q'.1 ∧ q.2 ≠ q'.2

/-- The vertices covered by the pairs of `M`. -/
def verts (M : Finset (V × V)) : Finset V := M.biUnion (fun q => {q.1, q.2})

lemma mem_verts {M : Finset (V × V)} {w : V} : w ∈ verts M ↔ ∃ q ∈ M, q.1 = w ∨ q.2 = w := by
  simp only [verts, mem_biUnion, mem_insert, mem_singleton]
  constructor
  · rintro ⟨q, hq, h⟩; exact ⟨q, hq, h.imp Eq.symm Eq.symm⟩
  · rintro ⟨q, hq, h⟩; exact ⟨q, hq, h.imp Eq.symm Eq.symm⟩

lemma verts_union (M M' : Finset (V × V)) : verts (M ∪ M') = verts M ∪ verts M' :=
  union_biUnion

lemma verts_insert (M : Finset (V × V)) (q : V × V) :
    verts (insert q M) = {q.1, q.2} ∪ verts M := by
  simp [verts, biUnion_insert]

lemma verts_mono {M M' : Finset (V × V)} (h : M ⊆ M') : verts M ⊆ verts M' :=
  biUnion_subset_biUnion_of_subset_left _ h

omit [DecidableEq V] in
lemma IsPairing.mono {F : SimpleGraph V} {M M' : Finset (V × V)} (h : IsPairing F M')
    (hM : M ⊆ M') : IsPairing F M :=
  ⟨fun q hq => h.1 q (hM hq), fun q hq q' hq' hne => h.2 q (hM hq) q' (hM hq') hne⟩

omit [DecidableEq V] in
lemma IsPairing.ne {F : SimpleGraph V} {M : Finset (V × V)} (h : IsPairing F M) {q : V × V}
    (hq : q ∈ M) : q.1 ≠ q.2 := (h.1 q hq).ne

lemma IsPairing.card_verts {F : SimpleGraph V} {M : Finset (V × V)} (h : IsPairing F M) :
    (verts M).card = 2 * M.card := by
  unfold verts
  rw [card_biUnion]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun q hq => ?_
    rw [card_pair (h.ne hq)]
  · intro q hq q' hq' hne
    obtain ⟨h1, h2, h3, h4⟩ := h.2 q hq q' hq' hne
    simp only [disjoint_insert_left, disjoint_insert_right, mem_insert, mem_singleton,
      disjoint_singleton]
    tauto

lemma IsPairing.union {F : SimpleGraph V} {M M' : Finset (V × V)} (h : IsPairing F M)
    (h' : IsPairing F M') (hd : Disjoint (verts M) (verts M')) : IsPairing F (M ∪ M') := by
  have hv : ∀ q ∈ M, ∀ q' ∈ M', q.1 ≠ q'.1 ∧ q.1 ≠ q'.2 ∧ q.2 ≠ q'.1 ∧ q.2 ≠ q'.2 := by
    intro q hq q' hq'
    have m1 : q.1 ∈ verts M := mem_verts.mpr ⟨q, hq, Or.inl rfl⟩
    have m2 : q.2 ∈ verts M := mem_verts.mpr ⟨q, hq, Or.inr rfl⟩
    have m3 : q'.1 ∈ verts M' := mem_verts.mpr ⟨q', hq', Or.inl rfl⟩
    have m4 : q'.2 ∈ verts M' := mem_verts.mpr ⟨q', hq', Or.inr rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first
        | exact disjoint_left.mp hd m1 (he ▸ m3) | exact disjoint_left.mp hd m1 (he ▸ m4)
        | exact disjoint_left.mp hd m2 (he ▸ m3) | exact disjoint_left.mp hd m2 (he ▸ m4)
  refine ⟨fun q hq => ?_, fun q hq q' hq' hne => ?_⟩
  · rcases mem_union.mp hq with hq | hq
    · exact h.1 q hq
    · exact h'.1 q hq
  · rcases mem_union.mp hq with hq | hq <;> rcases mem_union.mp hq' with hq' | hq'
    · exact h.2 q hq q' hq' hne
    · exact hv q hq q' hq'
    · obtain ⟨a, b, c, d⟩ := hv q' hq' q hq
      exact ⟨a.symm, c.symm, b.symm, d.symm⟩
    · exact h'.2 q hq q' hq' hne

lemma isPairing_insert {F : SimpleGraph V} {M : Finset (V × V)} (h : IsPairing F M)
    {x y : V} (hxy : F.Adj x y) (hx : x ∉ verts M) (hy : y ∉ verts M) :
    IsPairing F (insert (x, y) M) := by
  have hq : (x, y) ∉ M := fun hm => hx (mem_verts.mpr ⟨_, hm, Or.inl rfl⟩)
  rw [insert_eq]
  refine IsPairing.union ⟨fun q hq => ?_, fun q hq q' hq' hne => ?_⟩ h ?_
  · rw [mem_singleton] at hq; subst hq; exact hxy
  · rw [mem_singleton] at hq hq'; exact absurd (hq.trans hq'.symm) hne
  · rw [show verts {(x, y)} = {x, y} by simp [verts]]
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hx, hy⟩

/-! ### Greedy pairings -/

/-- **Greedy pairing.**  If every vertex of `X` has at least `d` neighbours in `X`, `2t ≤ d`
and `2t ≤ |X|`, there is a pairing with `t` pairs inside `X`. -/
lemma exists_pairing_greedy (F : SimpleGraph V) [DecidableRel F.Adj] (X : Finset V) (d : ℕ)
    (hdeg : ∀ x ∈ X, d ≤ (X.filter (F.Adj x)).card) :
    ∀ t : ℕ, 2 * t ≤ d → 2 * t ≤ X.card →
      ∃ M : Finset (V × V), IsPairing F M ∧ verts M ⊆ X ∧ M.card = t := by
  intro t
  induction t with
  | zero => intro _ _; exact ⟨∅, ⟨by simp, by simp⟩, by simp [verts], rfl⟩
  | succ t ih =>
    intro hd hX
    obtain ⟨M, hM, hMX, hMc⟩ := ih (by omega) (by omega)
    have hvc : (verts M).card = 2 * t := by rw [hM.card_verts, hMc]
    obtain ⟨x, hxX, hxM⟩ : ∃ x ∈ X, x ∉ verts M := by
      by_contra hcon
      push_neg at hcon
      have := card_le_card (show X ⊆ verts M from hcon)
      omega
    have hcard : 0 < ((X.filter (F.Adj x)) \ verts M).card := by
      have h1 := le_card_sdiff (verts M) (X.filter (F.Adj x))
      have h2 := hdeg x hxX
      omega
    obtain ⟨y, hy⟩ := card_pos.mp hcard
    obtain ⟨hy1, hyM⟩ := mem_sdiff.mp hy
    obtain ⟨hyX, hxy⟩ := mem_filter.mp hy1
    refine ⟨insert (x, y) M, isPairing_insert hM hxy hxM hyM, ?_, ?_⟩
    · rw [verts_insert]
      intro w hw
      rcases mem_union.mp hw with hw | hw
      · simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      · exact hMX hw
    · rw [card_insert_of_notMem (fun hm => hxM (mem_verts.mpr ⟨_, hm, Or.inl rfl⟩)), hMc]

/-! ### Large pairings (no augmenting path of length three) -/

lemma card_filter_pair (P : V → Prop) [DecidablePred P] {x y : V} (hxy : x ≠ y) :
    (({x, y} : Finset V).filter P).card = (if P x then 1 else 0) + (if P y then 1 else 0) := by
  rw [filter_insert, filter_singleton]
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy, hxy]

/-- **Large pairing.**  If every vertex of `X` has at least `d` neighbours in `X`, `t ≤ d` and
`2t < |X|`, there is a pairing with `t` pairs inside `X`. -/
lemma exists_pairing_large (F : SimpleGraph V) [DecidableRel F.Adj] (X : Finset V) (d t : ℕ)
    (hdeg : ∀ x ∈ X, d ≤ (X.filter (F.Adj x)).card) (htd : t ≤ d) (htX : 2 * t + 1 ≤ X.card) :
    ∃ M : Finset (V × V), IsPairing F M ∧ verts M ⊆ X ∧ M.card = t := by
  classical
  -- a pairing inside `X` of maximum size
  set S := ((X ×ˢ X).powerset.filter (fun M => IsPairing F M)) with hS
  have hSne : S.Nonempty := ⟨∅, by simp [hS, IsPairing]⟩
  obtain ⟨M, hMS, hmax⟩ := exists_max_image S Finset.card hSne
  obtain ⟨hMsub, hM⟩ := by simpa [hS] using hMS
  have hMX : verts M ⊆ X := by
    intro w hw
    obtain ⟨q, hq, hqw⟩ := mem_verts.mp hw
    have := mem_product.mp (hMsub hq)
    rcases hqw with rfl | rfl
    · exact this.1
    · exact this.2
  have hmax' : ∀ M' : Finset (V × V), IsPairing F M' → verts M' ⊆ X → M'.card ≤ M.card := by
    intro M' hM' hM'X
    refine hmax M' ?_
    simp only [hS, mem_filter, mem_powerset]
    refine ⟨fun q hq => mem_product.mpr ⟨hM'X (mem_verts.mpr ⟨q, hq, Or.inl rfl⟩),
      hM'X (mem_verts.mpr ⟨q, hq, Or.inr rfl⟩)⟩, hM'⟩
  by_cases hbig : t ≤ M.card
  · obtain ⟨M', hM'M, hM'c⟩ := exists_subset_card_eq hbig
    exact ⟨M', hM.mono hM'M, (verts_mono hM'M).trans hMX, hM'c⟩
  exfalso
  push_neg at hbig
  have hvc : (verts M).card = 2 * M.card := hM.card_verts
  -- two unmatched vertices
  have hfree : 2 ≤ (X \ verts M).card := by
    have := le_card_sdiff (verts M) X
    omega
  obtain ⟨u, hu, w, hw, huw⟩ := one_lt_card.mp (by omega : 1 < (X \ verts M).card)
  obtain ⟨huX, huM⟩ := mem_sdiff.mp hu
  obtain ⟨hwX, hwM⟩ := mem_sdiff.mp hw
  -- neighbours of an unmatched vertex are matched
  have hnb : ∀ a ∈ X, a ∉ verts M → X.filter (F.Adj a) ⊆ verts M := by
    intro a haX haM b hb
    obtain ⟨hbX, hab⟩ := mem_filter.mp hb
    by_contra hbM
    have hP := isPairing_insert hM hab haM hbM
    have := hmax' _ hP (by
      rw [verts_insert]; intro z hz
      rcases mem_union.mp hz with hz | hz
      · simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
      · exact hMX hz)
    rw [card_insert_of_notMem (fun hm => haM (mem_verts.mpr ⟨_, hm, Or.inl rfl⟩))] at this
    omega
  -- no augmenting path of length three through a pair of `M`
  have haug : ∀ q ∈ M, ∀ x y : V, ((x = q.1 ∧ y = q.2) ∨ (x = q.2 ∧ y = q.1)) →
      ¬ (F.Adj u x ∧ F.Adj w y) := by
    rintro q hq x y hxy ⟨h1, h2⟩
    set M' := insert (u, x) (insert (w, y) (M.erase q)) with hM'
    have hE : IsPairing F (M.erase q) := hM.mono (erase_subset _ _)
    have hnotE : ∀ z, (z = q.1 ∨ z = q.2) → z ∉ verts (M.erase q) := by
      intro z hz hm
      obtain ⟨q', hq', hh⟩ := mem_verts.mp hm
      obtain ⟨hne, hq'M⟩ := mem_erase.mp hq'
      obtain ⟨a, b, c, d⟩ := hM.2 q hq q' hq'M (Ne.symm hne)
      rcases hz with rfl | rfl <;> rcases hh with hh | hh
      · exact a hh.symm
      · exact b hh.symm
      · exact c hh.symm
      · exact d hh.symm
    have hinM : ∀ z, (z = q.1 ∨ z = q.2) → z ∈ verts M := by
      rintro z (rfl | rfl)
      · exact mem_verts.mpr ⟨q, hq, Or.inl rfl⟩
      · exact mem_verts.mpr ⟨q, hq, Or.inr rfl⟩
    have hx' : x = q.1 ∨ x = q.2 := by rcases hxy with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hy' : y = q.1 ∨ y = q.2 := by rcases hxy with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
    have hxE := hnotE x hx'
    have hyE := hnotE y hy'
    have hxM := hinM x hx'
    have hyM := hinM y hy'
    have huE : u ∉ verts (M.erase q) := fun hm => huM (verts_mono (erase_subset _ _) hm)
    have hwE : w ∉ verts (M.erase q) := fun hm => hwM (verts_mono (erase_subset _ _) hm)
    have hux : u ≠ x := fun h => huM (h ▸ hxM)
    have huy : u ≠ y := fun h => huM (h ▸ hyM)
    have hwx : w ≠ x := fun h => hwM (h ▸ hxM)
    have hxy' : x ≠ y := by
      have := hM.ne hq
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact Ne.symm this
    have hP1 : IsPairing F (insert (w, y) (M.erase q)) := isPairing_insert hE h2 hwE hyE
    have hP2 : IsPairing F M' := by
      refine isPairing_insert hP1 h1 ?_ ?_
      · rw [verts_insert]; simp only [mem_union, mem_insert, mem_singleton, not_or]
        exact ⟨⟨huw, huy⟩, huE⟩
      · rw [verts_insert]; simp only [mem_union, mem_insert, mem_singleton, not_or]
        exact ⟨⟨hwx.symm, hxy'⟩, hxE⟩
    have hM'X : verts M' ⊆ X := by
      rw [hM', verts_insert, verts_insert]
      intro z hz
      simp only [mem_union, mem_insert, mem_singleton] at hz
      rcases hz with (rfl | rfl) | (rfl | rfl) | hz
      · exact huX
      · exact hMX hxM
      · exact hwX
      · exact hMX hyM
      · exact hMX (verts_mono (erase_subset _ _) hz)
    have hc := hmax' M' hP2 hM'X
    have hc1 : (insert (w, y) (M.erase q)).card = M.card := by
      rw [card_insert_of_notMem (fun hm => hwE (mem_verts.mpr ⟨_, hm, Or.inl rfl⟩)),
        card_erase_of_mem hq]
      have : 0 < M.card := card_pos.mpr ⟨q, hq⟩
      omega
    have hc2 : M'.card = M.card + 1 := by
      rw [hM', card_insert_of_notMem, hc1]
      intro hm
      have := mem_verts.mpr ⟨_, hm, Or.inl rfl⟩
      rw [verts_insert] at this
      simp only [mem_union, mem_insert, mem_singleton] at this
      rcases this with (h | h) | h
      · exact huw h
      · exact huy h
      · exact huE h
    omega
  -- counting
  have hcount : ∀ a ∈ X, a ∉ verts M →
      (X.filter (F.Adj a)).card = ∑ q ∈ M, (({q.1, q.2} : Finset V).filter (F.Adj a)).card := by
    intro a haX haM
    have h1 : X.filter (F.Adj a) = (verts M).filter (F.Adj a) := by
      ext b; constructor
      · intro hb; exact mem_filter.mpr ⟨hnb a haX haM hb, (mem_filter.mp hb).2⟩
      · intro hb; obtain ⟨hbM, hab⟩ := mem_filter.mp hb; exact mem_filter.mpr ⟨hMX hbM, hab⟩
    rw [h1, verts, filter_biUnion, card_biUnion]
    intro q hq q' hq' hne
    obtain ⟨h1, h2, h3, h4⟩ := hM.2 q hq q' hq' hne
    refine disjoint_filter_filter ?_
    simp only [disjoint_insert_left, disjoint_insert_right, mem_insert, mem_singleton,
      disjoint_singleton]
    tauto
  have hpair : ∀ q ∈ M, (({q.1, q.2} : Finset V).filter (F.Adj u)).card +
      (({q.1, q.2} : Finset V).filter (F.Adj w)).card ≤ 2 := by
    intro q hq
    have h1 := haug q hq q.1 q.2 (Or.inl ⟨rfl, rfl⟩)
    have h2 := haug q hq q.2 q.1 (Or.inr ⟨rfl, rfl⟩)
    have hq12 : q.1 ≠ q.2 := hM.ne hq
    rw [card_filter_pair _ hq12, card_filter_pair _ hq12]
    by_cases a1 : F.Adj u q.1 <;> by_cases a2 : F.Adj u q.2 <;> by_cases b1 : F.Adj w q.1 <;>
      by_cases b2 : F.Adj w q.2 <;> simp [a1, a2, b1, b2] at h1 h2 ⊢
  have hsum : (X.filter (F.Adj u)).card + (X.filter (F.Adj w)).card ≤ 2 * M.card := by
    rw [hcount u huX huM, hcount w hwX hwM, ← sum_add_distrib]
    calc _ ≤ ∑ q ∈ M, 2 := sum_le_sum hpair
      _ = 2 * M.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have := hdeg u huX
  have := hdeg w hwX
  omega

/-! ### Bipartite pairings -/

/-- **Pairing into a set** (Hall).  If every vertex of `S` has at least `|S|` neighbours in a
disjoint set `T`, then `S` can be paired with a subset `T' ⊆ T`. -/
lemma exists_pairing_into (F : SimpleGraph V) [DecidableRel F.Adj] (S T : Finset V)
    (hST : Disjoint S T) (hdeg : ∀ x ∈ S, S.card ≤ (T.filter (F.Adj x)).card) :
    ∃ M : Finset (V × V), IsPairing F M ∧ ∃ T' ⊆ T, T'.card = S.card ∧ verts M = S ∪ T' ∧
      ∀ q ∈ M, q.1 ∈ S ∧ q.2 ∈ T' := by
  classical
  obtain ⟨f, hfinj, hf⟩ := (all_card_le_biUnion_card_iff_existsInjective'
    (fun x : S => T.filter (F.Adj x.1))).mp (by
      intro s
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · simp
      · calc s.card ≤ S.card := by
              simpa using card_le_card_of_injOn (fun x : S => x.1) (fun x _ => x.2)
                (fun x _ y _ h => Subtype.ext h)
          _ ≤ (T.filter (F.Adj x.1)).card := hdeg x.1 x.2
          _ ≤ _ := card_le_card (subset_biUnion_of_mem (fun x : S => T.filter (F.Adj x.1)) hx))
  have hfT : ∀ x : S, f x ∈ T := fun x => (mem_filter.mp (hf x)).1
  have hfA : ∀ x : S, F.Adj x.1 (f x) := fun x => (mem_filter.mp (hf x)).2
  set M := S.attach.image (fun x => (x.1, f x)) with hMdef
  refine ⟨M, ⟨fun q hq => ?_, fun q hq q' hq' hne => ?_⟩, S.attach.image f, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hq; exact hfA x
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hq
    obtain ⟨y, -, rfl⟩ := mem_image.mp hq'
    have hxy : x ≠ y := fun h => hne (by rw [h])
    refine ⟨fun h => hxy (Subtype.ext h), fun h => ?_, fun h => ?_, fun h => hxy (hfinj h)⟩
    · have h' : x.1 = f y := h
      exact disjoint_left.mp hST x.2 (h' ▸ hfT y)
    · have h' : f x = y.1 := h
      exact disjoint_left.mp hST y.2 (h' ▸ hfT x)
  · intro z hz; obtain ⟨x, -, rfl⟩ := mem_image.mp hz; exact hfT x
  · rw [card_image_of_injective _ hfinj, card_attach]
  · ext z
    simp only [mem_verts, hMdef, mem_image, mem_attach, true_and, mem_union]
    constructor
    · rintro ⟨q, ⟨x, rfl⟩, h | h⟩
      · left; rw [← h]; exact x.2
      · right; exact ⟨x, h⟩
    · rintro (h | ⟨x, rfl⟩)
      · exact ⟨_, ⟨⟨z, h⟩, rfl⟩, Or.inl rfl⟩
      · exact ⟨_, ⟨x, rfl⟩, Or.inr rfl⟩
  · intro q hq
    obtain ⟨x, -, rfl⟩ := mem_image.mp hq
    exact ⟨x.2, mem_image.mpr ⟨x, mem_attach _ _, rfl⟩⟩

/-- A bijection `X ≃ Y` along edges is a pairing covering `X ∪ Y`. -/
lemma pairing_of_equiv (F : SimpleGraph V) (X Y : Finset V) (hXY : Disjoint X Y) (f : X ≃ Y)
    (hf : ∀ x : X, F.Adj x (f x)) :
    ∃ M : Finset (V × V), IsPairing F M ∧ verts M = X ∪ Y ∧ ∀ q ∈ M, q.1 ∈ X ∧ q.2 ∈ Y := by
  classical
  set M := X.attach.image (fun x => (x.1, (f x).1)) with hMdef
  refine ⟨M, ⟨fun q hq => ?_, fun q hq q' hq' hne => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hq; exact hf x
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hq
    obtain ⟨y, -, rfl⟩ := mem_image.mp hq'
    have hxy : x ≠ y := fun h => hne (by rw [h])
    refine ⟨fun h => hxy (Subtype.ext h), fun h => ?_, fun h => ?_, fun h => hxy ?_⟩
    · have h' : x.1 = (f y).1 := h
      exact disjoint_left.mp hXY x.2 (h' ▸ (f y).2)
    · have h' : (f x).1 = y.1 := h
      exact disjoint_left.mp hXY y.2 (h' ▸ (f x).2)
    · exact f.injective (Subtype.ext h)
  · ext z
    simp only [mem_verts, hMdef, mem_image, mem_attach, true_and, mem_union]
    constructor
    · rintro ⟨q, ⟨x, rfl⟩, h | h⟩
      · left; rw [← h]; exact x.2
      · right; rw [← h]; exact (f x).2
    · rintro (h | h)
      · exact ⟨_, ⟨⟨z, h⟩, rfl⟩, Or.inl rfl⟩
      · refine ⟨_, ⟨f.symm ⟨z, h⟩, rfl⟩, Or.inr ?_⟩
        simp
  · intro q hq; obtain ⟨x, -, rfl⟩ := mem_image.mp hq; exact ⟨x.2, (f x).2⟩

/-! ### The triangles of a star given by a pairing of the link -/

open PartitionedTriangleAbsorption in
/-- The triangles `{z, x, y}` for the pairs `(x, y)` of `M`. -/
def starTris (z : V) (M : Finset (V × V)) : Finset (Finset V) :=
  M.image (fun q => ({z, q.1, q.2} : Finset V))

open PartitionedTriangleAbsorption in
lemma mem_triEdges_triple {z a b : V} {e : Sym2 V} (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) :
    e ∈ triEdges ({z, a, b} : Finset V) ↔ e = s(z, a) ∨ e = s(z, b) ∨ e = s(a, b) := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [mk_mem_triEdges]
    simp only [mem_insert, mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        first | exact ⟨by tauto, by tauto, by assumption⟩ | exact ⟨by tauto, by tauto, Ne.symm ‹_›⟩

open PartitionedTriangleAbsorption in
/-- **Star triangles from a pairing of the link of `z`.** -/
lemma starTris_spec (F : SimpleGraph V) (z : V) (M : Finset (V × V)) (hM : IsPairing F M)
    (hz : ∀ w ∈ verts M, F.Adj z w) :
    (∀ t ∈ starTris z M, F.IsNClique 3 t) ∧
    ((starTris z M : Set (Finset V)).PairwiseDisjoint triEdges) ∧
    (∀ e, e ∈ (starTris z M).biUnion triEdges ↔
      (∃ w ∈ verts M, e = s(z, w)) ∨ ∃ q ∈ M, e = s(q.1, q.2)) ∧
    (∀ t ∈ starTris z M, z ∈ t) ∧
    (∀ w, w ≠ z → ((starTris z M).filter (fun t => w ∈ t)).card ≤ 1) ∧
    (starTris z M).card = M.card := by
  have hz1 : ∀ q ∈ M, F.Adj z q.1 := fun q hq => hz _ (mem_verts.mpr ⟨q, hq, Or.inl rfl⟩)
  have hz2 : ∀ q ∈ M, F.Adj z q.2 := fun q hq => hz _ (mem_verts.mpr ⟨q, hq, Or.inr rfl⟩)
  -- distinct pairs give triangles sharing only `z`
  have hshare : ∀ q ∈ M, ∀ q' ∈ M, q ≠ q' → ∀ w, w ∈ ({z, q.1, q.2} : Finset V) →
      w ∈ ({z, q'.1, q'.2} : Finset V) → w = z := by
    intro q hq q' hq' hne w hw hw'
    obtain ⟨a, b, c, d⟩ := hM.2 q hq q' hq' hne
    simp only [mem_insert, mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with h | h | h <;> first | rfl | tauto
  have hinj : ∀ q ∈ M, ∀ q' ∈ M, ({z, q.1, q.2} : Finset V) = {z, q'.1, q'.2} → q = q' := by
    intro q hq q' hq' heq
    by_contra hne
    have := hshare q hq q' hq' hne q.1 (by simp) (by rw [← heq]; simp)
    exact (hz1 q hq).ne this.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hz1 q hq, hz2 q hq, hM.1 q hq⟩
  · intro t ht t' ht' htt
    obtain ⟨q, hq, rfl⟩ := mem_image.mp (mem_coe.mp ht)
    obtain ⟨q', hq', rfl⟩ := mem_image.mp (mem_coe.mp ht')
    have hne : q ≠ q' := fun h => htt (by rw [h])
    rw [Function.onFun, disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx, hy, hxy⟩ := mk_mem_triEdges.mp he
      obtain ⟨hx', hy', -⟩ := mk_mem_triEdges.mp he'
      exact hxy ((hshare q hq q' hq' hne x hx hx').trans (hshare q hq q' hq' hne y hy hy').symm)
  · intro e
    simp only [starTris, mem_biUnion, mem_image]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, he⟩
      rcases (mem_triEdges_triple (hz1 q hq).ne (hz2 q hq).ne (hM.ne hq)).mp he with h | h | h
      · exact Or.inl ⟨q.1, mem_verts.mpr ⟨q, hq, Or.inl rfl⟩, h⟩
      · exact Or.inl ⟨q.2, mem_verts.mpr ⟨q, hq, Or.inr rfl⟩, h⟩
      · exact Or.inr ⟨q, hq, h⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨q, hq, rfl⟩)
      · obtain ⟨q, hq, hqw⟩ := mem_verts.mp hw
        refine ⟨_, ⟨q, hq, rfl⟩, ?_⟩
        rw [mem_triEdges_triple (hz1 q hq).ne (hz2 q hq).ne (hM.ne hq)]
        rcases hqw with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact ⟨_, ⟨q, hq, rfl⟩, (mem_triEdges_triple (hz1 q hq).ne (hz2 q hq).ne
          (hM.ne hq)).mpr (Or.inr (Or.inr rfl))⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := mem_image.mp ht
    simp
  · intro w hw
    rw [card_le_one]
    intro t ht t' ht'
    obtain ⟨ht, hwt⟩ := mem_filter.mp ht
    obtain ⟨ht', hwt'⟩ := mem_filter.mp ht'
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    obtain ⟨q', hq', rfl⟩ := mem_image.mp ht'
    by_contra hne
    exact hw (hshare q hq q' hq' (fun h => hne (by rw [h])) w hwt hwt')
  · exact card_image_of_injOn fun q hq q' hq' h => hinj q hq q' hq' h

end NashWilliams18
