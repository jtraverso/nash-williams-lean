/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.Consumer
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # Typed physical nibble adapter (L5 → L5.a)

Input: a partition `p : V → Fin t`, a family `F` of three-element multiset types,
a graph `J` and weights `φ : Finset V → ℝ` with `0 ≤ φ T ≤ b/n` on every `F`-copy
`T` of `J` and exact unit load `∑_{T ∈ copies p F J, e ∈ triEdges T} φ T = 1` on
every edge `e` of `J`. The weights are an explicit input; nothing here constructs
them, and nothing is inferred from fractional divisibility.

Output (`typed_nibble_packing`): an actual finite family `D` of `F`-copies of `J`,
its edge union `Q = ⋃_{T ∈ D} triEdges T ⊆ E(J)`, with `IsDecomp p F Q D`, and the
actual uncovered set `E(J) \ Q` of maximum degree at most `η n`.

The physical system is `copySystem p F J`: the copies of `J`, enumerated bijectively
by `Fin (copies p F J).card`. The two `triEdges` definitions (Nibble and typed) are
the same expression; `nibble_triEdges_eq` records this without changing either.
No vertex-disjointness is required, the copy family may be empty, and isolated
vertices are included in `V`.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/TypedNibbleAdapter.lean.
Original SHA256: 5d7adf8eff35de53ba95287cd6d96b8bedc37887b6fe8193d816421c7c702e69.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The Nibble and the typed `triEdges` are extensionally (indeed definitionally) equal. -/
theorem nibble_triEdges_eq (T : Finset V) : Nibble.triEdges T = triEdges T := rfl

theorem mem_triEdges_iff {T : Finset V} {x y : V} :
    s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T ∧ x ≠ y :=
  Nibble.mem_triEdges

variable [Fintype V]

omit [DecidableEq V] in
theorem mem_copies_iff {p : V → Fin t} {F : Finset (Multiset (Fin t))} {J : SimpleGraph V}
    {s : Finset V} : s ∈ copies p F J ↔ IsCopy p F J s := by
  simp only [copies, mem_filter, mem_powersetCard, subset_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h.1.card_eq, h⟩⟩

omit [DecidableEq V] [Fintype V] in
theorem isTypedTri_of_isCopy {p : V → Fin t} {F : Finset (Multiset (Fin t))} {J : SimpleGraph V}
    {s : Finset V} (h : IsCopy p F J s) : IsTypedTri p F s :=
  ⟨h.1.card_eq, h.2⟩

/-- Every edge of a copy of `J` is an edge of `J`. -/
theorem triEdges_subset_of_isCopy {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : SimpleGraph V} [DecidableRel J.Adj] {s : Finset V} (h : IsCopy p F J s) :
    triEdges s ⊆ J.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := mem_triEdges_iff.mp he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact h.1.isClique hx hy hxy

/-! ### The physical triangle system of all typed copies -/

/-- The `F`-copies of `J`, enumerated bijectively by `Fin (copies p F J).card`. -/
noncomputable def copySystem (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) : Nibble.TriSystem V (copies p F J).card where
  tri i := ((copies p F J).equivFin.symm i).val
  card_tri i := (mem_copies_iff.mp ((copies p F J).equivFin.symm i).property).1.card_eq
  tri_inj := Subtype.val_injective.comp (copies p F J).equivFin.symm.injective

variable (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : SimpleGraph V)

theorem copySystem_tri_mem (i : Fin (copies p F J).card) :
    (copySystem p F J).tri i ∈ copies p F J :=
  ((copies p F J).equivFin.symm i).property

theorem copySystem_isCopy (i : Fin (copies p F J).card) :
    IsCopy p F J ((copySystem p F J).tri i) :=
  mem_copies_iff.mp (copySystem_tri_mem p F J i)

/-- The enumeration hits every copy (and, being injective, exactly once). -/
theorem copySystem_tri_surj {s : Finset V} (hs : s ∈ copies p F J) :
    ∃ i, (copySystem p F J).tri i = s :=
  ⟨(copies p F J).equivFin ⟨s, hs⟩, by simp [copySystem]⟩

/-- The weights on the physical system are the given weights of the copies. -/
noncomputable def copyWeights (φ : Finset V → ℝ) : Fin (copies p F J).card → ℝ :=
  fun i => φ ((copySystem p F J).tri i)

/-- The physical load of an edge equals the typed load of the input weighting. -/
theorem load_copySystem (φ : Finset V → ℝ) (e : Sym2 V) :
    (copySystem p F J).load (copyWeights p F J φ) e =
      ∑ s ∈ copies p F J with e ∈ triEdges s, φ s := by
  unfold Nibble.TriSystem.load Nibble.TriSystem.edgeTris copyWeights
  refine sum_bij (fun i _ => (copySystem p F J).tri i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨copySystem_tri_mem p F J i, hi.2⟩
  · intro i _ j _ hij
    exact (copySystem p F J).tri_inj hij
  · intro s hs
    rw [mem_filter] at hs
    obtain ⟨i, hi⟩ := copySystem_tri_surj p F J hs.1
    refine ⟨i, ?_, hi⟩
    rw [mem_filter]
    exact ⟨mem_univ _, by rw [hi]; exact hs.2⟩
  · intro i _
    rfl

/-! ### Typeability from exact unit load -/

omit [Fintype V] in
/-- A three-element set containing two distinct vertices `a, b` is `{a, b, c}` for a
third vertex `c`. -/
theorem exists_third_of_card_three {s : Finset V} (hs : s.card = 3) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c, a ≠ c ∧ b ≠ c ∧ s = {a, b, c} := by
  have hb' : b ∈ s.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  have hcard : ((s.erase a).erase b).card = 1 := by
    rw [card_erase_of_mem hb', card_erase_of_mem ha, hs]
  obtain ⟨c, hc⟩ := card_eq_one.mp hcard
  have hcmem : c ∈ (s.erase a).erase b := by rw [hc]; exact mem_singleton_self c
  have hcb : c ≠ b := (mem_erase.mp hcmem).1
  have hca : c ≠ a := (mem_erase.mp (mem_erase.mp hcmem).2).1
  refine ⟨c, hca.symm, hcb.symm, ?_⟩
  rw [← insert_erase ha, ← insert_erase hb', hc]

/-- **Typeability from exact load.** If the copies of `J` through `s(a, b)` carry total
weight `1`, some copy contains `s(a, b)`, hence some type `{p a, p b, k}` lies in `F`. -/
theorem exists_type_of_load_eq_one (φ : Finset V → ℝ) {a b : V}
    (hload : ∑ s ∈ copies p F J with s(a, b) ∈ triEdges s, φ s = 1) :
    ∃ k : Fin t, ({p a, p b, k} : Multiset (Fin t)) ∈ F := by
  obtain ⟨s, hs, -⟩ := exists_ne_zero_of_sum_ne_zero (by rw [hload]; exact one_ne_zero)
  rw [mem_filter] at hs
  obtain ⟨hsc, hab⟩ := hs
  have hcopy := mem_copies_iff.mp hsc
  obtain ⟨ha, hb, hne⟩ := mem_triEdges_iff.mp hab
  obtain ⟨c, hac, hbc, rfl⟩ := exists_third_of_card_three hcopy.1.card_eq ha hb hne
  refine ⟨p c, ?_⟩
  rw [← map_three p hne hac hbc]
  exact hcopy.2

/-! ### The adapter -/

/-- The packing extracted from a physical packing `P` of `copySystem`. -/
noncomputable def packedCopies (P : Finset (Fin (copies p F J).card)) : Finset (Finset V) :=
  P.image (copySystem p F J).tri

theorem edgesOf_eq_biUnion (P : Finset (Fin (copies p F J).card)) :
    Nibble.edgesOf (copySystem p F J) P = (packedCopies p F J P).biUnion triEdges := by
  rw [packedCopies, image_biUnion]
  rfl

theorem isDecomp_packedCopies (P : Finset (Fin (copies p F J).card))
    (hP : Nibble.IsPacking (copySystem p F J) P) :
    IsDecomp p F ((packedCopies p F J P).biUnion triEdges) (packedCopies p F J P) := by
  refine ⟨?_, ?_, rfl⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := mem_image.mp hs
    exact isTypedTri_of_isCopy (copySystem_isCopy p F J i)
  · intro s hs s' hs' hne
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hs'
    exact hP i hi j hj (fun hij => hne (by rw [hij]))

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

open Finset

/-- **Typed physical packing from exact unit loads.** For fixed `b > 0` and `0 < η ≤ 1`
there is `N`, chosen before the vertex type, partition, type family, graph and weights,
such that: for every finite `V` with `n = |V| ≥ N`, every `p, F, J` and every weighting
`φ` with `0 ≤ φ T ≤ b/n` on the `F`-copies of `J` and exact unit load on every edge of
`J`, there is an actual family `D ⊆ copies p F J` whose edge union `Q` is an
`F`-decomposition (`IsDecomp p F Q D`), and the uncovered edges `E(J) \ Q` have maximum
degree at most `η n`. -/
theorem typed_nibble_packing (b η : ℝ) (hb : 0 < b) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : SimpleGraph V)
        [DecidableRel J.Adj] (φ : Finset V → ℝ),
        (∀ s, IsCopy p F J s → 0 ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
        (∀ e ∈ J.edgeFinset, ∑ s ∈ copies p F J with e ∈ triEdges s, φ s = 1) →
        ∃ D : Finset (Finset V), ∃ Q : Finset (Sym2 V),
          D ⊆ copies p F J ∧ Q = D.biUnion triEdges ∧ Q ⊆ J.edgeFinset ∧
          IsDecomp p F Q D ∧ HasDecomp p F Q ∧
          DegBounded (J.edgeFinset \ Q) (η * Fintype.card V) := by
  obtain ⟨N, hN⟩ := Nibble.nibble_packing b η hb hη0 hη1
  refine ⟨N, ?_⟩
  intro V _ _ hV t p F J _ φ hw hload
  obtain ⟨P, hP, hdeg⟩ := hN V hV (copies p F J).card (copySystem p F J) J.edgeFinset
    (copyWeights p F J φ)
    (fun i => triEdges_subset_of_isCopy (copySystem_isCopy p F J i))
    (fun i => (hw _ (copySystem_isCopy p F J i)).1)
    (fun i => (hw _ (copySystem_isCopy p F J i)).2)
    (fun e he => by rw [load_copySystem]; exact hload e he)
  rw [edgesOf_eq_biUnion] at hdeg
  have hdec := isDecomp_packedCopies p F J P hP
  refine ⟨packedCopies p F J P, _, ?_, rfl, ?_, hdec, ⟨_, hdec⟩, fun v => hdeg v⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := mem_image.mp hs
    exact copySystem_tri_mem p F J i
  · intro e he
    obtain ⟨s, hs, he⟩ := mem_biUnion.mp he
    obtain ⟨i, -, rfl⟩ := mem_image.mp hs
    exact triEdges_subset_of_isCopy (copySystem_isCopy p F J i) he

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
