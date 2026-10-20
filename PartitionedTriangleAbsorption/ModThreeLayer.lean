/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.RefinerAssembly

/-!
# The mod-3 layer of a refiner (one-part triangle family)

For `t = 1` and ordinary triangles, an edge set is divisible iff all degrees are even and the
number of edges is divisible by `3` (`OnePart.isIntDiv_part1_iff`). A refiner therefore has
two jobs: a parity job and a counting job. This file does the counting job in general.

**Input (a parity refiner).** Pieces `B 0, …, B (N-1)` with even degrees, contained in
`X ∪ R`, such that every even-degree `L ⊆ X` selects pairwise disjoint pieces with union
`R ∪ L` (`ParityRefines`). We also assume `3 ∣ |R|`.

**Wires.** For every `i < N - 1` three wire cycles `W i 0, W i 1, W i 2`: even-degree edge
sets with `|W i k| ≡ 1 (mod 3)` (for instance 4-cycles, made of two anti-edges with the
same roots), pairwise disjoint and disjoint from `X ∪ R`.

**Output (a divisible refiner).** Position `i` gets the pieces
`(B i or ∅) ∪ (cycles k ≥ a of wire i-1) ∪ (cycles k < b of wire i)`, for `a b : Fin 3`,
kept only when their size is divisible by `3` (`layeredIndices`). The new remainder is
`R ∪ (all wires)`. Then:

* every layered piece is integrally `{T₀₀₀}`-divisible (`layeredPiece_isIntDiv`);
* the layered library refines **every** integrally divisible `L ⊆ X`
  (`layered_refinesReserve`), in the sense of `RefinerAssembly.RefinesReserve`;
* pieces stay inside `X ∪ R'`, and `R'` is disjoint from `X`.

The carry `b` of wire `i` is minus the running edge count of selected pieces, mod `3`.
This is a conditional reduction: it does **not** construct the parity refiner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ModThreeLayer

open Finset AntiEdgeSelection OnePart

variable {V : Type*} [DecidableEq V]

/-- A parity refiner: every even-degree `L ⊆ X` selects pairwise disjoint pieces among
`B 0, …, B (N-1)` covering exactly `R ∪ L`. -/
def ParityRefines (N : ℕ) (B : ℕ → Finset (Sym2 V)) (X R : Finset (Sym2 V)) : Prop :=
  ∀ L ⊆ X, (∀ v, Even (incidentLoad L v)) → ∃ s ⊆ range N,
    (s : Set ℕ).PairwiseDisjoint B ∧ s.biUnion B = R ∪ L

/-- Index set of the wire cycles. -/
def wireIdx (N : ℕ) : Finset (ℕ × Fin 3) := range (N - 1) ×ˢ univ

/-- All wire edges. -/
def wires (N : ℕ) (W : ℕ → Fin 3 → Finset (Sym2 V)) : Finset (Sym2 V) :=
  (wireIdx N).biUnion fun q => W q.1 q.2

/-- Cycles `k ≥ a` of the wire to the left of position `i` (none at `i = 0`). -/
def leftPart (W : ℕ → Fin 3 → Finset (Sym2 V)) (i : ℕ) (a : Fin 3) : Finset (Sym2 V) :=
  if i = 0 then ∅ else (univ.filter fun k : Fin 3 => a ≤ k).biUnion (W (i - 1))

/-- Cycles `k < b` of the wire to the right of position `i` (none at the last position). -/
def rightPart (N : ℕ) (W : ℕ → Fin 3 → Finset (Sym2 V)) (i : ℕ) (b : Fin 3) :
    Finset (Sym2 V) :=
  if i + 1 < N then (univ.filter fun k : Fin 3 => k < b).biUnion (W i) else ∅

/-- The layered piece with index `(i, selected, a, b)`. -/
def layeredPiece (N : ℕ) (B : ℕ → Finset (Sym2 V)) (W : ℕ → Fin 3 → Finset (Sym2 V))
    (j : ℕ × Bool × Fin 3 × Fin 3) : Finset (Sym2 V) :=
  ((if j.2.1 then B j.1 else ∅) ∪ leftPart W j.1 j.2.2.1) ∪ rightPart N W j.1 j.2.2.2

/-- The layered library: all indices whose piece has size divisible by three. -/
def layeredIndices (N : ℕ) (B : ℕ → Finset (Sym2 V)) (W : ℕ → Fin 3 → Finset (Sym2 V)) :
    Finset (ℕ × Bool × Fin 3 × Fin 3) :=
  (range N ×ˢ (univ ×ˢ (univ ×ˢ univ))).filter fun j => 3 ∣ (layeredPiece N B W j).card

/-- The hypotheses on the parity refiner and on the wires. -/
structure LayerData (N : ℕ) (B : ℕ → Finset (Sym2 V)) (W : ℕ → Fin 3 → Finset (Sym2 V))
    (X R : Finset (Sym2 V)) : Prop where
  refines : ParityRefines N B X R
  pieces_sub : ∀ i < N, B i ⊆ X ∪ R
  pieces_even : ∀ i < N, ∀ v, Even (incidentLoad (B i) v)
  rem_disj : Disjoint R X
  rem_card : 3 ∣ R.card
  loopless : ∀ e ∈ X ∪ R, ¬ e.IsDiag
  wire_even : ∀ i < N - 1, ∀ k v, Even (incidentLoad (W i k) v)
  wire_card : ∀ i < N - 1, ∀ k, (W i k).card % 3 = 1
  wire_disj : ((wireIdx N : Finset (ℕ × Fin 3)) : Set (ℕ × Fin 3)).PairwiseDisjoint
    fun q => W q.1 q.2
  wire_avoid : ∀ i < N - 1, ∀ k, Disjoint (W i k) (X ∪ R)
  wire_loopless : ∀ i < N - 1, ∀ k, ∀ e ∈ W i k, ¬ e.IsDiag

variable {N : ℕ} {B : ℕ → Finset (Sym2 V)} {W : ℕ → Fin 3 → Finset (Sym2 V)}
  {X R : Finset (Sym2 V)}


/-! ### Bookkeeping lemmas -/

theorem wire_disjoint (h : LayerData N B W X R) {i i' : ℕ} (hi : i < N - 1) (hi' : i' < N - 1)
    {k k' : Fin 3} (hne : (i, k) ≠ (i', k')) : Disjoint (W i k) (W i' k') :=
  h.wire_disj (by simp [wireIdx, hi]) (by simp [wireIdx, hi']) hne

theorem mem_wires {e : Sym2 V} : e ∈ wires N W ↔ ∃ i < N - 1, ∃ k, e ∈ W i k := by
  simp [wires, wireIdx]

theorem leftPart_subset_wires {i : ℕ} (hi : i < N) (a : Fin 3) :
    leftPart W i a ⊆ wires N W := by
  intro e he
  unfold leftPart at he
  split_ifs at he with h0
  · simp at he
  · obtain ⟨k, -, hk⟩ := mem_biUnion.mp he
    exact mem_wires.mpr ⟨i - 1, by omega, k, hk⟩

theorem rightPart_subset_wires (i : ℕ) (b : Fin 3) : rightPart N W i b ⊆ wires N W := by
  intro e he
  unfold rightPart at he
  split_ifs at he with h0
  · obtain ⟨k, -, hk⟩ := mem_biUnion.mp he
    exact mem_wires.mpr ⟨i, by omega, k, hk⟩
  · simp at he

theorem wires_disjoint (h : LayerData N B W X R) : Disjoint (wires N W) (X ∪ R) := by
  rw [disjoint_left]
  intro e he
  obtain ⟨i, hi, k, hk⟩ := mem_wires.mp he
  exact disjoint_left.mp (h.wire_avoid i hi k) hk

/-- Even degrees of the cycles of one wire indexed by a set of colours. -/
theorem wirePart_even (h : LayerData N B W X R) {i : ℕ} (hi : i < N - 1) (T : Finset (Fin 3)) :
    ∀ v, Even (incidentLoad (T.biUnion (W i)) v) :=
  even_incidentLoad_biUnion T (W i)
    (fun k _ k' _ hkk => wire_disjoint h hi hi (by simp [hkk]))
    (fun k _ v => h.wire_even i hi k v)

theorem leftPart_even (h : LayerData N B W X R) {i : ℕ} (hi : i < N) (a : Fin 3) :
    ∀ v, Even (incidentLoad (leftPart W i a) v) := by
  unfold leftPart
  split_ifs with h0
  · intro v; simp [incidentLoad_empty]
  · exact wirePart_even h (by omega) _

theorem rightPart_even (h : LayerData N B W X R) (i : ℕ) (b : Fin 3) :
    ∀ v, Even (incidentLoad (rightPart N W i b) v) := by
  unfold rightPart
  split_ifs with h0
  · exact wirePart_even h (by omega) _
  · intro v; simp [incidentLoad_empty]

theorem left_right_disjoint (h : LayerData N B W X R) (i : ℕ) (a b : Fin 3) :
    Disjoint (leftPart W i a) (rightPart N W i b) := by
  unfold leftPart rightPart
  split_ifs with h0 h1
  · simp
  · simp
  · rw [disjoint_biUnion_left]
    intro k _
    rw [disjoint_biUnion_right]
    intro k' _
    exact wire_disjoint h (by omega) (by omega) (by simp; omega)
  · simp

theorem selected_wire_disjoint (h : LayerData N B W X R) {i : ℕ} (hi : i < N) (sel : Bool)
    (a b : Fin 3) :
    Disjoint (if sel then B i else ∅) (leftPart W i a ∪ rightPart N W i b) := by
  split_ifs
  · exact disjoint_of_subset_left (h.pieces_sub i hi)
      (disjoint_of_subset_right (union_subset (leftPart_subset_wires hi a)
        (rightPart_subset_wires i b)) (wires_disjoint h).symm)
  · simp

theorem layeredPiece_eq (i : ℕ) (sel : Bool) (a b : Fin 3) :
    layeredPiece N B W (i, sel, a, b) =
      (if sel then B i else ∅) ∪ (leftPart W i a ∪ rightPart N W i b) := by
  simp [layeredPiece, union_assoc]

theorem layeredPiece_even (h : LayerData N B W X R) {i : ℕ} (hi : i < N) (sel : Bool)
    (a b : Fin 3) : ∀ v, Even (incidentLoad (layeredPiece N B W (i, sel, a, b)) v) := by
  rw [layeredPiece_eq]
  refine even_incidentLoad_union (selected_wire_disjoint h hi sel a b) ?_
    (even_incidentLoad_union (left_right_disjoint h i a b) (leftPart_even h hi a)
      (rightPart_even h i b))
  split_ifs
  · exact h.pieces_even i hi
  · intro v; simp [incidentLoad_empty]

theorem layeredPiece_subset' (h : LayerData N B W X R) {i : ℕ} (hi : i < N) (sel : Bool)
    (a b : Fin 3) : layeredPiece N B W (i, sel, a, b) ⊆ X ∪ (R ∪ wires N W) := by
  rw [layeredPiece_eq]
  refine union_subset ?_ (union_subset ?_ ?_)
  · split_ifs
    · exact (h.pieces_sub i hi).trans (by
        intro e he; rcases mem_union.mp he with h1 | h1 <;> simp [h1])
    · simp
  · exact (leftPart_subset_wires hi a).trans (by intro e he; simp [he])
  · exact (rightPart_subset_wires i b).trans (by intro e he; simp [he])

theorem loopless_of_subset (h : LayerData N B W X R) {E : Finset (Sym2 V)}
    (hE : E ⊆ X ∪ (R ∪ wires N W)) : ∀ e ∈ E, ¬ e.IsDiag := by
  intro e he
  rcases mem_union.mp (hE he) with h1 | h1
  · exact h.loopless e (mem_union_left _ h1)
  · rcases mem_union.mp h1 with h2 | h2
    · exact h.loopless e (mem_union_right _ h2)
    · obtain ⟨i, hi, k, hk⟩ := mem_wires.mp h2
      exact h.wire_loopless i hi k e hk

theorem mem_layeredIndices {j : ℕ × Bool × Fin 3 × Fin 3} :
    j ∈ layeredIndices N B W ↔ j.1 < N ∧ 3 ∣ (layeredPiece N B W j).card := by
  simp [layeredIndices]


/-! ### The carry and the selection -/

theorem wire_unique (h : LayerData N B W X R) {e : Sym2 V} {i i' : ℕ} {k k' : Fin 3}
    (hi : i < N - 1) (hi' : i' < N - 1) (he : e ∈ W i k) (he' : e ∈ W i' k') :
    i = i' ∧ k = k' := by
  by_contra hne
  have hne' : (i, k) ≠ (i', k') := fun heq => hne ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  exact disjoint_left.mp (wire_disjoint h hi hi' hne') he he'

theorem mem_layeredPiece {e : Sym2 V} {i : ℕ} {sel : Bool} {a b : Fin 3} :
    e ∈ layeredPiece N B W (i, sel, a, b) ↔
      (sel = true ∧ e ∈ B i) ∨ (i ≠ 0 ∧ ∃ k, a ≤ k ∧ e ∈ W (i - 1) k) ∨
        (i + 1 < N ∧ ∃ k, k < b ∧ e ∈ W i k) := by
  rw [layeredPiece_eq]
  simp only [mem_union, leftPart, rightPart]
  constructor
  · rintro (h1 | h1 | h1)
    · split_ifs at h1 with hs
      · exact Or.inl ⟨hs, h1⟩
      · simp at h1
    · split_ifs at h1 with h0
      · simp at h1
      · obtain ⟨k, hk, he⟩ := mem_biUnion.mp h1
        exact Or.inr (Or.inl ⟨h0, k, (mem_filter.mp hk).2, he⟩)
    · split_ifs at h1 with h0
      · obtain ⟨k, hk, he⟩ := mem_biUnion.mp h1
        exact Or.inr (Or.inr ⟨h0, k, (mem_filter.mp hk).2, he⟩)
      · simp at h1
  · rintro (⟨hs, he⟩ | ⟨h0, k, hk, he⟩ | ⟨h0, k, hk, he⟩)
    · left; simp [hs, he]
    · right; left
      rw [ite_eq_right h0]
      exact mem_biUnion.mpr ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩, he⟩
    · right; right
      rw [ite_eq_left h0]
      exact mem_biUnion.mpr ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩, he⟩

/-- Cardinality of a union of cycles of one wire, modulo three. -/
theorem card_wirePart_mod (h : LayerData N B W X R) {i : ℕ} (hi : i < N - 1)
    (T : Finset (Fin 3)) : (T.biUnion (W i)).card % 3 = T.card % 3 := by
  rw [card_biUnion (fun k _ k' _ hkk => wire_disjoint h hi hi (by simp [hkk])),
    Finset.sum_nat_mod, sum_congr rfl fun k _ => h.wire_card i hi k]
  simp

theorem card_filter_le (a : Fin 3) : (univ.filter fun k : Fin 3 => a ≤ k).card = 3 - a.val := by
  fin_cases a <;> rfl

theorem card_filter_lt (b : Fin 3) : (univ.filter fun k : Fin 3 => k < b).card = b.val := by
  fin_cases b <;> rfl

theorem card_leftPart_mod (h : LayerData N B W X R) {i : ℕ} (hi : i < N) (a : Fin 3) :
    (leftPart W i a).card % 3 = if i = 0 then 0 else (3 - a.val) % 3 := by
  unfold leftPart
  split_ifs with h0
  · simp
  · rw [card_wirePart_mod h (by omega), card_filter_le]

theorem card_rightPart_mod (h : LayerData N B W X R) (i : ℕ) (b : Fin 3) :
    (rightPart N W i b).card % 3 = if i + 1 < N then b.val else 0 := by
  unfold rightPart
  split_ifs with h0
  · rw [card_wirePart_mod h (by omega), card_filter_lt]
    exact Nat.mod_eq_of_lt b.isLt
  · simp

theorem card_layeredPiece (h : LayerData N B W X R) {i : ℕ} (hi : i < N) (sel : Bool)
    (a b : Fin 3) :
    (layeredPiece N B W (i, sel, a, b)).card =
      (if sel then (B i).card else 0) + (leftPart W i a).card + (rightPart N W i b).card := by
  rw [layeredPiece_eq, card_union_of_disjoint (selected_wire_disjoint h hi sel a b),
    card_union_of_disjoint (left_right_disjoint h i a b)]
  split_ifs <;> simp [Nat.add_assoc]

/-- The running count of selected piece sizes. -/
def runCount (s : Finset ℕ) (B : ℕ → Finset (Sym2 V)) (i : ℕ) : ℕ :=
  ∑ j ∈ range (i + 1), if j ∈ s then (B j).card else 0

/-- The carry of wire `i`: minus the running count, modulo three. -/
def carry (s : Finset ℕ) (B : ℕ → Finset (Sym2 V)) (i : ℕ) : Fin 3 :=
  ⟨(3 - runCount s B i % 3) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The layered index chosen at position `i`. -/
def chosen (N : ℕ) (s : Finset ℕ) (B : ℕ → Finset (Sym2 V)) (i : ℕ) :
    ℕ × Bool × Fin 3 × Fin 3 :=
  (i, decide (i ∈ s), if i = 0 then 0 else carry s B (i - 1),
    if i + 1 < N then carry s B i else 0)

omit [DecidableEq V] in
theorem runCount_succ (s : Finset ℕ) (i : ℕ) :
    runCount s B (i + 1) = runCount s B i + if i + 1 ∈ s then (B (i + 1)).card else 0 := by
  rw [runCount, runCount, sum_range_succ]

omit [DecidableEq V] in
theorem runCount_zero (s : Finset ℕ) : runCount s B 0 = if 0 ∈ s then (B 0).card else 0 := by
  rw [runCount, zero_add, sum_range_one]

omit [DecidableEq V] in
theorem carry_left (s : Finset ℕ) (i : ℕ) :
    (3 - (carry s B i).val) % 3 = runCount s B i % 3 := by
  simp only [carry]; omega

omit [DecidableEq V] in
theorem carry_right (s : Finset ℕ) (i : ℕ) :
    ((carry s B i).val + runCount s B i) % 3 = 0 := by
  simp only [carry]; omega

theorem chosen_card_dvd (h : LayerData N B W X R) {s : Finset ℕ} {i : ℕ} (hi : i < N)
    (hlast : 3 ∣ runCount s B (N - 1)) :
    3 ∣ (layeredPiece N B W (chosen N s B i)).card := by
  set a : Fin 3 := (if i = 0 then 0 else carry s B (i - 1)) with ha
  set b : Fin 3 := (if i + 1 < N then carry s B i else 0) with hb
  have hch : chosen N s B i = (i, decide (i ∈ s), a, b) := rfl
  have hc := card_layeredPiece h hi (decide (i ∈ s)) a b
  have hl := card_leftPart_mod h hi a
  have hr := card_rightPart_mod h i b
  rw [hch, hc, Nat.dvd_iff_mod_eq_zero]
  have hsel : (if decide (i ∈ s) = true then (B i).card else 0) =
      if i ∈ s then (B i).card else 0 := by simp
  rw [hsel]
  generalize (leftPart W i a).card = cl at hl ⊢
  generalize (rightPart N W i b).card = cr at hr ⊢
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    simp only [ite_true] at hl
    have hrc := runCount_zero (B := B) s
    by_cases hN : 0 + 1 < N
    · have hb' : b = carry s B 0 := by simp [hb, hN]
      rw [ite_eq_left hN, hb'] at hr
      have := carry_right (B := B) s 0
      omega
    · rw [ite_eq_right hN] at hr
      have : N - 1 = 0 := by omega
      rw [this] at hlast
      omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have ha' : a = carry s B j := by simp [ha]
    rw [ite_eq_right (by omega), ha', carry_left] at hl
    have hrc := runCount_succ (B := B) s j
    by_cases hN : j + 1 + 1 < N
    · have hb' : b = carry s B (j + 1) := by simp [hb, hN]
      rw [ite_eq_left hN, hb'] at hr
      have := carry_right (B := B) s (j + 1)
      omega
    · rw [ite_eq_right hN] at hr
      have : N - 1 = j + 1 := by omega
      rw [this] at hlast
      omega

omit [DecidableEq V] in
theorem runCount_last (s : Finset ℕ) (hs : s ⊆ range N) (hN : 0 < N) :
    runCount s B (N - 1) = ∑ j ∈ s, (B j).card := by
  unfold runCount
  rw [Nat.sub_add_cancel hN, sum_ite_mem, inter_eq_right.mpr hs]

theorem layeredPiece_isIntDiv (h : LayerData N B W X R) :
    ∀ j ∈ layeredIndices N B W, IsIntDiv part1 triFam (layeredPiece N B W j) := by
  rintro ⟨i, sel, a, b⟩ hj
  obtain ⟨hi, h3⟩ := mem_layeredIndices.mp hj
  exact (isIntDiv_part1_iff _ (loopless_of_subset h (layeredPiece_subset' h hi sel a b))).mpr
    ⟨h3, layeredPiece_even h hi sel a b⟩

theorem layeredPiece_subset (h : LayerData N B W X R) :
    ∀ j ∈ layeredIndices N B W, layeredPiece N B W j ⊆ X ∪ (R ∪ wires N W) := by
  rintro ⟨i, sel, a, b⟩ hj
  exact layeredPiece_subset' h (mem_layeredIndices.mp hj).1 sel a b

theorem layered_rem_disjoint (h : LayerData N B W X R) : Disjoint (R ∪ wires N W) X :=
  disjoint_union_left.mpr ⟨h.rem_disj,
    disjoint_of_subset_right subset_union_left (wires_disjoint h)⟩

theorem mem_chosen {s : Finset ℕ} {e : Sym2 V} {i : ℕ} :
    e ∈ layeredPiece N B W (chosen N s B i) ↔
      (i ∈ s ∧ e ∈ B i) ∨ (i ≠ 0 ∧ ∃ k, carry s B (i - 1) ≤ k ∧ e ∈ W (i - 1) k) ∨
        (i + 1 < N ∧ ∃ k, k < carry s B i ∧ e ∈ W i k) := by
  simp only [chosen, mem_layeredPiece, decide_eq_true_eq]
  by_cases hN : i + 1 < N <;> rcases eq_or_ne i 0 with rfl | h0 <;>
    (try simp only [zero_add] at hN) <;> simp [*]

theorem chosen_disjoint (h : LayerData N B W X R) {s : Finset ℕ}
    (hs : (s : Set ℕ).PairwiseDisjoint B) {i i' : ℕ} (hi : i < N) (hi' : i' < N)
    (hne : i ≠ i') :
    Disjoint (layeredPiece N B W (chosen N s B i)) (layeredPiece N B W (chosen N s B i')) := by
  rw [disjoint_left]
  intro e he he'
  have hBw : ∀ j < N, ∀ i₀ < N - 1, ∀ k, e ∈ B j → e ∉ W i₀ k := fun j hj i₀ hi₀ k hb hw =>
    disjoint_left.mp (h.wire_avoid i₀ hi₀ k) hw (h.pieces_sub j hj hb)
  rcases mem_chosen.mp he with ⟨hs1, hb1⟩ | ⟨h01, k1, hk1, hw1⟩ | ⟨hN1, k1, hk1, hw1⟩ <;>
  rcases mem_chosen.mp he' with ⟨hs2, hb2⟩ | ⟨h02, k2, hk2, hw2⟩ | ⟨hN2, k2, hk2, hw2⟩
  · exact disjoint_left.mp (hs (mem_coe.mpr hs1) (mem_coe.mpr hs2) hne) hb1 hb2
  · exact hBw i hi _ (by omega) k2 hb1 hw2
  · exact hBw i hi _ (by omega) k2 hb1 hw2
  · exact hBw i' hi' _ (by omega) k1 hb2 hw1
  · obtain ⟨h1, -⟩ := wire_unique h (by omega) (by omega) hw1 hw2; omega
  · obtain ⟨h1, rfl⟩ := wire_unique h (by omega) (by omega) hw1 hw2
    have : i - 1 = i' := h1
    subst this
    exact absurd hk2 (not_lt.mpr hk1)
  · exact hBw i' hi' _ (by omega) k1 hb2 hw1
  · obtain ⟨h1, rfl⟩ := wire_unique h (by omega) (by omega) hw1 hw2
    have : i = i' - 1 := h1
    subst this
    exact absurd hk1 (not_lt.mpr hk2)
  · obtain ⟨h1, -⟩ := wire_unique h (by omega) (by omega) hw1 hw2; omega

theorem layered_refinesReserve (h : LayerData N B W X R) :
    RefinerAssembly.RefinesReserve (p := part1) (F := triFam) (layeredIndices N B W)
      (layeredPiece N B W) X (R ∪ wires N W) := by
  intro L hLX hdiv
  have hloopL : ∀ e ∈ L, ¬ e.IsDiag := fun e he => h.loopless e (mem_union_left _ (hLX he))
  obtain ⟨hL3, hLev⟩ := (isIntDiv_part1_iff L hloopL).mp hdiv
  obtain ⟨s, hsN, hsd, hsU⟩ := h.refines L hLX hLev
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hs0 : s = ∅ := by simpa using hsN
    subst hs0
    have hw : wires 0 W = ∅ := by simp [wires, wireIdx]
    refine ⟨∅, empty_subset _, by simp, ?_⟩
    rw [hw]
    simpa using hsU
  · have hlast : 3 ∣ runCount s B (N - 1) := by
      rw [runCount_last s hsN hNpos, ← card_biUnion (fun i hi j hj hij => hsd hi hj hij), hsU,
        card_union_of_disjoint (disjoint_of_subset_right hLX h.rem_disj)]
      exact dvd_add h.rem_card hL3
    refine ⟨(range N).image (chosen N s B), ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      exact mem_layeredIndices.mpr ⟨mem_range.mp hi, chosen_card_dvd h (mem_range.mp hi) hlast⟩
    · intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_coe.mp hx)
      obtain ⟨i', hi', rfl⟩ := mem_image.mp (mem_coe.mp hy)
      have hne : i ≠ i' := fun h' => hxy (h' ▸ rfl)
      exact chosen_disjoint h hsd (mem_range.mp hi) (mem_range.mp hi') hne
    · ext e
      simp only [mem_biUnion, mem_image, mem_range]
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, he⟩
        rcases mem_chosen.mp he with ⟨hs1, hb1⟩ | ⟨h01, k1, -, hw1⟩ | ⟨hN1, k1, -, hw1⟩
        · have : e ∈ s.biUnion B := mem_biUnion.mpr ⟨i, hs1, hb1⟩
          rw [hsU] at this
          rcases mem_union.mp this with h1 | h1 <;> simp [h1]
        · have : e ∈ wires N W := mem_wires.mpr ⟨i - 1, by omega, k1, hw1⟩
          simp [this]
        · have : e ∈ wires N W := mem_wires.mpr ⟨i, by omega, k1, hw1⟩
          simp [this]
      · intro he
        rcases mem_union.mp he with h1 | h1
        · rcases mem_union.mp h1 with h2 | h2
          · have : e ∈ s.biUnion B := by rw [hsU]; exact mem_union_left _ h2
            obtain ⟨j, hj, hb⟩ := mem_biUnion.mp this
            exact ⟨_, ⟨j, mem_range.mp (hsN hj), rfl⟩, mem_chosen.mpr (Or.inl ⟨hj, hb⟩)⟩
          · obtain ⟨i, hi, k, hk⟩ := mem_wires.mp h2
            by_cases hc : k < carry s B i
            · exact ⟨_, ⟨i, by omega, rfl⟩,
                mem_chosen.mpr (Or.inr (Or.inr ⟨by omega, k, hc, hk⟩))⟩
            · exact ⟨_, ⟨i + 1, by omega, rfl⟩,
                mem_chosen.mpr (Or.inr (Or.inl ⟨by omega, k, by simpa using not_lt.mp hc,
                  by simpa using hk⟩))⟩
        · have : e ∈ s.biUnion B := by rw [hsU]; exact mem_union_right _ h1
          obtain ⟨j, hj, hb⟩ := mem_biUnion.mp this
          exact ⟨_, ⟨j, mem_range.mp (hsN hj), rfl⟩, mem_chosen.mpr (Or.inl ⟨hj, hb⟩)⟩

/-! ### Quantitative incidence bound -/

theorem incidentLoad_mono {A A' : Finset (Sym2 V)} (h : A ⊆ A') (v : V) :
    incidentLoad A v ≤ incidentLoad A' v :=
  card_le_card (filter_subset_filter _ h)

theorem incidentLoad_union_le (A A' : Finset (Sym2 V)) (v : V) :
    incidentLoad (A ∪ A') v ≤ incidentLoad A v + incidentLoad A' v := by
  unfold incidentLoad
  rw [filter_union]
  exact card_union_le _ _

theorem incidentLoad_biUnion_eq {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 V))
    (hd : (s : Set ι).PairwiseDisjoint E) (v : V) :
    incidentLoad (s.biUnion E) v = ∑ i ∈ s, incidentLoad (E i) v := by
  classical
  unfold incidentLoad
  rw [filter_biUnion, card_biUnion]
  intro i hi j hj hij
  exact disjoint_filter_filter (hd hi hj hij)

theorem leftPart_mono (i : ℕ) (a : Fin 3) : leftPart W i a ⊆ leftPart W i 0 := by
  unfold leftPart
  split_ifs
  · exact subset_refl _
  · exact biUnion_subset_biUnion_of_subset_left _ (by intro k; simp)

theorem rightPart_mono (i : ℕ) (b : Fin 3) : rightPart N W i b ⊆ rightPart N W i 2 := by
  unfold rightPart
  split_ifs
  · refine biUnion_subset_biUnion_of_subset_left _ ?_
    intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact lt_of_lt_of_le hk (Fin.le_last b)
  · exact subset_refl _

theorem leftPart_pairwiseDisjoint (h : LayerData N B W X R) :
    ((range N : Finset ℕ) : Set ℕ).PairwiseDisjoint fun i => leftPart W i 0 := by
  intro i hi i' hi' hne
  simp only [coe_range, Set.mem_Iio] at hi hi'
  change Disjoint (leftPart W i 0) (leftPart W i' 0)
  unfold leftPart
  split_ifs with h1 h2 h2
  · simp
  · simp
  · simp
  · rw [disjoint_left]
    intro e he he'
    obtain ⟨k, -, hk⟩ := mem_biUnion.mp he
    obtain ⟨k', -, hk'⟩ := mem_biUnion.mp he'
    have := (wire_unique h (by omega) (by omega) hk hk').1
    omega

theorem rightPart_pairwiseDisjoint (h : LayerData N B W X R) :
    ((range N : Finset ℕ) : Set ℕ).PairwiseDisjoint fun i => rightPart N W i 2 := by
  intro i hi i' hi' hne
  change Disjoint (rightPart N W i 2) (rightPart N W i' 2)
  unfold rightPart
  split_ifs with h1 h2 h2
  · rw [disjoint_left]
    intro e he he'
    obtain ⟨k, -, hk⟩ := mem_biUnion.mp he
    obtain ⟨k', -, hk'⟩ := mem_biUnion.mp he'
    exact hne (wire_unique h (by omega) (by omega) hk hk').1
  · simp
  · simp
  · simp

/-- **Incidence bound.** Summed over *all* alternatives of the layered library, the
incidence at any vertex is at most `18` times the total incidence of the parity library
plus `36` times the wire incidence. -/
theorem layered_incidence_le (h : LayerData N B W X R) (v : V) :
    ∑ j ∈ layeredIndices N B W, incidentLoad (layeredPiece N B W j) v ≤
      18 * ∑ i ∈ range N, incidentLoad (B i) v + 36 * incidentLoad (wires N W) v := by
  have hpiece : ∀ j ∈ range N ×ˢ ((univ : Finset Bool) ×ˢ ((univ : Finset (Fin 3)) ×ˢ
      (univ : Finset (Fin 3)))), incidentLoad (layeredPiece N B W j) v ≤
      incidentLoad (B j.1) v + incidentLoad (leftPart W j.1 0) v +
        incidentLoad (rightPart N W j.1 2) v := by
    rintro ⟨i, sel, a, b⟩ -
    refine (incidentLoad_union_le _ _ v).trans ?_
    refine Nat.add_le_add ((incidentLoad_union_le _ _ v).trans (Nat.add_le_add ?_ ?_))
      (incidentLoad_mono (rightPart_mono i b) v)
    · split_ifs
      · exact le_rfl
      · simp [incidentLoad]
    · exact incidentLoad_mono (leftPart_mono i a) v
  have hL : ∑ i ∈ range N, incidentLoad (leftPart W i 0) v ≤ incidentLoad (wires N W) v := by
    rw [← incidentLoad_biUnion_eq _ _ (leftPart_pairwiseDisjoint h)]
    exact incidentLoad_mono (biUnion_subset.mpr fun i hi =>
      leftPart_subset_wires (mem_range.mp hi) 0) v
  have hR : ∑ i ∈ range N, incidentLoad (rightPart N W i 2) v ≤ incidentLoad (wires N W) v := by
    rw [← incidentLoad_biUnion_eq _ _ (rightPart_pairwiseDisjoint h)]
    exact incidentLoad_mono (biUnion_subset.mpr fun i _ => rightPart_subset_wires i 2) v
  calc ∑ j ∈ layeredIndices N B W, incidentLoad (layeredPiece N B W j) v
      ≤ ∑ j ∈ range N ×ˢ ((univ : Finset Bool) ×ˢ ((univ : Finset (Fin 3)) ×ˢ
          (univ : Finset (Fin 3)))), incidentLoad (layeredPiece N B W j) v :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ ∑ j ∈ range N ×ˢ ((univ : Finset Bool) ×ˢ ((univ : Finset (Fin 3)) ×ˢ
          (univ : Finset (Fin 3)))), (incidentLoad (B j.1) v + incidentLoad (leftPart W j.1 0) v +
            incidentLoad (rightPart N W j.1 2) v) := sum_le_sum hpiece
    _ = 18 * (∑ i ∈ range N, incidentLoad (B i) v + ∑ i ∈ range N, incidentLoad (leftPart W i 0) v
          + ∑ i ∈ range N, incidentLoad (rightPart N W i 2) v) := by
        rw [sum_product]
        simp only [sum_const, card_univ, Fintype.card_bool, Fintype.card_fin, smul_eq_mul,
          card_product]
        rw [mul_add, mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        ring
    _ ≤ 18 * ∑ i ∈ range N, incidentLoad (B i) v + 36 * incidentLoad (wires N W) v := by
        omega

/-! ### Why the parity layer cannot be carried at one vertex -/

/-- **Split lemma.** If an even-degree edge set is split into two disjoint parts, the two
parts have exactly the same odd vertices. Hence any splittable gadget that changes the
parity of a selected piece at a root `u` also changes it at a second vertex. -/
theorem split_parity_agree {A A' : Finset (Sym2 V)} (hd : Disjoint A A')
    (hev : ∀ v, Even (incidentLoad (A ∪ A') v)) (v : V) :
    Even (incidentLoad A v) ↔ Even (incidentLoad A' v) := by
  have := hev v
  rw [incidentLoad_union hd] at this
  constructor
  · intro hA; exact (Nat.even_add.mp this).mp hA
  · intro hA; exact (Nat.even_add.mp this).mpr hA

/-! ### Conditional composition with private absorbers -/

/-- **Conditional composition.** If the layered pieces admit compatible private absorbers,
then `universal_of_refiner` gives one absorber for every divisible leftover in `X`.
The private absorbers and the parity refiner are hypotheses, not constructions. -/
theorem layered_universal (h : LayerData N B W X R)
    (A : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V))
    (hA : ∀ j ∈ layeredIndices N B W, HasDecomp part1 triFam (A j))
    (hAB : ∀ j ∈ layeredIndices N B W, HasDecomp part1 triFam (A j ∪ layeredPiece N B W j))
    (hprivate : ((layeredIndices N B W : Finset _) : Set _).PairwiseDisjoint A)
    (havoid : ∀ j ∈ layeredIndices N B W, Disjoint (A j) (X ∪ (R ∪ wires N W))) :
    Disjoint ((R ∪ wires N W) ∪ (layeredIndices N B W).biUnion A) X ∧
      HasDecomp part1 triFam ((R ∪ wires N W) ∪ (layeredIndices N B W).biUnion A) ∧
      ∀ L ⊆ X, IsIntDiv part1 triFam L →
        HasDecomp part1 triFam (((R ∪ wires N W) ∪ (layeredIndices N B W).biUnion A) ∪ L) :=
  RefinerAssembly.universal_of_refiner _ A _ X _ (layered_rem_disjoint h)
    (layered_refinesReserve h) hA hAB hprivate havoid (layeredPiece_subset h)

end PartitionedTriangleAbsorption.ModThreeLayer

