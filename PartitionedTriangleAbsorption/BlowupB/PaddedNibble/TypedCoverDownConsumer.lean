/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibbleAdapter
public import PartitionedTriangleAbsorption.ReserveCoverDown
public import PartitionedTriangleAbsorption.ReserveBudget

/-! # Uniform reserve cover-down and absorption from exact inputs (L5.a → L6)

Inputs: a graph `G`, a supplied universal absorber `A` for the reserve `X`
(`∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)`), an `α`-anti-edgeful reserve
graph on `X`, integral divisibility of `E(G)`, and an exact physical weighting with
cap `b/n` on the main graph `J = G - (A ∪ X)`. The absorber and the weighting are
explicit hypotheses; neither is constructed here.

Output (`typed_cover_down_absorption`): `HasDecomp p F E(G)` for all `n ≥ N`, with
`N` depending only on `b` and `α`. The packing `Q`, its residual degree bound and
the reserve cover are produced, not assumed: `Q` comes from
`TypedNibble.typed_nibble_packing`, the scalar budget from
`ReserveBudget.sparse_residue_budget`, and the cover-down/absorption step from
`ReserveCoverDown.hasDecomp_of_sparse_main_packing`, whose absorber receives
`X \ P_reserve` (not `E(J) \ Q`).

Scalar schedule: `η = α²/256`, `a = α n`, `r = ⌈η n⌉`, `m = |E(J) \ Q|`,
`q = ⌊a/16⌋`, `N = max N_nibble ⌈256/α²⌉`.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/TypedCoverDownConsumer.lean.
Original SHA256: 258a0bea3239e55bc127434bfde355fa4fa7628328125142f8f369a388e3a2b5.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A non-diagonal unordered pair has exactly two endpoints. -/
theorem card_endpoints_of_not_isDiag {e : Sym2 V} (he : ¬ e.IsDiag) :
    (univ.filter (fun v => v ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    have h : univ.filter (fun v => v ∈ s(x, y)) = {x, y} := by
      ext v
      simp
    rw [h, card_pair hxy]

/-- **Handshake identity for a loopless edge set.** -/
theorem sum_degrees_eq_two_mul_card (L : Finset (Sym2 V)) (hdiag : ∀ e ∈ L, ¬ e.IsDiag) :
    ∑ v, (L.filter (fun e => v ∈ e)).card = 2 * L.card := by
  simp_rw [card_filter]
  rw [sum_comm]
  have h : ∀ e ∈ L, (∑ v, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← card_filter]
    exact card_endpoints_of_not_isDiag (hdiag e he)
  rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_comm]

/-- **Degree/cardinality bridge.** A loopless edge set of maximum degree at most `r`
on `n` vertices has at most `n r / 2` edges. (The converse fails; see the examples.) -/
theorem card_le_of_degBounded (L : Finset (Sym2 V)) (hdiag : ∀ e ∈ L, ¬ e.IsDiag) (r : ℝ)
    (h : DegBounded L r) : (L.card : ℝ) ≤ Fintype.card V * r / 2 := by
  have hsum : ((2 * L.card : ℕ) : ℝ) ≤ Fintype.card V * r := by
    rw [← sum_degrees_eq_two_mul_card L hdiag]
    push_cast
    calc ∑ v, ((L.filter (fun e => v ∈ e)).card : ℝ) ≤ ∑ _v : V, r :=
          sum_le_sum (fun v _ => h v)
      _ = Fintype.card V * r := by rw [sum_const, card_univ, nsmul_eq_mul]
  push_cast at hsum
  linarith

omit [Fintype V] [DecidableEq V] in
theorem not_isDiag_of_mem_edgeFinset (G : SimpleGraph V) [Fintype G.edgeSet]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) : ∀ e ∈ E, ¬ e.IsDiag := fun _ he =>
  G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hE he))

/-- **Scalar schedule.** For `η = α²/256`, `n ≥ 256/α²`, `r = ⌈η n⌉`, `q = ⌊α n/16⌋` and
`m ≤ n r / 2`, the exact cover-down budget holds and `q > 0`. -/
theorem schedule_budget (α n m : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 256 / α ^ 2 ≤ n)
    (hm : m ≤ n * (⌈α ^ 2 / 256 * n⌉₊ : ℝ) / 2) :
    0 < ⌊α * n / 16⌋₊ ∧
      m / (⌊α * n / 16⌋₊ : ℝ) + 2 * ((⌈α ^ 2 / 256 * n⌉₊ : ℝ) + 2 * ⌊α * n / 16⌋₊) <
        α * n := by
  have hα2 : 0 < α ^ 2 := by positivity
  have hαn2 : 256 ≤ α ^ 2 * n := by
    have := mul_le_mul_of_nonneg_left hn hα2.le
    rwa [mul_div_cancel₀ _ hα2.ne'] at this
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hαα : α ^ 2 ≤ α := by nlinarith
  have hαn : 256 ≤ α * n := le_trans hαn2 (mul_le_mul_of_nonneg_right hαα hn0.le)
  set η := α ^ 2 / 256 with hη
  have hηn : 1 ≤ η * n := by rw [hη]; linarith
  set r : ℕ := ⌈η * n⌉₊ with hr
  set q : ℕ := ⌊α * n / 16⌋₊ with hq
  have hr2 : (r : ℝ) ≤ 2 * (η * n) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ η * n by linarith)
    rw [← hr] at this
    linarith
  have hqu : (q : ℝ) ≤ α * n / 16 := Nat.floor_le (by linarith)
  have hql : α * n / 32 ≤ q := by
    have := Nat.lt_floor_add_one (α * n / 16)
    rw [← hq] at this
    linarith
  have hqpos : 0 < q := by
    have : (0 : ℝ) < q := lt_of_lt_of_le (by linarith) hql
    exact_mod_cast this
  refine ⟨hqpos, ?_⟩
  have hrbound : 64 * n * r ≤ (α * n) ^ 2 := by
    have h1 : 64 * n * r ≤ 64 * n * (2 * (η * n)) :=
      mul_le_mul_of_nonneg_left hr2 (by linarith)
    have h2 : 64 * n * (2 * (η * n)) = (α * n) ^ 2 / 2 := by rw [hη]; ring
    have h3 : 0 ≤ (α * n) ^ 2 := sq_nonneg _
    linarith
  have hb := ReserveBudget.sparse_residue_budget n (α * n) m r q hn0 (by linarith)
    (by nlinarith) hm hrbound hql hqu
  linarith

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown

open Finset

/-- **Uniform reserve cover-down and absorption from exact inputs.** For fixed `b > 0`
and `0 < α ≤ 1` there is `N` such that for every finite `V` with `n = |V| ≥ N` and all
`p, F, G, A, X`: if `A, X ⊆ E(G)` are disjoint, `E(G)` is integrally `F`-divisible, `A`
absorbs every integrally divisible `L ⊆ X`, the reserve graph on `X` is
`α`-`F`-anti-edgeful, and the main graph `J = G - (A ∪ X)` carries weights
`0 ≤ φ ≤ b/n` on its `F`-copies with exact unit load on each of its edges, then `E(G)`
has an `F`-decomposition. -/
theorem typed_cover_down_absorption (b α : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
        (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset (Sym2 V))
        [DecidableRel (ReserveCoverDown.reserveGraph X).Adj] (φ : Finset V → ℝ),
        A ⊆ G.edgeFinset → X ⊆ G.edgeFinset → Disjoint A X →
        IsIntDiv p F G.edgeFinset →
        (∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)) →
        AntiEdgeful p F (ReserveCoverDown.reserveGraph X) α →
        (∀ s, IsCopy p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) s →
          0 ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
        (∀ e ∈ G.edgeFinset \ (A ∪ X),
          ∑ s ∈ copies p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V)))
            with e ∈ triEdges s, φ s = 1) →
        HasDecomp p F G.edgeFinset := by
  have hη0 : 0 < α ^ 2 / 256 := by positivity
  have hη1 : α ^ 2 / 256 ≤ 1 := by
    have : α ^ 2 ≤ 1 := by nlinarith
    linarith
  obtain ⟨N₀, hN₀⟩ := TypedNibble.typed_nibble_packing b (α ^ 2 / 256) hb hη0 hη1
  refine ⟨max N₀ ⌈256 / α ^ 2⌉₊, ?_⟩
  intro V _ _ hV t p F G _ A X _ φ hA hX hAX hE habs hres hw hload
  classical
  set J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V)) with hJdef
  have hJ : J.edgeFinset = G.edgeFinset \ (A ∪ X) := SimpleGraph.edgeFinset_deleteEdges _
  obtain ⟨D, Q, -, -, hQJ, -, hQdec, hdeg⟩ :=
    hN₀ V (le_trans (le_max_left _ _) hV) t p F J φ hw (fun e he => hload e (hJ ▸ he))
  rw [hJ] at hQJ hdeg
  set L := (G.edgeFinset \ (A ∪ X)) \ Q with hL
  have hn : 256 / α ^ 2 ≤ (Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hV)
  have hdegr : DegBounded L (⌈α ^ 2 / 256 * Fintype.card V⌉₊ : ℕ) :=
    fun v => (hdeg v).trans (Nat.le_ceil _)
  have hm := card_le_of_degBounded L
    (not_isDiag_of_mem_edgeFinset G (fun e he => (mem_sdiff.mp (mem_sdiff.mp he).1).1)) _ hdegr
  obtain ⟨hq, hbudget⟩ := schedule_budget α (Fintype.card V) L.card hα0 hα1 hn hm
  refine ReserveCoverDown.hasDecomp_of_sparse_main_packing p F G A X Q α hE hA hX hAX habs
    hres hQJ hQdec ?_ L.card _ _ hq le_rfl hdegr hbudget
  intro a c hac
  exact TypedNibble.exists_type_of_load_eq_one p F J φ (hload _ (mem_sdiff.mp hac).1)

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown
