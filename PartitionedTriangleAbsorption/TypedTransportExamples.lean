/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerTransport
public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse

/-! # Linear charge transport is forced, for each of F0--F3

For every `k` we take `k` vertex-disjoint copies of a twelve-vertex gadget. Each gadget is a
union of three four-cycles; the reserve is the union of all copies and the region `S` is
spanned by the inside cycles. No reserve edge joins the region to its complement. The whole
reserve is integrally divisible, the empty leftover is divisible, and their charges inside
the region differ by a fixed nonzero multiple of `k`.

Consequently every typed refiner of this reserve whose pieces are integrally divisible and
have at most `K` edges has at least `2k / K` library pieces crossing the region boundary,
for every remainder `R` disjoint from the reserve. In particular no refiner can route the
region's leftover through a boundary of bounded capacity, as the ordinary parity hierarchy
does. The pieces may be disconnected and `R` may use any vertices: the bound is about the
library, not about a geometric construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedTransportExamples

open Finset TypedApplicationLinks TypedTransformer TypedDivisibilityCollapse TypedRefinerCharge
  TypedRefinerTransport AntiEdgeSelection

variable {t : ℕ} {W : Type*} [DecidableEq W]

/-! ### Disjoint copies of a gadget -/

/-- Copy `j` of an edge set. -/
def liftEdges {k : ℕ} (j : Fin k) (E : Finset (Sym2 W)) : Finset (Sym2 (Fin k × W)) :=
  E.image (Sym2.map (Prod.mk j))

/-- All `k` copies. -/
def copies (k : ℕ) (E : Finset (Sym2 W)) : Finset (Sym2 (Fin k × W)) :=
  univ.biUnion fun j => liftEdges j E

/-- The parts on the copies. -/
def liftPart {k : ℕ} (q : W → Fin t) : Fin k × W → Fin t := fun x => q x.2

/-- The region spanned by the copies of `U₀`. -/
def region (k : ℕ) (U₀ : Finset W) : Finset (Sym2 (Fin k × W)) :=
  ((univ : Finset (Fin k)) ×ˢ U₀).sym2

omit [DecidableEq W] in
theorem map_injective {k : ℕ} (j : Fin k) :
    Function.Injective (Sym2.map (Prod.mk j : W → Fin k × W)) :=
  Sym2.map.injective (Prod.mk_right_injective j)

theorem liftEdges_disjoint {k : ℕ} (E : Finset (Sym2 W)) :
    ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint fun j => liftEdges j E := by
  intro j _ j' _ hjj'
  rw [Function.onFun, disjoint_left]
  intro e he he'
  obtain ⟨a, -, rfl⟩ := mem_image.mp he
  obtain ⟨b, -, hb⟩ := mem_image.mp he'
  induction a using Sym2.ind with
  | _ x y =>
    induction b using Sym2.ind with
    | _ u v =>
      simp only [Sym2.map_mk, Sym2.eq_iff, Prod.mk.injEq] at hb
      rcases hb with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact hjj' h.symm

omit [DecidableEq W] in
theorem pairVec_lift {k : ℕ} (q : W → Fin t) (j : Fin k) (e : Sym2 W) :
    pairVec (liftPart q) (Sym2.map (Prod.mk j) e) = pairVec q e := by
  induction e using Sym2.ind with
  | _ a b => rfl

theorem edgeVec_liftEdges {k : ℕ} (q : W → Fin t) (j : Fin k) (E : Finset (Sym2 W)) :
    edgeVec (liftPart q) (liftEdges j E) = edgeVec q E := by
  rw [edgeVec, liftEdges, sum_image fun a _ b _ h => map_injective j h]
  exact sum_congr rfl fun e _ => pairVec_lift q j e

theorem charge_liftEdges {k : ℕ} (χ : Fin t → Fin t → ℤ) (q : W → Fin t) (j : Fin k)
    (E : Finset (Sym2 W)) : charge χ (liftPart q) (liftEdges j E) = charge χ q E := by
  rw [charge, edgeVec_liftEdges]; rfl

theorem degContrib_lift {k : ℕ} (q : W → Fin t) (j j' : Fin k) (w : W) (e : Sym2 W) :
    degContrib (liftPart q) (j, w) (Sym2.map (Prod.mk j') e) =
      if j' = j then degContrib q w e else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    funext i
    simp only [degContrib, Sym2.map_mk, Sym2.lift_mk, Prod.mk.injEq, liftPart]
    by_cases hj : j' = j
    · subst hj; simp
    · simp [hj]

theorem degVec_copies {k : ℕ} (q : W → Fin t) (E : Finset (Sym2 W)) (j : Fin k) (w : W) :
    degVec (liftPart q) (copies k E) (j, w) = degVec q E w := by
  rw [degVec, copies, sum_biUnion (liftEdges_disjoint E)]
  rw [sum_eq_single_of_mem j (mem_univ j)]
  · rw [liftEdges, sum_image fun a _ b _ h => map_injective j h]
    simp only [degContrib_lift, ite_true]
    rfl
  · intro j' _ hj'
    rw [liftEdges, sum_image fun a _ b _ h => map_injective j' h]
    exact sum_eq_zero fun e _ => by rw [degContrib_lift, ite_eq_right hj']

theorem edgeVec_copies (k : ℕ) (q : W → Fin t) (E : Finset (Sym2 W)) :
    edgeVec (liftPart q) (copies k E) = (k : ℤ) • edgeVec q E := by
  rw [edgeVec, copies, sum_biUnion (liftEdges_disjoint E)]
  refine (sum_congr rfl fun j _ => edgeVec_liftEdges q j E).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, natCast_zsmul]

/-- Integral divisibility of the gadget passes to all its disjoint copies. -/
theorem isIntDiv_copies {F : Finset (Multiset (Fin t))} (k : ℕ) {q : W → Fin t}
    {E : Finset (Sym2 W)} (h : IsIntDiv q F E) : IsIntDiv (liftPart q) F (copies k E) := by
  obtain ⟨⟨c, hc⟩, hv⟩ := h
  refine ⟨⟨fun τ => (k : ℤ) * c τ, ?_⟩, ?_⟩
  · rw [edgeVec_copies, hc, smul_sum]
    exact sum_congr rfl fun τ _ => by rw [smul_smul]
  · rintro ⟨j, w⟩
    obtain ⟨c', hc'⟩ := hv w
    exact ⟨c', by rw [degVec_copies, hc']; rfl⟩

theorem copies_inter_region (k : ℕ) (E : Finset (Sym2 W)) (U₀ : Finset W) :
    copies k E ∩ region k U₀ = copies k (E ∩ U₀.sym2) := by
  ext e
  simp only [copies, region, liftEdges, mem_inter, mem_biUnion, mem_univ, true_and,
    mem_image]
  constructor
  · rintro ⟨⟨j, a, ha, rfl⟩, hreg⟩
    refine ⟨j, a, ⟨ha, ?_⟩, rfl⟩
    rw [mem_sym2_iff] at hreg ⊢
    intro x hx
    have := hreg (j, x) (Sym2.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using this
  · rintro ⟨j, a, ha, rfl⟩
    obtain ⟨haE, haU⟩ := ha
    refine ⟨⟨j, a, haE, rfl⟩, ?_⟩
    rw [mem_sym2_iff] at haU ⊢
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hx
    simpa using haU y hy

theorem charge_copies (χ : Fin t → Fin t → ℤ) (k : ℕ) (q : W → Fin t) (E : Finset (Sym2 W)) :
    charge χ (liftPart q) (copies k E) = k * charge χ q E := by
  rw [copies, charge_biUnion χ _ _ _ (liftEdges_disjoint E)]
  simp_rw [charge_liftEdges]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- No reserve edge joins the region to its complement. -/
theorem copies_respect_region (k : ℕ) {E : Finset (Sym2 W)} {U₀ : Finset W}
    (hE : ∀ e ∈ E, e ∈ U₀.sym2 ∨ ∀ x ∈ e, x ∉ U₀) :
    ∀ e ∈ copies k E, e ∈ region k U₀ ∨ ∀ x ∈ e, x.2 ∉ U₀ := by
  intro e he
  obtain ⟨j, -, he⟩ := mem_biUnion.mp he
  obtain ⟨a, ha, rfl⟩ := mem_image.mp he
  rcases hE a ha with h | h
  · left
    rw [region, mem_sym2_iff] at *
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hx
    simpa using h y hy
  · right
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hx
    exact h y hy

/-- **Generic obstruction.** Copies of a divisible gadget whose inside has nonzero charge
force linearly many crossing library pieces, for every refiner with divisible pieces. -/
theorem copies_crossing_bound {F : Finset (Multiset (Fin t))} {χ : Fin t → Fin t → ℤ}
    (hχ : Kills χ F) {m : ℤ} (hm0 : 0 ≤ m) (hm : ∀ i j, |χ i j| ≤ m)
    {q : W → Fin t} {E : Finset (Sym2 W)} (hE : IsIntDiv q F E) (U₀ : Finset W)
    (k K : ℕ) {I : Type*} [DecidableEq I] (indices : Finset I)
    (B : I → Finset (Sym2 (Fin k × W))) (R : Finset (Sym2 (Fin k × W)))
    (hRX : Disjoint R (copies k E))
    (href : RefinerAssembly.RefinesReserve (p := liftPart q) (F := F) indices B (copies k E) R)
    (hpieces : ∀ i ∈ indices, IsIntDiv (liftPart q) F (B i))
    (hsize : ∀ i ∈ indices, (B i).card ≤ K) :
    k * |charge χ q (E ∩ U₀.sym2)| ≤ 4 * m * K * (crossing (region k U₀) indices B).card := by
  have h := crossing_lower_bound χ (M := 2 * m) (by linarith)
    (fun e => abs_pair_pairVec_le hm _ e) indices B (copies k E) R hRX href
    (fun i hi => charge_eq_zero_of_isIntDiv hχ (hpieces i hi)) hsize (region k U₀)
    (copies k E) ∅ subset_rfl (isIntDiv_copies k hE) (empty_subset _) isIntDiv_empty
  rw [copies_inter_region, charge_copies, empty_inter, charge_empty, sub_zero, abs_mul,
    Nat.abs_cast] at h
  linarith

/-! ### The four gadgets -/

/-- Edges of three four-cycles on `0..3`, `4..7`, `8..11`. -/
def cycles : Finset (Sym2 (Fin 12)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(4, 5), s(5, 6), s(6, 7), s(7, 4),
    s(8, 9), s(9, 10), s(10, 11), s(11, 8)}

theorem cycles_loopless : ∀ e ∈ cycles, ¬ e.IsDiag := by decide

theorem cycles_even : ∀ v, Even (incidentLoad cycles v) := by
  unfold incidentLoad cycles; decide

/-- F0 gadget: two `0101` cycles inside, one `0000` cycle outside. -/
def q0 : Fin 12 → Fin 2 := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]
/-- F1/F2 gadget: two `0202` cycles inside, one `0000` cycle outside. -/
def q12 : Fin 12 → Fin 4 := ![0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0]
/-- F3 gadget: one `0101` cycle inside, `0202` and `1212` cycles outside. -/
def q3 : Fin 12 → Fin 4 := ![0, 1, 0, 1, 0, 2, 0, 2, 1, 2, 1, 2]

/-- Inside vertices for F0--F2. -/
def U8 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7}
/-- Inside vertices for F3. -/
def U4 : Finset (Fin 12) := {0, 1, 2, 3}

theorem cycles_respect_U8 : ∀ e ∈ cycles, e ∈ U8.sym2 ∨ ∀ x ∈ e, x ∉ U8 := by
  have h : ∀ e ∈ cycles, e ∈ U8.sym2 ∨ e ∈ (univ \ U8).sym2 := by
    unfold cycles U8; decide
  intro e he
  rcases h e he with h | h
  · exact Or.inl h
  · right; intro x hx; exact (mem_sdiff.mp ((mem_sym2_iff.mp h) x hx)).2

theorem cycles_respect_U4 : ∀ e ∈ cycles, e ∈ U4.sym2 ∨ ∀ x ∈ e, x ∉ U4 := by
  have h : ∀ e ∈ cycles, e ∈ U4.sym2 ∨ e ∈ (univ \ U4).sym2 := by
    unfold cycles U4; decide
  intro e he
  rcases h e he with h | h
  · exact Or.inl h
  · right; intro x hx; exact (mem_sdiff.mp ((mem_sym2_iff.mp h) x hx)).2

theorem F0_card : ∀ τ ∈ F0, Multiset.card τ = 3 := by unfold F0; decide
theorem F1_card : ∀ τ ∈ F1, Multiset.card τ = 3 := by unfold F1; decide
theorem F2_card : ∀ τ ∈ F2, Multiset.card τ = 3 := by unfold F2; decide
theorem F3_card : ∀ τ ∈ F3, Multiset.card τ = 3 := by unfold F3; decide

theorem gadget0_isIntDiv : IsIntDiv q0 F0 cycles := by
  refine isIntDiv_of_active_even F0_three_step cycles_loopless ?_ cycles_even
    ⟨fun τ => if τ = ({0, 0, 1} : Multiset (Fin 2)) then 4 else 0, ?_⟩
  · unfold ActiveEdges Link F0 q0 cycles; decide
  · unfold edgeVec pairVec cycles q0 F0 typeEdgeVec; decide

theorem gadget1_isIntDiv : IsIntDiv q12 F1 cycles := by
  refine isIntDiv_of_active_even F1_three_step cycles_loopless ?_ cycles_even
    ⟨fun τ => if τ = ({0, 0, 2} : Multiset (Fin 4)) then 4 else 0, ?_⟩
  · unfold ActiveEdges Link F1 q12 cycles; decide
  · unfold edgeVec pairVec cycles q12 F1 typeEdgeVec; decide

theorem gadget2_isIntDiv : IsIntDiv q12 F2 cycles := by
  refine isIntDiv_of_active_even F2_three_step cycles_loopless ?_ cycles_even
    ⟨fun τ => if τ = ({0, 0, 2} : Multiset (Fin 4)) then 4 else 0, ?_⟩
  · unfold ActiveEdges Link F2 q12 cycles; decide
  · unfold edgeVec pairVec cycles q12 F2 typeEdgeVec; decide

theorem gadget3_isIntDiv : IsIntDiv q3 F3 cycles := by
  refine isIntDiv_of_active_even F3_three_step cycles_loopless ?_ cycles_even
    ⟨fun τ => if τ = ({0, 1, 2} : Multiset (Fin 4)) then 4 else 0, ?_⟩
  · unfold ActiveEdges Link F3 q3 cycles; decide
  · unfold edgeVec pairVec cycles q3 F3 typeEdgeVec; decide

theorem gadget0_charge : charge chi0 q0 (cycles ∩ U8.sym2) = 16 := by
  unfold charge pair edgeVec pairVec cycles q0 U8 chi0; decide

theorem gadget1_charge : charge chi1 q12 (cycles ∩ U8.sym2) = -16 := by
  unfold charge pair edgeVec pairVec cycles q12 U8 chi1; decide

theorem gadget2_charge : charge chi2 q12 (cycles ∩ U8.sym2) = -16 := by
  unfold charge pair edgeVec pairVec cycles q12 U8 chi2; decide

theorem gadget3_charge : charge chi3a q3 (cycles ∩ U4.sym2) = 8 := by
  unfold charge pair edgeVec pairVec cycles q3 U4 chi3a; decide

/-! ### The obstruction for each family -/

/-- **F0.** Every typed refiner of `k` gadget copies, with divisible pieces of at most `K`
edges and any remainder disjoint from the reserve, has at least `2k/K` library pieces
crossing the region, although no reserve edge crosses it. -/
theorem F0_transport_obstruction (k K : ℕ) {I : Type*} [DecidableEq I] (indices : Finset I)
    (B : I → Finset (Sym2 (Fin k × Fin 12))) (R : Finset (Sym2 (Fin k × Fin 12)))
    (hRX : Disjoint R (copies k cycles))
    (href : RefinerAssembly.RefinesReserve (p := liftPart q0) (F := F0) indices B
      (copies k cycles) R)
    (hpieces : ∀ i ∈ indices, IsIntDiv (liftPart q0) F0 (B i))
    (hsize : ∀ i ∈ indices, (B i).card ≤ K) :
    2 * k ≤ K * (crossing (region k U8) indices B).card := by
  have h := copies_crossing_bound kills_chi0 (by norm_num) chi0_bound gadget0_isIntDiv U8
    k K indices B R hRX href hpieces hsize
  rw [gadget0_charge] at h
  have h' : ((2 * k : ℕ) : ℤ) ≤ ((K * (crossing (region k U8) indices B).card : ℕ) : ℤ) := by
    push_cast; norm_num at h; linarith
  exact_mod_cast h'

/-- **F1.** Same conclusion. -/
theorem F1_transport_obstruction (k K : ℕ) {I : Type*} [DecidableEq I] (indices : Finset I)
    (B : I → Finset (Sym2 (Fin k × Fin 12))) (R : Finset (Sym2 (Fin k × Fin 12)))
    (hRX : Disjoint R (copies k cycles))
    (href : RefinerAssembly.RefinesReserve (p := liftPart q12) (F := F1) indices B
      (copies k cycles) R)
    (hpieces : ∀ i ∈ indices, IsIntDiv (liftPart q12) F1 (B i))
    (hsize : ∀ i ∈ indices, (B i).card ≤ K) :
    2 * k ≤ K * (crossing (region k U8) indices B).card := by
  have h := copies_crossing_bound kills_chi1 (by norm_num) chi1_bound gadget1_isIntDiv U8
    k K indices B R hRX href hpieces hsize
  rw [gadget1_charge] at h
  have h' : ((2 * k : ℕ) : ℤ) ≤ ((K * (crossing (region k U8) indices B).card : ℕ) : ℤ) := by
    push_cast; norm_num at h; linarith
  exact_mod_cast h'

/-- **F2.** Same conclusion. -/
theorem F2_transport_obstruction (k K : ℕ) {I : Type*} [DecidableEq I] (indices : Finset I)
    (B : I → Finset (Sym2 (Fin k × Fin 12))) (R : Finset (Sym2 (Fin k × Fin 12)))
    (hRX : Disjoint R (copies k cycles))
    (href : RefinerAssembly.RefinesReserve (p := liftPart q12) (F := F2) indices B
      (copies k cycles) R)
    (hpieces : ∀ i ∈ indices, IsIntDiv (liftPart q12) F2 (B i))
    (hsize : ∀ i ∈ indices, (B i).card ≤ K) :
    2 * k ≤ K * (crossing (region k U8) indices B).card := by
  have h := copies_crossing_bound kills_chi2 (by norm_num) chi2_bound gadget2_isIntDiv U8
    k K indices B R hRX href hpieces hsize
  rw [gadget2_charge] at h
  have h' : ((2 * k : ℕ) : ℤ) ≤ ((K * (crossing (region k U8) indices B).card : ℕ) : ℤ) := by
    push_cast; norm_num at h; linarith
  exact_mod_cast h'

/-- **F3.** Same conclusion. -/
theorem F3_transport_obstruction (k K : ℕ) {I : Type*} [DecidableEq I] (indices : Finset I)
    (B : I → Finset (Sym2 (Fin k × Fin 12))) (R : Finset (Sym2 (Fin k × Fin 12)))
    (hRX : Disjoint R (copies k cycles))
    (href : RefinerAssembly.RefinesReserve (p := liftPart q3) (F := F3) indices B
      (copies k cycles) R)
    (hpieces : ∀ i ∈ indices, IsIntDiv (liftPart q3) F3 (B i))
    (hsize : ∀ i ∈ indices, (B i).card ≤ K) :
    2 * k ≤ K * (crossing (region k U4) indices B).card := by
  have h := copies_crossing_bound kills_chi3a (by norm_num) chi3a_bound gadget3_isIntDiv U4
    k K indices B R hRX href hpieces hsize
  rw [gadget3_charge] at h
  have h' : ((2 * k : ℕ) : ℤ) ≤ ((K * (crossing (region k U4) indices B).card : ℕ) : ℤ) := by
    push_cast; norm_num at h; linarith
  exact_mod_cast h'

/-- The reserve of the F0 example is divisible and does not cross the region. -/
theorem F0_reserve_facts (k : ℕ) :
    IsIntDiv (liftPart q0) F0 (copies k cycles) ∧
      ∀ e ∈ copies k cycles, e ∈ region k U8 ∨ ∀ x ∈ e, x.2 ∉ U8 :=
  ⟨isIntDiv_copies k gadget0_isIntDiv, copies_respect_region k cycles_respect_U8⟩

end PartitionedTriangleAbsorption.TypedTransportExamples
