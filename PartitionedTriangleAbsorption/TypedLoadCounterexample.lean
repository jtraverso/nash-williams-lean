/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadFamilies

/-! # A physical counterexample to a seed-only typed boost for F0

The graph is the complete four-partite graph `K_{x,x,y,y}` with the two
`x`-classes in part `0` and the two `y`-classes in part `1`. Every triangle
uses three distinct classes, so it is an F0-copy. Constant weight `1/(2y)` is a
`2`-regular, `(1 - x/y)`-almost packing. On the other hand, for every real
weighting whose loads are all within `τ` of one, the F0 balance functional
forces `(y-x)^2 ≤ τ (x+y)^2`.

Consequently no input tolerance `ε > 0`, chosen independently of the target
precision `τ`, lets a regular seed alone produce `τ`-precise loads, even with
the weights allowed to be negative or uncapped. For `x ≤ y ≤ 2x` the example is
also `1/6`-anti-edgeful, so anti-edge abundance does not repair this; the
missing hypothesis is the global type balance at precision `τ`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLoadCounterexample

open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem pairVec_eq_sum_degContrib (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    pairVec p e i j = ∑ v ∈ univ.filter (fun v => p v = i), degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, degContrib, Sym2.lift_mk, Finset.sum_add_distrib]
    rw [Finset.sum_filter, Finset.sum_filter]
    simp only [← ite_and]
    congr 1
    · rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    · rw [Finset.sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp

/-- Ordered edge counts from degree vectors. -/
theorem edgeVec_eq_sum_degVec (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = ∑ v ∈ univ.filter (fun v => p v = i), degVec p E v j := by
  simp only [edgeVec, degVec, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => pairVec_eq_sum_degContrib p e i j

/-- The degree vector of a graph counts typed neighbours. -/
theorem degVec_edgeFinset (p : V → Fin t) (J : SimpleGraph V) [DecidableRel J.Adj]
    (v : V) (j : Fin t) :
    degVec p J.edgeFinset v j = ((univ.filter (fun w => J.Adj v w ∧ p w = j)).card : ℤ) := by
  set W := univ.filter (fun w => J.Adj v w ∧ p w = j)
  have himg : W.image (fun w => s(v, w)) ⊆ J.edgeFinset := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp hw).2.1
  have hinj : Set.InjOn (fun w => s(v, w)) W := by
    intro w _ w' _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  rw [degVec, Finset.sum_apply, ← Finset.sum_subset himg, Finset.sum_image hinj,
    Finset.card_eq_sum_ones, Nat.cast_sum]
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' := (mem_filter.mp hw).2
    have hvw : w ≠ v := (J.ne_of_adj hw'.1).symm
    simp [degContrib, hw'.2, hvw]
  · intro e he hne
    induction e using Sym2.ind with
    | _ a b =>
      have hab : J.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      simp only [degContrib, Sym2.lift_mk]
      have h1 : ¬ (a = v ∧ p b = j) := by
        rintro ⟨rfl, hb⟩
        exact hne (mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hab, hb⟩, rfl⟩)
      have h2 : ¬ (b = v ∧ p a = j) := by
        rintro ⟨rfl, ha⟩
        exact hne (mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, hab.symm, ha⟩,
          Sym2.eq_swap⟩)
      simp [h1, h2]

/-- The copies through an edge are parametrized by their third vertex. -/
theorem card_edgeCopies (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] {u v : V} (huv : J.Adj u v) :
    ((copies p F J).filter (fun s => s(u, v) ∈ triEdges s)).card =
      (univ.filter (fun z => J.Adj u z ∧ J.Adj v z ∧
        ({p u, p v, p z} : Multiset (Fin t)) ∈ F)).card := by
  set Z := univ.filter (fun z => J.Adj u z ∧ J.Adj v z ∧
    ({p u, p v, p z} : Multiset (Fin t)) ∈ F)
  have hne := J.ne_of_adj huv
  have heq : (copies p F J).filter (fun s => s(u, v) ∈ triEdges s) =
      Z.image (fun z => ({u, v, z} : Finset V)) := by
    ext s
    simp only [mem_filter, mem_image, Z, mem_univ, true_and]
    constructor
    · rintro ⟨hs, he⟩
      have hc := mem_copies_iff.mp hs
      obtain ⟨hu, hv, -⟩ := mem_triEdges_iff.mp he
      obtain ⟨c, huc, hvc, rfl⟩ := exists_third_of_card_three hc.1.card_eq hu hv hne
      have hcl := (SimpleGraph.is3Clique_triple_iff).mp hc.1
      refine ⟨c, ⟨hcl.2.1, hcl.2.2, ?_⟩, rfl⟩
      rw [← map_three p hne huc hvc]
      exact hc.2
    · rintro ⟨z, ⟨huz, hvz, hF⟩, rfl⟩
      refine ⟨mem_copies_iff.mpr ⟨(SimpleGraph.is3Clique_triple_iff).mpr ⟨huv, huz, hvz⟩, ?_⟩,
        mem_triEdges_iff.mpr ⟨by simp, by simp, hne⟩⟩
      rw [map_three p hne (J.ne_of_adj huz) (J.ne_of_adj hvz)]
      exact hF
  rw [heq]
  refine Finset.card_image_of_injOn fun z hz z' hz' h => ?_
  have hz1 := (mem_filter.mp hz).2
  have hz2 := (mem_filter.mp hz').2
  have hmem : z ∈ ({u, v, z'} : Finset V) := by
    rw [← show ({u, v, z} : Finset V) = {u, v, z'} from h]
    simp
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with h' | h' | h'
  · exact absurd h'.symm (J.ne_of_adj hz1.1)
  · exact absurd h'.symm (J.ne_of_adj hz1.2.1)
  · exact h'

omit [Fintype V] [DecidableEq V] in
theorem pairFun_pairVec_mk (p : V → Fin t) (l : Fin t → Fin t → ℤ) (a b : V) :
    pairFun l (pairVec p s(a, b)) = l (p a) (p b) + l (p b) (p a) := by
  simp only [pairFun, pairVec, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_one, mul_zero]
  congr 1
  · rw [Finset.sum_eq_single (p a) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  · rw [Finset.sum_eq_single (p b) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp

end Counting

section Example

/-- Class sizes of `K_{x,x,y,y}`. -/
def sz (x y : ℕ) : Fin 4 → ℕ := ![x, x, y, y]

/-- Vertices of `K_{x,x,y,y}`: a class and an index inside it. -/
abbrev KV (x y : ℕ) := Σ c : Fin 4, Fin (sz x y c)

/-- Classes `0,1` lie in part `0`; classes `2,3` lie in part `1`. -/
def cls : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def kpart (x y : ℕ) : KV x y → Fin 2 := fun u => cls u.1

/-- The complete four-partite graph on the classes. -/
def kgraph (x y : ℕ) : SimpleGraph (KV x y) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance (x y : ℕ) : DecidableRel (kgraph x y).Adj :=
  fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))

variable {x y : ℕ}

theorem card_KV : Fintype.card (KV x y) = 2 * x + 2 * y := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  simp [Fin.sum_univ_four, sz]
  ring

theorem sum_filter_class (P : Fin 4 → Prop) [DecidablePred P] (g : Fin 4 → ℝ) :
    ∑ z ∈ univ.filter (fun z : KV x y => P z.1), g z.1 =
      ∑ c ∈ univ.filter P, (sz x y c : ℝ) * g c := by
  have h : univ.filter (fun z : KV x y => P z.1) =
      (univ.filter P).sigma (fun _ => univ) := by
    ext z
    simp
  rw [h, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

theorem card_filter_class (P : Fin 4 → Prop) [DecidablePred P] :
    ((univ.filter (fun z : KV x y => P z.1)).card : ℝ) =
      ∑ c ∈ univ.filter P, (sz x y c : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  have := sum_filter_class (x := x) (y := y) P (fun _ => 1)
  simp only [mul_one] at this
  simpa using this

theorem cls_type_mem (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({cls a, cls b, cls c} : Multiset (Fin 2)) ∈ F0 := by
  revert a b c
  decide

/-- Number of third vertices for an edge between classes `a ≠ b`. -/
def thirdCount (x y : ℕ) (a b : Fin 4) : ℝ :=
  ∑ c ∈ univ.filter (fun c => a ≠ c ∧ b ≠ c), (sz x y c : ℝ)

theorem thirdCount_bounds (hxy : x ≤ y) (a b : Fin 4) (hab : a ≠ b) :
    2 * (x : ℝ) ≤ thirdCount x y a b ∧ thirdCount x y a b ≤ 2 * y := by
  have h : (x : ℝ) ≤ y := by exact_mod_cast hxy
  fin_cases a <;> fin_cases b <;>
    simp [thirdCount, sz, Finset.sum_filter, Fin.sum_univ_four] at hab ⊢ <;>
    constructor <;> linarith

theorem kgraph_load_const (w : ℝ) {u v : KV x y} (huv : (kgraph x y).Adj u v) :
    edgeLoad (kpart x y) F0 (kgraph x y) (fun _ => w) s(u, v) = w * thirdCount x y u.1 v.1 := by
  unfold edgeLoad
  rw [Finset.sum_const, nsmul_eq_mul, card_edgeCopies _ _ _ huv, mul_comm]
  congr 1
  have hfil : univ.filter (fun z : KV x y => (kgraph x y).Adj u z ∧ (kgraph x y).Adj v z ∧
      ({kpart x y u, kpart x y v, kpart x y z} : Multiset (Fin 2)) ∈ F0) =
      univ.filter (fun z : KV x y => u.1 ≠ z.1 ∧ v.1 ≠ z.1) := by
    ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, cls_type_mem _ _ _ huv h1 h2⟩
  rw [hfil, card_filter_class (fun c => u.1 ≠ c ∧ v.1 ≠ c)]
  rfl

/-- **The seed.** Constant weight `1/(2y)` is a `2`-regular `(1-x/y)`-almost
F0-packing of `K_{x,x,y,y}`. -/
theorem kgraph_seed (hx : 0 < x) (hxy : x ≤ y) :
    IsRegularAlmostPacking (kpart x y) F0 (kgraph x y) 2 (1 - (x : ℝ) / y)
      (fun _ => 1 / (2 * (y : ℝ))) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le hx hxy)
  have hxyR : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hn : (Fintype.card (KV x y) : ℝ) = 2 * x + 2 * y := by
    rw [card_KV]; push_cast; ring
  refine ⟨fun s _ => ?_, fun e he => ?_⟩
  · rw [hn]
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · induction e using Sym2.ind with
    | _ u v =>
      have huv : (kgraph x y).Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have hload := kgraph_load_const (1 / (2 * (y : ℝ))) huv
      unfold edgeLoad at hload
      rw [hload]
      obtain ⟨hlo, hhi⟩ := thirdCount_bounds hxy u.1 v.1 huv
      constructor
      · rw [sub_sub_cancel, div_le_iff₀ hyR]
        rw [one_div, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      · rw [one_div, inv_mul_eq_div, div_le_one (by positivity)]
        exact hhi

theorem kgraph_edgeVec (i j : Fin 2) :
    (edgeVec (kpart x y) (kgraph x y).edgeFinset i j : ℝ) =
      ∑ a ∈ univ.filter (fun a => cls a = i), (sz x y a : ℝ) *
        ∑ c ∈ univ.filter (fun c => a ≠ c ∧ cls c = j), (sz x y c : ℝ) := by
  rw [edgeVec_eq_sum_degVec, Int.cast_sum]
  have hdeg : ∀ v : KV x y, (degVec (kpart x y) (kgraph x y).edgeFinset v j : ℝ) =
      ∑ c ∈ univ.filter (fun c => v.1 ≠ c ∧ cls c = j), (sz x y c : ℝ) := by
    intro v
    rw [degVec_edgeFinset, Int.cast_natCast, ← card_filter_class (fun c => v.1 ≠ c ∧ cls c = j)]
    rfl
  simp only [hdeg]
  exact sum_filter_class (fun a => cls a = i)
    (fun a => ∑ c ∈ univ.filter (fun c => a ≠ c ∧ cls c = j), (sz x y c : ℝ))

theorem pairFun_cast {t : ℕ} (l M : Fin t → Fin t → ℤ) :
    (pairFun l M : ℝ) = ∑ i, ∑ j, (l i j : ℝ) * (M i j : ℝ) := by
  simp [pairFun]

/-- The F0 balance functional of `K_{x,x,y,y}`. -/
theorem kgraph_defect :
    (pairFun (groupPair g0) (edgeVec (kpart x y) (kgraph x y).edgeFinset) : ℝ) =
      -4 * ((y : ℝ) - x) ^ 2 := by
  rw [pairFun_cast]
  simp only [Fin.sum_univ_two, kgraph_edgeVec]
  simp only [Finset.sum_filter, Fin.sum_univ_four]
  simp [cls, sz, groupPair, g0]
  ring

theorem abs_groupPair_g0 (i j : Fin 2) :
    |groupPair g0 i j + groupPair g0 j i| = groupMass g0 i j + groupMass g0 j i := by
  revert i j
  decide

/-- The absolute mass of the F0 balance functional on `K_{x,x,y,y}`. -/
theorem kgraph_mass :
    ∑ e ∈ (kgraph x y).edgeFinset,
        |(pairFun (groupPair g0) (pairVec (kpart x y) e) : ℝ)| =
      4 * ((x : ℝ) + y) ^ 2 := by
  have hper : ∀ e : Sym2 (KV x y), |(pairFun (groupPair g0) (pairVec (kpart x y) e) : ℝ)| =
      (pairFun (groupMass g0) (pairVec (kpart x y) e) : ℝ) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      rw [← Int.cast_abs, pairFun_pairVec_mk, pairFun_pairVec_mk, abs_groupPair_g0]
  simp only [hper]
  rw [← Int.cast_sum, ← pairFun_edgeVec, pairFun_cast]
  simp only [Fin.sum_univ_two, kgraph_edgeVec]
  simp only [Finset.sum_filter, Fin.sum_univ_four]
  simp [cls, sz, groupMass, g0]
  ring

/-- **Obstruction on the example.** Any real weights whose loads on
`K_{x,x,y,y}` are all within `τ` of one satisfy `(y-x)^2 ≤ τ (x+y)^2`. -/
theorem kgraph_near_loads_force (ψ : Finset (KV x y) → ℝ) {τ : ℝ}
    (hload : ∀ e ∈ (kgraph x y).edgeFinset,
      |edgeLoad (kpart x y) F0 (kgraph x y) ψ e - 1| ≤ τ) :
    ((y : ℝ) - x) ^ 2 ≤ τ * ((x : ℝ) + y) ^ 2 := by
  have h := annihilator_balance (kpart x y) F0 (kgraph x y) ψ annihilates_F0 hload
  rw [kgraph_defect, kgraph_mass, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ((y : ℝ) - x))] at h
  norm_num at h
  linarith

theorem common_class_mass (hxy : x ≤ y) (a b : Fin 4) (k : Fin 2)
    (hF : ({cls a, cls b, k} : Multiset (Fin 2)) ∈ F0) :
    (x : ℝ) ≤ ∑ c ∈ univ.filter (fun c => a ≠ c ∧ c ≠ b ∧ cls c = k), (sz x y c : ℝ) := by
  have h : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  fin_cases a <;> fin_cases b <;> fin_cases k <;> first
    | exact absurd hF (by decide)
    | (simp only [Finset.sum_filter, Fin.sum_univ_four]; simp [cls, sz] <;> linarith)

/-- `K_{x,x,y,y}` is `1/6`-anti-edgeful for F0 when `x ≤ y ≤ 2x`: every typed
pair has at least `x ≥ n/6` common neighbours in the required part. -/
theorem kgraph_antiEdgeful (hxy : x ≤ y) (hy2 : y ≤ 2 * x) :
    AntiEdgeful (kpart x y) F0 (kgraph x y) (1 / 6) := by
  intro τ hτ i j k hijk u v _ hu hv
  have hfil : univ.filter (fun w : KV x y => (kgraph x y).Adj u w ∧ (kgraph x y).Adj w v ∧
      kpart x y w = k) = univ.filter (fun w : KV x y => u.1 ≠ w.1 ∧ w.1 ≠ v.1 ∧ cls w.1 = k) := by
    rfl
  rw [hfil, card_filter_class (fun c => u.1 ≠ c ∧ c ≠ v.1 ∧ cls c = k)]
  have hF : ({cls u.1, cls v.1, k} : Multiset (Fin 2)) ∈ F0 := by
    have h1 : cls u.1 = i := hu
    have h2 : cls v.1 = j := hv
    rw [h1, h2, ← hijk]
    exact hτ
  refine le_trans ?_ (common_class_mass hxy u.1 v.1 k hF)
  rw [card_KV]
  have : (y : ℝ) ≤ 2 * x := by exact_mod_cast hy2
  push_cast
  linarith

end Example

/-- **Refutation of a seed-only typed boost for F0.** Already for `C = 2`, no
input tolerance `ε > 0` chosen independently of the target precision `τ` has the
property that every graph with a `2`-regular `ε`-almost F0-packing carries real
weights (not even required nonnegative or capped) with all loads within `τ` of
one, even when the graph is additionally assumed `1/6`-anti-edgeful. The witnesses
are `K_{qk,qk,(q+1)k,(q+1)k}` with `q ≥ 1/ε`, `τ = 1/(2(2q+1)^2)`. -/
theorem F0_seed_only_boost_refuted :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ τ : ℝ, 0 < τ → ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] (φ : Finset V → ℝ),
        IsRegularAlmostPacking p F0 J 2 ε φ → AntiEdgeful p F0 J (1 / 6) →
        ∃ ψ : Finset V → ℝ, ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ := by
  rintro ⟨ε, hε, h⟩
  set q : ℕ := ⌈1 / ε⌉₊ + 1 with hq
  have hqR : 1 / ε ≤ (q : ℝ) := by
    rw [hq]; push_cast; linarith [Nat.le_ceil (1 / ε)]
  have hq1 : (1 : ℝ) ≤ q := by rw [hq]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈1 / ε⌉₊]
  set τ : ℝ := 1 / (2 * (2 * (q : ℝ) + 1) ^ 2) with hτ
  obtain ⟨N, hN⟩ := h τ (by positivity)
  set k : ℕ := N + 1 with hk
  have hkR : (1 : ℝ) ≤ k := by rw [hk]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hqpos : 0 < q := by rw [hq]; omega
  have hxpos : 0 < q * k := Nat.mul_pos hqpos (by omega)
  have hxy : q * k ≤ (q + 1) * k := Nat.mul_le_mul_right _ (Nat.le_succ q)
  have hcard : N ≤ Fintype.card (KV (q * k) ((q + 1) * k)) := by
    rw [card_KV]; nlinarith
  have hseed := kgraph_seed hxpos hxy
  have hseed' : IsRegularAlmostPacking (kpart (q * k) ((q + 1) * k)) F0
      (kgraph (q * k) ((q + 1) * k)) 2 ε (fun _ => 1 / (2 * (((q + 1) * k : ℕ) : ℝ))) := by
    refine ⟨hseed.1, fun e he => ⟨?_, (hseed.2 e he).2⟩⟩
    have h1 := (hseed.2 e he).1
    have hle : 1 - (((q * k : ℕ) : ℝ) / (((q + 1) * k : ℕ) : ℝ)) ≤ ε := by
      push_cast
      have hkpos : (0 : ℝ) < k := by linarith
      rw [mul_div_mul_right _ _ hkpos.ne', one_sub_div (by positivity)]
      simp only [add_sub_cancel_left]
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hqR
      nlinarith
    linarith
  have hy2 : (q + 1) * k ≤ 2 * (q * k) := by nlinarith
  obtain ⟨ψ, hψ⟩ := hN (KV (q * k) ((q + 1) * k)) hcard (kpart _ _) (kgraph _ _) _ hseed'
    (kgraph_antiEdgeful hxy hy2)
  have hforce := kgraph_near_loads_force ψ hψ
  push_cast at hforce
  have hsq : (((q : ℝ) + 1) * k - q * k) ^ 2 = (k : ℝ) ^ 2 := by ring
  have hsum : ((q : ℝ) * k + (q + 1) * k) ^ 2 = (2 * q + 1) ^ 2 * (k : ℝ) ^ 2 := by ring
  rw [hsq, hsum, hτ] at hforce
  have hpos : (0 : ℝ) < (2 * q + 1) ^ 2 := by positivity
  rw [← mul_assoc, one_div, inv_mul_eq_div, div_mul_cancel_right₀ hpos.ne'] at hforce
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  linarith

end PartitionedTriangleAbsorption.TypedLoadCounterexample
