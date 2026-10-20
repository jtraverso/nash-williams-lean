/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

/-!
# Families with a disconnected class graph: exact splitting over components

A *component labelling* of a family `F` on four classes is a map `c : Fin 4 → Fin 4` that is
constant along allowed pairs (`CompLabel F c`). Every type of `F` then lies inside one component
(`TypesInside F c`, a decidable finite fact).

* `InsideE p c k e`: both ends of `e` lie in classes with label `k`; `insideE p c k E` is the part of
  `E` inside component `k`.
* `isIntDiv_insideE`: **integral divisibility splits over components**: if `L` has allowed support
  and is `F`-divisible, then so is each `insideE p c k L`.
* `universalAbsorbers_of_components`: **componentwise universal absorbers give universal
  absorbers.** If for every label `k` and every reserve `X` inside component `k` there is ONE
  absorber `A_k` inside component `k` (fixed before `L`) with `A_k ∪ L` decomposable for every
  divisible `L ⊆ X`, then the union `A = ⋃ₖ A_k` is a universal absorber for every reserve. The
  degree bound is not multiplied: the components are vertex disjoint.
* `universalCert_of_components`: the same statement at the level of `UniversalCert`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral

/-- `c` is constant along the allowed pairs of `F`. -/
def CompLabel (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) : Prop :=
  ∀ i j, (∃ k, Link F i j k) → c i = c j

/-- Every type of `F` lies inside one component. -/
def TypesInside (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) : Prop :=
  ∀ τ ∈ F, ∀ i j, 0 < τ.count i → 0 < τ.count j → c i = c j

section Inside

variable {V : Type*} [DecidableEq V]

/-- Both ends of `e` lie in component `k`. -/
def InsideE (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (e : Sym2 V) : Prop :=
  Sym2.map (fun v => c (p v)) e = s(k, k)

instance (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) : DecidablePred (InsideE p c k) :=
  fun e => by unfold InsideE; infer_instance

/-- The part of `E` inside component `k`. -/
def insideE (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (E : Finset (Sym2 V)) :
    Finset (Sym2 V) :=
  E.filter (InsideE p c k)

theorem insideE_mk (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (a b : V) :
    InsideE p c k s(a, b) ↔ c (p a) = k ∧ c (p b) = k := by
  unfold InsideE
  rw [Sym2.map_mk, Sym2.eq_iff]
  tauto

theorem insideE_subset (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (E : Finset (Sym2 V)) :
    insideE p c k E ⊆ E := filter_subset _ _

theorem mem_insideE {p : V → Fin 4} {c : Fin 4 → Fin 4} {k : Fin 4} {E : Finset (Sym2 V)}
    {e : Sym2 V} : e ∈ insideE p c k E ↔ e ∈ E ∧ InsideE p c k e := mem_filter

theorem insideE_unique {p : V → Fin 4} {c : Fin 4 → Fin 4} {k k' : Fin 4} {e : Sym2 V}
    (h : InsideE p c k e) (h' : InsideE p c k' e) : k = k' := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [insideE_mk] at h h'
    rw [← h.1, h'.1]

/-- An edge set whose edges are monochromatic for the component labelling. -/
def CompMono (p : V → Fin 4) (c : Fin 4 → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  ∀ a b, s(a, b) ∈ E → c (p a) = c (p b)

theorem insideE_of_mono {p : V → Fin 4} {c : Fin 4 → Fin 4} {E : Finset (Sym2 V)}
    (h : CompMono p c E) {a b : V} (hab : s(a, b) ∈ E) : InsideE p c (c (p a)) s(a, b) :=
  (insideE_mk p c _ a b).mpr ⟨rfl, (h a b hab).symm⟩

theorem exists_inside {p : V → Fin 4} {c : Fin 4 → Fin 4} {E : Finset (Sym2 V)}
    (h : CompMono p c E) {e : Sym2 V} (he : e ∈ E) : ∃ k, InsideE p c k e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨_, insideE_of_mono h he⟩

/-- A monochromatic edge set is the union of its parts inside the components. -/
theorem biUnion_insideE {p : V → Fin 4} {c : Fin 4 → Fin 4} {E : Finset (Sym2 V)}
    (h : CompMono p c E) : (univ : Finset (Fin 4)).biUnion (fun k => insideE p c k E) = E := by
  ext e
  simp only [mem_biUnion, mem_univ, true_and, mem_insideE]
  constructor
  · rintro ⟨k, he, -⟩; exact he
  · intro he
    obtain ⟨k, hk⟩ := exists_inside h he
    exact ⟨k, he, hk⟩

theorem insideE_pairwiseDisjoint (p : V → Fin 4) (c : Fin 4 → Fin 4) (E : Fin 4 → Finset (Sym2 V))
    (hE : ∀ k, ∀ e ∈ E k, InsideE p c k e) :
    ((univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint E := by
  intro k _ k' _ hkk'
  rw [Function.onFun, disjoint_left]
  intro e he he'
  exact hkk' (insideE_unique (hE k e he) (hE k' e he'))

end Inside

section Split

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairVec_inside (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (a b : V)
    (hab : c (p a) = c (p b)) (i j : Fin 4) :
    (if InsideE p c k s(a, b) then pairVec p s(a, b) i j else 0) =
      if c i = k ∧ c j = k then pairVec p s(a, b) i j else 0 := by
  simp only [insideE_mk, pairVec, Sym2.lift_mk]
  by_cases h1 : p a = i ∧ p b = j
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases hk : c (p a) = k
    · simp [hk, ← hab]
    · simp [hk]
  · by_cases h2 : p b = i ∧ p a = j
    · obtain ⟨rfl, rfl⟩ := h2
      by_cases hk : c (p a) = k
      · simp [hk, ← hab]
      · simp [hk, hab]
    · simp [h1, h2]

theorem edgeVec_insideE (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (E : Finset (Sym2 V))
    (hE : CompMono p c E) (i j : Fin 4) :
    edgeVec p (insideE p c k E) i j = if c i = k ∧ c j = k then edgeVec p E i j else 0 := by
  unfold edgeVec insideE
  simp only [Finset.sum_apply]
  rw [sum_filter]
  have hpt : ∀ e ∈ E, (if InsideE p c k e then pairVec p e i j else 0) =
      if c i = k ∧ c j = k then pairVec p e i j else 0 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact pairVec_inside p c k a b (hE a b he) i j
  rw [sum_congr rfl hpt]
  split_ifs <;> simp

theorem degContrib_inside (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (v a b : V)
    (hab : c (p a) = c (p b)) (j : Fin 4) :
    (if InsideE p c k s(a, b) then degContrib p v s(a, b) j else 0) =
      if c (p v) = k then degContrib p v s(a, b) j else 0 := by
  simp only [insideE_mk, degContrib, Sym2.lift_mk]
  by_cases h1 : a = v
  · subst h1
    by_cases hk : c (p a) = k
    · simp [hk, ← hab]
    · simp [hk]
  · by_cases h2 : b = v
    · subst h2
      by_cases hk : c (p b) = k
      · simp [hk, hab]
      · simp [hk, hab]
    · simp [h1, h2]

theorem degVec_insideE (p : V → Fin 4) (c : Fin 4 → Fin 4) (k : Fin 4) (E : Finset (Sym2 V))
    (hE : CompMono p c E) (v : V) (j : Fin 4) :
    degVec p (insideE p c k E) v j = if c (p v) = k then degVec p E v j else 0 := by
  unfold degVec insideE
  simp only [Finset.sum_apply]
  rw [sum_filter]
  have hpt : ∀ e ∈ E, (if InsideE p c k e then degContrib p v e j else 0) =
      if c (p v) = k then degContrib p v e j else 0 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact degContrib_inside p c k v a b (hE a b he) j
  rw [sum_congr rfl hpt]
  split_ifs <;> simp

theorem typeEdgeVec_eq_zero_left {τ : Multiset (Fin 4)} {i j : Fin 4} (hi : τ.count i = 0) :
    typeEdgeVec τ i j = 0 := by
  unfold typeEdgeVec; simp [hi]

theorem typeEdgeVec_eq_zero_right {τ : Multiset (Fin 4)} {i j : Fin 4} (hj : τ.count j = 0) :
    typeEdgeVec τ i j = 0 := by
  unfold typeEdgeVec
  by_cases hij : i = j
  · subst hij; simp [hj]
  · simp [hj, hij]

/-- The coefficients of the types inside component `k`. -/
noncomputable def restrictCoeff (c : Fin 4 → Fin 4) (k : Fin 4) (w : Multiset (Fin 4) → ℤ)
    (τ : Multiset (Fin 4)) : ℤ :=
  open Classical in if ∀ i, 0 < τ.count i → c i = k then w τ else 0

/-- **Integral divisibility splits over the components.** -/
theorem isIntDiv_insideE {F : Finset (Multiset (Fin 4))} {c : Fin 4 → Fin 4}
    (hτ : TypesInside F c) (p : V → Fin 4) (k : Fin 4) {L : Finset (Sym2 V)}
    (hL : CompMono p c L) (h : IsIntDiv p F L) : IsIntDiv p F (insideE p c k L) := by
  classical
  obtain ⟨⟨w, hw⟩, hdeg⟩ := h
  refine ⟨⟨restrictCoeff c k w, ?_⟩, fun v => ?_⟩
  · funext i j
    rw [edgeVec_insideE p c k L hL i j]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hw' := congrFun (congrFun hw i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw'
    have hpt : ∀ τ ∈ F, restrictCoeff c k w τ * typeEdgeVec τ i j =
        if c i = k ∧ c j = k then w τ * typeEdgeVec τ i j else 0 := by
      intro τ hτF
      by_cases hi : τ.count i = 0
      · simp [typeEdgeVec_eq_zero_left hi]
      by_cases hj : τ.count j = 0
      · simp [typeEdgeVec_eq_zero_right hj]
      have hi' : 0 < τ.count i := Nat.pos_of_ne_zero hi
      have hj' : 0 < τ.count j := Nat.pos_of_ne_zero hj
      have hall : ∀ l, 0 < τ.count l → c l = c i := fun l hl => hτ τ hτF l i hl hi'
      have hcij : c j = c i := hall j hj'
      unfold restrictCoeff
      by_cases hk : c i = k
      · have : ∀ l, 0 < τ.count l → c l = k := fun l hl => (hall l hl).trans hk
        rw [if_pos this, if_pos ⟨hk, hcij.trans hk⟩]
      · have : ¬ ∀ l, 0 < τ.count l → c l = k := fun hh => hk (hh i hi')
        rw [if_neg this, if_neg (fun h => hk h.1), zero_mul]
    rw [sum_congr rfl hpt]
    split_ifs with hk
    · exact hw'
    · simp
  · by_cases hk : c (p v) = k
    · obtain ⟨wv, hwv⟩ := hdeg v
      refine ⟨wv, ?_⟩
      funext j
      rw [degVec_insideE p c k L hL v j, if_pos hk]
      exact congrFun hwv j
    · refine ⟨0, ?_⟩
      funext j
      rw [degVec_insideE p c k L hL v j, if_neg hk]
      simp

end Split

section Union

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Componentwise universal absorbers give universal absorbers.** -/
theorem universalAbsorbers_of_components (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4)
    (hc : CompLabel F c) (hτ : TypesInside F c)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) (ρ δ : ℝ)
    (hk : ∀ k : Fin 4, ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
      DegBounded X (2 * ρ * Fintype.card V) → (∀ e ∈ X, InsideE p c k e) →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, InsideE p c k e) ∧
        HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)) :
    UniversalAbsorbers p F G ρ δ := by
  classical
  intro X hXG hX
  have hmonoG : ∀ E ⊆ G.edgeFinset, CompMono p c E := fun E hE a b hab =>
    hc _ _ (hG a b (SimpleGraph.mem_edgeFinset.mp (hE hab)))
  have hXk : ∀ k, insideE p c k X ⊆ G.edgeFinset := fun k => (insideE_subset p c k X).trans hXG
  have hXkdeg : ∀ k, DegBounded (insideE p c k X) (2 * ρ * Fintype.card V) := by
    intro k v
    exact le_trans (by exact_mod_cast card_le_card (filter_subset_filter _
      (insideE_subset p c k X))) (hX v)
  choose A hAG hAX hAin hAdec hAdeg hAL using fun k =>
    hk k (insideE p c k X) (hXk k) (hXkdeg k) (fun e he => (mem_insideE.mp he).2)
  have hdisA := insideE_pairwiseDisjoint p c A hAin
  refine ⟨univ.biUnion A, biUnion_subset.mpr fun k _ => hAG k, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_biUnion_left]
    intro k _
    rw [disjoint_left]
    intro e heA heX
    exact disjoint_left.mp (hAX k) heA (mem_insideE.mpr ⟨heX, hAin k e heA⟩)
  · exact RefinerAssembly.hasDecomp_biUnion univ A (fun k _ => hAdec k) hdisA
  · intro v
    have hsub : (univ.biUnion A).filter (fun e => v ∈ e) ⊆
        (A (c (p v))).filter (fun e => v ∈ e) := by
      intro e he
      obtain ⟨he, hv⟩ := mem_filter.mp he
      obtain ⟨k, -, hek⟩ := mem_biUnion.mp he
      refine mem_filter.mpr ⟨?_, hv⟩
      have hin := hAin k e hek
      induction e using Sym2.ind with
      | _ a b =>
        have hk' := (insideE_mk p c k a b).mp hin
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · rw [hk'.1]; exact hek
        · rw [hk'.2]; exact hek
    exact le_trans (by exact_mod_cast card_le_card hsub) (hAdeg (c (p v)) v)
  · intro L hLX hL
    have hLmono := hmonoG L (hLX.trans hXG)
    have hU : univ.biUnion A ∪ L = univ.biUnion (fun k => A k ∪ insideE p c k L) := by
      rw [biUnion_union, biUnion_insideE hLmono]
    rw [hU]
    refine RefinerAssembly.hasDecomp_biUnion univ _ (fun k _ => ?_) ?_
    · exact hAL k _ (fun e he => mem_insideE.mpr ⟨hLX (mem_insideE.mp he).1,
        (mem_insideE.mp he).2⟩) (isIntDiv_insideE hτ p k hLmono hL)
    · apply insideE_pairwiseDisjoint
      intro k e he
      rcases mem_union.mp he with he | he
      · exact hAin k e he
      · exact (mem_insideE.mp he).2

/-- A componentwise universal certificate: universal absorbers inside component `k`, at the
padded scales and in the hosts of `UniversalCert`. -/
def ComponentUniversalCert (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) (k : Fin 4) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ),
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    0 < ω → ω ≤ 1 → 1 ≤ paddedRho ω * Fintype.card V →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
      DegBounded X (2 * paddedRho ω * Fintype.card V) → (∀ e ∈ X, InsideE p c k e) →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, InsideE p c k e) ∧
        HasDecomp p F A ∧ DegBounded A (2 * paddedAbsDelta ω * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)

/-- **A componentwise certificate gives the universal certificate.** -/
theorem universalCert_of_components (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4)
    (hc : CompLabel F c) (hτ : TypesInside F c) (hk : ∀ k, ComponentUniversalCert F c k) :
    UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  exact universalAbsorbers_of_components F c hc hτ p G hG _ _
    (fun k => hk k V p G ω hG hs hω hω1 hn)

theorem hasDecomp_empty_set (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) :
    HasDecomp p F (∅ : Finset (Sym2 V)) := by
  simpa using RefinerAssembly.hasDecomp_biUnion (p := p) (F := F) (∅ : Finset (Fin 1))
    (fun _ => (∅ : Finset (Sym2 V))) (by simp) (by simp)

/-- An empty component (no class carries the label `k`) has the trivial certificate. -/
theorem componentUniversalCert_empty (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4)
    (k : Fin 4) (hk : ∀ i, c i ≠ k) : ComponentUniversalCert F c k := by
  intro V _ _ p G _ ω _ _ hω _ _ X _ _ hXin
  have hX : X = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro e he
    have h := hXin e he
    induction e using Sym2.ind with
    | _ a b => exact hk _ ((insideE_mk p c k a b).mp h).1
  subst hX
  refine ⟨∅, empty_subset _, disjoint_empty_left _, by simp, hasDecomp_empty_set p F, ?_, ?_⟩
  · intro v
    simp only [filter_empty, card_empty, Nat.cast_zero]
    have h1 : 0 ≤ paddedAbsDelta ω := by
      unfold paddedAbsDelta paddedKappa; positivity
    positivity
  · intro L hL _
    rw [subset_empty.mp hL, empty_union]
    exact hasDecomp_empty_set p F

end Union

end PaddedComponents

#print axioms PaddedComponents.isIntDiv_insideE
#print axioms PaddedComponents.universalAbsorbers_of_components
#print axioms PaddedComponents.universalCert_of_components
#print axioms PaddedComponents.componentUniversalCert_empty
