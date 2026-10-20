/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UnifiedAbsorber
public import PartitionedTriangleAbsorption.BlowupB.Family001

/-! # BlowupB.Splitting — absorbers for unions of families with disjoint pair sets

* `NearlyAbsorbing F`: the conclusion of `terminal_absorber_covered` (terminal absorbers of
  bounded sets in nearly complete `F`-blowups, avoiding a sparse forbidden set `B`).
* `nearlyAbsorbing_of_terminalShape`: terminal absorbers on few fresh vertices (the shape of
  `linear_terminal_absorber`, `phased_terminal_absorber`) give `NearlyAbsorbing`; e.g.
  `nearlyAbsorbing_001`.
* `isIntDiv_split`: if no class pair is allowed by both `F₁` and `F₂`, integral
  `F₁ ∪ F₂`-divisibility of `L` implies integral `F₁`-divisibility of the `F₁`-edges of `L`.
* **`nearlyAbsorbing_union`**: `NearlyAbsorbing` is closed under unions of families with disjoint
  allowed pairs. The absorber is the union of the absorbers of the two edge classes.

Examples: `{000, 001, 111}` (where same-class-sequence targets fail, see the census) and
`{001, 111}` (neither linear nor `ThreeStepLinks`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer

variable {t : ℕ}

/-- Nearly-complete terminal absorbers (the conclusion of `terminal_absorber_covered`). -/
def NearlyAbsorbing (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ (K : ℕ) (gamma eta : ℝ), 0 < gamma → 0 < eta →
    ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V →
      (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
      (d : ℝ) ≤ δ * Fintype.card V →
      (∀ i, gamma * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
      ∀ B X : Finset (Sym2 V), DegBounded B (δ * Fintype.card V) →
        X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
        ∃ C ⊆ G.edgeFinset, Disjoint C (B ∪ X) ∧ HasDecomp p F C ∧
          DegBounded C (eta * Fintype.card V) ∧
          ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (C ∪ L)

theorem nearlyAbsorbing_covered (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hcov : IsLinearFam F ∨ ThreeStepLinks F) :
    NearlyAbsorbing F :=
  fun K gamma eta hg he => terminal_absorber_covered F hcard hcov K gamma eta hg he

/-- Terminal absorbers on few fresh vertices. -/
def TerminalShape (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {p : V → Fin t} {G : SimpleGraph V}
    [DecidableRel G.Adj] {d K : ℕ}, (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) →
    (∀ v, missDeg p F G v ≤ d) →
    ∀ (X : Finset (Sym2 V)) (Z : Finset V), X ⊆ G.edgeFinset → X.card ≤ K →
    (∀ c, Z.card + 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) →
    ∃ A ⊆ G.edgeFinset, Disjoint A X ∧ HasDecomp p F A ∧
      (∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)) ∧
      ∃ U : Finset V, U.card ≤ 4 * K * 2 ^ K ∧ Disjoint U (Z ∪ vertsOf X) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf X ∨ v ∈ U

theorem terminalShape_001 : TerminalShape F001 :=
  fun hsub hmiss X Z hXG hK hcls => terminal_absorber_001 hsub hmiss X Z hXG hK hcls

/-- **Fresh-vertex terminal absorbers give nearly-complete absorbers avoiding `B`.** -/
theorem nearlyAbsorbing_of_terminalShape {F : Finset (Multiset (Fin t))} (hT : TerminalShape F) :
    NearlyAbsorbing F := by
  intro K gamma eta hg he
  set M : ℕ := 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) with hM
  set δ : ℝ := gamma / (8 * (4 * K + 2)) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨max (⌈4 * (M : ℝ) / gamma⌉₊ + 1) (⌈(2 * K + 4 * K * 2 ^ K : ℝ) / eta⌉₊ + 1), δ,
    hδpos, ?_⟩
  intro V _ _ G _ p d hN hsub hmiss hd hcls B X hB hXG hXB hK
  set n : ℕ := Fintype.card V with hn
  have hn1 : 4 * (M : ℝ) / gamma < n := by
    have := (le_max_left _ _).trans hN
    have h2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast h2)
  have hn2 : (2 * K + 4 * K * 2 ^ K : ℝ) / eta < n := by
    have := (le_max_right _ _).trans hN
    have h2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast h2)
  set d' : ℕ := d + ⌊δ * n⌋₊ with hd'
  have hmiss' : ∀ v, missDeg p F (delEdges G B) v ≤ d' := by
    intro v
    have h1 := missDeg_delEdges_le p F G B v
    have h2 : (B.filter fun e => v ∈ e).card ≤ ⌊δ * n⌋₊ := Nat.le_floor (hB v)
    have := hmiss v
    omega
  have hsub' : ∀ u v, (delEdges G B).Adj u v → AllowedPair F (p u) (p v) :=
    fun u v h => hsub u v h.1
  have hXG' : X ⊆ (delEdges G B).edgeFinset := by
    intro e heX
    have heG := hXG heX
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset] at heG ⊢
      exact ⟨heG, fun h => disjoint_left.mp hXB heX h⟩
  have hclsN : ∀ c, (∅ : Finset V).card + 4 * K * 2 ^ K + 2 * K + 6 * K +
      (4 * K + 2) * (d' + 1) < (univ.filter fun v => p v = c).card := by
    intro c
    have hc := hcls c
    have hfl : (⌊δ * n⌋₊ : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
    have hd'R : ((d' : ℕ) : ℝ) ≤ 2 * (δ * n) := by
      rw [hd']; push_cast; linarith
    have h4 : ((4 * K + 2 : ℕ) : ℝ) * ((d' : ℝ) + 1) ≤ gamma * n / 4 + (4 * K + 2) := by
      have h6 : (0 : ℝ) ≤ ((4 * K + 2 : ℕ) : ℝ) := by positivity
      have h7 := mul_le_mul_of_nonneg_left (show (d' : ℝ) + 1 ≤ 2 * (δ * n) + 1 by linarith) h6
      have h5 : ((4 * K + 2 : ℕ) : ℝ) * (2 * (δ * n) + 1) = gamma * n / 4 + (4 * K + 2) := by
        rw [hδ]; push_cast; field_simp; ring
      linarith
    have hMR : (M : ℝ) * 4 < gamma * n := by
      rw [div_lt_iff₀ hg] at hn1; linarith
    have key : ((∅ : Finset V).card + 4 * K * 2 ^ K + 2 * K + 6 * K +
        (4 * K + 2) * (d' + 1) : ℕ) < (gamma * n : ℝ) := by
      push_cast
      simp only [card_empty, Nat.cast_zero, zero_add]
      have hM' : (M : ℝ) = 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) := by
        rw [hM]; push_cast; ring
      push_cast at h4
      nlinarith
    exact_mod_cast key.trans_le hc
  obtain ⟨A, hAG', hAX, hAdec, hAall, U, hUc, _, hAv⟩ := hT hsub' hmiss' X ∅ hXG' hK hclsN
  refine ⟨A, hAG'.trans (delEdges_edgeFinset_sub G B), ?_, hAdec, ?_, hAall⟩
  · rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left hAG' (disjoint_delEdges G B), hAX⟩
  · intro v
    have h1 := card_filter_mem_le_of_verts (W := vertsOf X ∪ U)
      (fun e he w hw => (hAv e he w hw).elim (mem_union_left _) (mem_union_right _)) v
    have h2 := card_union_le (vertsOf X) U
    have h3 : (vertsOf X).card ≤ 2 * K := card_vertsOf_le.trans (by omega)
    have h4 : ((A.filter fun e => v ∈ e).card : ℝ) ≤ 2 * K + 4 * K * 2 ^ K := by
      exact_mod_cast (h1.trans h2).trans (by omega)
    rw [div_lt_iff₀ he] at hn2
    linarith

theorem nearlyAbsorbing_001 : NearlyAbsorbing F001 :=
  nearlyAbsorbing_of_terminalShape terminalShape_001

/-! ### Edges allowed by a family -/

section Allowed

variable {V : Type*} [Fintype V] [DecidableEq V] (F : Finset (Multiset (Fin t))) (p : V → Fin t)

/-- The edge `e` joins two classes allowed by `F`. -/
def aE (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => AllowedPair F (p u) (p v),
    fun _ _ => propext ⟨AllowedPair.symm, AllowedPair.symm⟩⟩ e

variable {F p}

theorem aE_mk {u v : V} : aE F p s(u, v) ↔ AllowedPair F (p u) (p v) := Iff.rfl

theorem AllowedPair.mono' {F F' : Finset (Multiset (Fin t))} {a b : Fin t}
    (h : AllowedPair F a b) (hs : F ⊆ F') : AllowedPair F' a b := by
  obtain ⟨τ, hτ, hc, hle⟩ := h
  exact ⟨τ, hs hτ, hc, hle⟩

theorem pairVec_cases {e : Sym2 V} {i j : Fin t} (h : pairVec p e i j ≠ 0) :
    ∃ u v, e = s(u, v) ∧ p u = i ∧ p v = j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk] at h
    by_cases h1 : p a = i ∧ p b = j
    · exact ⟨a, b, rfl, h1⟩
    · by_cases h2 : p b = i ∧ p a = j
      · exact ⟨b, a, Sym2.eq_swap, h2⟩
      · simp [h1, h2] at h

theorem degContrib_cases {v : V} {e : Sym2 V} {j : Fin t} (h : degContrib p v e j ≠ 0) :
    ∃ u, e = s(v, u) ∧ p u = j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk] at h
    by_cases h1 : a = v ∧ p b = j
    · exact ⟨b, by rw [h1.1], h1.2⟩
    · by_cases h2 : b = v ∧ p a = j
      · exact ⟨a, by rw [h2.1, Sym2.eq_swap], h2.2⟩
      · simp [h1, h2] at h

end Allowed

section TypeVec

variable {τ : Multiset (Fin t)} {a i j : Fin t}

theorem pair_le_of_count {τ : Multiset (Fin t)} {i j : Fin t} (hij : i ≠ j) (hi : i ∈ τ)
    (hj : j ∈ τ) : ({i, j} : Multiset (Fin t)) ≤ τ := by
  rw [Multiset.insert_eq_cons, Multiset.le_iff_subset (Multiset.nodup_cons.mpr ⟨by simpa using hij,
    Multiset.nodup_singleton _⟩)]
  intro x hx
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hi
  · exact hj

theorem pair_le_of_two {τ : Multiset (Fin t)} {i : Fin t} (h : 2 ≤ τ.count i) :
    ({i, i} : Multiset (Fin t)) ≤ τ := by
  have e : ({i, i} : Multiset (Fin t)) = Multiset.replicate 2 i := by
    rw [Multiset.replicate_succ, Multiset.replicate_one]; rfl
  rw [e]
  exact Multiset.le_count_iff_replicate_le.mp h

theorem le_of_typeEdgeVec_ne (h : typeEdgeVec τ i j ≠ 0) : ({i, j} : Multiset (Fin t)) ≤ τ := by
  unfold typeEdgeVec at h
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl] at h
    apply pair_le_of_two
    have h0 : (τ.count i : ℤ) ≠ 0 := by intro h0; rw [h0] at h; simp at h
    have h1 : (τ.count i : ℤ) ≠ 1 := by intro h1; rw [h1] at h; simp at h
    omega
  · rw [if_neg hij, sub_zero] at h
    have h1 : (τ.count i : ℤ) ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have h2 : (τ.count j : ℤ) ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    exact pair_le_of_count hij (Multiset.count_ne_zero.mp (by exact_mod_cast h1))
      (Multiset.count_ne_zero.mp (by exact_mod_cast h2))

theorem le_of_typeDegVec_ne (ha : a ∈ τ) (h : typeDegVec τ a j ≠ 0) :
    ({a, j} : Multiset (Fin t)) ≤ τ := by
  unfold typeDegVec at h
  by_cases hja : j = a
  · subst hja
    rw [if_pos rfl] at h
    apply pair_le_of_two
    have h1 : 1 ≤ τ.count j := Multiset.one_le_count_iff_mem.mpr ha
    have h2 : (τ.count j : ℤ) ≠ 1 := fun h1' => h (by rw [h1']; norm_num)
    omega
  · rw [if_neg hja, sub_zero] at h
    exact pair_le_of_count (Ne.symm hja) ha
      (Multiset.count_ne_zero.mp (by exact_mod_cast h))

end TypeVec

/-- **Splitting divisibility.** -/
theorem isIntDiv_split {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F₁ F₂ : Finset (Multiset (Fin t))} (hcard : ∀ τ ∈ F₁ ∪ F₂, Multiset.card τ = 3)
    (hdisj : ∀ a b, AllowedPair F₁ a b → ¬ AllowedPair F₂ a b) {L : Finset (Sym2 V)}
    [DecidablePred (aE F₁ p)] (hdiv : IsIntDiv p (F₁ ∪ F₂) L) :
    IsIntDiv p F₁ (L.filter (aE F₁ p)) := by
  have hev : ∀ (E : Finset (Sym2 V)) i j, edgeVec p E i j = ∑ e ∈ E, pairVec p e i j := by
    intro E i j; simp only [edgeVec, Finset.sum_apply]
  have hcv : ∀ (S : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) i j,
      (∑ τ ∈ S, c τ • typeEdgeVec τ) i j = ∑ τ ∈ S, c τ * typeEdgeVec τ i j := by
    intro S c i j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hdv : ∀ (E : Finset (Sym2 V)) v j, degVec p E v j = ∑ e ∈ E, degContrib p v e j := by
    intro E v j; simp only [degVec, Finset.sum_apply]
  have hcd : ∀ (S : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) (a j : Fin t),
      (∑ τ ∈ S, c τ • typeDegVec τ a) j = ∑ τ ∈ S, c τ * typeDegVec τ a j := by
    intro S c a j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc1 : ∀ τ ∈ F₁, Multiset.card τ = 3 := fun τ h => hcard τ (mem_union_left _ h)
  have hc2 : ∀ τ ∈ F₂, Multiset.card τ = 3 := fun τ h => hcard τ (mem_union_right _ h)
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := hdiv.1
    refine ⟨c, ?_⟩
    funext i j
    rw [hev, hcv]
    by_cases hA : AllowedPair F₁ i j
    · calc ∑ e ∈ L.filter (aE F₁ p), pairVec p e i j = ∑ e ∈ L, pairVec p e i j := by
            refine sum_subset (filter_subset _ _) fun e he hne => ?_
            by_contra h
            obtain ⟨u, v, rfl, hu, hv⟩ := pairVec_cases h
            exact hne (mem_filter.mpr ⟨he, by rw [aE_mk, hu, hv]; exact hA⟩)
        _ = ∑ τ ∈ F₁ ∪ F₂, c τ * typeEdgeVec τ i j := by rw [← hev, hc, hcv]
        _ = ∑ τ ∈ F₁, c τ * typeEdgeVec τ i j := by
            refine (sum_subset subset_union_left fun τ hτ hτ1 => ?_).symm
            have hτ2 : τ ∈ F₂ := (mem_union.mp hτ).resolve_left hτ1
            by_contra h
            have h' : typeEdgeVec τ i j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
            exact hdisj i j hA ⟨τ, hτ2, hc2 τ hτ2, le_of_typeEdgeVec_ne h'⟩
    · rw [sum_eq_zero, sum_eq_zero]
      · intro τ hτ
        by_contra h
        have h' : typeEdgeVec τ i j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
        exact hA ⟨τ, hτ, hc1 τ hτ, le_of_typeEdgeVec_ne h'⟩
      · intro e he
        by_contra h
        obtain ⟨u, v, rfl, hu, hv⟩ := pairVec_cases h
        have := (mem_filter.mp he).2
        rw [aE_mk, hu, hv] at this
        exact hA this
  · intro v
    obtain ⟨c, hc⟩ := hdiv.2 v
    refine ⟨c, ?_⟩
    funext j
    rw [hdv, hcd]
    by_cases hA : AllowedPair F₁ (p v) j
    · calc ∑ e ∈ L.filter (aE F₁ p), degContrib p v e j = ∑ e ∈ L, degContrib p v e j := by
            refine sum_subset (filter_subset _ _) fun e he hne => ?_
            by_contra h
            obtain ⟨u, rfl, hu⟩ := degContrib_cases h
            exact hne (mem_filter.mpr ⟨he, by rw [aE_mk, hu]; exact hA⟩)
        _ = ∑ τ ∈ (F₁ ∪ F₂).filter (fun τ => p v ∈ τ), c τ * typeDegVec τ (p v) j := by
            rw [← hdv, hc, hcd]
        _ = ∑ τ ∈ F₁.filter (fun τ => p v ∈ τ), c τ * typeDegVec τ (p v) j := by
            refine (sum_subset (filter_subset_filter _ subset_union_left) fun τ hτ hτ1 => ?_).symm
            obtain ⟨hτU, hvτ⟩ := mem_filter.mp hτ
            have hτ2 : τ ∈ F₂ := (mem_union.mp hτU).resolve_left
              (fun h => hτ1 (mem_filter.mpr ⟨h, hvτ⟩))
            by_contra h
            have h' : typeDegVec τ (p v) j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
            exact hdisj _ j hA ⟨τ, hτ2, hc2 τ hτ2, le_of_typeDegVec_ne hvτ h'⟩
    · rw [sum_eq_zero, sum_eq_zero]
      · intro τ hτ
        obtain ⟨hτ1, hvτ⟩ := mem_filter.mp hτ
        by_contra h
        have h' : typeDegVec τ (p v) j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
        exact hA ⟨τ, hτ1, hc1 τ hτ1, le_of_typeDegVec_ne hvτ h'⟩
      · intro e he
        by_contra h
        obtain ⟨u, rfl, hu⟩ := degContrib_cases h
        have := (mem_filter.mp he).2
        rw [aE_mk, hu] at this
        exact hA this

/-! ### Restriction of the host to the pairs of a subfamily -/

section Restrict

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` restricted to the pairs allowed by `F`. -/
def restrictF (G : SimpleGraph V) (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ AllowedPair F (p u) (p v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem mem_restrictF {G : SimpleGraph V} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    [DecidableRel G.Adj] [DecidableRel (restrictF G p F).Adj] {e : Sym2 V} :
    e ∈ (restrictF G p F).edgeFinset ↔ e ∈ G.edgeFinset ∧ aE F p e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, aE_mk]
    rfl

end Restrict

/-- **Unions of families with disjoint allowed pairs.** -/
theorem nearlyAbsorbing_union {F₁ F₂ : Finset (Multiset (Fin t))}
    (hcard : ∀ τ ∈ F₁ ∪ F₂, Multiset.card τ = 3)
    (hdisj : ∀ a b, AllowedPair F₁ a b → ¬ AllowedPair F₂ a b)
    (h₁ : NearlyAbsorbing F₁) (h₂ : NearlyAbsorbing F₂) : NearlyAbsorbing (F₁ ∪ F₂) := by
  intro K gamma eta hg he
  obtain ⟨N₁, δ₁, hδ₁, H₁⟩ := h₁ K gamma (eta / 2) hg (by positivity)
  obtain ⟨N₂, δ₂, hδ₂, H₂⟩ := h₂ K gamma (eta / 2) hg (by positivity)
  refine ⟨max N₁ N₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro V _ _ G _ p d hN hsub hmiss hd hcls B X hB hXG hXB hK
  classical
  set n := Fintype.card V with hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hdisj' : ∀ a b, AllowedPair F₂ a b → ¬ AllowedPair F₁ a b :=
    fun a b h h' => hdisj a b h' h
  have hcard' : ∀ τ ∈ F₂ ∪ F₁, Multiset.card τ = 3 := by rw [union_comm]; exact hcard
  -- edges of `G` are allowed by one of the two families, not by both
  have hsplit : ∀ e ∈ G.edgeFinset, aE F₁ p e ∨ aE F₂ p e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨τ, hτ, hc, hle⟩ := hsub u v (SimpleGraph.mem_edgeFinset.mp he)
      rcases mem_union.mp hτ with h | h
      · exact Or.inl ⟨τ, h, hc, hle⟩
      · exact Or.inr ⟨τ, h, hc, hle⟩
  have hnot : ∀ e, aE F₁ p e → aE F₂ p e → False := by
    intro e h1 h2
    induction e using Sym2.ind with
    | _ u v => exact hdisj _ _ h1 h2
  have hmissk : ∀ Fk : Finset (Multiset (Fin t)), Fk ⊆ F₁ ∪ F₂ →
      ∀ v, missDeg p Fk (restrictF G p Fk) v ≤ d := by
    intro Fk hk v
    refine le_trans (card_le_card fun r hr => ?_) (hmiss v)
    simp only [missSet, mem_filter, mem_univ, true_and] at hr ⊢
    obtain ⟨h1, h2, h3⟩ := hr
    exact ⟨h1, h2.mono' hk, fun h => h3 ⟨h, h2⟩⟩
  have hdk : ∀ δk : ℝ, min δ₁ δ₂ ≤ δk → (d : ℝ) ≤ δk * n :=
    fun δk h => hd.trans (mul_le_mul_of_nonneg_right h hn0)
  have hBk : ∀ δk : ℝ, min δ₁ δ₂ ≤ δk → DegBounded B (δk * n) :=
    fun δk h => DegBounded.mono' hB (mul_le_mul_of_nonneg_right h hn0)
  set X₁ := X.filter (aE F₁ p) with hX₁
  set X₂ := X.filter (aE F₂ p) with hX₂
  have hX₁G : X₁ ⊆ (restrictF G p F₁).edgeFinset := fun e he =>
    mem_restrictF.mpr ⟨hXG (mem_filter.mp he).1, (mem_filter.mp he).2⟩
  have hX₂G : X₂ ⊆ (restrictF G p F₂).edgeFinset := fun e he =>
    mem_restrictF.mpr ⟨hXG (mem_filter.mp he).1, (mem_filter.mp he).2⟩
  obtain ⟨C₁, hC₁G, hC₁d, hC₁dec, hC₁deg, hC₁L⟩ := H₁ (restrictF G p F₁) p d
    ((le_max_left _ _).trans hN) (fun u v h => h.2) (hmissk F₁ subset_union_left)
    (hdk δ₁ (min_le_left _ _)) hcls B X₁ (hBk δ₁ (min_le_left _ _)) hX₁G
    (disjoint_of_subset_left (filter_subset _ _) hXB) ((card_filter_le _ _).trans hK)
  obtain ⟨C₂, hC₂G, hC₂d, hC₂dec, hC₂deg, hC₂L⟩ := H₂ (restrictF G p F₂) p d
    ((le_max_right _ _).trans hN) (fun u v h => h.2) (hmissk F₂ subset_union_right)
    (hdk δ₂ (min_le_right _ _)) hcls B X₂ (hBk δ₂ (min_le_right _ _)) hX₂G
    (disjoint_of_subset_left (filter_subset _ _) hXB) ((card_filter_le _ _).trans hK)
  have hC₁a : ∀ e ∈ C₁, e ∈ G.edgeFinset ∧ aE F₁ p e := fun e he => mem_restrictF.mp (hC₁G he)
  have hC₂a : ∀ e ∈ C₂, e ∈ G.edgeFinset ∧ aE F₂ p e := fun e he => mem_restrictF.mp (hC₂G he)
  have hmono₁ : ∀ E : Finset (Sym2 V), HasDecomp p F₁ E → HasDecomp p (F₁ ∪ F₂) E := by
    rintro E ⟨D, hT, hP, hU⟩
    exact ⟨D, fun s hs => ⟨(hT s hs).1, mem_union_left _ (hT s hs).2⟩, hP, hU⟩
  have hmono₂ : ∀ E : Finset (Sym2 V), HasDecomp p F₂ E → HasDecomp p (F₁ ∪ F₂) E := by
    rintro E ⟨D, hT, hP, hU⟩
    exact ⟨D, fun s hs => ⟨(hT s hs).1, mem_union_right _ (hT s hs).2⟩, hP, hU⟩
  have hsep : ∀ E₁ E₂ : Finset (Sym2 V), (∀ e ∈ E₁, aE F₁ p e) → (∀ e ∈ E₂, aE F₂ p e) →
      Disjoint E₁ E₂ := fun E₁ E₂ h1 h2 =>
    disjoint_left.mpr fun e he1 he2 => hnot e (h1 e he1) (h2 e he2)
  refine ⟨C₁ ∪ C₂, union_subset (fun e he => (hC₁a e he).1) (fun e he => (hC₂a e he).1),
    ?_, ?_, ?_, ?_⟩
  · rw [disjoint_union_left]
    constructor
    · rw [disjoint_left]
      intro e he heBX
      rcases mem_union.mp heBX with h | h
      · exact disjoint_left.mp hC₁d he (mem_union_left _ h)
      · exact disjoint_left.mp hC₁d he (mem_union_right _ (mem_filter.mpr ⟨h, (hC₁a e he).2⟩))
    · rw [disjoint_left]
      intro e he heBX
      rcases mem_union.mp heBX with h | h
      · exact disjoint_left.mp hC₂d he (mem_union_left _ h)
      · exact disjoint_left.mp hC₂d he (mem_union_right _ (mem_filter.mpr ⟨h, (hC₂a e he).2⟩))
  · exact hasDecomp_union (hmono₁ _ hC₁dec) (hmono₂ _ hC₂dec)
      (hsep _ _ (fun e he => (hC₁a e he).2) (fun e he => (hC₂a e he).2))
  · intro v
    rw [filter_union]
    have h1 := hC₁deg v
    have h2 := hC₂deg v
    have h3 := card_union_le (C₁.filter fun e => v ∈ e) (C₂.filter fun e => v ∈ e)
    have h3' : (((C₁.filter fun e => v ∈ e) ∪ (C₂.filter fun e => v ∈ e)).card : ℝ) ≤
        ((C₁.filter fun e => v ∈ e).card : ℝ) + ((C₂.filter fun e => v ∈ e).card : ℝ) := by
      exact_mod_cast h3
    linarith
  · intro L hLX hLdiv
    set L₁ := L.filter (aE F₁ p) with hL₁
    set L₂ := L.filter (aE F₂ p) with hL₂
    have hL₁X : L₁ ⊆ X₁ := filter_subset_filter _ hLX
    have hL₂X : L₂ ⊆ X₂ := filter_subset_filter _ hLX
    have hd₁ : IsIntDiv p F₁ L₁ := isIntDiv_split hcard hdisj hLdiv
    have hd₂ : IsIntDiv p F₂ L₂ := by
      rw [union_comm] at hLdiv
      exact isIntDiv_split hcard' hdisj' hLdiv
    have hLe : L = L₁ ∪ L₂ := by
      ext e
      simp only [hL₁, hL₂, mem_union, mem_filter]
      constructor
      · intro he
        rcases hsplit e (hXG (hLX he)) with h | h
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, h⟩
      · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    have e : C₁ ∪ C₂ ∪ L = (C₁ ∪ L₁) ∪ (C₂ ∪ L₂) := by
      rw [hLe]; ext x; simp only [mem_union]; tauto
    rw [e]
    refine hasDecomp_union (hmono₁ _ (hC₁L L₁ hL₁X hd₁)) (hmono₂ _ (hC₂L L₂ hL₂X hd₂)) ?_
    refine hsep _ _ (fun e he => ?_) (fun e he => ?_)
    · rcases mem_union.mp he with h | h
      · exact (hC₁a e h).2
      · exact (mem_filter.mp h).2
    · rcases mem_union.mp he with h | h
      · exact (hC₂a e h).2
      · exact (mem_filter.mp h).2

/-! ### Examples -/

/-- `{000, 001} ∪ {111}`: the same-class-sequence (windmill) target fails here (census), but the
two pieces are separated: `{000, 001}` has three-step links, `{111}` too. -/
theorem nearlyAbsorbing_000_001_111 :
    NearlyAbsorbing ({{0, 0, 0}, {0, 0, 1}, {1, 1, 1}} : Finset (Multiset (Fin 2))) := by
  have h := nearlyAbsorbing_union (F₁ := ({{0, 0, 0}, {0, 0, 1}} : Finset (Multiset (Fin 2))))
    (F₂ := {{1, 1, 1}}) (by decide) (by unfold AllowedPair; decide)
    (nearlyAbsorbing_covered _ (by decide) (Or.inr (by unfold ThreeStepLinks Link; decide)))
    (nearlyAbsorbing_covered _ (by decide) (Or.inr (by unfold ThreeStepLinks Link; decide)))
  have e : (({{0, 0, 0}, {0, 0, 1}} : Finset (Multiset (Fin 2))) ∪ {{1, 1, 1}}) =
      {{0, 0, 0}, {0, 0, 1}, {1, 1, 1}} := by decide
  rwa [e] at h

/-- `{001, 111}`: neither linear nor with three-step links; covered by `F001` and splitting. -/
theorem nearlyAbsorbing_001_111 :
    NearlyAbsorbing ({{0, 0, 1}, {1, 1, 1}} : Finset (Multiset (Fin 2))) := by
  have h := nearlyAbsorbing_union (F₁ := F001) (F₂ := {{1, 1, 1}})
    (by unfold F001; decide) (by unfold AllowedPair F001; decide) nearlyAbsorbing_001
    (nearlyAbsorbing_covered _ (by decide) (Or.inr (by unfold ThreeStepLinks Link; decide)))
  have e : (F001 ∪ {{1, 1, 1}}) = ({{0, 0, 1}, {1, 1, 1}} : Finset (Multiset (Fin 2))) := by
    unfold F001; decide
  rwa [e] at h

theorem not_threeStepLinks_001_111 :
    ¬ ThreeStepLinks ({{0, 0, 1}, {1, 1, 1}} : Finset (Multiset (Fin 2))) := by
  unfold ThreeStepLinks Link; decide

theorem not_isLinearFam_001_111 :
    ¬ IsLinearFam ({{0, 0, 1}, {1, 1, 1}} : Finset (Multiset (Fin 2))) := by
  intro h
  have := h.nodup {0, 0, 1} (by decide)
  revert this; decide

end PartitionedTriangleAbsorption.BlowupB
