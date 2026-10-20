/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Rainbow

/-! # BlowupB.ZeroDeg — balanced residuals are physical

Let `G` be a complete `F`-blowup with at least `5` vertices in every class (`Reps p 5`). An
integer edge function `u` supported on edges of `G`, with zero edge-count vector and **zero degree
vector at every vertex** (`degVecZ p u v = 0`: for every vertex and every class, the signed number
of edges into that class vanishes), is a ℤ-combination of copies (`physDivZ_of_zeroDeg`).

Proof. Fix a base vertex `o i` in each class. With
`qg uv = [uv] - [u o(p v)] - [o(p u) v] + [o(p u) o(p v)]` one has `∑ e, u e • qg e = u`: the
middle terms are the spokes weighted by the degree vectors, the last term is the edge-count
vector. Each `qg` of a cross edge is an alternating `4`-cycle (or `0`); within a class the
`qg` are regrouped against a fixed reference edge `o₁ o₂`, which is possible because the free
edges of each class have total weight `0`. Alternating `4`-cycles are physical: four copies
through a common apex `s` (`c4_identity`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### Closure of physical divisibility -/

section Closure

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}

omit [Fintype V] in
theorem PhysDivZ.zero : PhysDivZ p F G (0 : Sym2 V → ℤ) :=
  physDivZ_of_physCostZ (PhysCostZ.zero p F G)

omit [Fintype V] in
theorem PhysDivZ.smul {w : Sym2 V → ℤ} (h : PhysDivZ p F G w) (a : ℤ) :
    PhysDivZ p F G (a • w) := by
  obtain ⟨ι, hι, T, c, hT, hw⟩ := h
  refine ⟨ι, hι, T, a • c, hT, fun e => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hw e, mul_sum]
  exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

omit [Fintype V] in
theorem PhysDivZ.neg {w : Sym2 V → ℤ} (h : PhysDivZ p F G w) : PhysDivZ p F G (-w) := by
  have := h.smul (-1)
  rwa [neg_one_smul] at this

omit [Fintype V] in
theorem PhysDivZ.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : PhysDivZ p F G w₁) (h₂ : PhysDivZ p F G w₂) :
    PhysDivZ p F G (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem PhysDivZ.sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, PhysDivZ p F G (f i)) : PhysDivZ p F G (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact PhysDivZ.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

omit [Fintype V] in
theorem physDivZ_of_isCopy {s : Finset V} (hs : IsCopy p F G s) :
    PhysDivZ p F G (indZ (triEdges s)) :=
  physDivZ_of_physCostZ (physCostZ_of_isCopy hs)

theorem aggDivZ_of_physDivZ {w : Sym2 V → ℤ} (h : PhysDivZ p F G w) : AggDivZ p F w := by
  obtain ⟨ι, _, T, c, hc⟩ := h
  exact aggDivZ_of_physCertZ hc

end Closure

/-! ### Supports in `G` -/

/-- The support of `w` consists of edges of `G`. -/
def OnG (G : SimpleGraph V) (w : Sym2 V → ℤ) : Prop := ∀ e, w e ≠ 0 → e ∈ G.edgeSet

section OnGLemmas

variable {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem OnG.add {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnG G w₁) (h₂ : OnG G w₂) : OnG G (w₁ + w₂) := by
  intro e he
  by_cases h : w₁ e = 0
  · exact h₂ e (by simpa [h] using he)
  · exact h₁ e h

omit [Fintype V] [DecidableEq V] in
theorem OnG.neg {w : Sym2 V → ℤ} (h : OnG G w) : OnG G (-w) :=
  fun e he => h e (by simpa using he)

omit [Fintype V] [DecidableEq V] in
theorem OnG.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnG G w₁) (h₂ : OnG G w₂) : OnG G (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem onG_of_isCopy {p : V → Fin t} {F : Finset (Multiset (Fin t))} {s : Finset V}
    (hs : IsCopy p F G s) : OnG G (indZ (triEdges s)) := by
  intro e he
  have hmem : e ∈ triEdges s := by
    by_contra h; exact he (indZ_not_mem h)
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := Reps.mem_triEdges_mk.mp hmem
    exact (G.mem_edgeSet).mpr (hs.1.1 hx hy hxy)

omit [Fintype V] in
theorem onG_of_physDivZ {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w : Sym2 V → ℤ}
    (h : PhysDivZ p F G w) : OnG G w := by
  obtain ⟨ι, hι, T, c, hT, hw⟩ := h
  intro e he
  rw [hw e] at he
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  exact onG_of_isCopy (hT j) e (fun h0 => hj (by rw [h0, mul_zero]))

theorem onG_indZ [DecidableRel G.Adj] {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) :
    OnG G (indZ E) := by
  intro e he
  have hmem : e ∈ E := by
    by_contra h; exact he (indZ_not_mem h)
  exact SimpleGraph.mem_edgeFinset.mp (hE hmem)

end OnGLemmas

/-! ### Alternating 4-cycles are physical -/

/-- The alternating `4`-cycle `a b c d`: `[ab] - [bc] + [cd] - [da]`. -/
def c4 (a b c d : V) : Sym2 V → ℤ := ind1 s(a, b) - ind1 s(b, c) + ind1 s(c, d) - ind1 s(d, a)

omit [Fintype V] in
theorem c4_identity {a b c d s : V} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
    (has : a ≠ s) (hbs : b ≠ s) (hcs : c ≠ s) (hds : d ≠ s) :
    c4 a b c d = indZ (triEdges {a, b, s}) - indZ (triEdges {b, c, s}) +
      indZ (triEdges {c, d, s}) - indZ (triEdges {d, a, s}) := by
  rw [indZ_triEdges_three hab has hbs, indZ_triEdges_three hbc hbs hcs,
    indZ_triEdges_three hcd hcs hds, indZ_triEdges_three hda hds has]
  unfold c4
  abel

omit [Fintype V] in
/-- An alternating `4`-cycle whose opposite vertices lie in the same class is physical. -/
theorem physDivZ_c4 {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) {q : ℕ} (R : Reps p q) (hq : 5 ≤ q) {a b c d : V}
    (hac : p a = p c) (hbd : p b = p d) (hA : AllowedPair F (p a) (p b))
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) : PhysDivZ p F G (c4 a b c d) := by
  have hτ := third_spec F (p a) (p b) hA
  set k := third F (p a) (p b) hA with hk
  obtain ⟨m, hm⟩ := R.exists_avoid k {a, b, c, d} (lt_of_le_of_lt card_le_four (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hm
  set s := R.rep k m with hs
  have hps : p s = k := R.cls _ _
  have has : a ≠ s := fun h => hm.1 h.symm
  have hbs : b ≠ s := fun h => hm.2.1 h.symm
  have hcs : c ≠ s := fun h => hm.2.2.1 h.symm
  have hds : d ≠ s := fun h => hm.2.2.2 h.symm
  have h1 := isCopy_of_complete hG hab has hbs (by rw [hps]; exact hτ)
  have h2 := isCopy_of_complete hG hbc hbs hcs (by rw [hps, ← hac, three_swap12]; exact hτ)
  have h3 := isCopy_of_complete hG hcd hcs hds (by rw [hps, ← hac, ← hbd]; exact hτ)
  have h4 := isCopy_of_complete hG hda hds has (by rw [hps, ← hbd, three_swap12]; exact hτ)
  rw [c4_identity hab hbc hcd hda has hbs hcs hds]
  exact (((physDivZ_of_isCopy h1).sub (physDivZ_of_isCopy h2)).add
    (physDivZ_of_isCopy h3)).sub (physDivZ_of_isCopy h4)

/-! ### The global identity -/

theorem sum_smul_ind1 (u : Sym2 V → ℤ) : ∑ e, u e • ind1 e = u := by
  funext f
  rw [Finset.sum_apply, Finset.sum_eq_single f]
  · simp [ind1_self]
  · intro e _ hne
    simp [ind1_of_ne (Ne.symm hne)]
  · intro h; exact absurd (mem_univ _) h

theorem sum_sum_ite_pair' {α γ β : Type*} [Fintype α] [Fintype γ] [DecidableEq α]
    [DecidableEq γ] [AddCommGroup β] [Module ℤ β] (a : α) (b : γ) (f : α → γ → β) :
    ∑ x, ∑ k, (if a = x ∧ b = k then (1 : ℤ) else 0) • f x k = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro k _ hk
      simp [show ¬ (b = k) from fun h => hk h.symm]
    · intro h; exact absurd (mem_univ _) h
  · intro x _ hx
    simp [show ¬ (a = x) from fun h => hx h.symm]
  · intro h; exact absurd (mem_univ _) h

omit [DecidableEq V] in
theorem edgeVecZ_apply (p : V → Fin t) (w : Sym2 V → ℤ) (i j : Fin t) :
    edgeVecZ p w i j = ∑ e, w e * pairVec p e i j := by
  simp only [edgeVecZ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem degVecZ_apply (p : V → Fin t) (w : Sym2 V → ℤ) (v : V) (j : Fin t) :
    degVecZ p w v j = ∑ e, w e * degContrib p v e j := by
  simp only [degVecZ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem sum_smul_spkOf (p : V → Fin t) (S : V → Fin t → Sym2 V → ℤ) (u : Sym2 V → ℤ) :
    ∑ e, u e • spkOf p S e = ∑ x, ∑ k, degVecZ p u x k • S x k := by
  simp_rw [spkOf_eq_sum, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [degVecZ_apply, sum_smul]
  exact sum_congr rfl fun e _ => by rw [mul_smul]

omit [DecidableEq V] in
theorem sum_smul_pairVec (p : V → Fin t) (u : Sym2 V → ℤ) (g : Fin t → Fin t → Sym2 V → ℤ) :
    ∑ e, u e • ∑ i, ∑ j, pairVec p e i j • g i j = ∑ i, ∑ j, edgeVecZ p u i j • g i j := by
  simp_rw [smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [edgeVecZ_apply, sum_smul]
  exact sum_congr rfl fun e _ => by rw [mul_smul]

variable {p : V → Fin t}

/-- Spokes to the base vertices. -/
def spoS (o : Fin t → V) (v : V) (j : Fin t) : Sym2 V → ℤ := ind1 s(v, o j)

/-- The base edge of the classes of an edge. -/
def kg (p : V → Fin t) (o : Fin t → V) (e : Sym2 V) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun x y => ind1 s(o (p x), o (p y)), fun _ _ => ind1_swap _ _⟩ e

/-- The pivot gadget `[xy] - [x o(p y)] - [y o(p x)] + [o(p x) o(p y)]`. -/
def qg (p : V → Fin t) (o : Fin t → V) (e : Sym2 V) : Sym2 V → ℤ :=
  ind1 e - spkOf p (spoS o) e + kg p o e

omit [Fintype V] in
theorem qg_mk (o : Fin t → V) (x y : V) :
    qg p o s(x, y) = ind1 s(x, y) - (ind1 s(x, o (p y)) + ind1 s(y, o (p x))) +
      ind1 s(o (p x), o (p y)) := rfl

omit [Fintype V] in
theorem two_smul_kg (o : Fin t → V) (e : Sym2 V) :
    (2 : ℤ) • kg p o e = ∑ i, ∑ j, pairVec p e i j • ind1 s(o i, o j) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [kg, pairVec, Sym2.lift_mk, add_smul, sum_add_distrib]
    rw [sum_sum_ite_pair', sum_sum_ite_pair', ind1_swap (o (p y)) (o (p x)), two_smul]

theorem sum_smul_kg_eq_zero (o : Fin t → V) {u : Sym2 V → ℤ} (hE : edgeVecZ p u = 0) :
    ∑ e, u e • kg p o e = 0 := by
  have h2 : (2 : ℤ) • ∑ e, u e • kg p o e = 0 := by
    rw [smul_sum]
    simp_rw [smul_comm (2 : ℤ), two_smul_kg]
    rw [sum_smul_pairVec, hE]
    simp
  funext f
  have := congrFun h2 f
  rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [Pi.zero_apply]
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

/-- **Global identity.** A function with zero edge-count and degree vectors is the
`u`-weighted sum of the pivot gadgets. -/
theorem sum_smul_qg (o : Fin t → V) {u : Sym2 V → ℤ} (hE : edgeVecZ p u = 0)
    (hD : ∀ v, degVecZ p u v = 0) : ∑ e, u e • qg p o e = u := by
  simp only [qg, smul_add, smul_sub, sum_add_distrib, sum_sub_distrib]
  rw [sum_smul_ind1, sum_smul_spkOf, sum_smul_kg_eq_zero o hE]
  simp [hD]

omit [Fintype V] in
theorem qg_eq_zero_left (o : Fin t → V) {x y : V} (hx : o (p x) = x) : qg p o s(x, y) = 0 := by
  rw [qg_mk, hx, ind1_swap y x]
  abel

omit [Fintype V] in
theorem qg_eq_zero_right (o : Fin t → V) {x y : V} (hy : o (p y) = y) :
    qg p o s(x, y) = 0 := by
  rw [Sym2.eq_swap]; exact qg_eq_zero_left o hy

omit [Fintype V] in
theorem qg_cross (o : Fin t → V) (x y : V) : qg p o s(x, y) = c4 x y (o (p x)) (o (p y)) := by
  rw [qg_mk]
  unfold c4
  rw [ind1_swap (o (p y)) x]
  abel

/-! ### Regrouping inside a class -/

/-- Indicator of the edges inside class `i`. -/
def mcls (p : V → Fin t) (i : Fin t) (e : Sym2 V) : ℤ :=
  Sym2.lift ⟨fun x y => if p x = i ∧ p y = i then 1 else 0, fun x y => by
    by_cases h1 : p x = i <;> by_cases h2 : p y = i <;> simp [h1, h2]⟩ e

/-- Coefficient of the class-`i` reference gadget: `1` on edges of class `i` avoiding the base
vertex, `0` on the other edges (and `-1` on the base loop, which carries no weight). -/
def lam (p : V → Fin t) (o : Fin t → V) (i : Fin t) (e : Sym2 V) : ℤ :=
  mcls p i e - degContrib p (o i) e i

omit [Fintype V] [DecidableEq V] in
theorem two_mul_mcls (i : Fin t) (e : Sym2 V) : 2 * mcls p i e = pairVec p e i i := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mcls, pairVec, Sym2.lift_mk]
    by_cases h1 : p x = i <;> by_cases h2 : p y = i <;> simp [h1, h2]

omit [DecidableEq V] in
theorem sum_mul_mcls_eq_zero {u : Sym2 V → ℤ} (hE : edgeVecZ p u = 0) (i : Fin t) :
    ∑ e, u e * mcls p i e = 0 := by
  have h : 2 * ∑ e, u e * mcls p i e = edgeVecZ p u i i := by
    rw [edgeVecZ_apply, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [← two_mul_mcls]; exact mul_left_comm _ _ _
  rw [hE, Pi.zero_apply, Pi.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem sum_mul_lam_eq_zero (o : Fin t → V) {u : Sym2 V → ℤ} (hE : edgeVecZ p u = 0)
    (hD : ∀ v, degVecZ p u v = 0) (i : Fin t) : ∑ e, u e * lam p o i e = 0 := by
  simp only [lam, mul_sub, sum_sub_distrib]
  rw [sum_mul_mcls_eq_zero hE i, ← degVecZ_apply, hD, Pi.zero_apply, sub_zero]

/-! ### Each piece is physical -/

omit [Fintype V] in
/-- Inside a class: a free edge against the reference edge `O₁ O₂`. -/
theorem physDivZ_mono_free {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) {q : ℕ} (R : Reps p q) (hq : 5 ≤ q) (o : Fin t → V)
    {i : Fin t} {x y O1 O2 : V} (hpx : p x = i) (hpy : p y = i) (hpO : p (o i) = i)
    (hp1 : p O1 = i) (hp2 : p O2 = i) (hA : AllowedPair F i i) (hxy : x ≠ y) (hxO : x ≠ o i)
    (hyO : y ≠ o i) (h1O : O1 ≠ o i) (h2O : O2 ≠ o i) (h12 : O1 ≠ O2) :
    PhysDivZ p F G (qg p o s(x, y) - qg p o s(O1, O2)) := by
  have hexp : qg p o s(x, y) - qg p o s(O1, O2) =
      ind1 s(x, y) - (ind1 s(x, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
        (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) := by
    rw [qg_mk, qg_mk, hpx, hpy, hp1, hp2]
  rw [hexp]
  have C : ∀ {a b c d : V}, p a = i → p b = i → p c = i → p d = i → a ≠ b → b ≠ c → c ≠ d →
      d ≠ a → PhysDivZ p F G (c4 a b c d) := by
    intro a b c d ha hb hc hd hab hbc hcd hda
    exact physDivZ_c4 hG R hq (ha.trans hc.symm) (hb.trans hd.symm) (by rw [ha, hb]; exact hA)
      hab hbc hcd hda
  by_cases hx1 : x = O1
  · rw [hx1]
    have hy1 : y ≠ O1 := fun h => hxy (hx1.trans h.symm)
    by_cases hy2 : y = O2
    · rw [hy2, sub_self]; exact PhysDivZ.zero
    · have key : ind1 s(O1, y) - (ind1 s(O1, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
          (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
          c4 O1 y (o i) O2 := by
        unfold c4; rw [ind1_swap (o i) O2, ind1_swap O2 O1]; abel
      rw [key]
      exact C hp1 hpy hpO hp2 (Ne.symm hy1) hyO (Ne.symm h2O) (Ne.symm h12)
  · by_cases hx2 : x = O2
    · rw [hx2]
      have hy2 : y ≠ O2 := fun h => hxy (hx2.trans h.symm)
      by_cases hy1 : y = O1
      · rw [hy1]
        have key : ind1 s(O2, O1) - (ind1 s(O2, o i) + ind1 s(O1, o i)) + ind1 s(o i, o i) -
            (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) = 0 := by
          rw [ind1_swap O2 O1]; abel
        rw [key]; exact PhysDivZ.zero
      · have key : ind1 s(O2, y) - (ind1 s(O2, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
            (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
            c4 O2 y (o i) O1 := by
          unfold c4; rw [ind1_swap (o i) O1]; abel
        rw [key]
        exact C hp2 hpy hpO hp1 (Ne.symm hy2) hyO (Ne.symm h1O) h12
    · by_cases hy1 : y = O1
      · rw [hy1]
        have key : ind1 s(x, O1) - (ind1 s(x, o i) + ind1 s(O1, o i)) + ind1 s(o i, o i) -
            (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
            c4 O1 x (o i) O2 := by
          unfold c4; rw [ind1_swap O1 x, ind1_swap (o i) O2, ind1_swap O2 O1]; abel
        rw [key]
        exact C hp1 hpx hpO hp2 (Ne.symm hx1) hxO (Ne.symm h2O) (Ne.symm h12)
      · by_cases hy2 : y = O2
        · rw [hy2]
          have key : ind1 s(x, O2) - (ind1 s(x, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i) -
              (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
              c4 O2 x (o i) O1 := by
            unfold c4; rw [ind1_swap O2 x, ind1_swap (o i) O1]; abel
          rw [key]
          exact C hp2 hpx hpO hp1 (Ne.symm hx2) hxO (Ne.symm h1O) h12
        · have key : ind1 s(x, y) - (ind1 s(x, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
              (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
              c4 x y (o i) O1 + c4 x O1 O2 (o i) := by
            unfold c4; rw [ind1_swap (o i) O1, ind1_swap O1 x, ind1_swap (o i) x]; abel
          rw [key]
          exact (C hpx hpy hpO hp1 hxy hyO (Ne.symm h1O) (Ne.symm hx1)).add
            (C hpx hp1 hp2 hpO hx1 h12 h2O (Ne.symm hxO))

omit [Fintype V] in
/-- The piece of an edge of `G` in the decomposition is physical. -/
theorem physDivZ_piece {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (R : Reps p 5) {x y : V} (hadj : G.Adj x y) :
    PhysDivZ p F G (qg p (fun i => R.rep i 0) s(x, y) -
      ∑ i, lam p (fun i => R.rep i 0) i s(x, y) •
        qg p (fun i => R.rep i 0) s(R.rep i 1, R.rep i 2)) := by
  set o : Fin t → V := fun i => R.rep i 0 with ho
  have hpo : ∀ i, p (o i) = i := fun i => R.cls i 0
  have hoinj : ∀ i j, o i = o j → i = j := fun i j h => (R.inj i 0 j 0 h).1
  have hxy : x ≠ y := G.ne_of_adj hadj
  have hA : AllowedPair F (p x) (p y) := allowedPair_of_adj hG hadj
  have hlam_other : ∀ i, i ≠ p x → lam p o i s(x, y) = 0 := by
    intro i hi
    have h1 : ¬ p x = i := fun h => hi h.symm
    have h2 : x ≠ o i := fun h => h1 (by rw [h, hpo])
    simp [lam, mcls, degContrib, h1, h2]
  rw [Finset.sum_eq_single (p x) (fun i _ hi => by rw [hlam_other i hi, zero_smul])
    (fun h => absurd (mem_univ _) h)]
  by_cases hc : p x = p y
  · obtain ⟨i, hpx⟩ : ∃ i, p x = i := ⟨_, rfl⟩
    have hpy : p y = i := hc.symm.trans hpx
    rw [hpx]
    have hAi : AllowedPair F i i := by rw [hpx, hpy] at hA; exact hA
    by_cases hxo : x = o i
    · have hyo : y ≠ o i := fun h => hxy (hxo.trans h.symm)
      have hl : lam p o i s(x, y) = 0 := by
        simp [lam, mcls, degContrib, hpy, hxo, hpo, hyo]
      rw [qg_eq_zero_left o (by rw [hpx]; exact hxo.symm), hl, zero_smul, sub_zero]
      exact PhysDivZ.zero
    · by_cases hyo : y = o i
      · have hl : lam p o i s(x, y) = 0 := by
          simp [lam, mcls, degContrib, hpx, hyo, hpo, hxo]
        rw [qg_eq_zero_right o (by rw [hpy]; exact hyo.symm), hl, zero_smul, sub_zero]
        exact PhysDivZ.zero
      · have hl : lam p o i s(x, y) = 1 := by
          simp [lam, mcls, degContrib, hpx, hpy, hxo, hyo]
        rw [hl, one_smul]
        have h1O : R.rep i 1 ≠ o i := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
        have h2O : R.rep i 2 ≠ o i := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
        have h12 : R.rep i 1 ≠ R.rep i 2 := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
        exact physDivZ_mono_free hG R le_rfl o hpx hpy (hpo i) (R.cls i 1) (R.cls i 2) hAi hxy
          hxo hyo h1O h2O h12
  · have hy' : y ≠ o (p x) := fun h => hc (by rw [h, hpo])
    have hl : lam p o (p x) s(x, y) = 0 := by
      simp [lam, mcls, degContrib, Ne.symm hc, hy']
    rw [hl, zero_smul, sub_zero]
    by_cases hxo : o (p x) = x
    · rw [qg_eq_zero_left o hxo]; exact PhysDivZ.zero
    · by_cases hyo : o (p y) = y
      · rw [qg_eq_zero_right o hyo]; exact PhysDivZ.zero
      · rw [qg_cross]
        exact physDivZ_c4 hG R le_rfl (hpo _).symm (hpo _).symm hA hxy hy'
          (fun h => hc (hoinj _ _ h)) (fun h => hc (by rw [← h, hpo]))

/-! ### The theorem -/

/-- **Balanced residuals are physical.** In a complete `F`-blowup with at least `5` vertices in
every class, an integer edge function supported on `G` with zero edge-count vector and zero
degree vector at every vertex is a ℤ-combination of `F`-copies. -/
theorem physDivZ_of_zeroDeg {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (R : Reps p 5) {u : Sym2 V → ℤ} (hsupp : OnG G u)
    (hE : edgeVecZ p u = 0) (hD : ∀ v, degVecZ p u v = 0) : PhysDivZ p F G u := by
  set o : Fin t → V := fun i => R.rep i 0 with ho
  have hdecomp : u = ∑ e, u e • (qg p o e - ∑ i, lam p o i e • qg p o s(R.rep i 1, R.rep i 2)) := by
    have h1 : ∑ e, u e • ∑ i, lam p o i e • qg p o s(R.rep i 1, R.rep i 2) = 0 := by
      simp_rw [smul_sum, smul_smul]
      rw [sum_comm]
      refine sum_eq_zero fun i _ => ?_
      rw [← sum_smul, sum_mul_lam_eq_zero o hE hD i, zero_smul]
    simp only [smul_sub, sum_sub_distrib]
    rw [h1, sub_zero, sum_smul_qg o hE hD]
  rw [hdecomp]
  refine PhysDivZ.sum _ _ fun e _ => ?_
  by_cases hue : u e = 0
  · rw [hue, zero_smul]; exact PhysDivZ.zero
  · refine PhysDivZ.smul ?_ _
    have he := hsupp e hue
    induction e using Sym2.ind with
    | _ x y => exact physDivZ_piece hG R ((G.mem_edgeSet).mp he)

end PartitionedTriangleAbsorption.BlowupB
