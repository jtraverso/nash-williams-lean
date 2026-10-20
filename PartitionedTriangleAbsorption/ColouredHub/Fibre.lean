/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.Main
public import PartitionedTriangleAbsorption.TypedTransformerConstruction
public import PartitionedTriangleAbsorption.TypedPaddingProducer
public import Mathlib.Tactic.LinearCombination

/-! # Coloured hubs I: the comparison graph and matched edge-type fibres

The comparison graph `Q` is a vertex-disjoint union of `c τ` triangles of each type `τ`.
Its edge slots are indexed by `Tri F c × Fin 3`: slot `(x, a)` is the edge between corners
`a` and `a + 1` of triangle `x`, whose parts are given by a word `triWord x : Fin 3 → Fin t`
with multiset equal to the type of `x`.

The project encodes edge types by *ordered* vectors (`pairVec`): an off-diagonal unordered
pair `{a, b}` contributes `1` to both coordinates `(a, b)` and `(b, a)`, and a diagonal pair
`{a, a}` contributes `2` to the coordinate `(a, a)`. `vecOf_apply` makes this explicit, and
`card_fibre_eq` recovers the exact cardinality of every unordered fibre from equal vectors:
the doubled diagonal is divided out, not ignored. `exists_fibre_equiv` then produces a
bijection of edge slots preserving the unordered part pair, fibre by fibre. No vertex map
and no orientation agreement is asserted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate

variable {t : ℕ}

/-- The ordered contribution of one unordered pair of parts. -/
abbrev pv (z : Sym2 (Fin t)) : Fin t → Fin t → ℤ := pairVec id z

/-- The ordered encoding counts an off-diagonal pair once in each coordinate, and a
diagonal pair twice. -/
theorem pv_apply (z : Sym2 (Fin t)) (a b : Fin t) :
    pv z a b = (if a = b then 2 else 1) * (if z = s(a, b) then 1 else 0) := by
  induction z using Sym2.ind with
  | _ u v =>
    simp only [pv, pairVec, Sym2.lift_mk, id, Sym2.eq_iff]
    by_cases hab : a = b
    · subst hab; by_cases hu : u = a <;> by_cases hv : v = a <;> simp [hu, hv]
    · by_cases hu : u = a <;> by_cases hv : v = b <;> by_cases hu' : u = b <;>
        by_cases hv' : v = a <;> simp_all

/-- The type vector of a triangle is the sum of its three edge pairs. -/
theorem typeEdgeVec_word (w : Fin 3 → Fin t) :
    typeEdgeVec ({w 0, w 1, w 2} : Multiset (Fin t)) =
      pv s(w 0, w 1) + pv s(w 1, w 2) + pv s(w 2, w 0) := by
  funext a b
  simp only [typeEdgeVec, Pi.add_apply, pv, pairVec, Sym2.lift_mk, id, Multiset.insert_eq_cons,
    Multiset.count_cons, Multiset.count_singleton]
  generalize w 0 = x
  generalize w 1 = y
  generalize w 2 = z
  have hp : ∀ u v : Fin t, (if u = a ∧ v = b then (1 : ℤ) else 0) =
      (if a = u then 1 else 0) * (if b = v then 1 else 0) := by
    intro u v; by_cases h1 : a = u <;> by_cases h2 : b = v <;> simp [h1, h2, eq_comm]
  have hd : ∀ u : Fin t, (if a = u then (1 : ℤ) else 0) * (if b = u then 1 else 0) =
      (if a = b then 1 else 0) * (if a = u then 1 else 0) := by
    intro u
    by_cases h1 : a = u
    · subst h1
      by_cases h2 : b = a
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · simp [h1]
  have hc : ∀ c : ℤ, (if a = b then c else 0) = (if a = b then 1 else 0) * c := by
    intro c; split_ifs <;> simp
  simp only [hp]
  rw [hc]
  push_cast
  linear_combination hd x + hd y + hd z

/-- The ordered edge-type vector of a finite family of unordered part pairs. -/
def vecOf {ι : Type*} [Fintype ι] (g : ι → Sym2 (Fin t)) : Fin t → Fin t → ℤ :=
  ∑ i, pv (g i)

/-- Each coordinate of `vecOf` is a fibre count, doubled on the diagonal. -/
theorem vecOf_apply {ι : Type*} [Fintype ι] (g : ι → Sym2 (Fin t)) (a b : Fin t) :
    vecOf g a b = (if a = b then 2 else 1) * ((univ.filter fun i => g i = s(a, b)).card : ℤ) := by
  classical
  simp only [vecOf, Finset.sum_apply, pv_apply, ← Finset.mul_sum, Finset.sum_boole]

/-- Equal ordered vectors give equal unordered fibre cardinalities. -/
theorem card_fibre_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {g : ι → Sym2 (Fin t)}
    {g' : κ → Sym2 (Fin t)} (h : vecOf g = vecOf g') (z : Sym2 (Fin t)) :
    (univ.filter fun i => g i = z).card = (univ.filter fun i => g' i = z).card := by
  induction z using Sym2.ind with
  | _ a b =>
    have := congrFun (congrFun h a) b
    rw [vecOf_apply, vecOf_apply] at this
    have hpos : (if a = b then (2 : ℤ) else 1) ≠ 0 := by split_ifs <;> norm_num
    exact_mod_cast mul_left_cancel₀ hpos this

/-- **Fibrewise matching.** Equal ordered vectors give a bijection preserving the
unordered part pair of every slot. -/
theorem exists_fibre_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] {g : ι → Sym2 (Fin t)}
    {g' : κ → Sym2 (Fin t)} (h : vecOf g = vecOf g') :
    ∃ π : ι ≃ κ, ∀ i, g' (π i) = g i := by
  classical
  refine ⟨Equiv.ofFiberEquiv (fun z => Fintype.equivOfCardEq ?_), Equiv.ofFiberEquiv_map _⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  exact card_fibre_eq h z

/-- The edge vector of an even piece, read along a closed-trail system. -/
theorem edgeVec_eq_vecOf {V : Type*} {P : Finset (Sym2 V)} {m : ℕ}
    {σ : Equiv.Perm (Fin m)} {X : Fin m → V} (hX : IsTrailSystem P σ X) (p : V → Fin t) :
    edgeVec p P = vecOf (fun i => s(p (X i), p (X (σ i)))) := by
  classical
  have hP : P = univ.image fun i => s(X i, X (σ i)) := by
    ext e; rw [hX.mem e]; simp [eq_comm]
  rw [edgeVec, hP, sum_image (fun i _ j _ h => hX.inj h), vecOf]
  rfl

/-! ### The comparison graph -/

/-- One index per triangle of the comparison graph: `c τ` triangles of type `τ`. -/
abbrev Tri (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℕ) :=
  (τ : {τ // τ ∈ F}) × Fin (c τ.val)

/-- Corner parts of a comparison triangle. -/
noncomputable def triWord (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (c : Multiset (Fin t) → ℕ) (x : Tri F c) : Fin 3 → Fin t :=
  (TypedPaddingProducer.exists_word (hF x.1.val x.1.property)).choose

theorem triWord_spec (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (c : Multiset (Fin t) → ℕ) (x : Tri F c) :
    ({triWord F hF c x 0, triWord F hF c x 1, triWord F hF c x 2} : Multiset (Fin t)) =
      x.1.val :=
  (TypedPaddingProducer.exists_word (hF x.1.val x.1.property)).choose_spec

theorem triWord_mem (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (c : Multiset (Fin t) → ℕ) (x : Tri F c) :
    ({triWord F hF c x 0, triWord F hF c x 1, triWord F hF c x 2} : Multiset (Fin t)) ∈ F := by
  rw [triWord_spec]; exact x.1.property

/-- The unordered part pair of a comparison edge slot. -/
def slotPair {T : Type*} (w : T → Fin 3 → Fin t) (z : T × Fin 3) : Sym2 (Fin t) :=
  s(w z.1 z.2, w z.1 (z.2 + 1))

/-- The comparison graph has the prescribed nonnegative type combination as its vector. -/
theorem vecOf_slotPair (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (c : Multiset (Fin t) → ℕ) :
    vecOf (slotPair (triWord F hF c)) = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ := by
  classical
  rw [vecOf, Fintype.sum_prod_type]
  have h3 : ∀ x : Tri F c, ∑ a : Fin 3, pv (slotPair (triWord F hF c) (x, a)) =
      typeEdgeVec x.1.val := by
    intro x
    rw [Fin.sum_univ_three, ← triWord_spec F hF c x, typeEdgeVec_word]
    rfl
  simp only [h3, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fin]
  rw [← F.sum_coe_sort (fun τ => (c τ : ℤ) • typeEdgeVec τ)]
  refine sum_congr rfl fun τ _ => ?_
  rw [natCast_zsmul]

end PartitionedTriangleAbsorption.ColouredHub
