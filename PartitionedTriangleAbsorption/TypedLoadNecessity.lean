/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedNearConsumer
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Necessary conditions for near-unit typed loads

For any family `F`, any graph `J` and any weights `ψ` on the `F`-copies of `J`,
the edge loads satisfy exact linear identities: every linear functional on the
ordered edge-count space that annihilates all type edge vectors of `F` has zero
load-weighted sum over `E(J)`. Consequently near-unit loads force the edge
vector of `J` to lie close to the span of the type edge vectors, at the same
precision as the loads. Similarly, every vertex-cone face gives a one-sided
inequality at every vertex, using only nonnegativity of the weights.

These are necessary conditions only. No sufficiency is claimed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLoadNecessity

open Finset TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The actual edge load of `ψ` on `e`, summing over the `F`-copies of `J`. -/
noncomputable def edgeLoad (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : SimpleGraph V)
    (ψ : Finset V → ℝ) (e : Sym2 V) : ℝ :=
  ∑ s ∈ copies p F J with e ∈ triEdges s, ψ s

/-- A linear functional on ordered edge-count vectors. -/
def pairFun (l : Fin t → Fin t → ℤ) (M : Fin t → Fin t → ℤ) : ℤ :=
  ∑ i, ∑ j, l i j * M i j

/-- A linear functional on degree vectors. -/
def degFun (m : Fin t → ℤ) (d : Fin t → ℤ) : ℤ :=
  ∑ i, m i * d i

/-- `l` vanishes on the edge vector of every type of `F`. -/
def Annihilates (F : Finset (Multiset (Fin t))) (l : Fin t → Fin t → ℤ) : Prop :=
  ∀ τ ∈ F, pairFun l (typeEdgeVec τ) = 0

/-- `m` is a (closed half-space containing the) cone face at a vertex of part `a`:
it is nonpositive on every degree vector available at that vertex. -/
def ConeFace (F : Finset (Multiset (Fin t))) (a : Fin t) (m : Fin t → ℤ) : Prop :=
  ∀ τ ∈ F, a ∈ τ → degFun m (typeDegVec τ a) ≤ 0

theorem pairFun_sum {ι : Type*} (l : Fin t → Fin t → ℤ) (S : Finset ι)
    (f : ι → Fin t → Fin t → ℤ) :
    pairFun l (∑ x ∈ S, f x) = ∑ x ∈ S, pairFun l (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pairFun]
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]
    simp only [pairFun, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem degFun_sum {ι : Type*} (m : Fin t → ℤ) (S : Finset ι) (f : ι → Fin t → ℤ) :
    degFun m (∑ x ∈ S, f x) = ∑ x ∈ S, degFun m (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [degFun]
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]
    simp only [degFun, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
theorem pairFun_edgeVec (l : Fin t → Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) :
    pairFun l (edgeVec p E) = ∑ e ∈ E, pairFun l (pairVec p e) :=
  pairFun_sum l E _

omit [Fintype V] in
theorem degFun_degVec (m : Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) :
    degFun m (degVec p E v) = ∑ e ∈ E, degFun m (degContrib p v e) :=
  degFun_sum m E _

/-- Exchange of summation: the load-weighted sum of an edge function over `E(J)`
equals the weighted sum, over copies, of its sum on the three copy edges. -/
theorem sum_mul_edgeLoad (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (ψ : Finset V → ℝ) (c : Sym2 V → ℝ) :
    ∑ e ∈ J.edgeFinset, c e * edgeLoad p F J ψ e =
      ∑ s ∈ copies p F J, ψ s * ∑ e ∈ triEdges s, c e := by
  unfold edgeLoad
  simp only [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsub := triEdges_subset_of_isCopy (mem_copies_iff.mp hs)
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfil : J.edgeFinset.filter (fun e => e ∈ triEdges s) = triEdges s := by
    ext e
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [hfil]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

/-- **Exact load identity.** An annihilating functional has zero load-weighted
sum, for arbitrary real weights (no sign condition is needed). -/
theorem annihilator_load_identity (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (ψ : Finset V → ℝ)
    {l : Fin t → Fin t → ℤ} (hl : Annihilates F l) :
    ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) * edgeLoad p F J ψ e = 0 := by
  rw [sum_mul_edgeLoad]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hc := mem_copies_iff.mp hs
  have hzero : ∑ e ∈ triEdges s, (pairFun l (pairVec p e) : ℝ) = 0 := by
    rw [← Int.cast_sum, ← pairFun_edgeVec, edgeVec_triEdges p hc.1.card_eq]
    exact_mod_cast hl _ hc.2
  rw [hzero, mul_zero]

/-- **Global balance is necessary.** If every edge load is within `τ` of one,
the annihilated edge-count functional of `J` is at most `τ` times its absolute
mass. -/
theorem annihilator_balance (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (ψ : Finset V → ℝ)
    {l : Fin t → Fin t → ℤ} (hl : Annihilates F l) {τ : ℝ}
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F J ψ e - 1| ≤ τ) :
    |(pairFun l (edgeVec p J.edgeFinset) : ℝ)| ≤
      τ * ∑ e ∈ J.edgeFinset, |(pairFun l (pairVec p e) : ℝ)| := by
  have hid := annihilator_load_identity p F J ψ hl
  have hrewrite : (pairFun l (edgeVec p J.edgeFinset) : ℝ) =
      ∑ e ∈ J.edgeFinset, (pairFun l (pairVec p e) : ℝ) * (1 - edgeLoad p F J ψ e) := by
    rw [pairFun_edgeVec, Int.cast_sum]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hid, sub_zero]
  rw [hrewrite, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  rw [abs_mul, mul_comm τ]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_sub_comm]
  exact hload e he

omit [Fintype V] in
/-- An annihilating functional vanishes on integrally divisible edge sets. -/
theorem annihilator_of_isIntDiv {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 V)} (hE : IsIntDiv p F E) {l : Fin t → Fin t → ℤ}
    (hl : Annihilates F l) : pairFun l (edgeVec p E) = 0 := by
  obtain ⟨c, hc⟩ := hE.1
  rw [hc, pairFun_sum]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  have hsmul : pairFun l (c τ • typeEdgeVec τ) = c τ * pairFun l (typeEdgeVec τ) := by
    unfold pairFun
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsmul, hl τ hτ, mul_zero]

/-- **Necessary condition on the deletion, decomposable-absorber form.** If `G` is
integrally divisible and the deleted absorber `A` has an `F`-decomposition, any
weights on `J = G - (A ∪ X)` with all loads within `τ` of one force the reserve
`X` to be balanced for every annihilating functional, to precision `τ` times the
functional mass of `J`. The weights need not be nonnegative or capped. -/
theorem reserve_balance_of_hasDecomp (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset (Sym2 V))
    (hA : A ⊆ G.edgeFinset) (hX : X ⊆ G.edgeFinset) (hAX : Disjoint A X)
    (hG : IsIntDiv p F G.edgeFinset) (hAdec : HasDecomp p F A)
    (ψ : Finset V → ℝ) {l : Fin t → Fin t → ℤ} (hl : Annihilates F l) {τ : ℝ}
    (hload : ∀ e ∈ G.edgeFinset \ (A ∪ X),
      |edgeLoad p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) ψ e - 1| ≤ τ) :
    |(pairFun l (edgeVec p X) : ℝ)| ≤
      τ * ∑ e ∈ G.edgeFinset \ (A ∪ X), |(pairFun l (pairVec p e) : ℝ)| := by
  classical
  set J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hJ : J.edgeFinset = G.edgeFinset \ (A ∪ X) := SimpleGraph.edgeFinset_deleteEdges _
  have hbal := annihilator_balance p F J ψ hl (τ := τ) (fun e he => hload e (hJ ▸ he))
  rw [hJ] at hbal
  have hA0 := annihilator_of_isIntDiv (isIntDiv_of_hasDecomp hAdec) hl
  have hG0 := annihilator_of_isIntDiv hG hl
  have hsplit : G.edgeFinset = (G.edgeFinset \ (A ∪ X)) ∪ (A ∪ X) :=
    (Finset.sdiff_union_of_subset (Finset.union_subset hA hX)).symm
  have hvec : edgeVec p G.edgeFinset =
      edgeVec p (G.edgeFinset \ (A ∪ X)) + (edgeVec p A + edgeVec p X) := by
    conv_lhs => rw [hsplit]
    rw [edgeVec_union p Finset.sdiff_disjoint, edgeVec_union p hAX]
  have hlin : pairFun l (edgeVec p G.edgeFinset) =
      pairFun l (edgeVec p (G.edgeFinset \ (A ∪ X))) +
        (pairFun l (edgeVec p A) + pairFun l (edgeVec p X)) := by
    rw [hvec]
    unfold pairFun
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hX0 : (pairFun l (edgeVec p X) : ℝ) =
      -(pairFun l (edgeVec p (G.edgeFinset \ (A ∪ X))) : ℝ) := by
    have : pairFun l (edgeVec p X) = -pairFun l (edgeVec p (G.edgeFinset \ (A ∪ X))) := by
      omega
    exact_mod_cast this
  rw [hX0, abs_neg]
  exact hbal

/-- **Necessary condition on the deletion.** Under the exact hypotheses that
`typed_cover_down_absorption_near` places on `G`, `A` and `X` (integral
divisibility of `G` and the universal-absorber property of `A`), any weights on
`J = G - (A ∪ X)` with all loads within `τ` of one force the reserve `X` itself to
be balanced for every annihilating functional, to precision `τ` times the
functional mass of `J`. The weights need not be nonnegative or capped. -/
theorem reserve_balance_of_near_loads (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset (Sym2 V))
    (hA : A ⊆ G.edgeFinset) (hX : X ⊆ G.edgeFinset) (hAX : Disjoint A X)
    (hG : IsIntDiv p F G.edgeFinset)
    (habs : ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L))
    (ψ : Finset V → ℝ) {l : Fin t → Fin t → ℤ} (hl : Annihilates F l) {τ : ℝ}
    (hload : ∀ e ∈ G.edgeFinset \ (A ∪ X),
      |edgeLoad p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) ψ e - 1| ≤ τ) :
    |(pairFun l (edgeVec p X) : ℝ)| ≤
      τ * ∑ e ∈ G.edgeFinset \ (A ∪ X), |(pairFun l (pairVec p e) : ℝ)| := by
  have hAdec : HasDecomp p F A := by
    have h := habs ∅ (Finset.empty_subset _) isIntDiv_empty
    rwa [Finset.union_empty] at h
  exact reserve_balance_of_hasDecomp p F G A X hA hX hAX hG hAdec ψ hl hload

/-- **Vertex-cone faces are necessary.** For nonnegative weights with all loads
within `τ` of one, every cone face at `v` holds for the degree vector of `v`
up to `τ` times its absolute mass. -/
theorem coneFace_balance (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (ψ : Finset V → ℝ)
    (hψ : ∀ s ∈ copies p F J, 0 ≤ ψ s) (v : V) {m : Fin t → ℤ}
    (hm : ConeFace F (p v) m) {τ : ℝ}
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F J ψ e - 1| ≤ τ) :
    (degFun m (degVec p J.edgeFinset v) : ℝ) ≤
      τ * ∑ e ∈ J.edgeFinset, |(degFun m (degContrib p v e) : ℝ)| := by
  have hid : ∑ e ∈ J.edgeFinset, (degFun m (degContrib p v e) : ℝ) * edgeLoad p F J ψ e ≤ 0 := by
    rw [sum_mul_edgeLoad]
    refine Finset.sum_nonpos fun s hs => ?_
    have hc := mem_copies_iff.mp hs
    have hface : ∑ e ∈ triEdges s, (degFun m (degContrib p v e) : ℝ) ≤ 0 := by
      rw [← Int.cast_sum, ← degFun_degVec, degVec_triEdges p hc.1.card_eq]
      split_ifs with hv
      · exact_mod_cast hm _ hc.2 (mem_triType hv)
      · simp [degFun]
    exact mul_nonpos_of_nonneg_of_nonpos (hψ s hs) hface
  have hrewrite : (degFun m (degVec p J.edgeFinset v) : ℝ) =
      ∑ e ∈ J.edgeFinset, (degFun m (degContrib p v e) : ℝ) * (1 - edgeLoad p F J ψ e) +
        ∑ e ∈ J.edgeFinset, (degFun m (degContrib p v e) : ℝ) * edgeLoad p F J ψ e := by
    rw [degFun_degVec, Int.cast_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hrewrite]
  have hbound : ∑ e ∈ J.edgeFinset, (degFun m (degContrib p v e) : ℝ) *
      (1 - edgeLoad p F J ψ e) ≤
      τ * ∑ e ∈ J.edgeFinset, |(degFun m (degContrib p v e) : ℝ)| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul, mul_comm τ]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_sub_comm]
    exact hload e he
  linarith

/-- **Vertex faces after deletion.** With `J = G - (A ∪ X)`, nonnegative weights
with all loads within `τ` of one force, at every vertex `v` and every cone face
`m`, `m(d_G(v)) - m(d_A(v)) - m(d_X(v)) ≤ τ · Σ_{e ∈ J} |m(contribution of e at v)|`.
Since `m(d_A(v)) ≤ 0` for a decomposable `A`, the absorber can only make this
harder at a vertex where `G` is close to the cone boundary. -/
theorem deletion_face_of_near_loads (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset (Sym2 V))
    (hA : A ⊆ G.edgeFinset) (hX : X ⊆ G.edgeFinset) (hAX : Disjoint A X)
    (ψ : Finset V → ℝ)
    (hψ : ∀ s ∈ copies p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))),
      0 ≤ ψ s)
    (v : V) {m : Fin t → ℤ} (hm : ConeFace F (p v) m) {τ : ℝ}
    (hload : ∀ e ∈ G.edgeFinset \ (A ∪ X),
      |edgeLoad p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) ψ e - 1| ≤ τ) :
    (degFun m (degVec p G.edgeFinset v) : ℝ) - degFun m (degVec p A v) -
        degFun m (degVec p X v) ≤
      τ * ∑ e ∈ G.edgeFinset \ (A ∪ X), |(degFun m (degContrib p v e) : ℝ)| := by
  classical
  set J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hJ : J.edgeFinset = G.edgeFinset \ (A ∪ X) := SimpleGraph.edgeFinset_deleteEdges _
  have hface := coneFace_balance p F J ψ hψ v hm (τ := τ) (fun e he => hload e (hJ ▸ he))
  rw [hJ] at hface
  have hsplit : G.edgeFinset = (G.edgeFinset \ (A ∪ X)) ∪ (A ∪ X) :=
    (Finset.sdiff_union_of_subset (Finset.union_subset hA hX)).symm
  have hvec : degVec p G.edgeFinset v =
      degVec p (G.edgeFinset \ (A ∪ X)) v + (degVec p A v + degVec p X v) := by
    conv_lhs => rw [hsplit]
    rw [degVec_union p Finset.sdiff_disjoint, degVec_union p hAX]
  have hlin : degFun m (degVec p G.edgeFinset v) =
      degFun m (degVec p (G.edgeFinset \ (A ∪ X)) v) +
        (degFun m (degVec p A v) + degFun m (degVec p X v)) := by
    rw [hvec]
    unfold degFun
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hcast : (degFun m (degVec p G.edgeFinset v) : ℝ) - degFun m (degVec p A v) -
      degFun m (degVec p X v) = (degFun m (degVec p (G.edgeFinset \ (A ∪ X)) v) : ℝ) := by
    rw [hlin]; push_cast; ring
  rw [hcast]
  exact hface

end PartitionedTriangleAbsorption.TypedLoadNecessity
