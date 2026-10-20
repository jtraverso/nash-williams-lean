/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadFamilies

/-! # Sparsity and anti-edgefulness do not determine preparability

The reserve properties consumed by `typed_cover_down_absorption_near`
(containment, disjointness from the absorber, a maximum-degree bound and
anti-edgefulness) are monotone under adding a few more edges, except for the
degree bound, which grows only by the degree of the added set. The balance
functional, however, changes by a fixed amount per added internal edge.

Consequently: if `X₀` is any reserve and `X₁` is a set of more than
`2 τ M` edges on which an annihilating functional is at most `-1` (where `M`
is the absolute functional mass of `G`), then `X₀` and `X₀ ∪ X₁` cannot both be
followed by weights on the corresponding main graphs with all loads within `τ`
of one. Hence no preparation theorem can hold for every sparse anti-edgeful
reserve: a producer must also control the reserve's type balance.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLoadReserveObstruction

open Finset TypedLoadNecessity TypedLoadFamilies

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [DecidableEq V] in
/-- Anti-edgefulness of reserve graphs is monotone in the reserve edge set. -/
theorem antiEdgeful_mono (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    {X X' : Finset (Sym2 V)} (hXX' : X ⊆ X')
    [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
    [DecidableRel (ReserveCoverDown.reserveGraph X').Adj] {α : ℝ}
    (h : AntiEdgeful p F (ReserveCoverDown.reserveGraph X) α) :
    AntiEdgeful p F (ReserveCoverDown.reserveGraph X') α := by
  intro τ hτ i j k hijk u v huv hu hv
  refine (h τ hτ i j k hijk u v huv hu hv).trans (Nat.cast_le.mpr
    (Finset.card_le_card fun w hw => ?_))
  have hmono : ∀ a b, (ReserveCoverDown.reserveGraph X).Adj a b →
      (ReserveCoverDown.reserveGraph X').Adj a b := by
    intro a b hab
    simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe] at hab ⊢
    exact ⟨hXX' hab.1, hab.2⟩
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, hmono _ _ hw.2.1, hmono _ _ hw.2.2.1, hw.2.2.2⟩

omit [Fintype V] in
theorem degBounded_union {X Y : Finset (Sym2 V)} {d e : ℝ} (hX : DegBounded X d)
    (hY : DegBounded Y e) : DegBounded (X ∪ Y) (d + e) := by
  intro v
  rw [Finset.filter_union]
  exact (Nat.cast_le.mpr (Finset.card_union_le _ _)).trans
    (by push_cast; linarith [hX v, hY v])

/-- **Two reserves, at most one preparable.** -/
theorem not_both_preparable (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (A X₀ X₁ : Finset (Sym2 V))
    (hA : A ⊆ G.edgeFinset) (hX₀ : X₀ ⊆ G.edgeFinset) (hX₁ : X₁ ⊆ G.edgeFinset)
    (hAX₀ : Disjoint A X₀) (hAX₁ : Disjoint A X₁) (h01 : Disjoint X₀ X₁)
    (hG : IsIntDiv p F G.edgeFinset) (hAdec : HasDecomp p F A)
    {l : Fin t → Fin t → ℤ} (hl : Annihilates F l)
    (hneg : ∀ e ∈ X₁, pairFun l (pairVec p e) ≤ -1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hbig : 2 * τ * ∑ e ∈ G.edgeFinset, |(pairFun l (pairVec p e) : ℝ)| < X₁.card)
    (ψ₀ ψ₁ : Finset V → ℝ)
    (hload₀ : ∀ e ∈ G.edgeFinset \ (A ∪ X₀),
      |edgeLoad p F (G.deleteEdges ((A ∪ X₀ : Finset (Sym2 V)) : Set (Sym2 V))) ψ₀ e - 1| ≤ τ)
    (hload₁ : ∀ e ∈ G.edgeFinset \ (A ∪ (X₀ ∪ X₁)),
      |edgeLoad p F (G.deleteEdges ((A ∪ (X₀ ∪ X₁) : Finset (Sym2 V)) : Set (Sym2 V)))
        ψ₁ e - 1| ≤ τ) :
    False := by
  set M := ∑ e ∈ G.edgeFinset, |(pairFun l (pairVec p e) : ℝ)|
  have hsub : ∀ S ⊆ G.edgeFinset, ∑ e ∈ S, |(pairFun l (pairVec p e) : ℝ)| ≤ M :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => abs_nonneg _)
  have b₀ := reserve_balance_of_hasDecomp p F G A X₀ hA hX₀ hAX₀ hG hAdec ψ₀ hl hload₀
  have b₁ := reserve_balance_of_hasDecomp p F G A (X₀ ∪ X₁) hA (Finset.union_subset hX₀ hX₁)
    (Finset.disjoint_union_right.mpr ⟨hAX₀, hAX₁⟩) hG hAdec ψ₁ hl hload₁
  have hX1val : (pairFun l (edgeVec p X₁) : ℝ) ≤ -(X₁.card : ℝ) := by
    rw [pairFun_edgeVec, Int.cast_sum]
    have := Finset.sum_le_sum (fun e he => (Int.cast_le (R := ℝ)).mpr (hneg e he))
    simpa using this
  have hsplit : (pairFun l (edgeVec p (X₀ ∪ X₁)) : ℝ) =
      (pairFun l (edgeVec p X₀) : ℝ) + (pairFun l (edgeVec p X₁) : ℝ) := by
    rw [pairFun_edgeVec, pairFun_edgeVec, pairFun_edgeVec, Finset.sum_union h01]
    push_cast
    ring
  have hM₀ := hsub (G.edgeFinset \ (A ∪ X₀)) Finset.sdiff_subset
  have hM₁ := hsub (G.edgeFinset \ (A ∪ (X₀ ∪ X₁))) Finset.sdiff_subset
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have e₀ : |(pairFun l (edgeVec p X₀) : ℝ)| ≤ τ * M :=
    b₀.trans (mul_le_mul_of_nonneg_left hM₀ hτ)
  have e₁ : |(pairFun l (edgeVec p (X₀ ∪ X₁)) : ℝ)| ≤ τ * M :=
    b₁.trans (mul_le_mul_of_nonneg_left hM₁ hτ)
  rw [hsplit] at e₁
  have := abs_le.mp e₀
  have := abs_le.mp e₁
  linarith

/-- **Packaged in the consumer's reserve vocabulary.** If `X₀` is an
anti-edgeful reserve with degree bound `d₀` and `X₁` is a set of more than
`2 τ M` g-internal edges of degree at most `d₁` (F0 version), then both `X₀` and
`X₀ ∪ X₁` are anti-edgeful reserves with degree bound `d₀ + d₁`, disjoint from a
decomposable `A`, but at most one of them admits `τ`-precise weights on its
main graph. -/
theorem F0_reserve_properties_do_not_determine_preparability (p : V → Fin 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (A X₀ X₁ : Finset (Sym2 V))
    [DecidableRel (ReserveCoverDown.reserveGraph X₀).Adj]
    [DecidableRel (ReserveCoverDown.reserveGraph (X₀ ∪ X₁)).Adj]
    (hA : A ⊆ G.edgeFinset) (hX₀ : X₀ ⊆ G.edgeFinset) (hX₁ : X₁ ⊆ G.edgeFinset)
    (hAX₀ : Disjoint A X₀) (hAX₁ : Disjoint A X₁) (h01 : Disjoint X₀ X₁)
    (hG : IsIntDiv p TypedApplicationLinks.F0 G.edgeFinset)
    (hAdec : HasDecomp p TypedApplicationLinks.F0 A)
    (hint : ∀ e ∈ X₁, ∀ a b, e = s(a, b) → p a = p b)
    {α d₀ d₁ τ : ℝ} (hτ : 0 ≤ τ) (hres₀ : AntiEdgeful p TypedApplicationLinks.F0
      (ReserveCoverDown.reserveGraph X₀) α)
    (hdeg₀ : DegBounded X₀ d₀) (hdeg₁ : DegBounded X₁ d₁)
    (hbig : 8 * τ * G.edgeFinset.card < X₁.card) :
    AntiEdgeful p TypedApplicationLinks.F0 (ReserveCoverDown.reserveGraph (X₀ ∪ X₁)) α ∧
    DegBounded (X₀ ∪ X₁) (d₀ + d₁) ∧
    ¬ ((∃ ψ₀ : Finset V → ℝ, ∀ e ∈ G.edgeFinset \ (A ∪ X₀),
          |edgeLoad p TypedApplicationLinks.F0
            (G.deleteEdges ((A ∪ X₀ : Finset (Sym2 V)) : Set (Sym2 V))) ψ₀ e - 1| ≤ τ) ∧
       (∃ ψ₁ : Finset V → ℝ, ∀ e ∈ G.edgeFinset \ (A ∪ (X₀ ∪ X₁)),
          |edgeLoad p TypedApplicationLinks.F0
            (G.deleteEdges ((A ∪ (X₀ ∪ X₁) : Finset (Sym2 V)) : Set (Sym2 V))) ψ₁ e - 1| ≤ τ)) := by
  refine ⟨antiEdgeful_mono p _ Finset.subset_union_left hres₀,
    degBounded_union hdeg₀ hdeg₁, ?_⟩
  rintro ⟨⟨ψ₀, h₀⟩, ⟨ψ₁, h₁⟩⟩
  have hper : ∀ e : Sym2 V, |(pairFun (groupPair g0) (pairVec p e) : ℝ)| ≤ 4 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      have key : ∀ i j : Fin 2, |groupPair g0 i j + groupPair g0 j i| ≤ 4 := by decide
      rw [← Int.cast_abs]
      have : (pairFun (groupPair g0) (pairVec p s(a, b))) =
          groupPair g0 (p a) (p b) + groupPair g0 (p b) (p a) := by
        simp only [pairFun, pairVec, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite,
          mul_one, mul_zero]
        congr 1
        · rw [Finset.sum_eq_single (p a) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
          simp
        · rw [Finset.sum_eq_single (p b) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
          simp
      rw [this]
      exact_mod_cast key _ _
  have hM : ∑ e ∈ G.edgeFinset, |(pairFun (groupPair g0) (pairVec p e) : ℝ)| ≤
      4 * G.edgeFinset.card := by
    calc _ ≤ ∑ _e ∈ G.edgeFinset, (4 : ℝ) := Finset.sum_le_sum fun e _ => hper e
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hneg : ∀ e ∈ X₁, pairFun (groupPair g0) (pairVec p e) ≤ -1 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab := hint _ he a b rfl
      have key : ∀ i : Fin 2, groupPair g0 i i + groupPair g0 i i ≤ -1 := by decide
      have : (pairFun (groupPair g0) (pairVec p s(a, b))) =
          groupPair g0 (p a) (p b) + groupPair g0 (p b) (p a) := by
        simp only [pairFun, pairVec, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite,
          mul_one, mul_zero]
        congr 1
        · rw [Finset.sum_eq_single (p a) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
          simp
        · rw [Finset.sum_eq_single (p b) (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
          simp
      rw [this, hab]
      exact key _
  have hbig' : 2 * τ * ∑ e ∈ G.edgeFinset, |(pairFun (groupPair g0) (pairVec p e) : ℝ)| <
      X₁.card := by
    nlinarith
  exact not_both_preparable p _ G A X₀ X₁ hA hX₀ hX₁ hAX₀ hAX₁ h01 hG hAdec annihilates_F0
    hneg hτ hbig' ψ₀ ψ₁ h₀ h₁

end PartitionedTriangleAbsorption.TypedLoadReserveObstruction
