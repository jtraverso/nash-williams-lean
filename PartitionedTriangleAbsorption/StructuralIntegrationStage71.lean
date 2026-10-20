/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.StructuralAbsorberStage70
public import PartitionedTriangleAbsorption.StructuralF3.Main
public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Hierarchy

/-! # Enumerating the concrete structural refiner without changing its pieces

This module transports selections and incidence exactly. The final producer
uses the constructed refiner, rather than a supplied-library hypothesis.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralIntegrationStage71

open Finset TypedApplicationLinks AntiEdgeSelection StructuralAbsorberStage70

variable {V I : Type*} [Fintype V] [DecidableEq V]

noncomputable def libraryIndex (s : Finset I) (i : Fin s.card) : I :=
  (s.equivFin.symm i : I)

theorem libraryIndex_mem (s : Finset I) (i : Fin s.card) : libraryIndex s i ∈ s :=
  (s.equivFin.symm i).2

theorem libraryIndex_injective (s : Finset I) : Function.Injective (libraryIndex s) :=
  fun _ _ h => s.equivFin.symm.injective (Subtype.ext h)

noncomputable def enumPiece (s : Finset I) (B : I → Finset (Sym2 V))
    (i : ℕ) : Finset (Sym2 V) :=
  if hi : i < s.card then B (libraryIndex s ⟨i, hi⟩) else ∅

omit [Fintype V] in
theorem enumPiece_sum (s : Finset I) (B : I → Finset (Sym2 V)) (v : V) :
    ∑ i ∈ range s.card, incidentLoad (enumPiece s B i) v =
      ∑ j ∈ s, incidentLoad (B j) v := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin s.card, incidentLoad (enumPiece s B i.val) v =
        ∑ i : Fin s.card, incidentLoad (B (libraryIndex s i)) v := by
      apply sum_congr rfl
      intro i _
      simp [enumPiece, i.isLt]
    _ = ∑ j ∈ s, incidentLoad (B j) v := by
      rw [← sum_coe_sort s]
      exact Equiv.sum_comp s.equivFin.symm (fun j => incidentLoad (B j) v)

omit [Fintype V] in
theorem enumPiece_refines (cls : V → Fin 4) (s : Finset I)
    (B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V))
    (href : RefinerAssembly.RefinesReserve (p := cls) (F := F3) s B X R) :
    RefinerAssembly.RefinesReserve (p := cls) (F := F3) (range s.card)
      (enumPiece s B) X R := by
  classical
  intro L hLX hdiv
  obtain ⟨J, hJs, hdis, hcover⟩ := href L hLX hdiv
  let T := (range s.card).filter fun i =>
    ∃ hi : i < s.card, libraryIndex s ⟨i, hi⟩ ∈ J
  have hT (i : ℕ) : i ∈ T ↔ ∃ hi : i < s.card, libraryIndex s ⟨i, hi⟩ ∈ J := by
    simp only [T, mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  refine ⟨T, filter_subset _ _, ?_, ?_⟩
  · intro i hi j hj hij
    obtain ⟨hi', hiJ⟩ := (hT i).mp hi
    obtain ⟨hj', hjJ⟩ := (hT j).mp hj
    have hne : libraryIndex s ⟨i, hi'⟩ ≠ libraryIndex s ⟨j, hj'⟩ := by
      intro he
      exact hij (congrArg Fin.val (libraryIndex_injective s he))
    change Disjoint (enumPiece s B i) (enumPiece s B j)
    simpa only [enumPiece, dite_eq_left hi', dite_eq_left hj'] using hdis hiJ hjJ hne
  · rw [← hcover]
    ext e
    simp only [mem_biUnion]
    constructor
    · rintro ⟨i, hi, he⟩
      obtain ⟨hi', hiJ⟩ := (hT i).mp hi
      exact ⟨libraryIndex s ⟨i, hi'⟩, hiJ, by
        simpa only [enumPiece, dite_eq_left hi'] using he⟩
    · rintro ⟨j, hj, he⟩
      let k := s.equivFin ⟨j, hJs hj⟩
      have hk : libraryIndex s k = j := by
        exact congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨j, hJs hj⟩)
      refine ⟨k.val, (hT k.val).mpr ⟨k.isLt, by simpa only [hk] using hj⟩, ?_⟩
      simpa only [enumPiece, dite_eq_left k.isLt, hk] using he

theorem card_le_order_mul_degree (E : Finset (Sym2 V)) (d : ℝ)
    (hE : DegBounded E d) : (E.card : ℝ) ≤ Fintype.card V * d := by
  classical
  have hcover : E ⊆ univ.biUnion (fun v : V => E.filter fun e => v ∈ e) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact mem_biUnion.mpr ⟨a, mem_univ _, mem_filter.mpr ⟨he, by simp⟩⟩
  have hc : E.card ≤ ∑ v : V, incidentLoad E v :=
    (card_le_card hcover).trans card_biUnion_le
  have hcR : (E.card : ℝ) ≤ ∑ v : V, (incidentLoad E v : ℝ) := by
    exact_mod_cast hc
  apply hcR.trans
  calc
    ∑ v : V, (incidentLoad E v : ℝ) ≤ ∑ _v : V, d := sum_le_sum fun v _ => hE v
    _ = Fintype.card V * d := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- A concrete producer: the refiner and the entire private family are constructed
before the universally quantified leftover. The displayed scalar inequalities
are ordinary parameter budgets, not refiner or absorber existence premises. -/
theorem producer_explicit (cls : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    (γ lam rho δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hsize : ∀ i, γ * Fintype.card V ≤
      ((ClassRepresentativesStage65.classSet cls i).card : ℝ))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hlamγ : 32 * lam ≤ γ)
    (hrho : 0 < rho) (hscale : 2 ^ 42 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (h1 : (2 * (1050 : ℝ) + 3) * (2 * δ * Fintype.card V) <
      γ ^ 2 * Fintype.card V / 4)
    (h2 : 2 ≤ γ ^ 2 * Fintype.card V / 4)
    (h3 : 56 * (2 * δ * Fintype.card V) ≤ γ ^ 3 * Fintype.card V / 8)
    (h4 : 4 * (2 * δ * Fintype.card V) ≤ γ ^ 2 * Fintype.card V / 4)
    (h5 : (SignedHinge.absorberBudget 6 (12 * 1050) : ℝ) <
      γ ^ 2 * Fintype.card V / 8)
    (h6 : (2 ^ 21 : ℝ) * SignedHinge.absorberBudget 6 (12 * 1050) <
      γ ^ 3 * Fintype.card V / 64)
    (hfixed : (PrivateTemplateStage69.templateConst 1050 : ℝ) + 2 * 1050 ≤
      δ * Fintype.card V / 4)
    (hledger : 8 * lam + 2 * rho ≤ δ)
    (hroots : 4200 * (PrivateTemplateStage69.templateConst 1050 : ℝ) * lam ≤ δ / 4)
    (hedges : 8 * lam + 2 * rho +
      2 ^ 35 * (PrivateTemplateStage69.templateConst 1050 : ℝ) * rho ≤ γ * δ / 4)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp cls F3 A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
      ∀ L ⊆ X, IsIntDiv cls F3 L → HasDecomp cls F3 (A ∪ L) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set C : ℝ := (PrivateTemplateStage69.templateConst 1050 : ℝ) with hC
  have hnpos : 0 < n := by
    have : 1 ≤ rho * n := hn1
    nlinarith
  obtain ⟨s, B, R, hRG, hRX, href, hpieces, hRd, hcard, hinc⟩ :=
    StructuralF3.exists_structural_refiner cls G hG γ lam rho hsize
      hlam hlam64 hlamγ hrho hscale hn1 hn2 X hXG hX
  let P := enumPiece s B
  have hYP : DegBounded (X ∪ R) ((2 * rho + 8 * lam) * n) := by
    have h := StructuralF3.degBounded_union hX hRd
    convert h using 1
    ring
  have hY : DegBounded (X ∪ R) (δ * n) := fun v =>
    (hYP v).trans (by nlinarith)
  have hpc (i : ℕ) (hi : i < s.card) : P i = B (libraryIndex s ⟨i, hi⟩) := by
    simp only [P, enumPiece, dite_eq_left hi]
  have hprops (i : ℕ) (hi : i < s.card) := hpieces _ (libraryIndex_mem s ⟨i, hi⟩)
  have hload (v : V) : (PrivateTemplateStage69.rootLoad P s.card v : ℝ) ≤
      4200 * lam * n := by
    have h := rootLoad_le_incidence_sum P s.card v
    have heq := enumPiece_sum s B v
    change ∑ i ∈ range s.card, incidentLoad (P i) v = _ at heq
    rw [heq] at h
    have hr : (PrivateTemplateStage69.rootLoad P s.card v : ℝ) ≤
        ((∑ j ∈ s, incidentLoad (B j) v : ℕ) : ℝ) := by exact_mod_cast h
    exact hr.trans (hinc v)
  have hD : max (δ * n) (δ * n + C) + C * (4200 * lam * n) + 2 * (1050 : ℝ) ≤
      2 * δ * n := by
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    rw [max_eq_right (by linarith)]
    have hr := mul_le_mul_of_nonneg_right hroots hnpos.le
    nlinarith
  have hcount : 4 * (((X ∪ R).card : ℝ) + (s.card : ℝ) * C) ≤ δ * n * γ * n := by
    have hy := card_le_order_mul_degree (X ∪ R) ((2 * rho + 8 * lam) * n) hYP
    have hc := mul_le_mul_of_nonneg_right hcard (show 0 ≤ C by rw [hC]; positivity)
    have he := mul_le_mul_of_nonneg_right hedges (sq_nonneg n)
    nlinarith
  exact universal_from_library 1050 cls G hG γ (δ * n) (2 * δ * n)
    (4200 * lam * n) (δ * n) hγ (mul_pos hδ hnpos) hsize h1 h2 h3 h4 h5 h6
    X R hRX hRG hY hD s.card P (enumPiece_refines cls s B X R href)
    (fun i hi => by rw [hpc i hi]; exact (hprops i hi).1)
    (fun i hi => by rw [hpc i hi]; exact (hprops i hi).1.trans (union_subset hXG hRG))
    (fun i hi => by rw [hpc i hi]; exact (hprops i hi).2.2)
    (fun i hi => by rw [hpc i hi]; exact (hprops i hi).2.1)
    hload hcount

/-- All coefficients and the order threshold are fixed before the host and its
reserve. This is a complete-four-class F3 producer, not general 13.16. -/
theorem exists_fixed_scales (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ δ lam rho : ℝ, 0 < δ ∧ 0 < lam ∧ 0 < rho ∧ δ ≤ γ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ a b, G.Adj a b ↔ cls a ≠ cls b) →
        (∀ i, γ * Fintype.card V ≤
          ((ClassRepresentativesStage65.classSet cls i).card : ℝ)) →
        ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
          DegBounded X (2 * rho * Fintype.card V) →
          ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
            HasDecomp cls F3 A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
            ∀ L ⊆ X, IsIntDiv cls F3 L → HasDecomp cls F3 (A ∪ L) := by
  let δ := PrivateTemplateStage69.hierDelta γ 1050
  let C : ℝ := PrivateTemplateStage69.templateConst 1050
  let Bud : ℝ := SignedHinge.absorberBudget 6 (12 * 1050)
  let lam := γ * δ / (2 ^ 24 * (C + 1))
  let rho := lam ^ 2 / 2 ^ 43
  have hδ : 0 < δ := by dsimp [δ, PrivateTemplateStage69.hierDelta]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBud : 0 ≤ Bud := by dsimp [Bud]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hδeq : 4096 * (1050 + 1 : ℝ) * δ = γ ^ 3 := by
    dsimp [δ, PrivateTemplateStage69.hierDelta]
    field_simp
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hγ3 : 0 < γ ^ 3 := by positivity
  have hγ32 : γ ^ 3 ≤ γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hγ21 : γ ^ 2 ≤ 1 := by nlinarith
  have hγ2γ : γ ^ 2 ≤ γ := by nlinarith
  have hδγ : δ ≤ γ := by nlinarith only [hδeq, hγ32, hγ2γ, hδ.le]
  have hlamEq : (2 ^ 24 : ℝ) * (C + 1) * lam = γ * δ := by
    dsimp [lam]
    field_simp
  have hrhoEq : (2 ^ 43 : ℝ) * rho = lam ^ 2 := by dsimp [rho]; ring
  have hγδ : γ * δ ≤ δ := mul_le_of_le_one_left hδ.le hγ1
  have hδsmall : δ ≤ 1 / 4096 := by nlinarith only [hδeq, hγ32, hγ21, hδ.le]
  have hlam64 : lam ≤ 1 / 64 := by
    norm_num at hlamEq
    nlinarith only [hlamEq, hC, hlam.le, hγδ, hδsmall]
  have hγδ' : γ * δ ≤ γ := mul_le_of_le_one_right hγ.le (by linarith only [hδsmall])
  have hlamγ : 32 * lam ≤ γ := by
    norm_num at hlamEq
    nlinarith only [hlamEq, hC, hlam.le, hγδ']
  have hscale : (2 ^ 42 : ℝ) * rho ≤ lam ^ 2 := by
    nlinarith only [hrhoEq, hrho.le]
  obtain ⟨hledger, hroots, hedges⟩ := compatible_scales C γ δ lam rho hC hδ.le hγ1
    hlam.le (by linarith) hlamEq.le hrhoEq.le
  let q1 := 1 / rho
  let q2 := 256 / lam
  let q3 := 8 / γ ^ 2
  let q4 := 8 * (Bud + 1) / γ ^ 2
  let q5 := 64 * 2 ^ 21 * (Bud + 1) / γ ^ 3
  let q6 := 4 * (C + 2 * 1050 + 1) / δ
  obtain ⟨N, hN⟩ := exists_nat_gt (q1 + q2 + q3 + q4 + q5 + q6)
  refine ⟨δ, lam, rho, hδ, hlam, hrho, hδγ, N, ?_⟩
  intro V _ _ hn cls G _ hG hsize X hXG hX
  set n : ℝ := (Fintype.card V : ℝ)
  have hsum : q1 + q2 + q3 + q4 + q5 + q6 < n :=
    hN.trans_le (by change (N : ℝ) ≤ (Fintype.card V : ℝ); exact_mod_cast hn)
  have hp1 : 0 ≤ q1 := by dsimp [q1]; positivity
  have hp2 : 0 ≤ q2 := by dsimp [q2]; positivity
  have hp3 : 0 ≤ q3 := by dsimp [q3]; positivity
  have hp4 : 0 ≤ q4 := by dsimp [q4]; positivity
  have hp5 : 0 ≤ q5 := by dsimp [q5]; positivity
  have hp6 : 0 < q6 := by dsimp [q6]; positivity
  have hnpos : 0 < n := by linarith
  have hn1 : 1 ≤ rho * n := by
    have hh : q1 ≤ n := by linarith
    dsimp [q1] at hh
    rw [div_le_iff₀ hrho] at hh
    nlinarith only [hh]
  have hn2 : 256 ≤ lam * n := by
    have hh : q2 ≤ n := by linarith
    dsimp [q2] at hh
    rw [div_le_iff₀ hlam] at hh
    nlinarith only [hh]
  have hn3 : 8 ≤ γ ^ 2 * n := by
    have hh : q3 ≤ n := by linarith
    dsimp [q3] at hh
    rw [div_le_iff₀ hγ2] at hh
    nlinarith only [hh]
  have hn4 : 8 * (Bud + 1) ≤ γ ^ 2 * n := by
    have hh : q4 ≤ n := by linarith
    dsimp [q4] at hh
    rw [div_le_iff₀ hγ2] at hh
    nlinarith only [hh]
  have hn5 : 64 * 2 ^ 21 * (Bud + 1) ≤ γ ^ 3 * n := by
    have hh : q5 ≤ n := by linarith
    dsimp [q5] at hh
    rw [div_le_iff₀ hγ3] at hh
    nlinarith only [hh]
  have hn6 : C + 2 * 1050 ≤ δ * n / 4 := by
    have hh : q6 ≤ n := by linarith
    dsimp [q6] at hh
    rw [div_le_iff₀ hδ] at hh
    nlinarith only [hh]
  have hγ32n := mul_le_mul_of_nonneg_right hγ32 hnpos.le
  have hδeqn := congrArg (fun z : ℝ => z * n) hδeq
  exact producer_explicit cls G hG γ lam rho δ hγ hδ hsize
    hlam hlam64 hlamγ hrho hscale hn1 hn2
    (by nlinarith only [hδeqn, hγ32n, mul_pos hγ2 hnpos])
    (by linarith)
    (by nlinarith only [hδeqn, mul_pos hγ3 hnpos])
    (by nlinarith only [hδeqn, hγ32n, mul_pos hγ3 hnpos])
    (by change Bud < _; linarith)
    (by change (2 ^ 21 : ℝ) * Bud < _; linarith)
    hn6 hledger hroots hedges X hXG hX

/-- An arbitrarily small final absorber coefficient can be prescribed before
the graph. A weaker class lower bound pays it without changing the host. -/
theorem exists_fixed_scales_below (γ ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hζ : 0 < ζ) :
    ∃ δ lam rho : ℝ, 0 < δ ∧ 0 < lam ∧ 0 < rho ∧ δ ≤ ζ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ a b, G.Adj a b ↔ cls a ≠ cls b) →
        (∀ i, γ * Fintype.card V ≤
          ((ClassRepresentativesStage65.classSet cls i).card : ℝ)) →
        ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
          DegBounded X (2 * rho * Fintype.card V) →
          ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
            HasDecomp cls F3 A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
            ∀ L ⊆ X, IsIntDiv cls F3 L → HasDecomp cls F3 (A ∪ L) := by
  obtain ⟨δ, lam, rho, hδ, hlam, hrho, hδγ, N, hN⟩ :=
    exists_fixed_scales (min γ ζ) (lt_min hγ hζ) ((min_le_left _ _).trans hγ1)
  refine ⟨δ, lam, rho, hδ, hlam, hrho, hδγ.trans (min_le_right _ _), N, ?_⟩
  intro V _ _ hn cls G _ hG hsize X hXG hX
  exact hN V hn cls G hG (fun i =>
    (mul_le_mul_of_nonneg_right (min_le_left γ ζ) (Nat.cast_nonneg (Fintype.card V))).trans
      (hsize i)) X hXG hX

end PartitionedTriangleAbsorption.StructuralIntegrationStage71
