/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Local
public import Mathlib.Tactic.Ring

/-! # BlowupB.Deletions — bounded-cost certificates after deletions

**Theorem** (`physDivCost_local`). For every family `F` of triangle types and every `K` there is
a constant `C = C(F, K)` such that: whenever `G` satisfies the local hypothesis `LocalHyp` with
respect to `5` representatives per class and a vertex predicate `W` covering the vertices of `E`
(every edge of `G` is an allowed pair; every representative is adjacent to every good vertex with
which it forms an allowed pair — all other edges may be deleted), every integrally `F`-divisible
`E ⊆ E(G)` with `|E| ≤ K` has a physical certificate of cost at most `C`.

The constant depends only on `F` and `K`, never on the host. Corollary for complete blowups:
`physDivCost_complete`.

Cost bookkeeping (`physCostZ_local_core`): with `L = |E| + 3 C₁` and `C_g = 4 C₂ L`,
`cost ≤ 8 (L + 3 C_g) + C₁ + C_g`, where `C₁` bounds the edge-count representation and `C₂` the
degree representations (finite boxes, `exists_rep_bound`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} {W : V → Prop}

/-- The core estimate, with explicit constants. -/
theorem physCostZ_local_core [DecidableRel G.Adj] {R : Reps p 5} (hL : LocalHyp p F G R W)
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset)
    (hW : ∀ e ∈ E, ∀ x ∈ e, W x) (hdiv : IsIntDiv p F E) {C1 L C2 : ℤ} (hC2 : 0 ≤ C2)
    (hc : ∃ c : Multiset (Fin t) → ℤ,
      edgeVec p E = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ ∑ τ ∈ F, |c τ| ≤ C1)
    (hL1 : (E.card : ℤ) + 3 * C1 ≤ L)
    (hdeg : ∀ (x : Fin t → ℤ) (i : Fin t), (∀ j, |x j| ≤ 2 * L) →
      (∃ d : Multiset (Fin t) → ℤ, x = ∑ τ ∈ F with i ∈ τ, d τ • typeDegVec τ i) →
      ∃ d : Multiset (Fin t) → ℤ, x = ∑ τ ∈ F with i ∈ τ, d τ • typeDegVec τ i ∧
        ∑ τ ∈ F with i ∈ τ, |d τ| ≤ C2) :
    PhysCostZ p F G (indZ E) (8 * (L + 3 * (4 * C2 * L)) + C1 + 4 * C2 * L) := by
  set Cg : ℤ := 4 * C2 * L with hCg
  obtain ⟨c, hcE, hcC⟩ := hc
  -- (a) copies of the types, on the representatives
  have hT : ∀ τ : Multiset (Fin t), ∃ T : Finset V, τ ∈ F →
      IsCopy p F G T ∧ triType p T = τ ∧ ∀ x ∈ T, Good R W x := by
    intro τ
    by_cases hτ : τ ∈ F
    · obtain ⟨T, h1, h2, h3⟩ := exists_copy_of_type_local hL hτ (hF3 τ hτ)
      exact ⟨T, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hτ⟩
  choose T hT using hT
  have hzC : PhysCostZ p F G (∑ τ ∈ F, c τ • indZ (triEdges (T τ))) (∑ τ ∈ F, |c τ|) :=
    (PhysCostZ.sum F _ (fun τ => |c τ| * 1) fun τ hτ =>
      (physCostZ_of_isCopy (hT τ hτ).1).smul _).mono
      (le_of_eq (sum_congr rfl fun τ _ => mul_one _))
  have hzG : OnGood R W (∑ τ ∈ F, c τ • indZ (triEdges (T τ))) :=
    OnGood.sum _ _ fun τ hτ => (onGood_triEdges (hT τ hτ).2.2).smul _
  have hzE : edgeVecZ p (∑ τ ∈ F, c τ • indZ (triEdges (T τ))) = edgeVec p E := by
    rw [edgeVecZ_sum, hcE]
    refine sum_congr rfl fun τ hτ => ?_
    rw [edgeVecZ_smul, edgeVecZ_indZ, edgeVec_triEdges p (hT τ hτ).1.1.card_eq, (hT τ hτ).2.1]
  set z := ∑ τ ∈ F, c τ • indZ (triEdges (T τ)) with hz
  set u := indZ E - z with hu
  have huE : edgeVecZ p u = 0 := by rw [hu, edgeVecZ_sub, edgeVecZ_indZ, hzE, sub_self]
  have huA : AggDivZ p F u :=
    ((aggDivZ_indZ_iff p F E).mpr hdiv).sub (aggDivZ_of_physDivZ (physDivZ_of_physCostZ hzC))
  have huG : OnGood R W u := (onGood_indZ hW).sub hzG
  have hl1u : l1 u ≤ L := by
    have h1 := l1_sub_le (indZ E) z
    have h2 := l1_le_of_physCostZ hzC
    rw [l1_indZ] at h1
    linarith
  -- (b) degree gadgets with bounded coefficients
  have hΓ : ∀ v : V, ∃ Γ : Sym2 V → ℤ,
      PhysCostZ p F G Γ (2 * C2 * ∑ j, |degVecZ p u v j|) ∧ OnGood R W Γ ∧
      edgeVecZ p Γ = 0 ∧ ∀ w, degVecZ p Γ w = (if w = v then degVecZ p u v else 0) -
        (if w = R.rep (p v) 0 then degVecZ p u v else 0) := by
    intro v
    have hnn : 0 ≤ 2 * C2 * ∑ j, |degVecZ p u v j| :=
      mul_nonneg (mul_nonneg (by norm_num) hC2) (sum_nonneg fun _ _ => abs_nonneg _)
    by_cases hv : v = R.rep (p v) 0
    · refine ⟨0, (PhysCostZ.zero p F G).mono hnn, OnGood.zero, edgeVecZ_zero p, fun w => ?_⟩
      rw [degVecZ_zero, ← hv, sub_self]
    by_cases hd0 : degVecZ p u v = 0
    · refine ⟨0, (PhysCostZ.zero p F G).mono hnn, OnGood.zero, edgeVecZ_zero p, fun w => ?_⟩
      rw [degVecZ_zero, hd0]
      simp
    have hgv : Good R W v := good_of_degVecZ_ne_zero huG hd0
    obtain ⟨d, hdv, hdC⟩ := hdeg (degVecZ p u v) (p v)
      (fun j => (abs_degVecZ_le p u v j).trans (by linarith)) (huA.2 v)
    have hg : ∀ τ : Multiset (Fin t), ∃ g : Sym2 V → ℤ, τ ∈ F.filter (p v ∈ ·) →
        PhysCostZ p F G g 2 ∧ OnGood R W g ∧ edgeVecZ p g = 0 ∧ ∀ w, degVecZ p g w =
          (if w = v then typeDegVec τ (p v) else 0) -
            (if w = R.rep (p v) 0 then typeDegVec τ (p v) else 0) := by
      intro τ
      by_cases hτ : τ ∈ F.filter (p v ∈ ·)
      · obtain ⟨hτF, hτv⟩ := mem_filter.mp hτ
        obtain ⟨g, h1, h2, h3, h4⟩ := exists_deg_gadget_local hL hF3 hv hgv hτF hτv
        exact ⟨g, fun _ => ⟨h1, h2, h3, h4⟩⟩
      · exact ⟨0, fun h => absurd h hτ⟩
    choose g hg using hg
    refine ⟨∑ τ ∈ F with p v ∈ τ, d τ • g τ, ?_,
      OnGood.sum _ _ fun τ hτ => ((hg τ hτ).2.1).smul _, ?_, fun w => ?_⟩
    · refine (PhysCostZ.sum _ _ (fun τ => |d τ| * 2) fun τ hτ => ((hg τ hτ).1).smul _).mono ?_
      have h1 := one_le_sum_abs_of_ne_zero hd0
      calc ∑ τ ∈ F with p v ∈ τ, |d τ| * 2 = 2 * ∑ τ ∈ F with p v ∈ τ, |d τ| := by
            rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
        _ ≤ 2 * C2 := by linarith
        _ ≤ 2 * C2 * ∑ j, |degVecZ p u v j| :=
            le_mul_of_one_le_right (mul_nonneg (by norm_num) hC2) h1
    · rw [edgeVecZ_sum]
      exact sum_eq_zero fun τ hτ => by rw [edgeVecZ_smul, (hg τ hτ).2.2.1, smul_zero]
    · have hLw : degVecZ p (∑ τ ∈ F with p v ∈ τ, d τ • g τ) w =
          ∑ τ ∈ F with p v ∈ τ, d τ • ((if w = v then typeDegVec τ (p v) else 0) -
            (if w = R.rep (p v) 0 then typeDegVec τ (p v) else 0)) := by
        rw [degVecZ_sum]
        exact sum_congr rfl fun τ hτ => by rw [degVecZ_smul, (hg τ hτ).2.2.2 w]
      rw [hLw, hdv]
      by_cases h1 : w = v
      · rw [h1]
        simp [hv]
      · by_cases h2 : w = R.rep (p v) 0
        · have h1' : R.rep (p v) 0 ≠ v := fun h => h1 (h2.trans h)
          rw [h2]
          simp [h1']
        · simp [h1, h2]
  choose Γ hΓC hΓG hΓE hΓD using hΓ
  have hΓP : PhysCostZ p F G (∑ v, Γ v) (∑ v, 2 * C2 * ∑ j, |degVecZ p u v j|) :=
    PhysCostZ.sum _ _ _ fun v _ => hΓC v
  have hΓbound : ∑ v, 2 * C2 * ∑ j, |degVecZ p u v j| ≤ Cg := by
    rw [← mul_sum]
    have hX : ∑ v, ∑ j, |degVecZ p u v j| ≤ 2 * L := by
      have := sum_abs_degVecZ_le p u; linarith
    calc 2 * C2 * ∑ v, ∑ j, |degVecZ p u v j| ≤ 2 * C2 * (2 * L) :=
          mul_le_mul_of_nonneg_left hX (mul_nonneg (by norm_num) hC2)
      _ = Cg := by rw [hCg]; ring
  set u' := u - ∑ v, Γ v with hu'
  have hu'E : edgeVecZ p u' = 0 := by
    rw [hu', edgeVecZ_sub, edgeVecZ_sum, huE, sum_eq_zero fun v _ => hΓE v, sub_zero]
  have hu'D : ∀ w, degVecZ p u' w = 0 := by
    intro w
    have hS : ∑ v, degVecZ p (Γ v) w = degVecZ p u w -
        ∑ v ∈ univ.filter (fun v => w = R.rep (p v) 0), degVecZ p u v := by
      rw [sum_congr rfl fun v _ => hΓD v w, sum_sub_distrib, Finset.sum_ite_eq,
        if_pos (mem_univ _), sum_filter]
    have hF : ∑ v ∈ univ.filter (fun v => w = R.rep (p v) 0), degVecZ p u v = 0 := by
      by_cases hw : w = R.rep (p w) 0
      · have hfil : univ.filter (fun v => w = R.rep (p v) 0) =
            univ.filter (fun v => p v = p w) := by
          ext v
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · intro h; rw [h, R.cls]
          · intro h; rw [h]; exact hw
        rw [hfil]
        funext j
        rw [Finset.sum_apply, sum_degVecZ_class, huE]
        rfl
      · refine sum_eq_zero fun v hv' => absurd ?_ hw
        have h := (mem_filter.mp hv').2
        have hpw : p w = p v := by rw [h, R.cls]
        rw [hpw]; exact h
    rw [hu', degVecZ_sub, degVecZ_sum, hS, hF, sub_zero, sub_self]
  have hOnG : OnG G u' := by
    rw [hu', hu]
    exact ((onG_indZ hE).sub (onG_of_physDivZ (physDivZ_of_physCostZ hzC))).sub
      (onG_of_physDivZ (physDivZ_of_physCostZ hΓP))
  have hOnGood : OnGood R W u' := huG.sub (OnGood.sum _ _ fun v _ => hΓG v)
  have hu'C := physCostZ_of_zeroDeg_local hL hOnG hOnGood hu'E hu'D
  have hl1u' : l1 u' ≤ L + 3 * Cg := by
    have h1 := l1_sub_le u (∑ v, Γ v)
    have h2 := l1_le_of_physCostZ hΓP
    linarith
  have hsplit : u' + z + ∑ v, Γ v = indZ E := by rw [hu', hu]; abel
  exact (((hu'C.add hzC).add hΓP).congr hsplit).mono (by linarith)

end Core

/-! ### Uniform constants -/

/-- **Bounded-cost certificates after deletions.** The constant depends only on `F` and `K`. -/
theorem physDivCost_local {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (K : ℕ) :
    ∃ C : ℤ, ∀ {V : Type} [Fintype V] [DecidableEq V] {p : V → Fin t} {G : SimpleGraph V}
      [DecidableRel G.Adj] {W : V → Prop} {R : Reps p 5}, LocalHyp p F G R W →
      ∀ {E : Finset (Sym2 V)}, E ⊆ G.edgeFinset → (∀ e ∈ E, ∀ x ∈ e, W x) →
        IsIntDiv p F E → E.card ≤ K → PhysDivCost p F G E C := by
  obtain ⟨C1, hC1, hrep1⟩ := exists_rep_bound F typeEdgeVec (boxMat (t := t) (2 * (K : ℤ)))
  have hC2 : ∀ i : Fin t, ∃ C : ℤ, 0 ≤ C ∧ ∀ x ∈ boxVec (t := t) (2 * ((K : ℤ) + 3 * C1)),
      (∃ c : Multiset (Fin t) → ℤ, x = ∑ τ ∈ F with i ∈ τ, c τ • typeDegVec τ i) →
      ∃ c : Multiset (Fin t) → ℤ, x = ∑ τ ∈ F with i ∈ τ, c τ • typeDegVec τ i ∧
        ∑ τ ∈ F with i ∈ τ, |c τ| ≤ C :=
    fun i => exists_rep_bound _ (fun τ => typeDegVec τ i) _
  choose C2f hC2f0 hC2f using hC2
  have hC2 : 0 ≤ ∑ i, C2f i := sum_nonneg fun i _ => hC2f0 i
  refine ⟨8 * (((K : ℤ) + 3 * C1) + 3 * (4 * (∑ i, C2f i) * ((K : ℤ) + 3 * C1))) + C1 +
    4 * (∑ i, C2f i) * ((K : ℤ) + 3 * C1), ?_⟩
  intro V _ _ p G _ W R hL E hE hW hdiv hK
  rw [physDivCost_iff_physCostZ]
  have hKc : (E.card : ℤ) ≤ K := by exact_mod_cast hK
  refine physCostZ_local_core hL hF3 hE hW hdiv hC2 ?_ (by linarith) ?_
  · have hbox : edgeVec p E ∈ boxMat (t := t) (2 * (K : ℤ)) := by
      rw [mem_boxMat]
      intro i j
      rw [← edgeVecZ_indZ]
      refine (abs_edgeVecZ_le p _ i j).trans ?_
      rw [l1_indZ]
      linarith
    exact hrep1 _ hbox hdiv.1
  · intro x i hx hlat
    obtain ⟨d, hd, hdC⟩ := hC2f i x (mem_boxVec.mpr hx) hlat
    refine ⟨d, hd, hdC.trans ?_⟩
    exact single_le_sum (f := C2f) (fun j _ => hC2f0 j) (mem_univ i)

/-- **Corollary (complete blowups).** Bounded certificates in complete blowups with at least `5`
vertices per class. -/
theorem physDivCost_complete {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (K : ℕ) :
    ∃ C : ℤ, ∀ {V : Type} [Fintype V] [DecidableEq V] {p : V → Fin t} {G : SimpleGraph V}
      [DecidableRel G.Adj], IsCompleteBlowup p F G → Reps p 5 →
      ∀ {E : Finset (Sym2 V)}, E ⊆ G.edgeFinset → IsIntDiv p F E → E.card ≤ K →
        PhysDivCost p F G E C := by
  obtain ⟨C, hC⟩ := physDivCost_local F hF3 K
  refine ⟨C, ?_⟩
  intro V _ _ p G _ hG R E hE hdiv hK
  exact hC (LocalHyp.of_complete hG R (fun _ => True)) hE (fun _ _ _ _ => trivial) hdiv hK

end PartitionedTriangleAbsorption.BlowupB
