/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedHostPackingStage177
public import PartitionedTriangleAbsorption.TypedTrimBudgetStage178
public import PartitionedTriangleAbsorption.TypedCoverDownConsumer

/-! # Physical F1 packing and balanced residual quotas

The selector's supply and incidence inequalities are derived from the physical
packing and its residual degree. Link feasibility and confinement are not claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedF1AssemblyStage179

open Finset BalancedTrimStage170 TypedTrimBudgetStage178

variable {V : Type} [Fintype V] [DecidableEq V]

theorem repair_from_degree_and_supply (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (κ η ζ : ℝ)
    (hn : 0 < Fintype.card V) (hκ : 0 < κ) (hη : 0 ≤ η) (hζ : 0 < ζ)
    (hscale : 32 ≤ ζ * Fintype.card V) (hsmall : η ≤ κ / 8)
    (hslack : 768 * η < κ * ζ)
    (hI : IsIntDiv p TypedApplicationLinks.F1 G.edgeFinset)
    (hR : IsFracDiv p TypedApplicationLinks.F1 G.edgeFinset)
    (hD : IsDecomp p TypedApplicationLinks.F1 Q D) (hQ : Q ⊆ G.edgeFinset)
    (hdeg : DegBounded (G.edgeFinset \ Q) (η * Fintype.card V))
    (hsupply : ∀ τ ∈ TypedApplicationLinks.F1,
      κ * (Fintype.card V : ℝ) ^ 2 ≤ (D.filter fun s => triType p s = τ).card) :
    ∃ D' Q', D' ⊆ D ∧ Q' ⊆ Q ∧ IsDecomp p TypedApplicationLinks.F1 Q' D' ∧
      IsIntDiv p TypedApplicationLinks.F1 (G.edgeFinset \ Q') ∧
      (∃ a : Multiset (Fin 4) → ℕ, edgeVec p (G.edgeFinset \ Q') =
        ∑ τ ∈ TypedApplicationLinks.F1, (a τ : ℤ) • typeEdgeVec τ) ∧
      D.card - D'.card ≤ 64 * (G.edgeFinset \ Q).card ∧
      (G.edgeFinset \ Q').card ≤ 193 * (G.edgeFinset \ Q).card ∧
      DegBounded (G.edgeFinset \ Q') ((η + ζ) * Fintype.card V) := by
  classical
  let n := Fintype.card V
  let M := (G.edgeFinset \ Q).card
  let d := ⌊ζ * n / 16⌋₊
  have hM : (M : ℝ) ≤ η * (n : ℝ) ^ 2 / 2 := by
    have h := TypedCoverDown.card_le_of_degBounded (G.edgeFinset \ Q)
      (TypedCoverDown.not_isDiag_of_mem_edgeFinset G sdiff_subset) (η * n) hdeg
    dsimp [M, n] at *
    nlinarith
  have hbudget := fun τ hτ => trim_budget n M
    (D.filter fun s => triType p s = τ).card n κ η ζ hn hκ hη hζ
    hscale hM (hsupply τ hτ) (le_refl n) hsmall hslack
  have hd : 0 < d := Nat.floor_pos.mpr (by dsimp [n] at *; linarith)
  have hinc : ∀ τ ∈ TypedApplicationLinks.F1, ∀ v,
      incidence (D.filter fun s => triType p s = τ) v ≤ n := by
    intro τ _ v
    have hsub : (D.filter fun s => triType p s = τ).filter (fun s => v ∈ s) ⊆
        D.filter (fun s => v ∈ s) := by
      intro s hs
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hs).1).1, (mem_filter.mp hs).2⟩
    exact (card_le_card hsub).trans (packing_incidence_le_order p _ Q D hD v)
  obtain ⟨D', Q', hsub, hQsub, hD', hI', ha, hloss, hcard, hdeg'⟩ :=
    repair_F1_balanced p G.edgeFinset Q D hI hR hD hQ n d hd hinc
      (fun τ hτ => ⟨(hbudget τ hτ).2.1, (hbudget τ hτ).2.2.1⟩)
  refine ⟨D', Q', hsub, hQsub, hD', hI', ha, hloss, hcard, ?_⟩
  intro v
  have hbound : (16 * d : ℕ) ≤ ζ * n := by
    have hf := Nat.floor_le (show 0 ≤ ζ * (n : ℝ) / 16 by positivity)
    dsimp [d]
    push_cast
    linarith
  have hv : (((G.edgeFinset \ Q').filter fun e => v ∈ e).card : ℝ) ≤
      ((G.edgeFinset \ Q).filter fun e => v ∈ e).card + (16 * d : ℕ) := by
    exact_mod_cast hdeg' v
  have hold := hdeg v
  dsimp [n] at hbound
  push_cast at hv hbound
  linarith

def a₀ : Fin 8 → Fin 4 := ![0, 0, 1, 1, 0, 1, 0, 1]
def a₁ : Fin 8 → Fin 4 := ![0, 0, 1, 1, 2, 2, 3, 3]
def a₂ : Fin 8 → Fin 4 := ![2, 3, 2, 3, 2, 2, 3, 3]

def admissiblePair (i j : Fin 4) : Prop :=
  i = j ∨ (i.val < 2 ∧ 2 ≤ j.val) ∨ (j.val < 2 ∧ 2 ≤ i.val)

instance (i j : Fin 4) : Decidable (admissiblePair i j) :=
  inferInstanceAs (Decidable (i = j ∨ (i.val < 2 ∧ 2 ≤ j.val) ∨ (j.val < 2 ∧ 2 ≤ i.val)))

theorem F1_enumeration : TypedApplicationLinks.F1 =
    univ.image (fun r : Fin 8 => ({a₀ r, a₁ r, a₂ r} : Multiset (Fin 4))) := by
  decide

theorem F1_pairs : ∀ (r : Fin 8) (i j : Fin 4),
    (i, j) ∈ ({(a₀ r, a₁ r), (a₀ r, a₂ r), (a₁ r, a₂ r)} : Finset (Fin 4 × Fin 4)) →
    admissiblePair i j := by
  decide

theorem uniform_F1_packing_and_quotas (α b ζ : ℝ)
    (hα : 0 < α) (hb : 0 < b) (hζ : 0 < ζ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ α / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Finset V → ℝ),
      (∀ l, α * Fintype.card V ≤ ((univ.filter fun v => p v = l).card : ℝ)) →
      (∀ i j, admissiblePair i j → ∀ x, p x = i →
        ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ0 * Fintype.card V) →
      (∀ s, IsCopy p TypedApplicationLinks.F1 G s →
        1 / (b * Fintype.card V) ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
      (∀ e ∈ G.edgeFinset,
        |(∑ s ∈ copies p TypedApplicationLinks.F1 G with e ∈ triEdges s, φ s) - 1| ≤ δ0) →
      IsIntDiv p TypedApplicationLinks.F1 G.edgeFinset →
      IsFracDiv p TypedApplicationLinks.F1 G.edgeFinset →
      ∃ D Q, D ⊆ copies p TypedApplicationLinks.F1 G ∧
        Q ⊆ G.edgeFinset ∧ IsDecomp p TypedApplicationLinks.F1 Q D ∧
        IsIntDiv p TypedApplicationLinks.F1 (G.edgeFinset \ Q) ∧
        (∃ a : Multiset (Fin 4) → ℕ, edgeVec p (G.edgeFinset \ Q) =
          ∑ τ ∈ TypedApplicationLinks.F1, (a τ : ℤ) • typeEdgeVec τ) ∧
        DegBounded (G.edgeFinset \ Q) (ζ * Fintype.card V) := by
  classical
  let a := min (α ^ 3 / (108 * b)) (ζ / 1000)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨γ, η, κ, hγ, hγ1, hγtypes, _, hη, hk, hκ, hwaste, hsmall, hslack⟩ :=
    compatible_parameters (ι := Fin 8) a (ζ / 2) ha (by positivity)
  have hηζ : η ≤ ζ / 2 := by
    have hga := mul_le_mul_of_nonneg_left (show a ≤ ζ / 1000 from min_le_right _ _) hγ.le
    have hgz := mul_le_mul_of_nonneg_right (show γ ≤ 1 by linarith) hζ.le
    rw [hk] at hsmall
    nlinarith
  obtain ⟨δ0, hδ0, hδα, N, hN⟩ :=
    TypedHostPackingStage177.typed_packing_from_host (ι := Fin 8)
      α b γ η hα hb hγ hγ1 hη hwaste hγtypes
  refine ⟨δ0, hδ0, hδα, max N (max 1 ⌈64 / ζ⌉₊), ?_⟩
  intro V _ _ hn p G _ φ hsize hmiss hw hload hI hR
  have hn1 : 1 ≤ Fintype.card V := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hscale : 32 ≤ (ζ / 2) * Fintype.card V := by
    have hc : ⌈64 / ζ⌉₊ ≤ Fintype.card V :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hr := (Nat.le_ceil (64 / ζ)).trans
      (show (⌈64 / ζ⌉₊ : ℝ) ≤ Fintype.card V by exact_mod_cast hc)
    have hm := mul_le_mul_of_nonneg_left hr hζ.le
    rw [mul_div_cancel₀ _ hζ.ne'] at hm
    linarith
  obtain ⟨D, Q, hcopies, _, hQ, hD, hdeg, htypes⟩ :=
    hN V ((le_max_left _ _).trans hn) 4 p TypedApplicationLinks.F1 G φ a₀ a₁ a₂
      (fun r => by rw [F1_enumeration]; exact mem_image.mpr ⟨r, mem_univ _, rfl⟩)
      (fun _ l _ => hsize l)
      (fun r i j hij x hx => hmiss i j (F1_pairs r i j hij) x hx) hw hload
  have hsupply : ∀ τ ∈ TypedApplicationLinks.F1,
      κ * (Fintype.card V : ℝ) ^ 2 ≤ (D.filter fun s => triType p s = τ).card := by
    intro τ hτ
    rw [F1_enumeration] at hτ
    obtain ⟨r, _, rfl⟩ := mem_image.mp hτ
    have hga := mul_le_mul_of_nonneg_left (show a ≤ α ^ 3 / (108 * b) from min_le_left _ _) hγ.le
    have hκa : κ ≤ γ * α ^ 3 / (432 * b) := by
      rw [hk]
      calc γ * a / 4 ≤ (γ * (α ^ 3 / (108 * b))) / 4 := div_le_div_of_nonneg_right hga (by norm_num)
        _ = γ * α ^ 3 / (432 * b) := by ring
    exact (mul_le_mul_of_nonneg_right hκa (sq_nonneg _)).trans (htypes r)
  obtain ⟨D', Q', hsub, hQsub, hD', hI', ha', _, _, hdeg'⟩ :=
    repair_from_degree_and_supply p G Q D κ η (ζ / 2) (by omega) hκ hη.le
      (by positivity) hscale hsmall hslack hI hR hD hQ hdeg hsupply
  refine ⟨D', Q', hsub.trans hcopies, hQsub.trans hQ, hD', hI', ha', ?_⟩
  intro v
  exact (hdeg' v).trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

end PartitionedTriangleAbsorption.TypedF1AssemblyStage179

