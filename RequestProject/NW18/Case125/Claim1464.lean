/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Claim1464Case2

/-!
# Claim 14.6.4 (`F₀`-hingefulness of an idealized host)

Proof of the statement `claim_14_6_4` (stated in `Theorem146.lean`), following the paper:
for two `F₀`-copies `T₁ = u₁u₂v₁`, `T₂ = u₁u₂v₂`,

* if `u₁, u₂` lie in the same part, there are `Ω(n⁴)` eight-vertex `F₀`-hinges of type 1 (when the
  part of `u₁, u₂` is not close to `T₂`/`T̄₂`) or of type 2 (when the other part is not close);
  the paper obtains the needed paths from Lemma 14.2, here they come from the stability lemma
  for walks of length four (`many_walks_of_not_sideClose`);
* if `u₁, u₂` lie in different parts, there are `Ω(n²)` six-vertex `F₀`-hinges.

The constants are not the paper's (`α³/(5·50·8·9)³`-type); only positivity matters.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)

/-- **Claim 14.6.4**, proof (same statement as `claim_14_6_4`). -/
theorem claim_14_6_4_proof :
    ∀ α : ℝ, 0 < α → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2) (G : SimpleGraph V)
        [DecidableRel G.Adj], n₀ ≤ Fintype.card V → IsF0Idealized ε₀ G p →
        (∃ i, ¬ IsSideClose α G (partClass p i)) → HingefulN p F0 G c 8 := by
  intro α hα
  set σ : ℝ := min (α / 200) (1 / 100) with hσdef
  have hσ0 : 0 < σ := lt_min (by positivity) (by norm_num)
  have hσ1 : σ ≤ 1 / 100 := min_le_right _ _
  have hσα : σ ≤ α / 200 := min_le_left _ _
  set e0 : ℝ := σ ^ 2 / 1000 with he0def
  have he0 : 0 < e0 := by positivity
  have hσsq : σ ^ 2 ≤ σ / 100 := by nlinarith
  have he0σ : 9 * e0 ≤ σ ^ 2 := by rw [he0def]; nlinarith [sq_nonneg σ]
  have he01 : e0 ≤ 1 / 1000 := by rw [he0def]; nlinarith
  have hθ : 100 * σ + 36 * e0 ≤ α := by rw [he0def]; nlinarith
  set c : ℝ := σ ^ 6 / 10000 with hcdef
  have hσ6 : 0 < σ ^ 6 := by positivity
  refine ⟨e0, he0, c, by positivity, ⌈18 / α + 10000 / σ ^ 6⌉₊ + 100, ?_⟩
  intro V _ _ p G _ hn hid hside
  have hf := idFacts_of G p hid
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hnN : 18 / α + 10000 / σ ^ 6 + 100 ≤ n := by
    have h1 : ((⌈18 / α + 10000 / σ ^ 6⌉₊ + 100 : ℕ) : ℝ) ≤ n := by
      rw [hndef]; exact_mod_cast hn
    push_cast at h1
    linarith [Nat.le_ceil (18 / α + 10000 / σ ^ 6)]
  have hpos1 : 0 ≤ 18 / α := by positivity
  have hpos2 : 0 ≤ 10000 / σ ^ 6 := by positivity
  have hn100 : 100 ≤ n := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hn18 : 18 ≤ α * n := by
    have : 18 / α ≤ n := by linarith
    rwa [div_le_iff₀ hα, mul_comm] at this
  have hnσ : 10000 ≤ σ ^ 6 * n := by
    have : 10000 / σ ^ 6 ≤ n := by linarith
    rwa [div_le_iff₀ hσ6, mul_comm] at this
  intro S S' hS hS' h1
  obtain ⟨u₁, u₂, v₁, v₂, h12, h13, h14, h23, h24, h34, rfl, rfl⟩ :=
    two_triangles_sharing_edge hS.1.2 hS'.1.2 h1
  have adj : ∀ {T : Finset V} {x y : V}, IsCopy p F0 G T → x ∈ T → y ∈ T → x ≠ y →
      G.Adj x y := fun hT hx hy hxy => hT.1.1 (mem_coe.mpr hx) (mem_coe.mpr hy) hxy
  have a11 : G.Adj u₁ v₁ := adj hS (by simp) (by simp) h13
  have a21 : G.Adj u₂ v₁ := adj hS (by simp) (by simp) h23
  have a12 : G.Adj u₁ v₂ := adj hS' (by simp) (by simp) h14
  have a22 : G.Adj u₂ v₂ := adj hS' (by simp) (by simp) h24
  have hT1 := hS.2
  rw [triple_val_map p h12 h13 h23, mem_F0_iff] at hT1
  have hT2 := hS'.2
  rw [triple_val_map p h12 h14 h24, mem_F0_iff] at hT2
  have inj4 : Function.Injective ![u₁, u₂, v₁, v₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp at hij; first | exact absurd hij ‹_› | exact absurd hij.symm ‹_›)
  have hcube : 22 * n ^ 3 * 10000 ≤ 22 * n ^ 3 * (σ ^ 6 * n) :=
    mul_le_mul_of_nonneg_left hnσ (by positivity)
  by_cases hpu : p u₁ = p u₂
  · -- Case 1: `u₁, u₂` in the same part
    have hb1 : p u₁ ≠ p v₁ := fun h => hT1 ⟨hpu, by rw [← hpu, h]⟩
    have hb2 : p u₁ ≠ p v₂ := fun h => hT2 ⟨hpu, by rw [← hpu, h]⟩
    have hv₂ : p v₂ = p v₁ := by
      rcases fin2_eq_of_ne hb1 (c := p v₂) with h | h
      · exact absurd h.symm hb2
      · exact h
    have hpow : n ^ (((8 : ℕ) : ℤ) - 4) = n ^ 4 := by
      rw [show ((8 : ℕ) : ℤ) - 4 = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
    obtain ⟨i, hi⟩ := hside
    refine ⟨8, by simp, ?_⟩
    rw [hpow]
    rcases fin2_eq_of_ne hb1 (c := i) with rfl | rfl
    · have hw := case1a_walks G p hf he0.le he0σ hσ0 hσ1 hθ hn18 hb1 hi a11 a12 a21 a22 rfl
        hpu.symm rfl hv₂
      have ht := thomCount_le mH1 (q1 (p u₁) (p v₁)) G p inj4
      have ht' : (thomCount mH1 (q1 (p u₁) (p v₁)) G p u₁ u₂ v₁ v₂ : ℝ) ≤
          tcfgCount mH1 (q1 (p u₁) (p v₁)) G p u₁ u₂ v₁ v₂ + 22 * n ^ 3 := by
        rw [hndef]; exact_mod_cast ht
      have hh := tcfgCount_le_hingeCount (model_hinge1_F0 _ _ hb1) vertSet_mH1 G p u₁ u₂ v₁ v₂
        (fun x y hx hy h => image_mH1_injective hx hy h)
      rw [hcdef]
      nlinarith
    · have hw := case1b_walks G p hf he0.le he0σ hσ0 hσ1 hθ hn18 hb1 hi a21 a22 rfl
        hpu.symm rfl hv₂
      have ht := thomCount_le mH2 (q2 (p u₁) (p v₁)) G p inj4
      have ht' : (thomCount mH2 (q2 (p u₁) (p v₁)) G p u₁ u₂ v₁ v₂ : ℝ) ≤
          tcfgCount mH2 (q2 (p u₁) (p v₁)) G p u₁ u₂ v₁ v₂ + 22 * n ^ 3 := by
        rw [hndef]; exact_mod_cast ht
      have hh := tcfgCount_le_hingeCount (model_hinge2_F0 _ _ hb1) vertSet_mH2 G p u₁ u₂ v₁ v₂
        (fun x y hx hy h => image_mH2_injective hx hy h)
      rw [hcdef]
      nlinarith
  · -- Case 2: `u₁, u₂` in different parts
    have hpow : n ^ (((6 : ℕ) : ℤ) - 4) = n ^ 2 := by
      rw [show ((6 : ℕ) : ℤ) - 4 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    refine ⟨6, by simp, ?_⟩
    rw [hpow]
    have h2 := case2_pairs G p hf he0.le he01 hn100 h12 h13 h14 h23 h24 h34 hpu
    have hc : c ≤ 1 / 25 := by
      rw [hcdef]
      have : σ ^ 6 ≤ 1 := pow_le_one₀ hσ0.le (by linarith)
      linarith
    have : c * n ^ 2 ≤ 1 / 25 * n ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    linarith

end NashWilliams18
