/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRoundStage172

/-! # Completing a type-rich seed without losing its copies

The first round is retained literally. Only untouched edges and surviving
physical triangles are sent to the accepted near-load consumer. Its weights
are rescaled, and its degree gap is proved from the same good first round.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedPackingStage173

open Finset Nibble TypedRoundStage172

/-- Untouched degrees have a uniform gap after a good round. -/
theorem untouched_degree_gap {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (β δ γ ε : ℝ) (hγ1 : γ ≤ 1)
    (hB : ∀ i, Nibble.triEdges (S.tri i) ⊆ B) (ω : Fin m → Bool)
    (hg : RoundGood S B w β δ γ (1 / 2) ε ω) :
    ∀ v, ((star (S.untouched B ω) v).card : ℝ) ≤
      (1 - γ / 8) * Fintype.card V := by
  intro v
  have hT : S.touched ω ⊆ B := biUnion_subset.mpr fun i _ => hB i
  have hPE : S.packEdges ω ⊆ B := (S.packEdges_subset_touched ω).trans hT
  have hdis : Disjoint (S.untouched B ω) (S.packEdges ω) :=
    disjoint_of_subset_right (S.packEdges_subset_touched ω) sdiff_disjoint
  have hsum : (star (S.untouched B ω) v).card + (star (S.packEdges ω) v).card ≤
      (star B v).card := by
    rw [← card_union_of_disjoint (show Disjoint
      (star (S.untouched B ω) v) (star (S.packEdges ω) v)
      from hdis.mono (filter_subset _ _) (filter_subset _ _))]
    exact card_le_card (union_subset (star_mono sdiff_subset v) (star_mono hPE v))
  have hsumR : ((star (S.untouched B ω) v).card : ℝ) + (star (S.packEdges ω) v).card ≤
      (star B v).card := by exact_mod_cast hsum
  have hcap : ((star B v).card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_star_le B v
  by_cases hθ : (1 / 2 : ℝ) * Fintype.card V ≤ (star B v).card
  · have hp := hg.1 v hθ
    have hscale := mul_le_mul_of_nonneg_left hcap (by linarith : 0 ≤ 1 - γ / 8)
    linarith
  · have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hscale : (1 / 2 : ℝ) * Fintype.card V ≤ (1 - γ / 8) * Fintype.card V := by
      nlinarith
    have hp : (0 : ℝ) ≤ (star (S.packEdges ω) v).card := Nat.cast_nonneg _
    push Not at hθ
    linarith

/-- From fractional type mass, construct a near-complete physical packing rich in every type. -/
theorem packing_with_supply {ι : Type} [Fintype ι] [Nonempty ι]
    (b γ a η : ℝ) (hb : 0 < b) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 128)
    (ha : 0 < a) (hη : 0 < η) (hwaste : 24 * γ ^ 2 ≤ η / 2)
    (hγtypes : γ ≤ 1 / (96 * Fintype.card ι)) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
        (J : ι → Finset (Fin m)),
      (∀ i, Nibble.triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
      (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, S.load w e = 1) →
      (∀ t, a * (Fintype.card V : ℝ) ^ 2 ≤ ∑ i ∈ J t, w i) →
      ∃ P : Finset (Fin m), IsPacking S P ∧
        (∀ v, ((star (B \ edgesOf S P) v).card : ℝ) ≤ η * Fintype.card V) ∧
        ∀ t, γ * a * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (J t ∩ P).card := by
  obtain ⟨δ, hδ, _, Nnear, hnear⟩ := nibble_packing_near
    (b * Real.exp (2 * γ)) (η / 2) (γ / 8) (by positivity) (by positivity) (by positivity)
  obtain ⟨Nround, hround⟩ := first_round_supply (ι := ι) b γ (1 / 2) (δ / 2) a
    hb hγ hγ1 (by norm_num) (by positivity) ha hγtypes
  refine ⟨max (max (max Nnear Nround) 1) ⌈10 * γ * b / δ⌉₊, ?_⟩
  intro V _ _ hN m S B w J hB hw hwb hload hmass
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  have hNnear : Nnear ≤ Fintype.card V :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hNround : Nround ≤ Fintype.card V :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hlarge : 10 * γ * b / δ ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [div_le_iff₀ hδ] at hlarge
  have hβ : 5 * γ * (b / Fintype.card V) ≤ δ / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hnpos]
    nlinarith
  obtain ⟨ω, hg, hs⟩ := hround V hNround m S B w J hB hw hwb hload hmass
  let U := S.untouched B ω
  let s := univ.filter (fun i => Nibble.triEdges (S.tri i) ⊆ U)
  let R := S.reindex s
  have hR : ∀ k, Nibble.triEdges (R.tri k) ⊆ U :=
    fun k => (mem_filter.mp (reidx_mem s k)).2
  have hRl : ∀ e ∈ U, |R.load (fun k => Real.exp (2 * γ) * w (reidx s k)) e - 1| ≤ δ := by
    intro e he
    have h := hg.2.2 e he
    have heq : R.load (fun k => Real.exp (2 * γ) * w (reidx s k)) e =
        Real.exp (2 * γ) * availLoad S B w e ω := by
      rw [reindex_load S s (fun i => Real.exp (2 * γ) * w i) e, ← mul_sum]
      congr 1
      unfold availLoad TriSystem.edgeTris
      simp only [s, filter_filter]
      congr 1
      exact filter_congr fun _ _ => and_comm
    rw [heq]
    simp only [mul_zero, zero_add] at h
    exact h.trans (by linarith)
  obtain ⟨P1, hp1, hd1⟩ := hnear V hNnear s.card R U
    (fun k => Real.exp (2 * γ) * w (reidx s k)) hR
    (fun k => mul_nonneg (Real.exp_pos _).le (hw _))
    (fun k => by
      have h := mul_le_mul_of_nonneg_left (hwb (reidx s k)) (Real.exp_pos (2 * γ)).le
      simpa only [mul_div_assoc', mul_comm b] using h)
    (untouched_degree_gap S B w _ _ γ _ (by linarith) hB ω hg) hRl
  let P := S.packing ω ∪ P1.image (reidx s)
  have himage : edgesOf S (P1.image (reidx s)) = edgesOf R P1 := by
    unfold edgesOf
    rw [image_biUnion]
    rfl
  have hEP : edgesOf S (S.packing ω) = S.packEdges ω := rfl
  have hdis : Disjoint (S.packEdges ω) U :=
    (disjoint_of_subset_right (S.packEdges_subset_touched ω) sdiff_disjoint).symm
  have hP : IsPacking S P := by
    intro i hi j hj hij
    have hsub : ∀ x ∈ S.packing ω, Nibble.triEdges (S.tri x) ⊆ S.packEdges ω :=
      fun x hx => subset_biUnion_of_mem (fun i => Nibble.triEdges (S.tri i)) hx
    rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hj with hj | hj
    · exact S.packing_edge_disjoint ω hi hj hij
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hj
      exact hdis.mono (hsub i hi) (hR k)
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hi
      exact (hdis.mono (hsub j hj) (hR k)).symm
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
      obtain ⟨k', hk', rfl⟩ := mem_image.mp hj
      exact hp1 k hk k' hk' (fun h => hij (h ▸ rfl))
  have hcover : B \ edgesOf S P ⊆ (U \ edgesOf R P1) ∪ S.waste ω := by
    have hE : edgesOf S P = S.packEdges ω ∪ edgesOf R P1 := by
      dsimp [P]
      calc
        edgesOf S (S.packing ω ∪ P1.image (reidx s)) =
            edgesOf S (S.packing ω) ∪ edgesOf S (P1.image (reidx s)) := by
          unfold edgesOf
          rw [union_biUnion]
        _ = _ := by rw [hEP, himage]
    intro e he
    rw [hE, mem_sdiff, mem_union, not_or] at he
    have he0 : e ∈ B \ S.packEdges ω := mem_sdiff.mpr ⟨he.1, he.2.1⟩
    rw [(S.residual_identity B hB ω).1] at he0
    rcases mem_union.mp he0 with hu | hwaste
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hu, he.2.2⟩)
    · exact mem_union_right _ hwaste
  refine ⟨P, hP, fun v => ?_, fun t => ?_⟩
  · have hc : ((star (B \ edgesOf S P) v).card : ℝ) ≤
        (star (U \ edgesOf R P1) v).card + (star (S.waste ω) v).card := by
      exact_mod_cast (card_le_card (star_mono hcover v)).trans (card_star_union_le _ _ v)
    have hwv := hg.2.1 v
    have hdv := hd1 v
    have hscale := mul_le_mul_of_nonneg_right hwaste hnpos.le
    linarith
  · have hmono : (J t ∩ S.packing ω).card ≤ (J t ∩ P).card := card_le_card (by
      intro i hi
      exact mem_inter.mpr ⟨(mem_inter.mp hi).1, mem_union_left _ (mem_inter.mp hi).2⟩)
    exact (hs t).trans (by exact_mod_cast hmono)

end PartitionedTriangleAbsorption.TypedPackingStage173

