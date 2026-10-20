/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.Reindex

/-! # Iterating the physical round: the ordinary nibble consumer

Each round is run in a fresh finite product space on the current surviving
triangle system (`TriSystem.reindex`), with the surviving weights rescaled by
`exp (2γ)`. The invariant `IterInv` records, after `j` rounds,

* surviving triangles lie in the current active edge set `Bj`;
* the accumulated packing `P` is edge-disjoint and avoids `Bj`;
* every original edge not covered by `P` is active or wasted (`B \ E(P) ⊆ Bj ∪ W`);
* waste degrees are at most `24 γ² n j`;
* active degrees are `< θ n` or at most `(1 - γ/8)^j n`;
* active loads are within `c j a^j` of one.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The load of `e` carried by the triangles in `s`. -/
def aliveLoad (S : TriSystem V m) (s : Finset (Fin m)) (w : Fin m → ℝ) (e : Sym2 V) : ℝ :=
  ∑ i ∈ s.filter (fun i => e ∈ triEdges (S.tri i)), w i

/-- The edges `E(P)` covered by a set of triangle indices. -/
def edgesOf (S : TriSystem V m) (P : Finset (Fin m)) : Finset (Sym2 V) :=
  P.biUnion (fun i => triEdges (S.tri i))

/-- `P` is an edge-disjoint triangle packing. -/
def IsPacking (S : TriSystem V m) (P : Finset (Fin m)) : Prop :=
  ∀ i ∈ P, ∀ j ∈ P, i ≠ j → Disjoint (triEdges (S.tri i)) (triEdges (S.tri j))

theorem card_star_union_le (A C : Finset (Sym2 V)) (v : V) :
    (star (A ∪ C) v).card ≤ (star A v).card + (star C v).card := by
  unfold star; rw [filter_union]; exact card_union_le _ _

theorem star_mono {A C : Finset (Sym2 V)} (h : A ⊆ C) (v : V) : star A v ⊆ star C v :=
  filter_subset_filter _ h

variable [Fintype V]

/-- The invariant after `j` rounds. -/
structure IterInv (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (γ θ c a : ℝ) (j : ℕ) (s : Finset (Fin m)) (Bj W : Finset (Sym2 V)) (P : Finset (Fin m)) :
    Prop where
  alive_sub : ∀ i ∈ s, triEdges (S.tri i) ⊆ Bj
  pack : IsPacking S P
  disj : Disjoint (edgesOf S P) Bj
  cover : B \ edgesOf S P ⊆ Bj ∪ W
  waste : ∀ v, ((star W v).card : ℝ) ≤ 24 * γ ^ 2 * Fintype.card V * j
  deg : ∀ v, ((star Bj v).card : ℝ) < θ * Fintype.card V ∨
    ((star Bj v).card : ℝ) ≤ (1 - γ / 8) ^ j * Fintype.card V
  load : ∀ e ∈ Bj,
    |aliveLoad S s (fun i => Real.exp (2 * γ * j) * w i) e - 1| ≤ c * j * a ^ j

theorem IterInv.start (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (γ θ c a : ℝ) (hB : ∀ i, triEdges (S.tri i) ⊆ B) (hload : ∀ e ∈ B, S.load w e = 1) :
    IterInv S B w γ θ c a 0 univ B ∅ ∅ where
  alive_sub i _ := hB i
  pack := by simp [IsPacking]
  disj := by simp [edgesOf]
  cover := by simp [edgesOf]
  waste v := by simp [star]
  deg v := Or.inr (by simpa using (show ((star B v).card : ℝ) ≤ Fintype.card V by
    exact_mod_cast card_star_le B v))
  load e he := by
    have h := hload e he
    simp only [TriSystem.load, TriSystem.edgeTris] at h
    simp [aliveLoad, h]

/-- One round of the iteration preserves the invariant. -/
theorem IterInv.step {S : TriSystem V m} {B : Finset (Sym2 V)} {w : Fin m → ℝ}
    {γ θ c a : ℝ} {j : ℕ} {s : Finset (Fin m)} {Bj W : Finset (Sym2 V)} {P : Finset (Fin m)}
    (hI : IterInv S B w γ θ c a j s Bj W P) (hγ : 0 ≤ γ) (hγ8 : γ ≤ 8)
    (ha : 1 + 5 * γ ≤ a) (hc : 0 ≤ c)
    (ω : Fin s.card → Bool) (β : ℝ) (hβ : 5 * γ * β ≤ c / 2)
    (hgood : RoundGood (S.reindex s) Bj (fun k => Real.exp (2 * γ * j) * w (reidx s k))
      β (c * j * a ^ j) γ θ (c / 2) ω) :
    IterInv S B w γ θ c a (j + 1)
      (s.filter (fun i => triEdges (S.tri i) ⊆ (S.reindex s).untouched Bj ω))
      ((S.reindex s).untouched Bj ω) (W ∪ (S.reindex s).waste ω)
      (P ∪ ((S.reindex s).packing ω).image (reidx s)) := by
  set R := S.reindex s with hRdef
  have hRtri : ∀ k, R.tri k = S.tri (reidx s k) := fun _ => rfl
  have hR : ∀ k, triEdges (R.tri k) ⊆ Bj := fun k => hI.alive_sub _ (reidx_mem s k)
  have hres := R.residual_identity Bj hR ω
  have hPE : edgesOf S ((R.packing ω).image (reidx s)) = R.packEdges ω :=
    (reindex_packEdges S s ω).symm
  have hTsub : R.touched ω ⊆ Bj := biUnion_subset.mpr fun k _ => hR k
  have hPEsub : R.packEdges ω ⊆ Bj := (R.packEdges_subset_touched ω).trans hTsub
  have hUsub : R.untouched Bj ω ⊆ Bj := sdiff_subset
  have hUPE : Disjoint (R.untouched Bj ω) (R.packEdges ω) :=
    disjoint_of_subset_right (R.packEdges_subset_touched ω) sdiff_disjoint
  have hEU : edgesOf S (P ∪ (R.packing ω).image (reidx s)) =
      edgesOf S P ∪ R.packEdges ω := by
    rw [← hPE]; unfold edgesOf; rw [union_biUnion]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i hi i' hi' hne
    have hsubP : ∀ x ∈ P, triEdges (S.tri x) ⊆ edgesOf S P := fun x hx =>
      subset_biUnion_of_mem (fun i => triEdges (S.tri i)) hx
    rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hi' with hi' | hi'
    · exact hI.pack i hi i' hi' hne
    · obtain ⟨k, -, rfl⟩ := mem_image.mp hi'
      exact (hI.disj.mono (hsubP i hi) (hR k))
    · obtain ⟨k, -, rfl⟩ := mem_image.mp hi
      exact (hI.disj.mono (hsubP i' hi') (hR k)).symm
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
      obtain ⟨k', hk', rfl⟩ := mem_image.mp hi'
      exact R.packing_edge_disjoint ω hk hk' (fun h => hne (h ▸ rfl))
  · rw [hEU, disjoint_union_left]
    exact ⟨hI.disj.mono_right hUsub, hUPE.symm⟩
  · intro e he
    rw [hEU, mem_sdiff, mem_union, not_or] at he
    obtain ⟨heB, heP, hePE⟩ := he
    rcases mem_union.mp (hI.cover (mem_sdiff.mpr ⟨heB, heP⟩)) with h | h
    · have : e ∈ Bj \ R.packEdges ω := mem_sdiff.mpr ⟨h, hePE⟩
      rw [hres.1] at this
      rcases mem_union.mp this with h' | h'
      · exact mem_union_left _ h'
      · exact mem_union_right _ (mem_union_right _ h')
    · exact mem_union_right _ (mem_union_left _ h)
  · intro v
    have h1 : ((star (W ∪ R.waste ω) v).card : ℝ) ≤
        (star W v).card + (star (R.waste ω) v).card := by
      exact_mod_cast card_star_union_le _ _ v
    have h2 := hI.waste v
    have h3 := hgood.2.1 v
    push_cast
    nlinarith
  · intro v
    have hsum : (star (R.untouched Bj ω) v).card + (star (R.packEdges ω) v).card ≤
        (star Bj v).card := by
      rw [← card_union_of_disjoint (show Disjoint
        (star (R.untouched Bj ω) v) (star (R.packEdges ω) v)
        from hUPE.mono (filter_subset _ _) (filter_subset _ _))]
      exact card_le_card (union_subset (star_mono hUsub v) (star_mono hPEsub v))
    have hsumR : ((star (R.untouched Bj ω) v).card : ℝ) + (star (R.packEdges ω) v).card ≤
        (star Bj v).card := by exact_mod_cast hsum
    have hp0 : (0 : ℝ) ≤ (star (R.packEdges ω) v).card := by positivity
    rcases hI.deg v with h | h
    · exact Or.inl (by linarith)
    · by_cases hθ : θ * (Fintype.card V : ℝ) ≤ (star Bj v).card
      · right
        have hp := hgood.1 v hθ
        have hg : 0 ≤ 1 - γ / 8 := by linarith
        calc ((star (R.untouched Bj ω) v).card : ℝ) ≤ (1 - γ / 8) * (star Bj v).card := by
              linarith
          _ ≤ (1 - γ / 8) * ((1 - γ / 8) ^ j * Fintype.card V) :=
              mul_le_mul_of_nonneg_left h hg
          _ = (1 - γ / 8) ^ (j + 1) * Fintype.card V := by ring
      · exact Or.inl (by push Not at hθ; linarith)
  · intro e he
    have hg := hgood.2.2 e he
    have hav := reindex_availLoad S s Bj (fun i => Real.exp (2 * γ * j) * w i) e ω
    have heq : aliveLoad S (s.filter (fun i => triEdges (S.tri i) ⊆ R.untouched Bj ω))
        (fun i => Real.exp (2 * γ * ((j + 1 : ℕ) : ℝ)) * w i) e =
        Real.exp (2 * γ) * availLoad R Bj (fun k => Real.exp (2 * γ * j) * w (reidx s k)) e ω := by
      rw [hav, aliveLoad, filter_filter, mul_sum]
      rw [filter_congr (q := fun i => e ∈ triEdges (S.tri i) ∧
        triEdges (S.tri i) ⊆ R.untouched Bj ω) (fun _ _ => and_comm)]
      refine sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      push_cast; ring
    rw [heq]
    refine hg.trans ?_
    have ha1 : 1 ≤ a := by linarith
    have hA : 0 ≤ c * j * a ^ j := by positivity
    have h1 : (1 + 5 * γ) * (c * j * a ^ j) ≤ a * (c * j * a ^ j) :=
      mul_le_mul_of_nonneg_right ha hA
    have h2 : c ≤ c * a ^ (j + 1) := le_mul_of_one_le_right hc (one_le_pow₀ ha1)
    have h3 : c * ((j + 1 : ℕ) : ℝ) * a ^ (j + 1) = a * (c * j * a ^ j) + c * a ^ (j + 1) := by
      push_cast; ring
    rw [h3]
    linarith

end PartitionedTriangleAbsorption.Nibble
