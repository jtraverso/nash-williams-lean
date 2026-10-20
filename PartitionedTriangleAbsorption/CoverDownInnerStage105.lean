/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownBasicStage105

/-! # Stage105 cover-down, step 1: outer leftover edges

Every leftover edge `xy` with both ends outside `U` is covered by an actual
triangle `xyz`, `z ∈ U`, whose two spokes `xz, yz` are taken from the reserve
`R1`. The greedy choice only needs the explicit two-root reserve richness
`a1 ≥ 2h`, where `h` bounds the leftover degree at outer vertices.
Each outer vertex receives exactly as many reserve spokes as leftover edges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

theorem card_spoke_filter_le (U : Finset V) (S : Finset (Sym2 V)) (x : V) :
    (U.filter fun z => s(x, z) ∈ S).card ≤ incidentLoad S x := by
  apply card_le_card_of_injOn (fun z => s(x, z))
  · intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).2, Sym2.mem_mk_left x z⟩
  · intro a _ b _ hab
    rcases Sym2.eq_iff.mp hab with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

/-- **Step 1 of the cover-down.** -/
theorem inner_cover (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ a b, s(a, b) ∈ E → p a ≠ p b) (U : Finset V)
    (H1 R1 : Finset (Sym2 V)) (h a1 : ℕ)
    (hH1E : H1 ⊆ E) (hR1E : R1 ⊆ E)
    (hH1 : ∀ x y, s(x, y) ∈ H1 → x ∉ U ∧ y ∉ U)
    (hR1 : ∀ e ∈ R1, IsSpoke U e)
    (hdeg : ∀ v, v ∉ U → incidentLoad H1 v ≤ h)
    (hrich : ∀ x y, s(x, y) ∈ H1 →
      a1 ≤ (U.filter fun z => s(x, z) ∈ R1 ∧ s(y, z) ∈ R1).card)
    (hb : 2 * h ≤ a1) :
    ∃ S ⊆ R1, HasDecomp p F3 (H1 ∪ S) ∧
      ∀ x, x ∉ U → incidentLoad S x = incidentLoad H1 x := by
  have hspoke_not : ∀ e ∈ R1, e ∉ H1 := by
    intro e he heH
    obtain ⟨a, b, ha, hb, rfl⟩ := hR1 e he
    exact (hH1 a b heH).2 hb
  suffices key : ∀ A ⊆ H1, ∃ S ⊆ R1, HasDecomp p F3 (A ∪ S) ∧
      ∀ x, x ∉ U → incidentLoad S x = incidentLoad A x from key H1 subset_rfl
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, empty_subset _, by simpa using hasDecomp_empty, fun x _ => rfl⟩
  | @insert e A heA ih =>
    intro hsub
    obtain ⟨S, hSR, hdec, hload⟩ := ih ((subset_insert e A).trans hsub)
    have heH : e ∈ H1 := hsub (mem_insert_self e A)
    induction e using Sym2.ind with
    | _ x y =>
    obtain ⟨hx, hy⟩ := hH1 x y heH
    have hxy : p x ≠ p y := hcross x y (hH1E heH)
    have nxy : x ≠ y := fun h => hxy (h ▸ rfl)
    have hAx : incidentLoad A x + 1 ≤ h := by
      have h1 := incidentLoad_insert heA x
      have h2 := incidentLoad_mono hsub x
      simp only [Sym2.mem_iff, true_or, ↓reduceIte] at h1
      have := hdeg x hx
      omega
    have hAy : incidentLoad A y + 1 ≤ h := by
      have h1 := incidentLoad_insert heA y
      have h2 := incidentLoad_mono hsub y
      simp only [Sym2.mem_iff, or_true, ↓reduceIte] at h1
      have := hdeg y hy
      omega
    set Bad := (U.filter fun z => s(x, z) ∈ S) ∪ (U.filter fun z => s(y, z) ∈ S) with hBad
    have hbad : Bad.card + 2 ≤ 2 * h := by
      have := card_union_le (U.filter fun z => s(x, z) ∈ S) (U.filter fun z => s(y, z) ∈ S)
      have h1 := card_spoke_filter_le U S x
      have h2 := card_spoke_filter_le U S y
      rw [hload x hx] at h1
      rw [hload y hy] at h2
      rw [hBad]
      omega
    obtain ⟨z, hzR, hzB⟩ : ∃ z ∈ U.filter (fun z => s(x, z) ∈ R1 ∧ s(y, z) ∈ R1), z ∉ Bad := by
      by_contra hno
      push Not at hno
      have := card_le_card (show U.filter (fun z => s(x, z) ∈ R1 ∧ s(y, z) ∈ R1) ⊆ Bad from hno)
      have := hrich x y heH
      omega
    obtain ⟨hzU, hxz, hyz⟩ := mem_filter.mp hzR
    have hxzS : s(x, z) ∉ S := fun h => hzB (mem_union_left _ (mem_filter.mpr ⟨hzU, h⟩))
    have hyzS : s(y, z) ∉ S := fun h => hzB (mem_union_right _ (mem_filter.mpr ⟨hzU, h⟩))
    have nxz : x ≠ z := fun h => hx (h ▸ hzU)
    have nyz : y ≠ z := fun h => hy (h ▸ hzU)
    have hne : s(x, z) ≠ s(y, z) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact nxy h1
      · exact nxz h1
    have hyzS' : s(y, z) ∉ insert s(x, z) S := by
      simp only [mem_insert, not_or]; exact ⟨hne.symm, hyzS⟩
    refine ⟨insert s(y, z) (insert s(x, z) S), ?_, ?_, ?_⟩
    · intro f hf
      simp only [mem_insert] at hf
      rcases hf with rfl | rfl | hf
      exacts [hyz, hxz, hSR hf]
    · have htri := hasDecomp_tri p E hcross (hH1E heH) (hR1E hxz) (hR1E hyz)
      have hdisj : Disjoint (A ∪ S) {s(x, y), s(x, z), s(y, z)} := by
        rw [disjoint_left]
        intro f hf hf'
        simp only [mem_insert, mem_singleton] at hf'
        rcases mem_union.mp hf with hfA | hfS
        · rcases hf' with rfl | rfl | rfl
          · exact heA hfA
          · exact (hH1 x z (hsub (mem_insert_of_mem hfA))).2 hzU
          · exact (hH1 y z (hsub (mem_insert_of_mem hfA))).2 hzU
        · rcases hf' with rfl | rfl | rfl
          · exact hspoke_not _ (hSR hfS) heH
          · exact hxzS hfS
          · exact hyzS hfS
      have := hdec.union htri hdisj
      convert this using 1
      ext f
      simp only [mem_union, mem_insert, mem_singleton]
      tauto
    · intro w hw
      rw [incidentLoad_insert hyzS', incidentLoad_insert (by exact hxzS),
        incidentLoad_insert heA, hload w hw]
      have hwz : w ≠ z := fun h => hw (h ▸ hzU)
      simp only [Sym2.mem_iff, hwz, or_false]
      by_cases hwx : w = x
      · subst hwx; simp [nxy]
      · by_cases hwy : w = y
        · subst hwy; simp [hwx]
        · simp [hwx, hwy]

end PartitionedTriangleAbsorption.CoverDownStage105
