/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownInnerStage105

/-! # Covering bases with a bound on auxiliary use

The roots lie outside `U`, the auxiliaries inside `U`. Taking `U` to be the
outside of a vortex child covers an internal recut towards the parent.
The two-root reserve is an input; it is not inferred from degree bounds.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.LoadControlledCoverStage116

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105

variable {V : Type*} [Finite V] [DecidableEq V]

theorem exists_cover (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ x y, s(x, y) ∈ E → p x ≠ p y) (U : Finset V)
    (H R : Finset (Sym2 V)) (h a q : ℕ) (hq : 0 < q)
    (hHE : H ⊆ E) (hRE : R ⊆ E)
    (hH : ∀ x y, s(x, y) ∈ H → x ∉ U ∧ y ∉ U)
    (hR : ∀ e ∈ R, IsSpoke U e)
    (hdeg : ∀ x, x ∉ U → incidentLoad H x ≤ h)
    (hrich : ∀ x y, s(x, y) ∈ H →
      a ≤ (U.filter fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R).card)
    (hbudget : 2 * h + H.card / q < a) :
    ∃ S ⊆ R, HasDecomp p F3 (H ∪ S) ∧
      (∀ x, x ∉ U → incidentLoad S x = incidentLoad H x) ∧
      ∀ z ∈ U, incidentLoad S z ≤ 2 * q := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hspoke_not : ∀ e ∈ R, e ∉ H := by
    intro e he heH
    obtain ⟨x, y, hx, hy, rfl⟩ := hR e he
    exact (hH x y heH).2 hy
  have key : ∀ A ⊆ H, ∃ S ⊆ R, ∃ f : V → ℕ,
      HasDecomp p F3 (A ∪ S) ∧
      (∀ x, x ∉ U → incidentLoad S x = incidentLoad A x) ∧
      (∀ z ∈ U, incidentLoad S z = 2 * f z) ∧
      (∀ z, f z ≤ q) ∧ ∑ z, f z = A.card := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨∅, empty_subset _, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [hasDecomp_empty, incidentLoad]
    | @insert e A heA ih =>
      intro hsub
      obtain ⟨S, hSR, f, hdec, hload, haux, hf, hsum⟩ :=
        ih ((subset_insert e A).trans hsub)
      have heH : e ∈ H := hsub (mem_insert_self e A)
      induction e using Sym2.ind with
      | _ x y =>
      obtain ⟨hx, hy⟩ := hH x y heH
      have nxy : x ≠ y := fun hh => hcross x y (hHE heH) (hh ▸ rfl)
      let Bad := (U.filter fun z => s(x, z) ∈ S) ∪ (U.filter fun z => s(y, z) ∈ S)
      let Sat := univ.filter (fun z => q ≤ f z)
      have hbad : Bad.card ≤ 2 * h := by
        have hxload := (incidentLoad_mono ((subset_insert _ _).trans hsub) x).trans (hdeg x hx)
        have hyload := (incidentLoad_mono ((subset_insert _ _).trans hsub) y).trans (hdeg y hy)
        have hxcard := card_spoke_filter_le U S x
        have hycard := card_spoke_filter_le U S y
        rw [hload x hx] at hxcard
        rw [hload y hy] at hycard
        exact (card_union_le _ _).trans (by omega)
      have hsat : Sat.card ≤ H.card / q := by
        apply (Nat.le_div_iff_mul_le hq).mpr
        have hs := saturated_card_budget f q
        rw [hsum] at hs
        have ha := card_le_card ((subset_insert _ _).trans hsub)
        change q * Sat.card ≤ A.card at hs
        simpa only [Nat.mul_comm] using hs.trans ha
      have hblocked : (Bad ∪ Sat).card < a :=
        (card_union_le _ _).trans_lt (by omega)
      obtain ⟨z, hzR, hzB⟩ : ∃ z ∈ U.filter (fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R),
          z ∉ Bad ∪ Sat := by
        by_contra hno
        push Not at hno
        have hs := card_le_card (show U.filter (fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R)
          ⊆ Bad ∪ Sat from hno)
        have hr := hrich x y heH
        omega
      obtain ⟨hzU, hxz, hyz⟩ := mem_filter.mp hzR
      have hzBad : z ∉ Bad := fun hz => hzB (mem_union_left _ hz)
      have hzSat : z ∉ Sat := fun hz => hzB (mem_union_right _ hz)
      have hfz : f z < q := by simpa only [Sat, mem_filter, mem_univ, true_and, not_le] using hzSat
      have hxzS : s(x, z) ∉ S := fun hh => hzBad (mem_union_left _ (mem_filter.mpr ⟨hzU, hh⟩))
      have hyzS : s(y, z) ∉ S := fun hh => hzBad (mem_union_right _ (mem_filter.mpr ⟨hzU, hh⟩))
      have nxz : x ≠ z := fun hh => hx (hh ▸ hzU)
      have nyz : y ≠ z := fun hh => hy (hh ▸ hzU)
      have hne : s(x, z) ≠ s(y, z) := by
        intro hh
        rcases Sym2.eq_iff.mp hh with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact nxy h1
        · exact nxz h1
      have hyzS' : s(y, z) ∉ insert s(x, z) S := by
        simp only [mem_insert, not_or]
        exact ⟨hne.symm, hyzS⟩
      refine ⟨insert s(y, z) (insert s(x, z) S), ?_,
        fun w => f w + if w = z then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [mem_insert] at hg
        rcases hg with rfl | rfl | hg
        exacts [hyz, hxz, hSR hg]
      · have htri := hasDecomp_tri p E hcross (hHE heH) (hRE hxz) (hRE hyz)
        have hd : Disjoint (A ∪ S) {s(x, y), s(x, z), s(y, z)} := by
          rw [disjoint_left]
          intro g hg hg'
          simp only [mem_insert, mem_singleton] at hg'
          rcases mem_union.mp hg with hgA | hgS
          · rcases hg' with rfl | rfl | rfl
            · exact heA hgA
            · exact (hH x z (hsub (mem_insert_of_mem hgA))).2 hzU
            · exact (hH y z (hsub (mem_insert_of_mem hgA))).2 hzU
          · rcases hg' with rfl | rfl | rfl
            · exact hspoke_not _ (hSR hgS) heH
            · exact hxzS hgS
            · exact hyzS hgS
        have hh := hdec.union htri hd
        convert hh using 1
        ext g
        simp only [mem_union, mem_insert, mem_singleton]
        tauto
      · intro w hw
        rw [incidentLoad_insert hyzS', incidentLoad_insert hxzS,
          incidentLoad_insert heA, hload w hw]
        have hwz : w ≠ z := fun hh => hw (hh ▸ hzU)
        simp only [Sym2.mem_iff, hwz, or_false]
        by_cases hwx : w = x
        · subst hwx; simp [nxy]
        · by_cases hwy : w = y
          · subst hwy; simp [hwx]
          · simp [hwx, hwy]
      · intro w hw
        have hwx : w ≠ x := fun hh => hx (hh ▸ hw)
        have hwy : w ≠ y := fun hh => hy (hh ▸ hw)
        rw [incidentLoad_insert hyzS', incidentLoad_insert hxzS, haux w hw]
        simp only [Sym2.mem_iff, hwx, hwy, false_or]
        split_ifs <;> omega
      · intro w
        by_cases hw : w = z
        · subst hw; simpa using hfz
        · simp [hw, hf w]
      · rw [sum_add_distrib, hsum, card_insert_of_notMem heA]
        simp
  obtain ⟨S, hSR, f, hd, hr, ha, hf, _⟩ := key H subset_rfl
  exact ⟨S, hSR, hd, hr, fun z hz => (ha z hz).trans_le (Nat.mul_le_mul_left 2 (hf z))⟩

end PartitionedTriangleAbsorption.LoadControlledCoverStage116
