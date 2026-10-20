/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Tauto

/-! # Repair a prescribed cross-class pairing without changing its profile

A same-class transposition repairs two pairs at once. The bound is on all
missing cross-class neighbours together, rather than on a single block.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairingRepairStage145

open Finset

variable {V K : Type*} [Fintype V]

def badPairs (R : V → V → Prop) [DecidableRel R] (f : V ≃ V) : Finset V :=
  univ.filter fun v => ¬ R v (f v)

def conjugate (f e : V ≃ V) : V ≃ V := (e.symm.trans f).trans e

omit [Fintype V] in
theorem conjugate_involutive (f e : V ≃ V) (hf : Function.Involutive f) :
    Function.Involutive (conjugate f e) := by
  intro v
  change ∀ x, f (f x) = x at hf
  simp only [conjugate, Equiv.trans_apply, Equiv.symm_apply_apply, hf,
    Equiv.apply_symm_apply]

omit [Fintype V] in
/-- A same-class swap preserves the class restriction on every pair. -/
theorem conjugate_cross (p : V → K) (f e : V ≃ V)
    (hf : ∀ v, p (f v) ≠ p v) (he : ∀ v, p (e v) = p v) :
    ∀ v, p (conjugate f e v) ≠ p v := by
  intro v
  have hs : p (e.symm v) = p v := by simpa using (he (e.symm v)).symm
  simpa only [conjugate, Equiv.trans_apply, he, hs] using hf (e.symm v)

/-- A physical two-pair switch strictly reduces the bad-vertex set. -/
theorem swap_repair [DecidableEq V] (R : V → V → Prop) [DecidableRel R]
    (hsym : ∀ u v, R u v → R v u) (p : V → K) (f : V ≃ V)
    (hf : Function.Involutive f) (hcross : ∀ v, p (f v) ≠ p v)
    (u w : V) (hp : p u = p w)
    (hbad : ¬ R u (f u)) (h1 : R u (f w)) (h2 : R w (f u)) :
    (badPairs R (conjugate f (Equiv.swap u w))).card < (badPairs R f).card := by
  classical
  change ∀ x, f (f x) = x at hf
  let g := conjugate f (Equiv.swap u w)
  have hfu_u : f u ≠ u := fun h => hcross u (congrArg p h)
  have hfw_w : f w ≠ w := fun h => hcross w (congrArg p h)
  have hfu_w : f u ≠ w := fun h => hcross u ((congrArg p h).trans hp.symm)
  have hfw_u : f w ≠ u := fun h => hcross w ((congrArg p h).trans hp)
  have hswfu : Equiv.swap u w (f u) = f u :=
    Equiv.swap_apply_of_ne_of_ne hfu_u hfu_w
  have hswfw : Equiv.swap u w (f w) = f w :=
    Equiv.swap_apply_of_ne_of_ne hfw_u hfw_w
  have hgu : g u = f w := by simp [g, conjugate, Equiv.symm_swap, hswfw]
  have hgw : g w = f u := by simp [g, conjugate, Equiv.symm_swap, hswfu]
  have hgfu : g (f u) = w := by simp [g, conjugate, Equiv.symm_swap, hswfu, hf]
  have hgfw : g (f w) = u := by simp [g, conjugate, Equiv.symm_swap, hswfw, hf]
  have hsub : badPairs R g ⊆ badPairs R f := by
    intro v hv
    have hvbad : ¬ R v (g v) := (mem_filter.mp hv).2
    by_cases hvu : v = u
    · exact False.elim (hvbad (hvu ▸ hgu ▸ h1))
    by_cases hvw : v = w
    · exact False.elim (hvbad (hvw ▸ hgw ▸ h2))
    by_cases hvfu : v = f u
    · subst v
      exact False.elim (hvbad (hgfu ▸ hsym _ _ h2))
    by_cases hvfw : v = f w
    · subst v
      exact False.elim (hvbad (hgfw ▸ hsym _ _ h1))
    have hfvu : f v ≠ u := fun h => hvfu (by simpa only [hf] using congrArg f h)
    have hfvw : f v ≠ w := fun h => hvfw (by simpa only [hf] using congrArg f h)
    have hgv : g v = f v := by
      simp only [g, conjugate, Equiv.trans_apply, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hvu hvw,
        Equiv.swap_apply_of_ne_of_ne hfvu hfvw]
    exact mem_filter.mpr ⟨mem_univ _, hgv ▸ hvbad⟩
  have huold : u ∈ badPairs R f := mem_filter.mpr ⟨mem_univ _, hbad⟩
  have hunew : u ∉ badPairs R g := by
    simp only [badPairs, mem_filter, mem_univ, true_and, hgu, not_not]
    exact h1
  exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hunew (h.symm ▸ huold)⟩)

/-- At most 2D+1 vertices are forbidden for a same-class repair. -/
theorem exists_switch_vertex [DecidableEq K]
    (R : V → V → Prop) [DecidableRel R]
    (hsym : ∀ u v, R u v → R v u) (p : V → K) (f : V ≃ V)
    (hcross : ∀ v, p (f v) ≠ p v) (u : V) (D : ℕ)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D)
    (hlarge : 2 * D + 1 < (univ.filter fun w => p w = p u).card) :
    ∃ w, u ≠ w ∧ p u = p w ∧ R u (f w) ∧ R w (f u) := by
  classical
  let C := univ.filter fun w => p w = p u
  let B₁ := C.filter fun w => ¬ R (f u) w
  let B₂ := C.filter fun w => ¬ R u (f w)
  have hb₁ : B₁.card ≤ D := by
    apply (card_le_card (t := univ.filter fun w => p w ≠ p (f u) ∧ ¬ R (f u) w) ?_).trans
      (hmiss (f u))
    intro w hw
    obtain ⟨hwC, hwR⟩ := mem_filter.mp hw
    have hpw : p w = p u := (mem_filter.mp hwC).2
    exact mem_filter.mpr ⟨mem_univ _, fun h => hcross u (h.symm.trans hpw), hwR⟩
  have hb₂ : B₂.card ≤ D := by
    have hsub : B₂.image f ⊆ univ.filter fun w => p w ≠ p u ∧ ¬ R u w := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      obtain ⟨hvC, hvR⟩ := mem_filter.mp hv
      have hpv : p v = p u := (mem_filter.mp hvC).2
      exact mem_filter.mpr ⟨mem_univ _, fun h => hcross v (h.trans hpv.symm), hvR⟩
    have hc := (card_le_card hsub).trans (hmiss u)
    rwa [card_image_of_injective B₂ f.injective] at hc
  let excluded := (B₁ ∪ B₂) ∪ {u}
  have hc : excluded.card ≤ 2 * D + 1 := by
    have h12 := card_union_le B₁ B₂
    have h3 := card_union_le (B₁ ∪ B₂) ({u} : Finset V)
    simp only [card_singleton] at h3
    dsimp only [excluded]
    omega
  obtain ⟨w, hwC, hwex⟩ := exists_mem_notMem_of_card_lt_card (hc.trans_lt hlarge)
  have hwu : w ≠ u := by
    intro h
    exact hwex (mem_union_right _ (mem_singleton.mpr h))
  have hn₁ : w ∉ B₁ := fun h => hwex (mem_union_left _ (mem_union_left _ h))
  have hn₂ : w ∉ B₂ := fun h => hwex (mem_union_left _ (mem_union_right _ h))
  have h1 : R u (f w) := by
    by_contra h
    exact hn₂ (mem_filter.mpr ⟨hwC, h⟩)
  have h2 : R (f u) w := by
    by_contra h
    exact hn₁ (mem_filter.mpr ⟨hwC, h⟩)
  exact ⟨w, hwu.symm, (mem_filter.mp hwC).2.symm, h1, hsym _ _ h2⟩

/-- Any cross-class pairing can be made physical by permuting within classes.
Thus all its prescribed class-pair counts are retained. -/
theorem exists_physical_conjugate [DecidableEq K]
    (R : V → V → Prop) [DecidableRel R]
    (hsym : ∀ u v, R u v → R v u) (p : V → K) (f : V ≃ V)
    (hf : Function.Involutive f) (hcross : ∀ v, p (f v) ≠ p v) (D : ℕ)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D)
    (hlarge : ∀ j k, j ≠ k →
      2 * D + 1 < (univ.filter fun w => p w = j).card ∨
      2 * D + 1 < (univ.filter fun w => p w = k).card) :
    ∃ e : V ≃ V, (∀ v, p (e v) = p v) ∧
      ∀ v, R v (conjugate f e v) := by
  classical
  let E : Finset (V ≃ V) := univ.filter fun e => ∀ v, p (e v) = p v
  have hE : E.Nonempty := ⟨Equiv.refl V, by simp [E]⟩
  obtain ⟨e, heE, hmin⟩ := exists_min_image E (fun e => (badPairs R (conjugate f e)).card) hE
  have he : ∀ v, p (e v) = p v := (mem_filter.mp heE).2
  let g := conjugate f e
  have hg : Function.Involutive g := conjugate_involutive f e hf
  have hgcross : ∀ v, p (g v) ≠ p v := conjugate_cross p f e hcross he
  refine ⟨e, he, ?_⟩
  intro v
  by_contra hv
  have hex : ∃ u, ¬ R u (g u) ∧
      2 * D + 1 < (univ.filter fun w => p w = p u).card := by
    obtain h | h := hlarge (p v) (p (g v)) (hgcross v).symm
    · exact ⟨v, hv, h⟩
    · refine ⟨g v, ?_, h⟩
      rw [show g (g v) = v from hg v]
      exact fun h => hv (hsym _ _ h)
  obtain ⟨u, hu, hularge⟩ := hex
  obtain ⟨w, _, hp, h1, h2⟩ := exists_switch_vertex R hsym p g hgcross u D hmiss hularge
  let e' := e.trans (Equiv.swap u w)
  have he' : e' ∈ E := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro x
    change p (Equiv.swap u w (e x)) = p x
    rw [Equiv.apply_swap_eq_self hp, he]
  have hc := swap_repair R hsym p g hg hgcross u w hp hu h1 h2
  have heq : conjugate f e' = conjugate g (Equiv.swap u w) := by
    ext x
    simp [conjugate, e', g]
  have hm := hmin e' he'
  rw [heq] at hm
  change (badPairs R g).card ≤ (badPairs R (conjugate g (Equiv.swap u w))).card at hm
  omega

/-- Relabelling within classes retains every oriented class-pair count. -/
theorem conjugate_count [DecidableEq K] (p : V → K) (f e : V ≃ V)
    (he : ∀ v, p (e v) = p v) (j k : K) :
    (univ.filter fun v => p v = j ∧ p (conjugate f e v) = k).card =
      (univ.filter fun v => p v = j ∧ p (f v) = k).card := by
  classical
  have hs (v : V) : p (e.symm v) = p v := by simpa using (he (e.symm v)).symm
  have hg (v : V) : conjugate f e (e v) = e (f v) := by simp [conjugate]
  have heq : (univ.filter fun v => p v = j ∧ p (conjugate f e v) = k) =
      (univ.filter fun v => p v = j ∧ p (f v) = k).image e := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hv
      refine ⟨e.symm v, ⟨(hs v).trans hv.1, ?_⟩, e.apply_symm_apply v⟩
      simpa only [conjugate, Equiv.trans_apply, he] using hv.2
    · rintro ⟨w, hw, rfl⟩
      simpa only [he, hg] using hw
  rw [heq, card_image_of_injective _ e.injective]

end PartitionedTriangleAbsorption.PairingRepairStage145
