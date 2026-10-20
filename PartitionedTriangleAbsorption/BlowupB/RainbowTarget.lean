/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.RainbowTrails

/-! # BlowupB.RainbowTarget — the windmill target for rainbow trails

Positions `I` with a permutation `σ` and a phase `κ : I → Fin 3` increasing by one along `σ`
(for rainbow trails, `κ i` is the class of `x i`). Fresh vertices are given by an injective
`g : Slot3 I σ → W`: a centre `Z o` for every cycle `o` of `σ`, and `U j`, `Wt j` for every
position. The target trail

  `y i = Z ⟦i⟧`, `U (σ⁻¹ i)`, `Wt (σ⁻² i)` according as `κ i = 0, 1, 2`

is a **windmill** at every cycle: its edges are the triangles `{Z ⟦j⟧, U j, Wt j}` over the
positions `j` of phase `0` (`srcE_windmill`), hence it decomposes (`windmill_hasDecomp`). The
trail data `y i ≠ y (σ i)` and injectivity of the trail edges also hold.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv

variable {I : Type*} [Fintype I] [DecidableEq I] (σ : Perm I)

/-- The cycles of `σ`. -/
abbrev Orb : Type _ := Quotient (Perm.SameCycle.setoid σ)

/-- Slots of fresh target vertices: centres, `U`, `Wt`. -/
abbrev Slot3 : Type _ := Orb σ ⊕ (I ⊕ I)

variable {σ} {W : Type*} [DecidableEq W] (g : Slot3 σ → W) (κ : I → Fin 3)

/-- The windmill target trail. -/
noncomputable def windY (i : I) : W :=
  if κ i = 0 then g (Sum.inl ⟦i⟧)
  else if κ i = 1 then g (Sum.inr (Sum.inl (σ.symm i)))
  else g (Sum.inr (Sum.inr (σ.symm (σ.symm i))))

variable {g κ}

theorem orb_apply (i : I) : (⟦σ i⟧ : Orb σ) = ⟦i⟧ :=
  Quotient.sound (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl σ i))

theorem orb_symm (i : I) : (⟦σ.symm i⟧ : Orb σ) = ⟦i⟧ := by
  conv_rhs => rw [← σ.apply_symm_apply i]
  exact (orb_apply (σ.symm i)).symm

theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide

section Phase

variable (hκ : ∀ i, κ (σ i) = κ i + 1)
include hκ

theorem kappa_symm (i : I) : κ (σ.symm i) = κ i + 2 := by
  have := hκ (σ.symm i)
  rw [σ.apply_symm_apply] at this
  rw [this]; generalize κ (σ.symm i) = c; revert c; decide

theorem windY_zero {j : I} (hj : κ j = 0) : windY g κ j = g (Sum.inl ⟦j⟧) := by
  simp [windY, hj]

theorem windY_succ {j : I} (hj : κ j = 0) : windY g κ (σ j) = g (Sum.inr (Sum.inl j)) := by
  have h1 : κ (σ j) = 1 := by rw [hκ, hj]; rfl
  simp [windY, h1]

theorem windY_succ_succ {j : I} (hj : κ j = 0) :
    windY g κ (σ (σ j)) = g (Sum.inr (Sum.inr j)) := by
  have h2 : κ (σ (σ j)) = 2 := by rw [hκ, hκ, hj]; rfl
  simp [windY, h2]

theorem windY_succ3 {j : I} (hj : κ j = 0) :
    windY g κ (σ (σ (σ j))) = g (Sum.inl ⟦j⟧) := by
  have h3 : κ (σ (σ (σ j))) = 0 := by rw [hκ, hκ, hκ, hj]; rfl
  rw [windY_zero hκ h3, orb_apply, orb_apply, orb_apply]

/-- The block of a position: the phase-`0` position starting its triangle. -/
noncomputable def block (i : I) : I :=
  if κ i = 0 then i else if κ i = 1 then σ.symm i else σ.symm (σ.symm i)

omit hκ in
theorem block_spec (i : I) :
    (κ i = 0 ∧ block (κ := κ) (σ := σ) i = i) ∨ (κ i = 1 ∧ σ (block (κ := κ) (σ := σ) i) = i) ∨
      (κ i = 2 ∧ σ (σ (block (κ := κ) (σ := σ) i)) = i) := by
  unfold block
  rcases fin3_cases (κ i) with h | h | h <;> simp [h]

theorem kappa_block (i : I) : κ (block (κ := κ) (σ := σ) i) = 0 := by
  rcases block_spec (κ := κ) (σ := σ) i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩
  · rw [e]; exact h
  · rw [← e, hκ] at h
    generalize κ (block i) = c at h; revert c; decide
  · rw [← e, hκ, hκ] at h
    generalize κ (block i) = c at h; revert c; decide

/-- Every target trail edge is an edge of the triangle of its block. -/
theorem windY_edge (i : I) :
    s(windY g κ i, windY g κ (σ i)) = s(g (Sum.inl ⟦block (κ := κ) (σ := σ) i⟧),
        g (Sum.inr (Sum.inl (block (κ := κ) (σ := σ) i)))) ∧ κ i = 0 ∨
    s(windY g κ i, windY g κ (σ i)) = s(g (Sum.inr (Sum.inl (block (κ := κ) (σ := σ) i))),
        g (Sum.inr (Sum.inr (block (κ := κ) (σ := σ) i)))) ∧ κ i = 1 ∨
    s(windY g κ i, windY g κ (σ i)) = s(g (Sum.inr (Sum.inr (block (κ := κ) (σ := σ) i))),
        g (Sum.inl ⟦block (κ := κ) (σ := σ) i⟧)) ∧ κ i = 2 := by
  have bs := block_spec (κ := κ) (σ := σ) i
  have hj := kappa_block hκ i
  set j := block (κ := κ) (σ := σ) i with hjdef
  rcases bs with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩
  · left
    refine ⟨?_, h⟩
    rw [e, windY_zero hκ h, windY_succ hκ h]
  · right; left
    refine ⟨?_, h⟩
    rw [← e, windY_succ hκ hj, windY_succ_succ hκ hj]
  · right; right
    refine ⟨?_, h⟩
    rw [← e, windY_succ_succ hκ hj, windY_succ3 hκ hj]

end Phase

/-- Classes of the target slots. -/
def slotCls : Slot3 σ → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- The windmill triangles. -/
def windTri (g : Slot3 σ → W) (j : I) : Finset W :=
  {g (Sum.inl ⟦j⟧), g (Sum.inr (Sum.inl j)), g (Sum.inr (Sum.inr j))}

section Decomp

variable (hκ : ∀ i, κ (σ i) = κ i + 1) (hg : Function.Injective g)
include hκ hg

theorem windTri_edges (j : I) :
    triEdges (windTri g j) = {s(g (Sum.inl ⟦j⟧), g (Sum.inr (Sum.inl j))),
      s(g (Sum.inl ⟦j⟧), g (Sum.inr (Sum.inr j))),
      s(g (Sum.inr (Sum.inl j)), g (Sum.inr (Sum.inr j)))} :=
  triEdges_three (fun h => by simpa using hg h) (fun h => by simpa using hg h)
    (fun h => by simpa using hg h)

/-- **The windmill edges.** -/
theorem srcE_windmill :
    srcE σ (windY g κ) = (univ.filter fun j => κ j = 0).biUnion fun j => triEdges (windTri g j) := by
  ext e
  simp only [srcE, mem_image, mem_univ, true_and, mem_biUnion, mem_filter, windTri_edges hκ hg,
    mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨block (κ := κ) (σ := σ) i, kappa_block hκ i, ?_⟩
    rcases windY_edge (g := g) hκ i with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (h.trans Sym2.eq_swap))
  · rintro ⟨j, hj, h | h | h⟩
    · exact ⟨j, by rw [h, windY_zero hκ hj, windY_succ hκ hj]⟩
    · exact ⟨σ (σ j), by rw [h, windY_succ_succ hκ hj, windY_succ3 hκ hj, Sym2.eq_swap]⟩
    · exact ⟨σ j, by rw [h, windY_succ hκ hj, windY_succ_succ hκ hj]⟩

theorem slot_pair_eq {s1 s2 t1 t2 : Slot3 σ} (h : s(g s1, g s2) = s(g t1, g t2)) :
    (s1 = t1 ∧ s2 = t2) ∨ (s1 = t2 ∧ s2 = t1) := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hg h1, hg h2⟩
  · exact Or.inr ⟨hg h1, hg h2⟩

/-- **The windmill decomposes** (classes `0, 1, 2` on centres, `U`, `Wt`). -/
theorem windmill_hasDecomp {p : W → Fin 3}
    (hcls : ∀ s, p (g s) = slotCls s) :
    HasDecomp p R3 (srcE σ (windY g κ)) := by
  rw [srcE_windmill hκ hg]
  refine hasDecomp_biUnion _ _ (fun j _ => hasDecomp_tri ?_ ?_) ?_
  · exact Finset.card_eq_three.mpr ⟨_, _, _, fun h => by simpa using hg h,
      fun h => by simpa using hg h, fun h => by simpa using hg h, rfl⟩
  · unfold windTri
    rw [map_three p (fun h => by simpa using hg h) (fun h => by simpa using hg h)
      (fun h => by simpa using hg h), hcls, hcls, hcls]
    simp only [slotCls]; unfold R3; decide
  · intro j hj j' hj' hjj
    rw [windTri_edges hκ hg, windTri_edges hκ hg, disjoint_left]
    intro e he he'
    simp only [mem_insert, mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with h0 | h0 | h0 <;>
      rcases slot_pair_eq hκ hg h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h1 h2 <;>
      first
      | exact hjj h1
      | exact hjj h2

/-- Target trail data: consecutive target vertices differ. -/
theorem windY_ne (i : I) : windY g κ i ≠ windY g κ (σ i) := by
  intro h
  rcases windY_edge (g := g) hκ i with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [h] at e <;>
    rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact absurd (hg (h1.symm.trans h2)) (by simp)

/-- Target trail edges are injective. -/
theorem windY_edge_injective :
    Function.Injective fun i => s(windY g κ i, windY g κ (σ i)) := by
  intro i i' hii
  simp only at hii
  have hblock : ∀ i i', κ i = κ i' → block (κ := κ) (σ := σ) i = block (κ := κ) (σ := σ) i' →
      i = i' := by
    intro i i' hk hb
    rcases block_spec (κ := κ) (σ := σ) i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;>
      rcases block_spec (κ := κ) (σ := σ) i' with ⟨h', e'⟩ | ⟨h', e'⟩ | ⟨h', e'⟩ <;>
      first
      | (rw [h, h'] at hk; exact absurd hk (by decide))
      | (calc i = block (κ := κ) (σ := σ) i := e.symm
          _ = block (κ := κ) (σ := σ) i' := hb
          _ = i' := e')
      | (calc i = σ (block (κ := κ) (σ := σ) i) := e.symm
          _ = σ (block (κ := κ) (σ := σ) i') := by rw [hb]
          _ = i' := e')
      | (calc i = σ (σ (block (κ := κ) (σ := σ) i)) := e.symm
          _ = σ (σ (block (κ := κ) (σ := σ) i')) := by rw [hb]
          _ = i' := e')
  rcases windY_edge (g := g) hκ i with ⟨e, k⟩ | ⟨e, k⟩ | ⟨e, k⟩ <;>
    rcases windY_edge (g := g) hκ i' with ⟨e', k'⟩ | ⟨e', k'⟩ | ⟨e', k'⟩ <;>
    rw [e, e'] at hii <;>
    rcases slot_pair_eq hκ hg hii with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h1 h2 <;>
    first
    | exact hblock i i' (k.trans k'.symm) h1
    | exact hblock i i' (k.trans k'.symm) h2

end Decomp

end PartitionedTriangleAbsorption.BlowupB
