/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups

/-! # Two-mode assembly of a signed certificate (abstract cancellation mechanism)

This is the cancellation/multiplicity mechanism, stated abstractly and generically in `F`.

* `O` is the set of **occurrences** (a certificate term `c_j t_j` contributes `|c_j|`
  occurrences of `t_j`), each with a sign `pos o`.
* `S` is the set of **slots** (one per edge of each occurrence), `occ σ` its occurrence.
  Each slot carries a *wedge* `W σ` (the two edges joining its base edge to its apex).
* Every occurrence carries a *local closure* `Y o` such that both `Y o` and
  `R o = Y o ∪ ⋃_{σ ∈ o} W σ` are decomposable (the occurrence gadget).
* A bijection `μ` between positive slots and `P ⊕ negative slots` pairs every positive slot
  either with an edge of `P` (whose triangle with the slot wedge is decomposable) or with a
  negative slot `τ`; each negative slot carries a *slot hinge* `H τ` with both
  `H τ ∪ W τ` and `H τ ∪ W (μ⁻¹ τ)` decomposable.

Then, with all atoms pairwise edge-disjoint, `X = ⋃ Y ∪ ⋃ W ∪ ⋃ H` satisfies:
`X` is decomposable and `X ∪ P` is decomposable.

Mode `X`: hinges take the **negative** wedges, positive occurrences use `R o`, negative ones
use `Y o`. Mode `X ∪ P`: hinges take the **positive** wedges, each edge of `P` closes its
positive slot wedge to a triangle, negative occurrences use `R o`, positive ones use `Y o`.
No physical edge is ever used twice: a physical edge with multiplicity in the integer
certificate is represented by distinct slot wedges with distinct apices, and the slot hinges
cancel a positive against a negative use.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

theorem mem_group {ι κ : Type*} [Fintype ι] [DecidableEq κ] (a : ι → Finset (Sym2 V))
    (g : ι → κ) (k : κ) (e : Sym2 V) :
    e ∈ (univ.filter fun i => g i = k).biUnion a ↔ ∃ i, g i = k ∧ e ∈ a i := by
  simp

variable {O S : Type*} [Fintype O] [Fintype S] [DecidableEq O] [DecidableEq S]

/-- The local block `R o = Y o ∪ ⋃_{occ σ = o} W σ` of an occurrence. -/
def localBlock (occ : S → O) (Y : O → Finset (Sym2 V)) (W : S → Finset (Sym2 V)) (o : O) :
    Finset (Sym2 V) :=
  Y o ∪ (univ.filter fun σ => occ σ = o).biUnion W

omit [DecidableEq S] in
/-- **Two-mode assembly.** -/
theorem two_mode_assembly (pos : O → Prop) [DecidablePred pos] (occ : S → O)
    (P : Finset (Sym2 V)) (Y : O → Finset (Sym2 V)) (W : S → Finset (Sym2 V))
    (H : {τ : S // ¬ pos (occ τ)} → Finset (Sym2 V))
    (μ : {σ : S // pos (occ σ)} ≃ {f // f ∈ P} ⊕ {τ : S // ¬ pos (occ τ)})
    (hR : ∀ o, HasDecomp p F (localBlock occ Y W o))
    (hY : ∀ o, HasDecomp p F (Y o))
    (hHneg : ∀ τ, HasDecomp p F (H τ ∪ W τ.1))
    (hHpos : ∀ τ, HasDecomp p F (H τ ∪ W (μ.symm (Sum.inr τ)).1))
    (hPedge : ∀ f, HasDecomp p F (insert f.1 (W (μ.symm (Sum.inl f)).1)))
    (hYW : ∀ σ, Disjoint (Y (occ σ)) (W σ))
    (hWW : ∀ σ σ', σ ≠ σ' → occ σ = occ σ' → Disjoint (W σ) (W σ'))
    (hRR : ∀ o o', o ≠ o' → Disjoint (localBlock occ Y W o) (localBlock occ Y W o'))
    (hHR : ∀ τ o, Disjoint (H τ) (localBlock occ Y W o))
    (hHH : ∀ τ τ', τ ≠ τ' → Disjoint (H τ) (H τ'))
    (hRP : ∀ o, Disjoint (localBlock occ Y W o) P)
    (hHP : ∀ τ, Disjoint (H τ) P) :
    HasDecomp p F (univ.biUnion Y ∪ univ.biUnion W ∪ univ.biUnion H) ∧
      HasDecomp p F (univ.biUnion Y ∪ univ.biUnion W ∪ univ.biUnion H ∪ P) ∧
      Disjoint (univ.biUnion Y ∪ univ.biUnion W ∪ univ.biUnion H) P := by
  classical
  -- basic containments
  have hYR : ∀ o, Y o ⊆ localBlock occ Y W o := fun o => subset_union_left
  have hWR : ∀ σ, W σ ⊆ localBlock occ Y W (occ σ) := fun σ =>
    (subset_biUnion_of_mem W (by simp : σ ∈ univ.filter fun σ' => occ σ' = occ σ)).trans
      subset_union_right
  -- the atoms
  let atom : O ⊕ S ⊕ {τ : S // ¬ pos (occ τ)} ⊕ {f // f ∈ P} → Finset (Sym2 V) :=
    Sum.elim Y (Sum.elim W (Sum.elim H fun f => {f.1}))
  have hsing : ∀ (f : {f // f ∈ P}) (E : Finset (Sym2 V)), Disjoint E P →
      Disjoint E {f.1} := fun f E h => h.mono_right (singleton_subset_iff.mpr f.2)
  have hYW' : ∀ o σ, Disjoint (Y o) (W σ) := by
    intro o σ
    by_cases h : occ σ = o
    · rw [← h]; exact hYW σ
    · exact (hRR o (occ σ) (Ne.symm h)).mono (hYR o) (hWR σ)
  have hWW' : ∀ σ σ', σ ≠ σ' → Disjoint (W σ) (W σ') := by
    intro σ σ' hne
    by_cases h : occ σ = occ σ'
    · exact hWW σ σ' hne h
    · exact (hRR _ _ h).mono (hWR σ) (hWR σ')
  have hpair : Pairwise fun i j => Disjoint (atom i) (atom j) := by
    intro i j hij
    rcases i with o | σ | τ | f <;> rcases j with o' | σ' | τ' | f'
    · exact (hRR o o' (fun h => hij (by rw [h]))).mono (hYR o) (hYR o')
    · exact hYW' o σ'
    · exact ((hHR τ' o).mono_right (hYR o)).symm
    · exact hsing f' _ ((hRP o).mono_left (hYR o))
    · exact (hYW' o' σ).symm
    · exact hWW' σ σ' (fun h => hij (by rw [h]))
    · exact ((hHR τ' (occ σ)).mono_right (hWR σ)).symm
    · exact hsing f' _ ((hRP _).mono_left (hWR σ))
    · exact (hHR τ o').mono_right (hYR o')
    · exact (hHR τ (occ σ')).mono_right (hWR σ')
    · exact hHH τ τ' (fun h => hij (by rw [h]))
    · exact hsing f' _ (hHP τ)
    · exact (hsing f _ ((hRP o').mono_left (hYR o'))).symm
    · exact (hsing f _ ((hRP _).mono_left (hWR σ'))).symm
    · exact (hsing f _ (hHP τ')).symm
    · have hff : f.1 ≠ f'.1 := fun h => hij (by rw [Subtype.ext h])
      exact disjoint_singleton.mpr hff
  -- slots of an occurrence share its sign
  have hslot : ∀ o (e : Sym2 V),
      e ∈ (univ.filter fun σ => occ σ = o).biUnion W ↔ ∃ σ, occ σ = o ∧ e ∈ W σ := by
    intro o e; simp
  -- the two total unions
  have hunionB : univ.biUnion atom =
      univ.biUnion Y ∪ univ.biUnion W ∪ univ.biUnion H ∪ P := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, mem_union, Sum.exists, atom, Sum.elim_inl,
      Sum.elim_inr, mem_singleton]
    constructor
    · rintro (⟨o, h⟩ | ⟨σ, h⟩ | ⟨τ, h⟩ | ⟨f, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨o, h⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨σ, h⟩))
      · exact Or.inl (Or.inr ⟨τ, h⟩)
      · exact Or.inr f.2
    · rintro (((⟨o, h⟩ | ⟨σ, h⟩) | ⟨τ, h⟩) | h)
      · exact Or.inl ⟨o, h⟩
      · exact Or.inr (Or.inl ⟨σ, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨τ, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨e, h⟩, rfl⟩))
  let atomA : O ⊕ S ⊕ {τ : S // ¬ pos (occ τ)} ⊕ {f // f ∈ P} → Finset (Sym2 V) :=
    Sum.elim Y (Sum.elim W (Sum.elim H fun _ => ∅))
  have hpairA : Pairwise fun i j => Disjoint (atomA i) (atomA j) := by
    intro i j hij
    have h := hpair hij
    rcases i with o | σ | τ | f <;> rcases j with o' | σ' | τ' | f' <;>
      first | exact h | simp [atomA]
  have hunionA : univ.biUnion atomA = univ.biUnion Y ∪ univ.biUnion W ∪ univ.biUnion H := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, mem_union, Sum.exists, atomA, Sum.elim_inl,
      Sum.elim_inr, notMem_empty, exists_false, or_false]
    tauto
  -- disjointness from `P`
  have hXP : Disjoint (univ.biUnion Y ∪ univ.biUnion W ∪ univ.biUnion H) P := by
    simp only [disjoint_union_left, disjoint_biUnion_left]
    exact ⟨⟨fun o _ => (hRP o).mono_left (hYR o), fun σ _ => (hRP _).mono_left (hWR σ)⟩,
      fun τ _ => hHP τ⟩
  -- group maps
  let κ := O ⊕ {τ : S // ¬ pos (occ τ)} ⊕ {f // f ∈ P}
  let gA : O ⊕ S ⊕ {τ : S // ¬ pos (occ τ)} ⊕ {f // f ∈ P} → κ :=
    Sum.elim Sum.inl (Sum.elim
      (fun σ => if h : pos (occ σ) then Sum.inl (occ σ) else Sum.inr (Sum.inl ⟨σ, h⟩))
      (Sum.elim (fun τ => Sum.inr (Sum.inl τ)) (fun f => Sum.inr (Sum.inr f))))
  let gB : O ⊕ S ⊕ {τ : S // ¬ pos (occ τ)} ⊕ {f // f ∈ P} → κ :=
    Sum.elim Sum.inl (Sum.elim
      (fun σ => if h : pos (occ σ) then
        Sum.elim (fun f => Sum.inr (Sum.inr f)) (fun τ => Sum.inr (Sum.inl τ)) (μ ⟨σ, h⟩)
        else Sum.inl (occ σ))
      (Sum.elim (fun τ => Sum.inr (Sum.inl τ)) (fun f => Sum.inr (Sum.inr f))))
  refine ⟨?_, ?_, hXP⟩
  · -- mode `X`
    rw [← hunionA]
    refine hasDecomp_of_groups atomA gA hpairA ?_
    rintro (o | τ | f)
    · by_cases ho : pos o
      · convert hR o using 1
        ext e
        rw [mem_group]
        simp only [Sum.exists, gA, atomA, Sum.elim_inl, Sum.elim_inr, localBlock, mem_union,
          hslot]
        constructor
        · rintro (⟨o', h1, h2⟩ | ⟨σ, h1, h2⟩ | ⟨τ, h1, -⟩ | ⟨f, h1, -⟩)
          · cases h1; exact Or.inl h2
          · by_cases hσ : pos (occ σ)
            · rw [dite_eq_left hσ] at h1; cases h1; exact Or.inr ⟨σ, rfl, h2⟩
            · rw [dite_eq_right hσ] at h1; cases h1
          · cases h1
          · cases h1
        · rintro (h | ⟨σ, rfl, h⟩)
          · exact Or.inl ⟨o, rfl, h⟩
          · exact Or.inr (Or.inl ⟨σ, by rw [dite_eq_left ho], h⟩)
      · convert hY o using 1
        ext e
        rw [mem_group]
        simp only [Sum.exists, gA, atomA, Sum.elim_inl, Sum.elim_inr]
        constructor
        · rintro (⟨o', h1, h2⟩ | ⟨σ, h1, -⟩ | ⟨τ, h1, -⟩ | ⟨f, h1, -⟩)
          · cases h1; exact h2
          · by_cases hσ : pos (occ σ)
            · rw [dite_eq_left hσ] at h1; cases h1; exact absurd hσ ho
            · rw [dite_eq_right hσ] at h1; cases h1
          · cases h1
          · cases h1
        · intro h; exact Or.inl ⟨o, rfl, h⟩
    · convert hHneg τ using 1
      ext e
      rw [mem_group]
      simp only [Sum.exists, gA, atomA, Sum.elim_inl, Sum.elim_inr, mem_union]
      constructor
      · rintro (⟨o', h1, -⟩ | ⟨σ, h1, h2⟩ | ⟨τ', h1, h2⟩ | ⟨f, h1, -⟩)
        · cases h1
        · by_cases hσ : pos (occ σ)
          · rw [dite_eq_left hσ] at h1; cases h1
          · rw [dite_eq_right hσ] at h1; cases h1; exact Or.inr h2
        · cases h1; exact Or.inl h2
        · cases h1
      · rintro (h | h)
        · exact Or.inr (Or.inr (Or.inl ⟨τ, rfl, h⟩))
        · exact Or.inr (Or.inl ⟨τ.1, by rw [dite_eq_right τ.2], h⟩)
    · convert (empty_hasDecomp (p := p) (F := F)) using 1
      ext e
      rw [mem_group]
      simp only [Sum.exists, gA, atomA, Sum.elim_inl, Sum.elim_inr, notMem_empty, iff_false]
      rintro (⟨o', h1, -⟩ | ⟨σ, h1, -⟩ | ⟨τ', h1, -⟩ | ⟨f', -, h2⟩)
      · cases h1
      · by_cases hσ : pos (occ σ)
        · rw [dite_eq_left hσ] at h1; cases h1
        · rw [dite_eq_right hσ] at h1; cases h1
      · cases h1
      · exact h2
  · -- mode `X ∪ P`
    rw [← hunionB]
    refine hasDecomp_of_groups atom gB hpair ?_
    rintro (o | τ | f)
    · by_cases ho : pos o
      · convert hY o using 1
        ext e
        rw [mem_group]
        simp only [Sum.exists, gB, atom, Sum.elim_inl, Sum.elim_inr]
        constructor
        · rintro (⟨o', h1, h2⟩ | ⟨σ, h1, -⟩ | ⟨τ, h1, -⟩ | ⟨f, h1, -⟩)
          · cases h1; exact h2
          · by_cases hσ : pos (occ σ)
            · rw [dite_eq_left hσ] at h1
              rcases hμ : μ ⟨σ, hσ⟩ with f | τ <;> rw [hμ] at h1 <;> cases h1
            · rw [dite_eq_right hσ] at h1; cases h1; exact absurd ho hσ
          · cases h1
          · cases h1
        · intro h; exact Or.inl ⟨o, rfl, h⟩
      · convert hR o using 1
        ext e
        rw [mem_group]
        simp only [Sum.exists, gB, atom, Sum.elim_inl, Sum.elim_inr, localBlock, mem_union,
          hslot]
        constructor
        · rintro (⟨o', h1, h2⟩ | ⟨σ, h1, h2⟩ | ⟨τ, h1, -⟩ | ⟨f, h1, -⟩)
          · cases h1; exact Or.inl h2
          · by_cases hσ : pos (occ σ)
            · rw [dite_eq_left hσ] at h1
              rcases hμ : μ ⟨σ, hσ⟩ with f | τ <;> rw [hμ] at h1 <;> cases h1
            · rw [dite_eq_right hσ] at h1; cases h1; exact Or.inr ⟨σ, rfl, h2⟩
          · cases h1
          · cases h1
        · rintro (h | ⟨σ, rfl, h⟩)
          · exact Or.inl ⟨o, rfl, h⟩
          · exact Or.inr (Or.inl ⟨σ, by rw [dite_eq_right ho], h⟩)
    · convert hHpos τ using 1
      ext e
      rw [mem_group]
      simp only [Sum.exists, gB, atom, Sum.elim_inl, Sum.elim_inr, mem_union]
      constructor
      · rintro (⟨o', h1, -⟩ | ⟨σ, h1, h2⟩ | ⟨τ', h1, h2⟩ | ⟨f, h1, -⟩)
        · cases h1
        · by_cases hσ : pos (occ σ)
          · rw [dite_eq_left hσ] at h1
            rcases hμ : μ ⟨σ, hσ⟩ with f | τ'
            · rw [hμ] at h1; cases h1
            · rw [hμ] at h1
              cases h1
              have : (⟨σ, hσ⟩ : {σ : S // pos (occ σ)}) = μ.symm (Sum.inr τ) := by
                rw [← hμ, Equiv.symm_apply_apply]
              right; rw [← this]; exact h2
          · rw [dite_eq_right hσ] at h1; cases h1
        · cases h1; exact Or.inl h2
        · cases h1
      · rintro (h | h)
        · exact Or.inr (Or.inr (Or.inl ⟨τ, rfl, h⟩))
        · refine Or.inr (Or.inl ⟨(μ.symm (Sum.inr τ)).1, ?_, h⟩)
          rw [dite_eq_left (μ.symm (Sum.inr τ)).2]
          simp
    · convert hPedge f using 1
      ext e
      rw [mem_group]
      simp only [Sum.exists, gB, atom, Sum.elim_inl, Sum.elim_inr, mem_insert, mem_singleton]
      constructor
      · rintro (⟨o', h1, -⟩ | ⟨σ, h1, h2⟩ | ⟨τ', h1, -⟩ | ⟨f', h1, h2⟩)
        · cases h1
        · by_cases hσ : pos (occ σ)
          · rw [dite_eq_left hσ] at h1
            rcases hμ : μ ⟨σ, hσ⟩ with f' | τ'
            · rw [hμ] at h1
              cases h1
              have : (⟨σ, hσ⟩ : {σ : S // pos (occ σ)}) = μ.symm (Sum.inl f) := by
                rw [← hμ, Equiv.symm_apply_apply]
              right; rw [← this]; exact h2
            · rw [hμ] at h1; cases h1
          · rw [dite_eq_right hσ] at h1; cases h1
        · cases h1
        · cases h1; exact Or.inl h2
      · rintro (h | h)
        · exact Or.inr (Or.inr (Or.inr ⟨f, rfl, h⟩))
        · refine Or.inr (Or.inl ⟨(μ.symm (Sum.inl f)).1, ?_, h⟩)
          rw [dite_eq_left (μ.symm (Sum.inl f)).2]
          simp

end PartitionedTriangleAbsorption.SignedHinge
