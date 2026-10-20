/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Template

/-! # Coloured hubs III: the two transformers share the target `J`

`T_P` transforms the trail of `P₂` into `J`, read along the trail system of `P`.
`T_Q` transforms the trail of `Q₂` into `J`, read along the comparison triangles, and
traversing each private path `J_i` forwards or backwards according to the orientation of the
matched comparison slot (`flipPos`). Both are genuine part-preserving trail maps; the edge
sets of the two targets coincide (`srcEdges_pathJQ`). No agreement of directed type counts is
used: only the unordered matching `hM` of each slot with its position.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer

variable {t : ℕ} {V : Type*} {m : ℕ} {T : Type*}
variable {p : V → Fin t} {σ : Equiv.Perm (Fin m)} {X : Fin m → V}
  {w : T → Fin 3 → Fin t} {π : Fin m ≃ T × Fin 3}

/-- The matched comparison slot of position `i` has the same unordered part pair. -/
def Matched (p : V → Fin t) (σ : Equiv.Perm (Fin m)) (X : Fin m → V)
    (w : T → Fin 3 → Fin t) (π : Fin m ≃ T × Fin 3) : Prop :=
  ∀ i, s(pq w π i, pq w π (qPerm π i)) = s(rP p X i, sP p σ X i)

theorem orient_fwd (hM : Matched p σ X w π) (i : Fin m) (h : pq w π i = rP p X i) :
    pq w π (qPerm π i) = sP p σ X i := by
  rcases Sym2.eq_iff.mp (hM i) with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · rw [h2, ← h, h1]

theorem orient_rev (hM : Matched p σ X w π) (i : Fin m) (h : pq w π i ≠ rP p X i) :
    pq w π i = sP p σ X i ∧ pq w π (qPerm π i) = rP p X i := by
  rcases Sym2.eq_iff.mp (hM i) with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd h1 h
  · exact ⟨h1, h2⟩

/-- The third corner completes the matched pair to an allowed type. -/
theorem matched_mem {F : Finset (Multiset (Fin t))}
    (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) (hM : Matched p σ X w π)
    (i : Fin m) : ({rP p X i, sP p σ X i, cP w π i} : Multiset (Fin t)) ∈ F := by
  have h := pq_mem hw π i
  by_cases hf : pq w π i = rP p X i
  · rw [← hf, ← orient_fwd hM i hf]; exact h
  · obtain ⟨h1, h2⟩ := orient_rev hM i hf
    rw [← h1, ← h2]
    have e : ({pq w π (qPerm π i), pq w π i, cP w π i} : Multiset (Fin t)) =
        {pq w π i, pq w π (qPerm π i), cP w π i} := by
      simp only [Multiset.insert_eq_cons]; rw [Multiset.cons_swap]
    rw [e]; exact h

theorem pathJQ_zero (i : Fin m) : pathJQ p X w π (i, 0) = (hub (pq w π i) : HV V m t) := by
  unfold pathJQ
  split_ifs with h
  · simp [pathJ, h]
  · simp [pathJrev]

/-- Reversal of the four positions of a path. -/
def rev4 : Fin 4 → Fin 4 := ![3, 2, 1, 0]

theorem rev4_injective : Function.Injective rev4 := by decide

/-- The position of `J` hit by the comparison trail at `z`. -/
def flipPos (p : V → Fin t) (X : Fin m → V) (w : T → Fin 3 → Fin t) (π : Fin m ≃ T × Fin 3)
    (z : Fin m × Fin 4) : Fin m × Fin 4 :=
  if pq w π z.1 = rP p X z.1 then z else (z.1, rev4 z.2)

theorem flipPos_injective : Function.Injective (flipPos p X w π) := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  have hi : i = i' := by
    unfold flipPos at h; split_ifs at h <;> exact congrArg Prod.fst h
  subst hi
  unfold flipPos at h
  split_ifs at h with h1
  · exact h
  · simp only [Prod.mk.injEq, true_and] at h
    rw [rev4_injective h]

theorem flipPos_surjective : Function.Surjective (flipPos p X w π) :=
  Finite.injective_iff_surjective.mp flipPos_injective

theorem pathJQ_fwd {i : Fin m} (h : pq w π i = rP p X i) (k : Fin 4) :
    pathJQ p X w π (i, k) = (pathJ p X (i, k) : HV V m t) := by
  simp [pathJQ, h]

theorem pathJQ_rev {i : Fin m} (h : pq w π i ≠ rP p X i) (k : Fin 4) :
    pathJQ p X w π (i, k) = (pathJrev w π (i, k) : HV V m t) := by
  simp [pathJQ, h]

/-- **Edge correspondence.** The comparison trail traverses exactly the edges of `J`. -/
theorem pathJQ_edge (hM : Matched p σ X w π) (z : Fin m × Fin 4) :
    s(pathJQ p X w π z, pathJQ p X w π (blowPerm (qPerm π) z)) =
      (s(pathJ p X (flipPos p X w π z), pathJ p X (blowPerm σ (flipPos p X w π z))) :
        Sym2 (HV V m t)) := by
  obtain ⟨i, k⟩ := z
  by_cases hf : pq w π i = rP p X i
  · have h2 := orient_fwd hM i hf
    have hφ : flipPos p X w π (i, k) = (i, k) := by simp [flipPos, hf]
    rw [hφ]
    fin_cases k
    · simp only [Fin.zero_eta, blowPerm_apply]
      simp only [Fin.isValue, Fin.reduceEq, ite_false, zero_add, pathJQ_fwd hf]
    · simp only [Fin.mk_one, blowPerm_apply]
      simp only [Fin.isValue, Fin.reduceEq, ite_false, Fin.reduceAdd, pathJQ_fwd hf]
    · simp only [Fin.reduceFinMk, blowPerm_apply]
      simp only [Fin.isValue, Fin.reduceEq, ite_false, Fin.reduceAdd, pathJQ_fwd hf]
    · simp only [Fin.reduceFinMk, blowPerm_apply]
      simp only [Fin.isValue, ite_true, pathJQ_fwd hf, pathJQ_zero, h2]
      simp [pathJ, sP, rP]
  · obtain ⟨h1, h2⟩ := orient_rev hM i hf
    have hφ : ∀ k, flipPos p X w π (i, k) = (i, rev4 k) := by simp [flipPos, hf]
    rw [hφ]
    fin_cases k
    · simp only [Fin.zero_eta, blowPerm_apply]
      simp only [Fin.isValue, Fin.reduceEq, ite_false, zero_add, pathJQ_rev hf, rev4]
      simp [pathJrev, pathJ, h1, sP, rP, Sym2.eq_swap]
    · simp only [Fin.mk_one, blowPerm_apply]
      simp only [Fin.isValue, Fin.reduceEq, ite_false, Fin.reduceAdd, pathJQ_rev hf, rev4]
      simp [pathJrev, pathJ, Sym2.eq_swap]
    · simp only [Fin.reduceFinMk, blowPerm_apply]
      simp only [Fin.isValue, Fin.reduceEq, ite_false, Fin.reduceAdd, pathJQ_rev hf, rev4]
      simp [pathJrev, pathJ, Sym2.eq_swap]
    · simp only [Fin.reduceFinMk, blowPerm_apply]
      simp only [Fin.isValue, ite_true, pathJQ_rev hf, pathJQ_zero, h2, rev4]
      simp [pathJrev, pathJ, rP, Sym2.eq_swap]

/-- `J` read along the comparison graph. -/
theorem srcEdges_pathJQ [DecidableEq V] (hM : Matched p σ X w π) :
    srcEdges (blowPerm (qPerm π)) (pathJQ p X w π) = blkJ (V := V) p σ X := by
  rw [blkJ, srcEdges, srcEdges, posEdges, posEdges]
  ext e
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨flipPos p X w π z, (pathJQ_edge hM z).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨z', rfl⟩ := flipPos_surjective (p := p) (X := X) (w := w) (π := π) z
    exact ⟨z', pathJQ_edge hM z'⟩

/-! ### Transformer data -/

theorem tdata_P :
    TransformerData (blowPerm σ) (pathP (t := t) X) (pathJ (V := V) p X) auxTP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, k⟩; fin_cases k <;> simp [pathP, fourPath]
  · rintro ⟨j, k⟩; fin_cases k <;> simp [pathJ, fourPath]
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [pathP, fourPath] at h ⊢ <;> simp_all
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [pathJ, fourPath] at h ⊢ <;> simp_all
  · rintro ⟨⟨j, k⟩, c⟩ ⟨⟨j', k'⟩, c'⟩ h
    simp [auxTP] at h ⊢; tauto
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxTP, pathP, fourPath]
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxTP, pathJ, fourPath]
  · rintro ⟨j, k⟩ ⟨j', k'⟩; fin_cases k <;> fin_cases k' <;> simp [pathP, pathJ, fourPath]

theorem tdata_Q (hM : Matched p σ X w π) :
    TransformerData (blowPerm (qPerm π)) (pathQ (V := V) (t := t)) (pathJQ p X w π) auxTQ := by
  have hP := tdata_P (p := p) (σ := σ) (X := X)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, k⟩; fin_cases k <;> simp [pathQ, fourPath]
  · intro z hz
    have h1 := pathJQ_edge hM z
    rw [hz] at h1
    rcases Sym2.eq_iff.mp h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hP.hy _ (e1.symm.trans e2)
    · exact hP.hy _ (e2.symm.trans e1)
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [pathQ, fourPath] at h ⊢ <;> simp_all
  · intro z z' h
    simp only [pathJQ_edge hM] at h
    exact flipPos_injective (hP.hyinj h)
  · rintro ⟨⟨j, k⟩, c⟩ ⟨⟨j', k'⟩, c'⟩ h
    simp [auxTQ] at h ⊢; tauto
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxTQ, pathQ, fourPath]
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩
    unfold pathJQ
    split_ifs <;> fin_cases k' <;> simp [auxTQ, pathJ, pathJrev, fourPath]
  · rintro ⟨j, k⟩ ⟨j', k'⟩
    unfold pathJQ
    split_ifs <;> fin_cases k <;> fin_cases k' <;> simp [pathQ, pathJ, pathJrev, fourPath]

end PartitionedTriangleAbsorption.ColouredHub
