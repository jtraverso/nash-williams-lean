/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Packing158
public import RequestProject.NW18.Case125.Furedi

@[expose] public section

/-!
# Counting lemmas for the oddball cleaning (proof of Lemma 15.9)

For a triangle packing `T₁` every triangle of which meets `A`:
* `card_filter_mem_le_of_meets`: a vertex `v ∉ A` lies in at most `|A|` triangles of `T₁`;
* `two_mul_card_le_of_meets`: `2|T₁| ≤ |A| n`;
* `card_offA_le_of_meets`: `T₁` has at most `|T₁|` edges avoiding `A`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma card_filter_mem_le_of_meets (G : SimpleGraph V) {T : Finset (Finset V)}
    (hT : IsTrianglePacking G T) {A : Finset V} (hmeet : ∀ t ∈ T, ∃ a ∈ t, a ∈ A) {v : V}
    (hv : v ∉ A) : (T.filter (fun t => v ∈ t)).card ≤ A.card := by
  classical
  let f : Finset V → V := fun t => if h : ∃ a ∈ t, a ∈ A then h.choose else v
  have hf : ∀ t ∈ T, f t ∈ t ∧ f t ∈ A := by
    intro t ht
    have h := hmeet t ht
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine card_le_card_of_injOn f ?_ ?_
  · intro t ht
    exact (hf t (mem_filter.mp ht).1).2
  · intro t ht t' ht' heq
    simp only [coe_filter, Set.mem_setOf_eq] at ht ht'
    by_contra hne
    have ha := hf t ht.1
    have ha' := hf t' ht'.1
    have hva : v ≠ f t := fun h => hv (h ▸ ha.2)
    have h1 : s(v, f t) ∈ triEdges t := mk_mem_triEdges.mpr ⟨ht.2, ha.1, hva⟩
    have h2 : s(v, f t) ∈ triEdges t' := mk_mem_triEdges.mpr ⟨ht'.2, heq ▸ ha'.1, hva⟩
    exact disjoint_left.mp (hT.2 ht.1 ht'.1 hne) h1 h2

lemma two_mul_card_le_of_meets (G : SimpleGraph V) {T : Finset (Finset V)}
    (hT : IsTrianglePacking G T) {A : Finset V} (hmeet : ∀ t ∈ T, ∃ a ∈ t, a ∈ A) :
    2 * T.card ≤ A.card * Fintype.card V := by
  have hsub : T ⊆ A.biUnion (fun a => T.filter (fun t => a ∈ t)) := by
    intro t ht
    obtain ⟨a, hat, haA⟩ := hmeet t ht
    exact mem_biUnion.mpr ⟨a, haA, mem_filter.mpr ⟨ht, hat⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ a ∈ A, 2 * (T.filter (fun t => a ∈ t)).card ≤ ∑ _a ∈ A, Fintype.card V :=
    sum_le_sum fun a _ => two_mul_card_filter_mem_le G hT a
  rw [← mul_sum, sum_const, smul_eq_mul] at h2
  omega

lemma card_offA_le_of_meets (G : SimpleGraph V) {T : Finset (Finset V)}
    (hT : IsTrianglePacking G T) {A : Finset V} (hmeet : ∀ t ∈ T, ∃ a ∈ t, a ∈ A) :
    ((T.biUnion triEdges).filter (fun e => ∀ x ∈ e, x ∉ A)).card ≤ T.card := by
  have hsub : (T.biUnion triEdges).filter (fun e => ∀ x ∈ e, x ∉ A) ⊆
      T.biUnion (fun t => (triEdges t).filter (fun e => ∀ x ∈ e, x ∉ A)) := by
    intro e he
    simp only [mem_filter, mem_biUnion] at he ⊢
    obtain ⟨⟨t, ht, het⟩, hA⟩ := he
    exact ⟨t, ht, het, hA⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ t ∈ T, ((triEdges t).filter (fun e => ∀ x ∈ e, x ∉ A)).card ≤ ∑ _t ∈ T, 1 :=
        sum_le_sum fun t ht => by
          obtain ⟨a, hat, haA⟩ := hmeet t ht
          have h2 : (t.erase a).card = 2 := by
            rw [card_erase_of_mem hat, (hT.1 t ht).card_eq]
          obtain ⟨b, c, hbc, hbc'⟩ := card_eq_two.mp h2
          refine card_le_one.mpr fun e he e' he' => ?_
          have key : ∀ f ∈ (triEdges t).filter (fun e => ∀ x ∈ e, x ∉ A), f = s(b, c) := by
            intro f hf
            simp only [mem_filter] at hf
            obtain ⟨hft, hfA⟩ := hf
            induction f using Sym2.ind with
            | _ x y =>
              obtain ⟨hx, hy, hxy⟩ := mk_mem_triEdges.mp hft
              have hxa : x ≠ a := fun h => hfA x (Sym2.mem_mk_left x y) (h ▸ haA)
              have hya : y ≠ a := fun h => hfA y (Sym2.mem_mk_right x y) (h ▸ haA)
              have hx' : x ∈ t.erase a := mem_erase.mpr ⟨hxa, hx⟩
              have hy' : y ∈ t.erase a := mem_erase.mpr ⟨hya, hy⟩
              rw [hbc'] at hx' hy'
              simp only [mem_insert, mem_singleton] at hx' hy'
              rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
              · exact absurd rfl hxy
              · rfl
              · exact Sym2.eq_swap
              · exact absurd rfl hxy
          rw [key e he, key e' he']
    _ = T.card := by rw [sum_const, smul_eq_mul, mul_one]

end NashWilliams18
