/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReservePhysicalQueryStage200

/-! # Degree tails for the same physical triangle-union reserve -/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReservePhysicalDegreeStage201

open Finset MeasureTheory ProbabilityTheory ReservePhysicalQueryStage200

variable {V : Type} [DecidableEq V] {t : ℕ}

theorem triangle_degree (s : Finset V) (hc : s.card = 3) (v : V) :
    ((triEdges s).filter fun e => v ∈ e).card = if v ∈ s then 2 else 0 := by
  classical
  by_cases hv : v ∈ s
  · have heq : ((triEdges s).filter fun e => v ∈ e) =
        (s.erase v).image (fun a => s(v, a)) := by
      ext e
      induction e using Sym2.ind with
      | _ a b =>
        simp only [mem_filter, TypedNibble.mem_triEdges_iff, mem_image, mem_erase, Sym2.mem_iff]
        constructor
        · rintro ⟨⟨ha, hb, hab⟩, rfl | rfl⟩
          · exact ⟨b, ⟨hab.symm, hb⟩, rfl⟩
          · exact ⟨a, ⟨hab, ha⟩, Sym2.eq_swap⟩
        · rintro ⟨c, ⟨hcv, hcs⟩, he⟩
          rw [Sym2.eq_iff] at he
          rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨hv, hcs, hcv.symm⟩, Or.inl rfl⟩
          · exact ⟨⟨hcs, hv, hcv⟩, Or.inr rfl⟩
    rw [heq, card_image_of_injective _ (fun a b h => Sym2.congr_right.mp h),
      card_erase_of_mem hv, hc]
    simp [hv]
  · have heq : ((triEdges s).filter fun e => v ∈ e) = ∅ := by
      ext e
      induction e using Sym2.ind with
      | _ a b =>
        simp only [mem_filter, TypedNibble.mem_triEdges_iff, Sym2.mem_iff, notMem_empty, iff_false]
        rintro ⟨⟨ha, hb, _⟩, rfl | rfl⟩ <;> contradiction
    simp [heq, hv]

theorem packing_degree (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (v : V) :
    (Q.filter fun e => v ∈ e).card = 2 * (D.filter fun s => v ∈ s).card := by
  classical
  rw [← hD.2.2, filter_biUnion, card_biUnion]
  · rw [sum_congr rfl (fun s hs => triangle_degree s (hD.1 s hs).1 v)]
    simp only [card_eq_sum_ones, sum_filter, mul_sum]
    apply sum_congr rfl
    intro s _
    split_ifs <;> simp
  · intro a ha b hb hab
    exact (hD.2.1 ha hb hab).mono (filter_subset _ _) (filter_subset _ _)

theorem physical_degree_upper_tail [Fintype V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (v : V)
    (μ : Measure (Finset V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun s => {ω | ω s = true}) μ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmarg : ∀ s, μ {ω | ω s = true} = ENNReal.ofReal ρ) :
    μ.real {ω | 2 * ρ * Fintype.card V ≤ ((reserve D ω).filter fun e => v ∈ e).card} ≤
      Real.exp (-ρ ^ 2 * Fintype.card V) := by
  classical
  have hn : 0 < (Fintype.card V : ℝ) := by
    have : Nonempty V := ⟨v⟩
    exact_mod_cast Fintype.card_pos
  have hcard : 2 * ((D.filter fun s => v ∈ s).card : ℝ) ≤ Fintype.card V := by
    have h := Nibble.card_star_le Q v
    change (Q.filter fun e => v ∈ e).card ≤ _ at h
    rw [packing_degree p F Q D hD v] at h
    exact_mod_cast h
  have heq : ∀ ω, (((reserve D ω).filter fun e => v ∈ e).card : ℝ) =
      2 * (((D.filter fun s => v ∈ s).filter fun s => ω s = true).card : ℝ) := by
    intro ω
    have hs : IsDecomp p F (reserve D ω) (selected D ω) :=
      ⟨fun s hs => hD.1 s (mem_filter.mp hs).1,
        hD.2.1.subset (filter_subset _ _), rfl⟩
    rw [packing_degree p F _ _ hs v, Nat.cast_mul, Nat.cast_ofNat]
    have hf : (selected D ω).filter (fun s => v ∈ s) =
        (D.filter fun s => v ∈ s).filter (fun s => ω s = true) := by
      ext s
      simp only [selected, mem_filter]
      tauto
    rw [hf]
  have hb := ReserveBlockTailsStage199.triangle_block_count_upper_tail μ hind ρ hρ hmarg
    (D.filter fun s => v ∈ s) (Fintype.card V) hn hcard
  simpa only [heq] using hb


end PartitionedTriangleAbsorption.ReservePhysicalDegreeStage201
