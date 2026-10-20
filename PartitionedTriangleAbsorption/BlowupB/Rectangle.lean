/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CompleteBlowup
public import Mathlib.Tactic.Abel

/-! # BlowupB.Rectangle — step 1 of the reduction: edges ↦ canonical spokes + representative edges

For an edge `uv` of a complete `F`-blowup with representatives `R` (at least `5` per class), the
eight-triangle identity `edge_identity` rewrites `ind1 uv` modulo copies as

  `cs u (p v) + cs v (p u) + (edges among representatives)`,

where `cs x k = ind1 s(x, canon k x)` is the **canonical spoke** of `x` into class `k`
(`canon k x` is the representative of class `k` of index `0`, or of index `1` when `x` is that
representative). Summing over `E` (`step1`) gives the canonical form

  `indZ E ≡ ∑ x, ∑ k, degVec p E x k • cs x k + wRR`

at cost `8 |E|`, with `wRR` supported on representative–representative edges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### The eight-triangle identity -/

omit [Fintype V] in
/-- `uv ≡ u c₀ + v b₀ + (rep–rep edges)`: rectangle through `a` with corners `b, c`, then two
transfers of the spokes `u c ↦ u c₀` (through `s₁`) and `v b ↦ v b₀` (through `s₂`). -/
theorem edge_identity {u v a b c b₀ c₀ s₁ s₂ : V}
    (huv : u ≠ v) (hua : u ≠ a) (huc : u ≠ c) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hus₁ : u ≠ s₁) (hcs₁ : c ≠ s₁) (huc₀ : u ≠ c₀)
    (hc₀s₁ : c₀ ≠ s₁) (hvs₂ : v ≠ s₂) (hbs₂ : b ≠ s₂) (hvb₀ : v ≠ b₀) (hb₀s₂ : b₀ ≠ s₂) :
    ind1 s(u, v) - (ind1 s(u, c₀) + ind1 s(v, b₀) +
      (-(ind1 s(b, c)) - ind1 s(c, s₁) + ind1 s(c₀, s₁) - ind1 s(b, s₂) + ind1 s(b₀, s₂))) =
    (indZ (triEdges {u, a, v}) - indZ (triEdges {u, a, c}) - indZ (triEdges {b, a, v}) +
        indZ (triEdges {b, a, c})) +
      (indZ (triEdges {u, c, s₁}) - indZ (triEdges {u, c₀, s₁})) +
      (indZ (triEdges {v, b, s₂}) - indZ (triEdges {v, b₀, s₂})) := by
  rw [indZ_triEdges_three hua huv hva.symm, indZ_triEdges_three hua huc hac,
    indZ_triEdges_three hab.symm hvb.symm hva.symm, indZ_triEdges_three hab.symm hbc hac,
    indZ_triEdges_three huc hus₁ hcs₁, indZ_triEdges_three huc₀ hus₁ hc₀s₁,
    indZ_triEdges_three hvb hvs₂ hbs₂, indZ_triEdges_three hvb₀ hvs₂ hb₀s₂, ind1_swap b v]
  abel

/-! ### Canonical spokes -/

variable {p : V → Fin t} {q : ℕ}

/-- The canonical spoke of `x` into class `k`. -/
noncomputable def cs (R : Reps p q) (hq : 5 ≤ q) (x : V) (k : Fin t) : Sym2 V → ℤ :=
  ind1 s(x, R.canon (by omega) k x)

/-- The two canonical spokes of an edge: each endpoint into the class of the other. -/
noncomputable def spk (R : Reps p q) (hq : 5 ≤ q) (e : Sym2 V) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun u v => cs R hq u (p v) + cs R hq v (p u), fun u v => add_comm _ _⟩ e

omit [Fintype V] in
theorem spk_mk (R : Reps p q) (hq : 5 ≤ q) (u v : V) :
    spk R hq s(u, v) = cs R hq u (p v) + cs R hq v (p u) := rfl

theorem sum_sum_ite_pair {β : Type*} [AddCommGroup β] [Module ℤ β] (u : V) (j : Fin t)
    (f : V → Fin t → β) :
    ∑ x, ∑ k, (if u = x ∧ j = k then (1 : ℤ) else 0) • f x k = f u j := by
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [show ¬ (j = k) from fun h => hk h.symm]
    · intro h; exact absurd (mem_univ _) h
  · intro x _ hx
    simp [show ¬ (u = x) from fun h => hx h.symm]
  · intro h; exact absurd (mem_univ _) h

/-- The canonical spokes of an edge, written through `degContrib`. -/
theorem spk_eq_sum (R : Reps p q) (hq : 5 ≤ q) (e : Sym2 V) :
    spk R hq e = ∑ x, ∑ k, degContrib p x e k • cs R hq x k := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [spk_mk]
    simp only [degContrib, Sym2.lift_mk, add_smul, sum_add_distrib]
    rw [sum_sum_ite_pair, sum_sum_ite_pair]

/-- The canonical form of a sum of spokes: coefficients are the degree vectors. -/
theorem sum_spk (R : Reps p q) (hq : 5 ≤ q) (E : Finset (Sym2 V)) :
    ∑ e ∈ E, spk R hq e = ∑ x, ∑ k, degVec p E x k • cs R hq x k := by
  simp_rw [spk_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [degVec, Finset.sum_apply, sum_smul]

/-! ### Step 1 for one edge -/

omit [Fintype V] in
/-- **Step 1 for an edge.** In a complete blowup with at least `5` representatives per class,
`ind1 uv ≡ spk uv + wRR` modulo copies, at cost `8`, with `wRR` on representative edges. -/
theorem edge_step {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) (R : Reps p q) (hq : 5 ≤ q) {u v : V} (huv : G.Adj u v) :
    ∃ wRR : Sym2 V → ℤ, OnReps R wRR ∧
      PhysCostZ p F G (ind1 s(u, v) - (spk R hq s(u, v) + wRR)) 8 := by
  have hq2 : 2 ≤ q := by omega
  have hne : u ≠ v := G.ne_of_adj huv
  have hA : AllowedPair F (p u) (p v) := allowedPair_of_adj hG huv
  have hτ := third_spec F (p u) (p v) hA
  set k := third F (p u) (p v) hA with hk
  have hτ' : ({p u, k, p v} : Multiset (Fin t)) ∈ F := by rw [three_swap23]; exact hτ
  have hτ'' : ({p v, p u, k} : Multiset (Fin t)) ∈ F := by rw [three_swap12]; exact hτ
  obtain ⟨ic, hic⟩ := R.exists_avoid (p v) {u, v} (lt_of_le_of_lt card_le_two (by omega))
  obtain ⟨ib, hib⟩ := R.exists_avoid (p u) {u, v, R.rep (p v) ic}
    (lt_of_le_of_lt card_le_three (by omega))
  obtain ⟨ia, hia⟩ := R.exists_avoid k {u, v, R.rep (p u) ib, R.rep (p v) ic}
    (lt_of_le_of_lt card_le_four (by omega))
  obtain ⟨is₁, his₁⟩ := R.exists_avoid k {u, R.rep (p v) ic, R.canon hq2 (p v) u}
    (lt_of_le_of_lt card_le_three (by omega))
  obtain ⟨is₂, his₂⟩ := R.exists_avoid k {v, R.rep (p u) ib, R.canon hq2 (p u) v}
    (lt_of_le_of_lt card_le_three (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hic hib hia his₁ his₂
  set c := R.rep (p v) ic with hc
  set b := R.rep (p u) ib with hb
  set a := R.rep k ia with ha
  set s₁ := R.rep k is₁ with hs₁
  set s₂ := R.rep k is₂ with hs₂
  set c₀ := R.canon hq2 (p v) u with hc₀
  set b₀ := R.canon hq2 (p u) v with hb₀
  have hpc : p c = p v := R.cls _ _
  have hpb : p b = p u := R.cls _ _
  have hpa : p a = k := R.cls _ _
  have hps₁ : p s₁ = k := R.cls _ _
  have hps₂ : p s₂ = k := R.cls _ _
  have hpc₀ : p c₀ = p v := R.canon_cls hq2 _ _
  have hpb₀ : p b₀ = p u := R.canon_cls hq2 _ _
  have huc₀ : u ≠ c₀ := (R.canon_ne hq2 _ _).symm
  have hvb₀ : v ≠ b₀ := (R.canon_ne hq2 _ _).symm
  have hua : u ≠ a := fun h => hia.1 h.symm
  have hva : v ≠ a := fun h => hia.2.1 h.symm
  have hab : a ≠ b := hia.2.2.1
  have hac : a ≠ c := hia.2.2.2
  have huc : u ≠ c := fun h => hic.1 h.symm
  have hvb : v ≠ b := fun h => hib.2.1 h.symm
  have hbc : b ≠ c := hib.2.2
  have hus₁ : u ≠ s₁ := fun h => his₁.1 h.symm
  have hcs₁ : c ≠ s₁ := fun h => his₁.2.1 h.symm
  have hc₀s₁ : c₀ ≠ s₁ := fun h => his₁.2.2 h.symm
  have hvs₂ : v ≠ s₂ := fun h => his₂.1 h.symm
  have hbs₂ : b ≠ s₂ := fun h => his₂.2.1 h.symm
  have hb₀s₂ : b₀ ≠ s₂ := fun h => his₂.2.2 h.symm
  -- the eight copies
  have hT1 := physCostZ_of_isCopy (isCopy_of_complete hG hua hne hva.symm
    (by rw [hpa]; exact hτ'))
  have hT2 := physCostZ_of_isCopy (isCopy_of_complete hG hua huc hac
    (by rw [hpa, hpc]; exact hτ'))
  have hT3 := physCostZ_of_isCopy (isCopy_of_complete hG hab.symm hvb.symm hva.symm
    (by rw [hpa, hpb]; exact hτ'))
  have hT4 := physCostZ_of_isCopy (isCopy_of_complete hG hab.symm hbc hac
    (by rw [hpa, hpb, hpc]; exact hτ'))
  have hT5 := physCostZ_of_isCopy (isCopy_of_complete hG huc hus₁ hcs₁
    (by rw [hpc, hps₁]; exact hτ))
  have hT6 := physCostZ_of_isCopy (isCopy_of_complete hG huc₀ hus₁ hc₀s₁
    (by rw [hpc₀, hps₁]; exact hτ))
  have hT7 := physCostZ_of_isCopy (isCopy_of_complete hG hvb hvs₂ hbs₂
    (by rw [hpb, hps₂]; exact hτ''))
  have hT8 := physCostZ_of_isCopy (isCopy_of_complete hG hvb₀ hvs₂ hb₀s₂
    (by rw [hpb₀, hps₂]; exact hτ''))
  have hsum := ((((hT1.sub hT2).sub hT3).add hT4).add (hT5.sub hT6)).add (hT7.sub hT8)
  refine ⟨-(ind1 s(b, c)) - ind1 s(c, s₁) + ind1 s(c₀, s₁) - ind1 s(b, s₂) + ind1 s(b₀, s₂),
    ?_, ?_⟩
  · have hbR : b ∈ R.set := R.rep_mem _ _
    have hcR : c ∈ R.set := R.rep_mem _ _
    have hs₁R : s₁ ∈ R.set := R.rep_mem _ _
    have hs₂R : s₂ ∈ R.set := R.rep_mem _ _
    have hc₀R : c₀ ∈ R.set := R.canon_mem hq2 _ _
    have hb₀R : b₀ ∈ R.set := R.canon_mem hq2 _ _
    exact (((((OnReps.ind1 hbR hcR).neg.sub (OnReps.ind1 hcR hs₁R)).add
      (OnReps.ind1 hc₀R hs₁R)).sub (OnReps.ind1 hbR hs₂R)).add (OnReps.ind1 hb₀R hs₂R))
  · refine (hsum.congr ?_).mono (by norm_num)
    rw [spk_mk]
    unfold cs
    exact (edge_identity hne hua huc hva hvb hab hac hbc hus₁ hcs₁ huc₀ hc₀s₁ hvs₂ hbs₂ hvb₀
      hb₀s₂).symm

/-! ### Step 1 for an edge set -/

/-- **Step 1.** `indZ E ≡ ∑ x, ∑ k, degVec p E x k • cs x k + wRR` at cost `8 |E|`. -/
theorem step1 {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsCompleteBlowup p F G) (R : Reps p q) (hq : 5 ≤ q) {E : Finset (Sym2 V)}
    (hE : E ⊆ G.edgeFinset) :
    ∃ wRR : Sym2 V → ℤ, OnReps R wRR ∧
      PhysCostZ p F G (indZ E - (∑ x, ∑ k, degVec p E x k • cs R hq x k + wRR))
        (8 * E.card) := by
  have key : ∀ e : Sym2 V, ∃ w : Sym2 V → ℤ, e ∈ G.edgeFinset →
      OnReps R w ∧ PhysCostZ p F G (ind1 e - (spk R hq e + w)) 8 := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      by_cases he : s(u, v) ∈ G.edgeFinset
      · obtain ⟨w, hw, hc⟩ := edge_step hG R hq (SimpleGraph.mem_edgeFinset.mp he)
        exact ⟨w, fun _ => ⟨hw, hc⟩⟩
      · exact ⟨0, fun h => absurd h he⟩
  choose w hw using key
  refine ⟨∑ e ∈ E, w e, OnReps.sum _ _ (fun e he => (hw e (hE he)).1), ?_⟩
  have hrw : indZ E - (∑ x, ∑ k, degVec p E x k • cs R hq x k + ∑ e ∈ E, w e) =
      ∑ e ∈ E, (ind1 e - (spk R hq e + w e)) := by
    rw [← sum_spk, indZ_eq_sum_ind1, sum_sub_distrib, sum_add_distrib]
  rw [hrw]
  refine (PhysCostZ.sum E _ (fun _ => 8) (fun e he => (hw e (hE he)).2)).mono ?_
  rw [sum_const, nsmul_eq_mul, mul_comm]

end PartitionedTriangleAbsorption.BlowupB
