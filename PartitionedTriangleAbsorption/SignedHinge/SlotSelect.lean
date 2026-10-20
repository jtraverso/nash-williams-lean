/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Select
public import PartitionedTriangleAbsorption.SignedHinge.Wedge
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # Greedy selection of all occurrence hinges and all slot hinges

Both selections only use `HingeSupply` through `exists_hinge_avoiding` (the vertex-only
exclusion count) and the anti-edge degree for the occurrence apices. Every chosen hinge has
its non-root support disjoint from a prescribed vertex set `U₀` and from the non-root
supports of all other chosen hinges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- **Slot hinges.** For every index `τ`, a hinge for `{u,v,w}` and `{u,v,w'}`, with non-root
supports pairwise disjoint and disjoint from `U₀`. -/
theorem exists_slot_hinges {N : Type*} [Fintype N] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj] {β : ℝ}
    {C0 : ℕ} (hsup : HingeSupply p F G β C0) (u v w w' : N → V)
    (hdist : ∀ τ, u τ ≠ v τ ∧ u τ ≠ w τ ∧ u τ ≠ w' τ ∧ v τ ≠ w τ ∧ v τ ≠ w' τ ∧ w τ ≠ w' τ)
    (hS : ∀ τ, IsCopy p F G {u τ, v τ, w τ}) (hS' : ∀ τ, IsCopy p F G {u τ, v τ, w' τ})
    (U₀ : Finset V) (M : ℕ) (hM : U₀.card + Fintype.card N * C0 ≤ M)
    (hβ : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * M < β * Fintype.card V) :
    ∃ H : N → Finset (Sym2 V),
      (∀ τ, H τ ⊆ G.edgeFinset ∧ IsHinge p F {u τ, v τ, w τ} {u τ, v τ, w' τ} (H τ) ∧
        (vertSet (H τ)).card ≤ C0 ∧
        Disjoint (vertSet (H τ) \ {u τ, v τ, w τ, w' τ}) U₀) ∧
      ∀ τ τ', τ ≠ τ' → Disjoint (vertSet (H τ) \ {u τ, v τ, w τ, w' τ})
        (vertSet (H τ') \ {u τ', v τ', w τ', w' τ'}) := by
  classical
  obtain ⟨H, hH, hHd⟩ := greedy_disjoint (univ : Finset N)
    (fun τ H => vertSet H \ {u τ, v τ, w τ, w' τ})
    (fun τ H => H ⊆ G.edgeFinset ∧ IsHinge p F {u τ, v τ, w τ} {u τ, v τ, w' τ} H ∧
      (vertSet H).card ≤ C0) U₀ C0 M
    (by
      intro τ _ U _ hU
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdist τ
      have hUβ : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * U.card < β * Fintype.card V := by
        refine lt_of_le_of_lt ?_ hβ
        gcongr
      obtain ⟨H, hHG, hHh, hHc, hHU⟩ :=
        exists_hinge_avoiding hsup h1 h2 h3 h4 h5 h6 (hS τ) (hS' τ) U hUβ
      refine ⟨H, ⟨hHG, hHh, hHc⟩, ?_, (card_le_card sdiff_subset).trans hHc⟩
      rw [disjoint_left]
      intro x hx hxU
      obtain ⟨hxH, hxR⟩ := mem_sdiff.mp hx
      apply hxR
      rcases hHU x hxH hxU with rfl | rfl | rfl | rfl <;> simp)
    (by simpa using hM)
  exact ⟨H, fun τ => ⟨(hH τ (mem_univ _)).1.1, (hH τ (mem_univ _)).1.2.1,
    (hH τ (mem_univ _)).1.2.2, (hH τ (mem_univ _)).2.1⟩,
    fun τ τ' h => hHd τ (mem_univ _) τ' (mem_univ _) h⟩

/-- **Occurrence apices and hinges.** For every index `o` with copy `{a,b,c}`, a fresh apex
`x` (a common neighbour of `a, b` in the part of `c`) and a hinge for `{a,b,c}`, `{a,b,x}`,
whose non-root supports (which contain `x`) are pairwise disjoint and disjoint from `U₀`. -/
theorem exists_occurrence_hinges {O : Type*} [Fintype O] [Inhabited V]
    {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]
    {α β : ℝ} {C0 : ℕ} (hsup : HingeSupply p F G β C0) (a b c : O → V)
    (hS : ∀ o, IsCopy p F G {a o, b o, c o})
    (hdist : ∀ o, a o ≠ b o ∧ a o ≠ c o ∧ b o ≠ c o)
    (hcand : ∀ o, α * Fintype.card V ≤
      (univ.filter fun w => G.Adj (a o) w ∧ G.Adj w (b o) ∧ p w = p (c o)).card)
    (U₀ : Finset V) (hroots : ∀ o, ({a o, b o, c o} : Finset V) ⊆ U₀) (M : ℕ)
    (hM : U₀.card + Fintype.card O * C0 ≤ M) (hα : (M : ℝ) < α * Fintype.card V)
    (hβ : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * (M + 1) < β * Fintype.card V) :
    ∃ (x : O → V) (H : O → Finset (Sym2 V)),
      (∀ o, G.Adj (a o) (x o) ∧ G.Adj (x o) (b o) ∧ p (x o) = p (c o) ∧
        H o ⊆ G.edgeFinset ∧ IsHinge p F {a o, b o, c o} {a o, b o, x o} (H o) ∧
        (vertSet (H o)).card ≤ C0 ∧ x o ∈ vertSet (H o) \ {a o, b o, c o} ∧
        Disjoint (vertSet (H o) \ {a o, b o, c o}) U₀) ∧
      ∀ o o', o ≠ o' → Disjoint (vertSet (H o) \ {a o, b o, c o})
        (vertSet (H o') \ {a o', b o', c o'}) := by
  classical
  obtain ⟨f, hf, hfd⟩ := greedy_disjoint (univ : Finset O)
    (fun o (xH : V × Finset (Sym2 V)) => vertSet xH.2 \ {a o, b o, c o})
    (fun o xH => G.Adj (a o) xH.1 ∧ G.Adj xH.1 (b o) ∧ p xH.1 = p (c o) ∧
      xH.2 ⊆ G.edgeFinset ∧ IsHinge p F {a o, b o, c o} {a o, b o, xH.1} xH.2 ∧
      (vertSet xH.2).card ≤ C0 ∧ xH.1 ∈ vertSet xH.2 \ {a o, b o, c o}) U₀ C0 M
    (by
      intro o _ U hU0 hU
      obtain ⟨hab, hac, hbc⟩ := hdist o
      -- the apex
      obtain ⟨x, hx, hxU⟩ := exists_mem_notMem_of_card_lt_card
        (s := U) (t := univ.filter fun w => G.Adj (a o) w ∧ G.Adj w (b o) ∧ p w = p (c o))
        (by
          have : (U.card : ℝ) < (univ.filter fun w =>
              G.Adj (a o) w ∧ G.Adj w (b o) ∧ p w = p (c o)).card :=
            lt_of_le_of_lt (by exact_mod_cast hU) (hα.trans_le (hcand o))
          exact_mod_cast this)
      obtain ⟨hax, hxb, hpx⟩ := (mem_filter.mp hx).2
      have hrU : ∀ y ∈ ({a o, b o, c o} : Finset V), y ∈ U := fun y hy => hU0 (hroots o hy)
      have hxa : x ≠ a o := fun h => hxU (h ▸ hrU _ (by simp))
      have hxb' : x ≠ b o := fun h => hxU (h ▸ hrU _ (by simp))
      have hxc : x ≠ c o := fun h => hxU (h ▸ hrU _ (by simp))
      obtain ⟨hAab, hAac, hAbc⟩ := SimpleGraph.is3Clique_triple_iff.mp (hS o).1
      have hS' : IsCopy p F G {a o, b o, x} := by
        refine isCopy_three hAab hax hxb.symm ?_
        rw [map_three p hab (Ne.symm hxa) (Ne.symm hxb'), hpx,
          ← map_three p hab hac hbc]
        exact (hS o).2
      have hU' : (2 ^ Nat.choose (C0 + 1) 2 : ℝ) * (insert x U).card <
          β * Fintype.card V := by
        refine lt_of_le_of_lt ?_ hβ
        gcongr
        exact_mod_cast (card_insert_le _ _).trans (Nat.succ_le_succ hU)
      obtain ⟨H, hHG, hHh, hHc, hHU⟩ := exists_hinge_avoiding hsup hab hac (Ne.symm hxa)
        hbc (Ne.symm hxb') (Ne.symm hxc) (hS o) hS' (insert x U) hU'
      have hroot := IsHinge.four_roots H _ _ _ _ hab hac (Ne.symm hxa) hbc (Ne.symm hxb')
        (Ne.symm hxc) hHh
      rw [← vertSet_eq_support] at hroot
      have hxv : x ∈ vertSet H \ {a o, b o, c o} :=
        mem_sdiff.mpr ⟨hroot (by simp), by simp [hxa, hxb', hxc]⟩
      refine ⟨(x, H), ⟨hax, hxb, hpx, hHG, hHh, hHc, hxv⟩, ?_,
        (card_le_card sdiff_subset).trans hHc⟩
      rw [disjoint_left]
      intro y hy hyU
      obtain ⟨hyH, hyR⟩ := mem_sdiff.mp hy
      rcases hHU y hyH (mem_insert_of_mem hyU) with rfl | rfl | rfl | rfl
      · exact hyR (by simp)
      · exact hyR (by simp)
      · exact hyR (by simp)
      · exact hxU hyU)
    (by simpa using hM)
  refine ⟨fun o => (f o).1, fun o => (f o).2, fun o => ?_,
    fun o o' h => hfd o (mem_univ _) o' (mem_univ _) h⟩
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, -⟩ := hf o (mem_univ _)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end PartitionedTriangleAbsorption.SignedHinge
