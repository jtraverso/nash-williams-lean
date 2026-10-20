/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedDefinitions
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! # The exact padded extension condition supplies guarded common neighbours -/

namespace PaddedInputs

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V] {t K : ℕ}

/-- `ExtendableT` is invariant under numbering any finite template domain. -/
theorem ExtendableT.domain {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω : ℝ} (hext : ExtendableT K p F J ω)
    {D : Type*} [Fintype D] [DecidableEq D] (hD : Fintype.card D ≤ K)
    (κ : D → Fin t) (S : Finset D) (T : Finset (Sym2 D)) (φ : D → V)
    (hφ : Set.InjOn φ S) (hlabel : ∀ x ∈ S, p (φ x) = κ x) :
    ω * (Fintype.card V : ℝ) ^ (Fintype.card D - S.card) ≤
      ((goodExt p F J κ T S φ).card : ℝ) := by
  classical
  let e : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  let S' := S.image e
  let T' := T.image (Sym2.map e)
  have hScard : S'.card = S.card := card_image_of_injective S e.injective
  have hSmem (x : D) : e x ∈ S' ↔ x ∈ S := by simp [S']
  have hφ' : Set.InjOn (φ ∘ e.symm) (S' : Set (Fin (Fintype.card D))) := by
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at hab
    exact congrArg e (hφ hx hy hab)
  have hlabel' : ∀ x ∈ S', p ((φ ∘ e.symm) x) = (κ ∘ e.symm) x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hlabel y hy
  have hbase := hext (Fintype.card D) hD (κ ∘ e.symm) S' T' (φ ∘ e.symm) hφ' hlabel'
  have hcount : (goodExt p F J (κ ∘ e.symm) T' S' (φ ∘ e.symm)).card ≤
      (goodExt p F J κ T S φ).card := by
    apply card_le_card_of_injOn (fun ψ : Fin (Fintype.card D) → V => ψ ∘ e)
    · intro ψ hψ
      obtain ⟨hfix, hinj, hp, hT⟩ := (mem_goodExt _ _ _ _ _ _ _ _).mp hψ
      apply (mem_goodExt _ _ _ _ _ _ _ _).mpr
      refine ⟨?_, hinj.comp e.injective, ?_, ?_⟩
      · intro x hx
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hfix (e x) ((hSmem x).mpr hx)
      · intro x
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hp (e x)
      · intro x y hxy hne hroot hallowed
        apply hT (e x) (e y)
        · exact mem_image.mpr ⟨s(x, y), hxy, by simp⟩
        · exact fun h => hne (e.injective h)
        · simpa only [hSmem] using hroot
        · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hallowed
    · intro ψ hψ θ hθ hψθ
      funext z
      obtain ⟨x, rfl⟩ := e.surjective z
      exact congrFun hψθ x
  calc
    _ ≤ ((goodExt p F J (κ ∘ e.symm) T' S' (φ ∘ e.symm)).card : ℝ) := by
      simpa only [hScard] using hbase
    _ ≤ _ := by exact_mod_cast hcount

/-- A query with at most D roots uses only D+1 template vertices. -/
theorem guardedSupply_of_extendable (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ) (D : ℕ)
    (hK : D + 1 ≤ K) (hext : ExtendableT K p F G.edgeFinset ω) :
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) D (ω * Fintype.card V) := by
  classical
  by_cases hV : Fintype.card V = 0
  · intro U hU i hguard
    simpa only [hV, Nat.cast_zero, mul_zero] using
      (Nat.cast_nonneg (guardedNeighbours p G U i).card : (0 : ℝ) ≤ _)
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let fallback : V := Classical.choice (inferInstance : Nonempty V)
    intro U hU i hguard
    let W := Option {u : V // u ∈ U}
    let roots : Finset W := univ.image Option.some
    let label : W → Fin t := fun x => x.elim i (fun u => p u.val)
    let φ : W → V := fun x => x.elim fallback Subtype.val
    have hW : Fintype.card W = U.card + 1 := by simp [W]
    have hroots : roots.card = U.card := by
      rw [card_image_of_injective _ (fun _ _ h => Option.some.inj h)]
      simp
    have hroot (u : {u : V // u ∈ U}) : (some u : W) ∈ roots :=
      mem_image.mpr ⟨u, mem_univ _, rfl⟩
    have hnone : (none : W) ∉ roots := by simp [roots]
    have hφ : Set.InjOn φ roots := by
      intro a ha b hb hab
      obtain ⟨u, _, rfl⟩ := mem_image.mp ha
      obtain ⟨v, _, rfl⟩ := mem_image.mp hb
      exact congrArg Option.some (Subtype.ext hab)
    have hlabel : ∀ x ∈ roots, p (φ x) = label x := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := mem_image.mp hx
      rfl
    have hc := hext.domain (D := W) (by rw [hW]; omega) label roots univ φ hφ hlabel
    have hcount : (goodExt p F G.edgeFinset label univ roots φ).card ≤
        (guardedNeighbours p G U i).card := by
      apply card_le_card_of_injOn (fun ψ : W → V => ψ none)
      · intro ψ hψ
        obtain ⟨hfix, hinj, hp, hT⟩ := (mem_goodExt _ _ _ _ _ _ _ _).mp hψ
        apply mem_filter.mpr
        refine ⟨mem_univ _, hp none, ?_⟩
        intro u hu
        have hedge := hT (some ⟨u, hu⟩) none (mem_univ _) (by simp) (Or.inr hnone)
          ((allowedPair_iff_link F (p u) i).mpr (hguard u hu))
        rw [hfix (some ⟨u, hu⟩) (hroot ⟨u, hu⟩)] at hedge
        exact SimpleGraph.mem_edgeFinset.mp hedge
      · intro ψ hψ θ hθ heq
        have hfixψ := ((mem_goodExt _ _ _ _ _ _ _ _).mp hψ).1
        have hfixθ := ((mem_goodExt _ _ _ _ _ _ _ _).mp hθ).1
        funext x
        cases x with
        | none => exact heq
        | some u => exact (hfixψ _ (hroot u)).trans (hfixθ _ (hroot u)).symm
    have hbase : ω * Fintype.card V ≤ ((goodExt p F G.edgeFinset label univ roots φ).card : ℝ) := by
      have hexp : Fintype.card W - roots.card = 1 := by omega
      simpa only [hexp, pow_one] using hc
    exact hbase.trans (by exact_mod_cast hcount)

theorem class_card_of_extendable (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ)
    (hK : 1 ≤ K) (hext : ExtendableT K p F G.edgeFinset ω) (i : Fin t) :
    ω * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) :=
  (guardedSupply_of_extendable p F G ω 0 (by simpa using hK) hext).class_card i

#print axioms ExtendableT.domain
#print axioms guardedSupply_of_extendable
#print axioms class_card_of_extendable

end PaddedInputs
