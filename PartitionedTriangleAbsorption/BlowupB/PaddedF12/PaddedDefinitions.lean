/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostSupply
import PartitionedTriangleAbsorption.TypedTransformerLabels
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact padded input definitions supplied in INPUT_TASK.md

The unavailable `BlowupB.KeevashPadded` source is not imported or impersonated.
These definitions reproduce the supplied statement in the separate namespace
`PaddedInputs`, while using the original `IsIntDiv`, `triEdges` and `HasDecomp`.
-/

namespace PaddedInputs

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer

variable {t : ℕ}

def AllowedPair (F : Finset (Multiset (Fin t))) (i j : Fin t) : Prop :=
  ∃ τ ∈ F, Multiset.card τ = 3 ∧ ({i, j} : Multiset (Fin t)) ≤ τ

abbrev PosT (t m : ℕ) := Fin t × Fin (m + 3)

abbrev qT (t m : ℕ) : ℕ := t * (m + 3)

def patPosT (m : ℕ) (τ : Multiset (Fin t)) : Finset (PosT t m) :=
  univ.filter fun x => x.2.val < τ.count x.1

variable {V : Type*} [Fintype V] [DecidableEq V]

def copyTriT (m : ℕ) (τ : Multiset (Fin t)) (φ : PosT t m → V) : Finset V :=
  (patPosT m τ).image φ

def IsEmbT (m : ℕ) (p : V → Fin t) (φ : PosT t m → V) : Prop :=
  Function.Injective φ ∧ ∀ x, p (φ x) = x.1

def ValidCopyT (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V)) (τ : Multiset (Fin t))
    (φ : PosT t m → V) : Prop :=
  IsEmbT m p φ ∧ triEdges (copyTriT m τ φ) ⊆ J

open Classical in
def PaddedRegularT (m : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V)) (ω c : ℝ) : Prop :=
  ∃ y : Multiset (Fin t) → (PosT t m → V) → ℝ,
    (∀ τ ∈ F, ∀ φ, ValidCopyT m p J τ φ →
      ω / (Fintype.card V : ℝ) ^ (qT t m - 2) ≤ y τ φ ∧
        y τ φ ≤ 1 / (ω * (Fintype.card V : ℝ) ^ (qT t m - 2))) ∧
    ∀ e ∈ J, |(∑ τ ∈ F, ∑ φ ∈ univ.filter (fun φ => ValidCopyT m p J τ φ ∧
      e ∈ triEdges (copyTriT m τ φ)), y τ φ) - 1| ≤ c

noncomputable def goodExt {D : Type*} [Fintype D] [DecidableEq D] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V)) (κ : D → Fin t)
    (T : Finset (Sym2 D)) (S : Finset D) (φ : D → V) : Finset (D → V) := by
  classical exact univ.filter fun ψ : D → V =>
    (∀ x ∈ S, ψ x = φ x) ∧ Function.Injective ψ ∧ (∀ x, p (ψ x) = κ x) ∧
      ∀ x y, s(x, y) ∈ T → x ≠ y → (x ∉ S ∨ y ∉ S) →
        AllowedPair F (κ x) (κ y) → s(ψ x, ψ y) ∈ J

def ExtendableT (K : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V)) (ω : ℝ) : Prop :=
  ∀ k ≤ K, ∀ (κ : Fin k → Fin t) (S : Finset (Fin k)) (T : Finset (Sym2 (Fin k)))
    (φ : Fin k → V), Set.InjOn φ S → (∀ x ∈ S, p (φ x) = κ x) →
      ω * (Fintype.card V : ℝ) ^ (k - S.card) ≤ ((goodExt p F J κ T S φ).card : ℝ)

def hKT (t m : ℕ) : ℕ := 2 ^ (50 * qT t m ^ 3)

noncomputable def δKT (t m : ℕ) : ℝ := (2 : ℝ) ^ (-(1000 * (qT t m : ℝ) ^ 5))

def KeevashPaddedSpec (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ m : ℕ, ∃ ω0 : ℝ, 0 < ω0 ∧ ∃ n0 : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V], n0 < Fintype.card V → ∀ ω : ℝ,
      (Fintype.card V : ℝ) ^ (-δKT t m) < ω → ω < ω0 →
      ∀ (p : V → Fin t) (J : Finset (Sym2 V)), (∀ e ∈ J, ¬ e.IsDiag) →
        (∀ u v, s(u, v) ∈ J → AllowedPair F (p u) (p v)) →
        (∀ i, (Fintype.card V : ℝ) / hKT t m ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        IsIntDiv p F J → PaddedRegularT m p F J ω (ω ^ (hKT t m ^ 20)) →
        ExtendableT (qT t m * hKT t m) p F J ω → HasDecomp p F J

theorem allowedPair_iff_link (F : Finset (Multiset (Fin t))) (i j : Fin t) :
    AllowedPair F i j ↔ ∃ k, Link F i j k := by
  constructor
  · rintro ⟨τ, hτ, hcard, hpair⟩
    obtain ⟨rest, hrest⟩ := Multiset.le_iff_exists_add.mp hpair
    have hc : rest.card = 1 := by
      rw [hrest, Multiset.card_add] at hcard
      change 2 + rest.card = 3 at hcard
      omega
    obtain ⟨k, rfl⟩ := Multiset.card_eq_one.mp hc
    refine ⟨k, ?_⟩
    simpa [Link, hrest] using hτ
  · rintro ⟨k, hk⟩
    refine ⟨{i, j, k}, hk, by simp, ?_⟩
    exact Multiset.le_iff_exists_add.mpr ⟨{k}, by simp⟩

theorem mem_goodExt {D : Type*} [Fintype D] [DecidableEq D]
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V))
    (κ : D → Fin t) (T : Finset (Sym2 D)) (S : Finset D) (φ ψ : D → V) :
    ψ ∈ goodExt p F J κ T S φ ↔
      (∀ x ∈ S, ψ x = φ x) ∧ Function.Injective ψ ∧ (∀ x, p (ψ x) = κ x) ∧
        ∀ x y, s(x, y) ∈ T → x ≠ y → (x ∉ S ∨ y ∉ S) →
          AllowedPair F (κ x) (κ y) → s(ψ x, ψ y) ∈ J := by
  classical
  simp [goodExt]

#print axioms allowedPair_iff_link

end PaddedInputs
