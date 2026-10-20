/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveAverage
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply

@[expose] public section

/-!
# Sequential placement with bounded earlier neighbours

A plan may have arbitrarily many auxiliary vertices. Each step requests
only its listed earlier neighbours. Coincidences between unrelated vertices
are permitted; an edge request in a loopless host ensures that its own two
endpoints are distinct. This is the geometry needed for weighted octahedron
and prism refinements, whose auxiliary set need not embed injectively.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset StructuralF3General

universe u

inductive SequentialPlan (t : ℕ) : (R : Type u) → (R → Fin t) → ℕ → Type (u + 1)
  | nil {R : Type u} {label : R → Fin t} : SequentialPlan t R label 0
  | step {R : Type u} {label : R → Fin t} {n : ℕ}
      (target : Fin t) (parents : Finset R)
      (tail : SequentialPlan t (R ⊕ Unit) (Sum.elim label (fun _ => target)) n) :
      SequentialPlan t R label (n + 1)

namespace SequentialPlan

variable {t : ℕ}

def Legal (Allowed : Fin t → Fin t → Prop) (D : ℕ) :
    {R : Type u} → {label : R → Fin t} → {n : ℕ} → SequentialPlan t R label n → Prop
  | _, _, _, .nil => True
  | _, label, _, .step target parents tail =>
      parents.card ≤ D ∧ (∀ r ∈ parents, Allowed (label r) target) ∧ Legal Allowed D tail

variable {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def grow :
    {R : Type u} → {label : R → Fin t} → {n : ℕ} →
      SequentialPlan t R label n → (R → V) → ChoiceTree V n
  | _, _, _, .nil, _ => .leaf
  | _, _, _, .step target parents tail, φ =>
      .step (guardedNeighbours p G (parents.image φ) target)
        (fun w => grow tail (Sum.elim φ (fun _ => w)))

theorem grow_lower (Allowed : Fin t → Fin t → Prop) (D : ℕ) (a : ℝ)
    (hs : GuardedSupply p G Allowed D a)
    {R : Type u} {label : R → Fin t} {n : ℕ} (P : SequentialPlan t R label n)
    (hP : Legal Allowed D P) (φ : R → V) (hφ : ∀ r, p (φ r) = label r) :
    ChoiceTree.Lower a (grow p G P φ) := by
  induction P with
  | nil => trivial
  | @step R label n target parents tail ih =>
    change a ≤ (guardedNeighbours p G (parents.image φ) target).card ∧ _
    have hcard : (parents.image φ).card ≤ D := card_image_le.trans hP.1
    have hguard : ∀ u ∈ parents.image φ, Allowed (p u) target := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hu
      rw [hφ r]
      exact hP.2.1 r hr
    refine ⟨hs _ hcard _ hguard, ?_⟩
    intro w hw
    apply ih hP.2.2 (Sum.elim φ (fun _ => w))
    intro r
    cases r with
    | inl r => exact hφ r
    | inr r => exact (mem_filter.mp hw).2.1

def Realizes : {R : Type u} → {label : R → Fin t} → {n : ℕ} →
    SequentialPlan t R label n → (R → V) → (Fin n → V) → Prop
  | _, _, _, .nil, _, _ => True
  | _, _, _, .step target parents tail, φ, f =>
      p (f 0) = target ∧ (∀ r ∈ parents, G.Adj (φ r) (f 0)) ∧
        Realizes tail (Sum.elim φ (fun _ => f 0)) (fun i => f i.succ)

end SequentialPlan

namespace ChoiceTree

variable {V : Type u}

def Supports : {n : ℕ} → ChoiceTree V n → (Fin n → V) → Prop
  | _, .leaf, _ => True
  | _, .step choices next, f => f 0 ∈ choices ∧ Supports (next (f 0)) (fun i => f i.succ)

end ChoiceTree

namespace SequentialPlan

variable {V : Type u} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]

theorem supports_grow_iff {R : Type u} {label : R → Fin t} {n : ℕ}
    (P : SequentialPlan t R label n) (φ : R → V) (f : Fin n → V) :
    ChoiceTree.Supports (grow p G P φ) f ↔ Realizes p G P φ f := by
  induction P with
  | nil => rfl
  | step target parents tail ih =>
    simp only [grow, ChoiceTree.Supports, Realizes, guardedNeighbours, mem_filter,
      mem_univ, true_and, forall_mem_image, ih, and_assoc]

/-- Every prescribed collection of auxiliary images has the expected inverse
power bound, independent of the total length of the sequential plan. -/
theorem placement_mass_le (Allowed : Fin t → Fin t → Prop) (D : ℕ) (a : ℝ)
    (ha : 0 < a) (hs : GuardedSupply p G Allowed D a)
    {R : Type u} {label : R → Fin t} {n : ℕ} (P : SequentialPlan t R label n)
    (hP : Legal Allowed D P) (φ : R → V) (hφ : ∀ r, p (φ r) = label r)
    (M : CoordinateMask V n) :
    ChoiceTree.mass (grow p G P φ) M ≤ (1 / a) ^ M.count :=
  ChoiceTree.mass_le _ M a ha (grow_lower p G Allowed D a hs P hP φ hφ)

#print axioms grow_lower
#print axioms supports_grow_iff
#print axioms placement_mass_le

end SequentialPlan

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
