/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.Transformer
public import PartitionedTriangleAbsorption.PrivateTemplate.ClosedTrails

/-!
# The explicit private absorber template

Fix a root type `Rt`, `m` positions with a successor permutation `σt` and roots
`xr : Fin m → Rt` (a closed-trail system of the piece `P`, lifted to the roots).  The
auxiliary vertices are `34` tagged vertices per position and one centre.

* `P₁ = ∇P` (middle `p1`), `P₂ = ∇P₁` (middles `p2a, p2b`), seen as closed trails of
  length `4m` with successor `blowPerm σt`;
* `Q` = `m/3` disjoint triangles on the vertices `q`, `Q₁ = ∇Q`, `Q₂ = ∇Q₁`;
* `J` = `m` four-cycles `centre, j1, j2, j3` sharing the centre;
* `T_P`, `T_Q` = the transformers `P₂ → J` and `Q₂ → J` (auxiliaries `tp`, `tq`).

The template is `A = P₁ ∪ P₂ ∪ T_P ∪ J ∪ T_Q ∪ Q₂ ∪ Q₁ ∪ Q`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

/-- Tags of the auxiliary vertices attached to one position. -/
inductive Tag
  | q | j1 | j2 | j3 | p1 | p2a | p2b | q1 | q2a | q2b
  | tp (k : Fin 4) (c : Fin 3)
  | tq (k : Fin 4) (c : Fin 3)
  deriving DecidableEq

instance : Fintype Tag where
  elems := {.q, .j1, .j2, .j3, .p1, .p2a, .p2b, .q1, .q2a, .q2b} ∪
    (Finset.univ : Finset (Fin 4 × Fin 3)).image (fun p => .tp p.1 p.2) ∪
    (Finset.univ : Finset (Fin 4 × Fin 3)).image (fun p => .tq p.1 p.2)
  complete := by intro t; cases t <;> simp

theorem card_tag : Fintype.card Tag = 34 := by decide

/-- Auxiliary vertices: `34` tagged vertices per position, plus one centre when `0 < m`. -/
abbrev AuxV (m : ℕ) := (Fin m × Tag) ⊕ {_u : Unit // 0 < m}

/-- Template vertices: roots and auxiliaries. -/
abbrev TV (Rt : Type*) (m : ℕ) := Rt ⊕ AuxV m

noncomputable section Defs

variable {Rt : Type*} {m : ℕ}

/-- A tagged auxiliary vertex. -/
abbrev aux (j : Fin m) (t : Tag) : TV Rt m := Sum.inr (Sum.inl (j, t))

/-- The centre of `J`. -/
abbrev centre (hm : 0 < m) : TV Rt m := Sum.inr (Sum.inr ⟨(), hm⟩)

/-- Successor on the length-four blow-up of a closed-trail system. -/
def blowFun (σ : Equiv.Perm (Fin m)) (p : Fin m × Fin 4) : Fin m × Fin 4 :=
  if p.2 = 3 then (σ p.1, 0) else (p.1, p.2 + 1)

theorem blowFun_injective (σ : Equiv.Perm (Fin m)) : Function.Injective (blowFun σ) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  fin_cases k <;> fin_cases k' <;> simp_all [blowFun]

/-- The successor permutation of the subdivided trails. -/
def blowPerm (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m × Fin 4) :=
  Equiv.ofBijective (blowFun σ) (Finite.injective_iff_bijective.mp (blowFun_injective σ))

@[simp] theorem blowPerm_apply (σ : Equiv.Perm (Fin m)) (p : Fin m × Fin 4) :
    blowPerm σ p = if p.2 = 3 then (σ p.1, 0) else (p.1, p.2 + 1) := rfl

/-- The vertices along a doubly subdivided trail edge: base vertex, then three middles. -/
def pathV (base : Fin m → TV Rt m) (t1 t2 t3 : Tag) (p : Fin m × Fin 4) : TV Rt m :=
  ![base p.1, aux p.1 t1, aux p.1 t2, aux p.1 t3] p.2

/-- The vertices of the petals of `J`. -/
def petalV (p : Fin m × Fin 4) : TV Rt m :=
  ![centre p.1.pos, aux p.1 .j1, aux p.1 .j2, aux p.1 .j3] p.2

/-- The `Q` vertices. -/
abbrev qv (j : Fin m) : TV Rt m := aux j .q

/-- Transformer auxiliaries for `T_P`. -/
def auxP (i : (Fin m × Fin 4) × Fin 3) : TV Rt m := aux i.1.1 (.tp i.1.2 i.2)

/-- Transformer auxiliaries for `T_Q`. -/
def auxQ (i : (Fin m × Fin 4) × Fin 3) : TV Rt m := aux i.1.1 (.tq i.1.2 i.2)

/-- Rotation inside consecutive triples: the closed-trail system of `Q`. -/
def triFun (h3 : 3 ∣ m) (j : Fin m) : Fin m :=
  if h : j.val % 3 = 2 then ⟨j.val - 2, by omega⟩ else ⟨j.val + 1, by
    obtain ⟨k, hk⟩ := h3; have := j.isLt; omega⟩

theorem triFun_val (h3 : 3 ∣ m) (j : Fin m) :
    (triFun h3 j).val = if j.val % 3 = 2 then j.val - 2 else j.val + 1 := by
  unfold triFun; split_ifs <;> rfl

theorem triFun_injective (h3 : 3 ∣ m) : Function.Injective (triFun h3) := by
  intro j j' h
  have h' := congrArg Fin.val h
  rw [triFun_val, triFun_val] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

/-- The permutation of `Fin m` rotating each consecutive triple. -/
def triPerm (h3 : 3 ∣ m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (triFun h3) (Finite.injective_iff_bijective.mp (triFun_injective h3))

theorem triPerm_val (h3 : 3 ∣ m) (j : Fin m) :
    (triPerm h3 j).val = if j.val % 3 = 2 then j.val - 2 else j.val + 1 :=
  triFun_val h3 j

variable [DecidableEq Rt]

variable (σt : Equiv.Perm (Fin m)) (xr : Fin m → Rt) (h3 : 3 ∣ m)

/-- The lifted piece `P`. -/
def edgesP : Finset (Sym2 (TV Rt m)) :=
  posEdges (fun j => Sum.inl (xr j)) fun j => Sum.inl (xr (σt j))

/-- `P₁ = ∇P`. -/
def edgesP1 : Finset (Sym2 (TV Rt m)) :=
  posEdges (fun j => Sum.inl (xr j)) (fun j => aux j .p1) ∪
    posEdges (fun j => aux j .p1) fun j => Sum.inl (xr (σt j))

/-- The vertices of the trails of `P₂`. -/
def xP : Fin m × Fin 4 → TV Rt m := pathV (fun j => Sum.inl (xr j)) .p2a .p1 .p2b

/-- `P₂ = ∇P₁`. -/
def edgesP2 : Finset (Sym2 (TV Rt m)) := srcEdges (blowPerm σt) (xP xr)

/-- `J`: `m` four-cycles sharing the centre. -/
def edgesJ : Finset (Sym2 (TV Rt m)) := srcEdges (blowPerm σt) petalV

/-- The transformer `T_P` between `P₂` and `J`. -/
def edgesTP : Finset (Sym2 (TV Rt m)) := transEdges (blowPerm σt) (xP xr) petalV auxP

/-- The vertices of the trails of `Q₂`. -/
def xQ : Fin m × Fin 4 → TV Rt m := pathV qv .q2a .q1 .q2b

/-- `Q`: `m/3` disjoint triangles. -/
def edgesQ : Finset (Sym2 (TV Rt m)) := posEdges qv fun j => qv (triPerm h3 j)

/-- `Q₁ = ∇Q`. -/
def edgesQ1 : Finset (Sym2 (TV Rt m)) :=
  posEdges qv (fun j => aux j .q1) ∪ posEdges (fun j => aux j .q1) fun j => qv (triPerm h3 j)

/-- `Q₂ = ∇Q₁`. -/
def edgesQ2 : Finset (Sym2 (TV Rt m)) := srcEdges (blowPerm (triPerm h3)) xQ

/-- The transformer `T_Q` between `Q₂` and `J`. -/
def edgesTQ : Finset (Sym2 (TV Rt m)) := transEdges (blowPerm (triPerm h3)) xQ petalV auxQ

/-- **The private absorber template** `A = P₁ ∪ P₂ ∪ T_P ∪ J ∪ T_Q ∪ Q₂ ∪ Q₁ ∪ Q`. -/
def template : Finset (Sym2 (TV Rt m)) :=
  edgesP1 σt xr ∪ edgesP2 σt xr ∪ edgesTP σt xr ∪ edgesJ σt ∪ edgesTQ h3 ∪ edgesQ2 h3 ∪
    edgesQ1 h3 ∪ edgesQ h3

end Defs

end PartitionedTriangleAbsorption.PrivateTemplate
