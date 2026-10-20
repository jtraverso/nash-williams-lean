/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Fibre

/-! # Coloured hubs II: the explicit vertex type and the eight blocks

Vertices are `V ⊕ HAux m t`, where `HAux m t = (Fin m × Tag) ⊕ Fin t`: the original
vertices, `34` tagged auxiliaries per trail position (the tags of the ordinary template),
and **one hub per part**. Thus exactly `34 m + t` vertices are new.

Data: a closed-trail system `(σ, X)` of the piece `P` on `Fin m`, a comparison graph given by
corner words `w : T → Fin 3 → Fin t`, and a slot bijection `π : Fin m ≃ T × Fin 3`.
Position `i` of `P` is matched with comparison slot `π i`; the comparison vertex of slot
`π i` is the auxiliary `(i, q)`, and the comparison trail successor is `qPerm π`.

For position `i` write `r = p (X i)`, `s = p (X (σ i))` and `c` for the third corner part of
the matched comparison triangle. The doubly subdivided paths have part words
`r, s, c, r, s` (for `P`) and `a, b, c, a, b` (for the comparison slot with ends `a, b`).
The private path `J_i` is `hub r — j1 — j2 — j3 — hub s`; the comparison slot is mapped onto
it forwards when `a = r`, and backwards otherwise (`pathJQ`). Every original vertex goes to the
hub of its own part.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer

variable {t : ℕ}

/-- Auxiliary vertices: `34` tagged vertices per trail position, and one hub per part. -/
abbrev HAux (m t : ℕ) := (Fin m × Tag) ⊕ Fin t

/-- Vertices of the coloured-hub template. -/
abbrev HV (V : Type*) (m t : ℕ) := V ⊕ HAux m t

theorem card_hAux (m t : ℕ) : Fintype.card (HAux m t) = 34 * m + t := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_tag, Fintype.card_fin,
    mul_comm]

section Generic

variable {W : Type*} {m : ℕ}

/-- A doubly subdivided trail position. -/
def fourPath (v0 v1 v2 v3 : Fin m → W) (z : Fin m × Fin 4) : W :=
  ![v0 z.1, v1 z.1, v2 z.1, v3 z.1] z.2

@[simp] theorem fourPath_zero (v0 v1 v2 v3 : Fin m → W) (i : Fin m) :
    fourPath v0 v1 v2 v3 (i, 0) = v0 i := rfl

@[simp] theorem fourPath_one (v0 v1 v2 v3 : Fin m → W) (i : Fin m) :
    fourPath v0 v1 v2 v3 (i, 1) = v1 i := rfl

@[simp] theorem fourPath_two (v0 v1 v2 v3 : Fin m → W) (i : Fin m) :
    fourPath v0 v1 v2 v3 (i, 2) = v2 i := rfl

@[simp] theorem fourPath_three (v0 v1 v2 v3 : Fin m → W) (i : Fin m) :
    fourPath v0 v1 v2 v3 (i, 3) = v3 i := rfl

variable [DecidableEq W]

theorem mem_srcEdges_fourPath {v0 v1 v2 v3 : Fin m → W} {σ : Equiv.Perm (Fin m)}
    {e : Sym2 W} :
    e ∈ srcEdges (blowPerm σ) (fourPath v0 v1 v2 v3) ↔
      ∃ j, e = s(v0 j, v1 j) ∨ e = s(v1 j, v2 j) ∨ e = s(v2 j, v3 j) ∨
        e = s(v3 j, v0 (σ j)) := by
  rw [srcEdges, mem_posEdges]
  constructor
  · rintro ⟨⟨j, k⟩, rfl⟩
    fin_cases k <;> refine ⟨j, ?_⟩ <;> simp
  · rintro ⟨j, h | h | h | h⟩
    · exact ⟨(j, 0), by simp [h]⟩
    · exact ⟨(j, 1), by simp [h]⟩
    · exact ⟨(j, 2), by simp [h]⟩
    · exact ⟨(j, 3), by simp [h]⟩

/-- Every transformer edge has an auxiliary endpoint; the other endpoint is a source,
target or auxiliary vertex. -/
theorem mem_transEdges_cases {I : Type*} [Fintype I] {σ : Equiv.Perm I} {x y : I → W}
    {a : I × Fin 3 → W} {e : Sym2 W} (he : e ∈ transEdges σ x y a) :
    ∃ q u, e = s(a q, u) ∧ ((∃ i, u = x i) ∨ (∃ i, u = y i) ∨ ∃ q', u = a q') := by
  simp only [transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨i, he⟩ := he
  simp only [transAt, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, Sym2.eq_swap, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inr (Or.inl ⟨i, rfl⟩)⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inr (Or.inl ⟨i, rfl⟩)⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inr (Or.inl ⟨i, rfl⟩)⟩
  · exact ⟨_, _, Sym2.eq_swap, Or.inr (Or.inl ⟨i, rfl⟩)⟩
  · exact ⟨_, _, rfl, Or.inr (Or.inr ⟨_, rfl⟩)⟩
  · exact ⟨_, _, rfl, Or.inr (Or.inr ⟨_, rfl⟩)⟩
  · exact ⟨_, _, rfl, Or.inr (Or.inr ⟨_, rfl⟩)⟩

end Generic

/-! ### The comparison trail -/

section Comparison

variable {m : ℕ} {T : Type*}

/-- Rotation of the corners of each comparison triangle. -/
def qPerm (π : Fin m ≃ T × Fin 3) : Equiv.Perm (Fin m) :=
  π.trans ((Equiv.prodCongr (Equiv.refl T) (Equiv.addRight (1 : Fin 3))).trans π.symm)

@[simp] theorem pi_qPerm (π : Fin m ≃ T × Fin 3) (i : Fin m) :
    π (qPerm π i) = ((π i).1, (π i).2 + 1) := by
  simp [qPerm, Prod.map]

theorem qPerm_ne (π : Fin m ≃ T × Fin 3) (i : Fin m) : qPerm π i ≠ i := by
  intro h
  have := congrArg (fun j => (π j).2) h
  simp only [pi_qPerm] at this
  generalize (π i).2 = a at this
  fin_cases a <;> simp_all

theorem qPerm_ne2 (π : Fin m ≃ T × Fin 3) (i : Fin m) : qPerm π (qPerm π i) ≠ i := by
  intro h
  have := congrArg (fun j => (π j).2) h
  simp only [pi_qPerm] at this
  generalize (π i).2 = a at this
  fin_cases a <;> simp_all

theorem qPerm_three (π : Fin m ≃ T × Fin 3) (i : Fin m) :
    qPerm π (qPerm π (qPerm π i)) = i := by
  apply π.injective
  simp only [pi_qPerm, add_assoc]
  ext
  · rfl
  · generalize (π i).2 = a
    fin_cases a <;> rfl

/-- Parts of the comparison vertices. -/
def pq (w : T → Fin 3 → Fin t) (π : Fin m ≃ T × Fin 3) (i : Fin m) : Fin t :=
  w (π i).1 (π i).2

@[simp] theorem pq_qPerm (w : T → Fin 3 → Fin t) (π : Fin m ≃ T × Fin 3) (i : Fin m) :
    pq w π (qPerm π i) = w (π i).1 ((π i).2 + 1) := by
  simp [pq]

/-- Rotating a multiset of size three. -/
theorem multiset_rot3 {α : Type*} (a b c : α) : ({b, c, a} : Multiset α) = {a, b, c} := by
  simp only [Multiset.insert_eq_cons]
  rw [← Multiset.cons_zero a, ← Multiset.cons_zero c, Multiset.cons_swap c a,
    Multiset.cons_swap b a]

/-- Every comparison triangle has an allowed type. -/
theorem pq_mem {F : Finset (Multiset (Fin t))} {w : T → Fin 3 → Fin t}
    (hw : ∀ x, ({w x 0, w x 1, w x 2} : Multiset (Fin t)) ∈ F) (π : Fin m ≃ T × Fin 3)
    (i : Fin m) :
    ({pq w π i, pq w π (qPerm π i), pq w π (qPerm π (qPerm π i))} : Multiset (Fin t)) ∈ F := by
  simp only [pq_qPerm, pi_qPerm, add_assoc]
  unfold pq
  generalize (π i).1 = x
  generalize (π i).2 = a
  have h := hw x
  rcases (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) a with rfl | rfl | rfl
  · simpa using h
  · simp only [Fin.isValue, Fin.reduceAdd]; rwa [multiset_rot3]
  · simp only [Fin.isValue, Fin.reduceAdd]; rwa [← multiset_rot3]

end Comparison

/-! ### Links of an allowed triangle in any order -/

theorem link_of_mem {F : Finset (Multiset (Fin t))} {a b c : Fin t}
    (h : ({a, b, c} : Multiset (Fin t)) ∈ F) :
    Link F a b c ∧ Link F b c a ∧ Link F c a b ∧ Link F a c b ∧ Link F b a c ∧
      Link F c b a := by
  have h1 : Link F a b c := h
  have h2 : Link F b a c := (link_root_swap F a b c).mp h1
  have h3 : Link F a c b := (link_swap F a b c).mp h1
  have h4 : Link F b c a := (link_swap F b a c).mp h2
  have h5 : Link F c a b := (link_root_swap F a c b).mp h3
  have h6 : Link F c b a := (link_swap F c a b).mp h5
  exact ⟨h1, h4, h5, h3, h2, h6⟩

/-! ### Vertices, parts and blocks -/

noncomputable section Defs

variable {V : Type*} {m : ℕ} {T : Type*}

/-- An original vertex. -/
abbrev old (v : V) : HV V m t := Sum.inl v

/-- A tagged auxiliary vertex. -/
abbrev ax (i : Fin m) (g : Tag) : HV V m t := Sum.inr (Sum.inl (i, g))

/-- The hub of part `r`. -/
abbrev hub (r : Fin t) : HV V m t := Sum.inr (Sum.inr r)

variable (p : V → Fin t) (σ : Equiv.Perm (Fin m)) (X : Fin m → V)
  (w : T → Fin 3 → Fin t) (π : Fin m ≃ T × Fin 3)

/-- Part of the tail of trail position `i`. -/
def rP (i : Fin m) : Fin t := p (X i)

/-- Part of the head of trail position `i`. -/
def sP (i : Fin m) : Fin t := p (X (σ i))

/-- Third corner part of the comparison triangle matched with position `i`. -/
def cP (i : Fin m) : Fin t := pq w π (qPerm π (qPerm π i))

variable (aP aQ : (Fin m × Fin 4) × Fin 3 → Fin t)

/-- Parts of the tagged auxiliaries. -/
def tagPart (i : Fin m) : Tag → Fin t
  | .q => pq w π i
  | .q1 => cP w π i
  | .q2a => pq w π (qPerm π i)
  | .q2b => pq w π i
  | .p1 => cP w π i
  | .p2a => sP p σ X i
  | .p2b => rP p X i
  | .j1 => sP p σ X i
  | .j2 => cP w π i
  | .j3 => rP p X i
  | .tp k c => aP ((i, k), c)
  | .tq k c => aQ ((i, k), c)

/-- **The extended partition.** Original vertices keep their part and the hub of part `r`
lies in part `r`. -/
def hpart : HV V m t → Fin t :=
  Sum.elim p (Sum.elim (fun z => tagPart p σ X w π aP aQ z.1 z.2) id)

variable [DecidableEq V]

/-- Trail of `P₂` (part word `r, s, c, r`). -/
def pathP : Fin m × Fin 4 → HV V m t :=
  fourPath (fun i => old (X i)) (fun i => ax i .p2a) (fun i => ax i .p1) (fun i => ax i .p2b)

/-- Trail of `J` along `P` (part word `r, s, c, r`). -/
def pathJ : Fin m × Fin 4 → HV V m t :=
  fourPath (fun i => hub (rP p X i)) (fun i => ax i .j1) (fun i => ax i .j2) (fun i => ax i .j3)

/-- Backwards traversal of `J_i`, used when the comparison slot is reversed. -/
def pathJrev : Fin m × Fin 4 → HV V m t :=
  fourPath (fun i => hub (pq w π i)) (fun i => ax i .j3) (fun i => ax i .j2) (fun i => ax i .j1)

/-- Trail of `J` along the comparison graph: forwards or backwards on each `J_i`. -/
def pathJQ (z : Fin m × Fin 4) : HV V m t :=
  if pq w π z.1 = rP p X z.1 then pathJ p X z else pathJrev w π z

/-- Trail of `Q₂` (part word `a, b, c, a`). -/
def pathQ : Fin m × Fin 4 → HV V m t :=
  fourPath (fun i => ax i .q) (fun i => ax i .q2a) (fun i => ax i .q1) (fun i => ax i .q2b)

/-- Transformer auxiliaries for `T_P`. -/
def auxTP (z : (Fin m × Fin 4) × Fin 3) : HV V m t := ax z.1.1 (.tp z.1.2 z.2)

/-- Transformer auxiliaries for `T_Q`. -/
def auxTQ (z : (Fin m × Fin 4) × Fin 3) : HV V m t := ax z.1.1 (.tq z.1.2 z.2)

/-- The lifted piece `P`. -/
def blkP : Finset (Sym2 (HV V m t)) :=
  posEdges (fun i => old (X i)) fun i => old (X (σ i))

/-- `P₁`: `P` subdivided once. -/
def blkP1 : Finset (Sym2 (HV V m t)) :=
  posEdges (fun i => old (X i)) (fun i => ax i .p1) ∪
    posEdges (fun i => ax i .p1) fun i => old (X (σ i))

/-- `P₂`: `P₁` subdivided once more. -/
def blkP2 : Finset (Sym2 (HV V m t)) := srcEdges (blowPerm σ) (pathP X)

/-- `J`: one private four-edge path (or four-cycle) between hubs per position. -/
def blkJ : Finset (Sym2 (HV V m t)) := srcEdges (blowPerm σ) (pathJ p X)

/-- The transformer `T_P` between `P₂` and `J`. -/
def blkTP : Finset (Sym2 (HV V m t)) := transEdges (blowPerm σ) (pathP X) (pathJ p X) auxTP

/-- The comparison graph `Q`. -/
def blkQ : Finset (Sym2 (HV V m t)) :=
  posEdges (fun i => ax i .q) fun i => ax (qPerm π i) .q

/-- `Q₁`: `Q` subdivided once. -/
def blkQ1 : Finset (Sym2 (HV V m t)) :=
  posEdges (fun i => ax i .q) (fun i => ax i .q1) ∪
    posEdges (fun i => ax i .q1) fun i => ax (qPerm π i) .q

/-- `Q₂`: `Q₁` subdivided once more. -/
def blkQ2 : Finset (Sym2 (HV V m t)) := srcEdges (blowPerm (qPerm π)) (pathQ (V := V))

/-- The transformer `T_Q` between `Q₂` and `J`. -/
def blkTQ : Finset (Sym2 (HV V m t)) :=
  transEdges (blowPerm (qPerm π)) (pathQ (V := V)) (pathJQ p X w π) auxTQ

/-- **The coloured-hub private absorber**
`A = P₁ ∪ P₂ ∪ T_P ∪ J ∪ T_Q ∪ Q₂ ∪ Q₁ ∪ Q`. -/
def hubTemplate : Finset (Sym2 (HV V m t)) :=
  blkP1 σ X ∪ blkP2 σ X ∪ blkTP p σ X ∪ blkJ p σ X ∪ blkTQ p X w π ∪
    blkQ2 (V := V) π ∪ blkQ1 (V := V) π ∪ blkQ (V := V) π

end Defs

end PartitionedTriangleAbsorption.ColouredHub
