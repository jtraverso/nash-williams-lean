/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.RainbowTerminal

/-! # BlowupB.LinearTrails — admissible trails for linear families

A family is **linear** (`IsLinearFam`) if its types have three distinct classes and two distinct
classes lie in at most one type. Linear families never satisfy `ThreeStepLinks` (their links are
matchings), so the tree's absorbers do not apply to them.

An `Orientation` fixes a cyclic order `x → y → z → x` of every type. An arc of `P` is an edge
`u w` of `P` together with the type `τ` of its classes, oriented along `τ`
(`p w = cycNext τ (p u)`). Integral divisibility gives, at every vertex and for every type, as
many incoming as outgoing arcs (`card_headFib_eq_card_tailFib`), so a fibrewise bijection gives
a permutation `σ` of the arcs with `tail (σ i) = head i` and `type (σ i) = type i` (`linPerm`):
closed trails running around the cycle of a single type, whose edges are exactly `P`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

/-- A linear family. -/
structure IsLinearFam (F : Finset (Multiset (Fin t))) : Prop where
  card3 : ∀ τ ∈ F, Multiset.card τ = 3
  nodup : ∀ τ ∈ F, τ.Nodup
  unique : ∀ τ ∈ F, ∀ τ' ∈ F, ∀ a b : Fin t, a ≠ b → a ∈ τ → b ∈ τ → a ∈ τ' → b ∈ τ' →
    τ = τ'

/-- A cyclic order of every type. -/
structure Orientation (F : Finset (Multiset (Fin t))) where
  ord : Multiset (Fin t) → Fin t × Fin t × Fin t
  spec : ∀ τ ∈ F, ({(ord τ).1, (ord τ).2.1, (ord τ).2.2} : Multiset (Fin t)) = τ

theorem exists_orientation (F : Finset (Multiset (Fin t))) (h3 : ∀ τ ∈ F, Multiset.card τ = 3)
    (ht : 0 < t) : Nonempty (Orientation F) := by
  classical
  refine ⟨⟨fun τ => if h : ∃ x y z : Fin t, τ = {x, y, z} then
      (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
    else (⟨0, ht⟩, ⟨0, ht⟩, ⟨0, ht⟩), fun τ hτ => ?_⟩⟩
  have h : ∃ x y z : Fin t, τ = {x, y, z} := Multiset.card_eq_three.mp (h3 τ hτ)
  simp only [dif_pos h]
  exact h.choose_spec.choose_spec.choose_spec.symm

/-! ### Cyclic successor in an ordered triple -/

section Cyc

/-- The cyclic successor `x → y → z → x`. -/
def cycNext (o : Fin t × Fin t × Fin t) (c : Fin t) : Fin t :=
  if c = o.1 then o.2.1 else if c = o.2.1 then o.2.2 else o.1

/-- The position in the cycle. -/
def phaseOf (o : Fin t × Fin t × Fin t) (c : Fin t) : Fin 3 :=
  if c = o.1 then 0 else if c = o.2.1 then 1 else 2

/-- Distinct entries. -/
def Distinct3 (o : Fin t × Fin t × Fin t) : Prop := o.1 ≠ o.2.1 ∧ o.1 ≠ o.2.2 ∧ o.2.1 ≠ o.2.2

variable {o : Fin t × Fin t × Fin t} (hd : Distinct3 o)
include hd

theorem mem_three_iff {c : Fin t} :
    c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t)) ↔ c = o.1 ∨ c = o.2.1 ∨ c = o.2.2 := by
  simp

theorem cycNext_cases {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    (c = o.1 ∧ cycNext o c = o.2.1) ∨ (c = o.2.1 ∧ cycNext o c = o.2.2) ∨
      (c = o.2.2 ∧ cycNext o c = o.1) := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases (mem_three_iff hd).mp hc with rfl | rfl | rfl
  · left; simp [cycNext]
  · right; left; simp [cycNext, Ne.symm h1]
  · right; right; simp [cycNext, Ne.symm h2, Ne.symm h3]

theorem cycNext_mem {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    cycNext o c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t)) := by
  rcases cycNext_cases hd hc with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> simp

theorem cycNext_ne {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    cycNext o c ≠ c := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases cycNext_cases hd hc with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e]
  · exact Ne.symm h1
  · exact Ne.symm h3
  · exact h2

theorem cycNext_cycNext_ne {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    cycNext o (cycNext o c) ≠ c := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases cycNext_cases hd hc with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e] <;>
    simp [cycNext, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem cycNext_cycNext_ne' {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    cycNext o (cycNext o c) ≠ cycNext o c :=
  cycNext_ne hd (cycNext_mem hd hc)

theorem cycNext3 {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    cycNext o (cycNext o (cycNext o c)) = c := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases cycNext_cases hd hc with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e] <;>
    simp [cycNext, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem phase_cycNext {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    phaseOf o (cycNext o c) = phaseOf o c + 1 := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases cycNext_cases hd hc with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e] <;>
    simp [phaseOf, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3] <;> rfl

theorem phase_eq_zero_iff {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    phaseOf o c = 0 ↔ c = o.1 := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases (mem_three_iff hd).mp hc with rfl | rfl | rfl <;>
    simp [phaseOf, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem phase_eq_one_iff {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    phaseOf o c = 1 ↔ c = o.2.1 := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases (mem_three_iff hd).mp hc with rfl | rfl | rfl <;>
    simp [phaseOf, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem phase_eq_two_iff {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    phaseOf o c = 2 ↔ c = o.2.2 := by
  have h1 := hd.1
  have h2 := hd.2.1
  have h3 := hd.2.2
  rcases (mem_three_iff hd).mp hc with rfl | rfl | rfl <;>
    simp [phaseOf, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem cyc_x : cycNext o o.1 = o.2.1 := by simp [cycNext]

theorem cyc_y : cycNext o o.2.1 = o.2.2 := by
  simp [cycNext, Ne.symm hd.1]

theorem cyc_z : cycNext o o.2.2 = o.1 := by
  simp [cycNext, Ne.symm hd.2.1, Ne.symm hd.2.2]

/-- The three classes along the cycle starting anywhere form the type. -/
theorem tri_rot {c : Fin t} (hc : c ∈ ({o.1, o.2.1, o.2.2} : Multiset (Fin t))) :
    ({c, cycNext o c, cycNext o (cycNext o c)} : Multiset (Fin t)) = {o.1, o.2.1, o.2.2} := by
  rcases (mem_three_iff hd).mp hc with rfl | rfl | rfl
  · rw [cyc_x hd, cyc_y hd]
  · rw [cyc_y hd, cyc_z hd]
    show o.2.1 ::ₘ o.2.2 ::ₘ o.1 ::ₘ 0 = o.1 ::ₘ o.2.1 ::ₘ o.2.2 ::ₘ 0
    rw [Multiset.cons_swap o.2.2 o.1, Multiset.cons_swap o.2.1 o.1]
  · rw [cyc_z hd, cyc_x hd]
    show o.2.2 ::ₘ o.1 ::ₘ o.2.1 ::ₘ 0 = o.1 ::ₘ o.2.1 ::ₘ o.2.2 ::ₘ 0
    rw [Multiset.cons_swap o.2.2 o.1, Multiset.cons_swap o.2.2 o.2.1]

end Cyc

/-! ### Linear families: distinctness and uniqueness -/

section Lin

variable {F : Finset (Multiset (Fin t))} (hL : IsLinearFam F) (O : Orientation F)
include hL

theorem distinct_ord {τ : Multiset (Fin t)} (hτ : τ ∈ F) : Distinct3 (O.ord τ) := by
  have h := hL.nodup τ hτ
  rw [← O.spec τ hτ] at h
  exact (nodup_three_iff _ _ _).mp h

theorem mem_ord_iff {τ : Multiset (Fin t)} (hτ : τ ∈ F) {c : Fin t} :
    c ∈ τ ↔ c ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t)) := by
  rw [O.spec τ hτ]

end Lin

/-! ### Arcs and trails -/

section Trails

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} (O : Orientation F) (P : Finset (Sym2 V))

/-- Arcs: an edge of `P`, the type of its classes, oriented along the type. -/
abbrev ArcL : Type _ :=
  {a : V × V × F // s(a.1, a.2.1) ∈ P ∧ p a.1 ∈ (a.2.2 : Multiset (Fin t)) ∧
    p a.2.1 = cycNext (O.ord a.2.2) (p a.1)}

variable {O P}

def ArcL.tail (i : ArcL (p := p) O P) : V := i.1.1
def ArcL.head (i : ArcL (p := p) O P) : V := i.1.2.1
def ArcL.typ (i : ArcL (p := p) O P) : F := i.1.2.2

/-- The phase of an arc: the position of its tail class in the cycle of its type. -/
def ArcL.phase (i : ArcL (p := p) O P) : Fin 3 := phaseOf (O.ord i.typ) (p i.tail)

omit [Fintype V] [DecidableEq V] in
theorem ArcL.head_cls (i : ArcL (p := p) O P) : p i.head = cycNext (O.ord i.typ) (p i.tail) :=
  i.2.2.2

variable (hL : IsLinearFam F)
include hL

theorem ArcL.dist (i : ArcL (p := p) O P) : Distinct3 (O.ord i.typ) :=
  distinct_ord hL O i.typ.2

theorem ArcL.tail_mem (i : ArcL (p := p) O P) :
    p i.tail ∈ ({(O.ord i.typ).1, (O.ord i.typ).2.1, (O.ord i.typ).2.2} : Multiset (Fin t)) :=
  (mem_ord_iff hL O i.typ.2).mp i.2.2.1

/-- The incoming arcs at `v` of type `τ` correspond to the neighbours in the preceding class. -/
theorem card_headFib (v : V) (τ : F)
    (hv : p v ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t))) :
    Fintype.card {i : ArcL (p := p) O P // (i.head, i.typ) = (v, τ)} =
      (univ.filter fun u => s(v, u) ∈ P ∧
        p u = cycNext (O.ord τ) (cycNext (O.ord τ) (p v))).card := by
  have hd := distinct_ord hL O τ.2
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun i => ⟨i.1.1.1, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩⟩
      invFun := fun u => ⟨⟨(u.1, v, τ), ?_, ?_, ?_⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := i.1.2.1
    have h2 : i.1.1.2.1 = v := congrArg Prod.fst i.2
    rw [h2, Sym2.eq_swap] at h1; exact h1
  · have h2 : i.1.1.2.1 = v := congrArg Prod.fst i.2
    have h3 : i.1.1.2.2 = τ := congrArg Prod.snd i.2
    have hc := i.1.2.2.2
    have hm := i.1.2.2.1
    rw [h2, h3] at hc
    rw [h3] at hm
    rw [hc, cycNext3 hd ((mem_ord_iff hL O τ.2).mp hm)]
  · rw [Sym2.eq_swap]; exact (mem_filter.mp u.2).2.1
  · rw [mem_ord_iff hL O τ.2, (mem_filter.mp u.2).2.2]
    exact cycNext_mem hd (cycNext_mem hd hv)
  · show p v = cycNext (O.ord τ) (p u.1)
    rw [(mem_filter.mp u.2).2.2, cycNext3 hd hv]
  · rintro ⟨⟨⟨a, b, c⟩, h1⟩, h2⟩
    simp only [ArcL.head, ArcL.typ, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rfl
  · rintro ⟨u, hu⟩; rfl

/-- The outgoing arcs at `v` of type `τ` correspond to the neighbours in the next class. -/
theorem card_tailFib (v : V) (τ : F)
    (hv : p v ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t))) :
    Fintype.card {i : ArcL (p := p) O P // (i.tail, i.typ) = (v, τ)} =
      (univ.filter fun u => s(v, u) ∈ P ∧ p u = cycNext (O.ord τ) (p v)).card := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun i => ⟨i.1.1.2.1, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩⟩
      invFun := fun u => ⟨⟨(v, u.1, τ), (mem_filter.mp u.2).2.1,
        (mem_ord_iff hL O τ.2).mpr hv, (mem_filter.mp u.2).2.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := i.1.2.1
    have h2 : i.1.1.1 = v := congrArg Prod.fst i.2
    rw [h2] at h1; exact h1
  · have h2 : i.1.1.1 = v := congrArg Prod.fst i.2
    have h3 : i.1.1.2.2 = τ := congrArg Prod.snd i.2
    have hc := i.1.2.2.2
    rw [h2, h3] at hc; exact hc
  · rintro ⟨⟨⟨a, b, c⟩, h1⟩, h2⟩
    simp only [ArcL.tail, ArcL.typ, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rfl
  · rintro ⟨u, hu⟩; rfl

/-- For a linear family, the degrees into the two other classes of a type agree. -/
theorem degVec_lin_eq (hdiv : IsIntDiv p F P) (v : V) (τ : F)
    (hv : p v ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t))) :
    degVec p P v (cycNext (O.ord τ) (p v)) =
      degVec p P v (cycNext (O.ord τ) (cycNext (O.ord τ) (p v))) := by
  have hd := distinct_ord hL O τ.2
  obtain ⟨c, hc⟩ := hdiv.2 v
  have key : ∀ j, j ≠ p v → j ∈ (τ : Multiset (Fin t)) →
      degVec p P v j = c τ := by
    intro j hj hjτ
    rw [hc, Finset.sum_apply, Finset.sum_eq_single (τ : Multiset (Fin t))]
    · simp only [Pi.smul_apply, smul_eq_mul, typeDegVec, if_neg hj]
      rw [Multiset.count_eq_one_of_mem (hL.nodup _ τ.2) hjτ]
      ring
    · intro τ' hτ' hne
      obtain ⟨hτ'F, hvτ'⟩ := mem_filter.mp hτ'
      simp only [Pi.smul_apply, smul_eq_mul, typeDegVec, if_neg hj]
      have hjτ' : j ∉ τ' := fun hj' =>
        hne (hL.unique τ' hτ'F τ τ.2 j (p v) hj hj' hvτ' hjτ ((mem_ord_iff hL O τ.2).mpr hv))
      rw [Multiset.count_eq_zero.mpr hjτ']
      ring
    · intro h
      exact (h (mem_filter.mpr ⟨τ.2, (mem_ord_iff hL O τ.2).mpr hv⟩)).elim
  rw [key _ (cycNext_ne hd hv) ((mem_ord_iff hL O τ.2).mpr (cycNext_mem hd hv)),
    key _ (cycNext_cycNext_ne hd hv)
      ((mem_ord_iff hL O τ.2).mpr (cycNext_mem hd (cycNext_mem hd hv)))]

/-- In-degree equals out-degree, at every vertex and for every type. -/
theorem card_headFib_eq_card_tailFib (hdiv : IsIntDiv p F P) (k : V × F) :
    Fintype.card {i : ArcL (p := p) O P // (i.head, i.typ) = k} =
      Fintype.card {i : ArcL (p := p) O P // (i.tail, i.typ) = k} := by
  obtain ⟨v, τ⟩ := k
  have hd := distinct_ord hL O τ.2
  by_cases hv : p v ∈ ({(O.ord τ).1, (O.ord τ).2.1, (O.ord τ).2.2} : Multiset (Fin t))
  · rw [card_headFib hL v τ hv, card_tailFib hL v τ hv]
    have h1 := degVec_eq_card p P v (cycNext_ne hd hv)
    have h2 := degVec_eq_card p P v (cycNext_cycNext_ne hd hv)
    have := degVec_lin_eq hL hdiv v τ hv
    rw [h1, h2] at this
    exact_mod_cast this.symm
  · rw [Fintype.card_eq_zero_iff.mpr ⟨fun i => hv ?_⟩, Fintype.card_eq_zero_iff.mpr ⟨fun i => hv ?_⟩]
    · have h2 : i.1.tail = v := congrArg Prod.fst i.2
      have h3 : i.1.typ = τ := congrArg Prod.snd i.2
      have hm := i.1.tail_mem hL
      rw [h2, h3] at hm
      exact hm
    · have h2 : i.1.head = v := congrArg Prod.fst i.2
      have h3 : i.1.typ = τ := congrArg Prod.snd i.2
      have hm := cycNext_mem (i.1.dist hL) (i.1.tail_mem hL)
      rw [← i.1.head_cls, h2, h3] at hm
      exact hm

/-- **The trail permutation of a linear family.** -/
noncomputable def linPerm (hdiv : IsIntDiv p F P) : Equiv.Perm (ArcL (p := p) O P) :=
  Equiv.ofFiberEquiv (f := fun i => (ArcL.head i, ArcL.typ i))
    (g := fun i => (ArcL.tail i, ArcL.typ i))
    fun k => Fintype.equivOfCardEq (card_headFib_eq_card_tailFib hL hdiv k)

theorem linPerm_map (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    ((linPerm hL hdiv i).tail, (linPerm hL hdiv i).typ) = (i.head, i.typ) := by
  unfold linPerm
  exact Equiv.ofFiberEquiv_map (f := fun i => (ArcL.head i, ArcL.typ i))
    (g := fun i => (ArcL.tail i, ArcL.typ i)) _ i

theorem tail_linPerm (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    (linPerm hL hdiv i).tail = i.head := (Prod.ext_iff.mp (linPerm_map hL hdiv i)).1

theorem typ_linPerm (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    (linPerm hL hdiv i).typ = i.typ := (Prod.ext_iff.mp (linPerm_map hL hdiv i)).2

theorem cls_linPerm (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    p (linPerm hL hdiv i).tail = cycNext (O.ord i.typ) (p i.tail) := by
  rw [tail_linPerm]; exact i.head_cls

theorem phase_linPerm (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    (linPerm hL hdiv i).phase = i.phase + 1 := by
  unfold ArcL.phase
  rw [typ_linPerm hL hdiv i, cls_linPerm hL hdiv i]
  exact phase_cycNext (i.dist hL) (i.tail_mem hL)

theorem tail_ne_tail_linPerm (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    i.tail ≠ (linPerm hL hdiv i).tail := by
  intro h
  have := cls_linPerm hL hdiv i
  rw [← h] at this
  exact cycNext_ne (i.dist hL) (i.tail_mem hL) this.symm

theorem linPerm_edge (hdiv : IsIntDiv p F P) (i : ArcL (p := p) O P) :
    s(i.tail, (linPerm hL hdiv i).tail) = s(i.1.1, i.1.2.1) := by
  rw [tail_linPerm]; rfl

theorem lin_edge_injective (hdiv : IsIntDiv p F P) :
    Function.Injective fun i : ArcL (p := p) O P => s(i.tail, (linPerm hL hdiv i).tail) := by
  intro i j hij
  simp only [linPerm_edge] at hij
  have hdi := i.dist hL
  have hti := i.tail_mem hL
  have hci : p i.head = cycNext (O.ord i.typ) (p i.tail) := i.head_cls
  have hcj : p j.head = cycNext (O.ord j.typ) (p j.tail) := j.head_cls
  have hne : p i.tail ≠ p i.head := by rw [hci]; exact (cycNext_ne hdi hti).symm
  have hmi1 : p i.tail ∈ (i.typ : Multiset (Fin t)) := (mem_ord_iff hL O i.typ.2).mpr hti
  have hmi2 : p i.head ∈ (i.typ : Multiset (Fin t)) := by
    rw [mem_ord_iff hL O i.typ.2, hci]; exact cycNext_mem hdi hti
  have hmj1 : p j.tail ∈ (j.typ : Multiset (Fin t)) :=
    (mem_ord_iff hL O j.typ.2).mpr (j.tail_mem hL)
  have hmj2 : p j.head ∈ (j.typ : Multiset (Fin t)) := by
    rw [mem_ord_iff hL O j.typ.2, hcj]; exact cycNext_mem (j.dist hL) (j.tail_mem hL)
  rcases Sym2.eq_iff.mp hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ht : i.typ = j.typ := Subtype.ext (hL.unique _ i.typ.2 _ j.typ.2 _ _ hne hmi1 hmi2
      (by rw [show i.tail = j.tail from h1]; exact hmj1)
      (by rw [show i.head = j.head from h2]; exact hmj2))
    exact Subtype.ext (Prod.ext h1 (Prod.ext h2 ht))
  · exfalso
    have h1' : i.tail = j.head := h1
    have h2' : i.head = j.tail := h2
    have ht : i.typ = j.typ := Subtype.ext (hL.unique _ i.typ.2 _ j.typ.2 _ _ hne hmi1 hmi2
      (by rw [h1']; exact hmj2) (by rw [h2']; exact hmj1))
    rw [h1', h2'] at hci
    rw [← ht] at hcj
    -- p(head j) = cyc (p (tail j)) and p (tail j) = cyc (p (head j))
    have hmem : p j.head ∈ ({(O.ord i.typ).1, (O.ord i.typ).2.1, (O.ord i.typ).2.2} :
        Multiset (Fin t)) := by rw [← mem_ord_iff hL O i.typ.2, ht]; exact hmj2
    have := cycNext_cycNext_ne hdi hmem
    rw [← hci, ← hcj] at this
    exact this rfl

/-- The trail edges are exactly `P` (for `P` inside an `F`-blowup). -/
theorem srcE_linPerm (hdiv : IsIntDiv p F P)
    (hP : ∀ a b, s(a, b) ∈ P → AllowedPair F (p a) (p b)) :
    srcE (linPerm (O := O) hL hdiv) ArcL.tail = P := by
  ext e
  simp only [srcE, mem_image, mem_univ, true_and, linPerm_edge]
  constructor
  · rintro ⟨i, rfl⟩; exact i.2.1
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨τ, hτ, _, hle⟩ := hP a b he
      have hd := distinct_ord hL O hτ
      have ha : p a ∈ τ := Multiset.mem_of_le hle (by simp)
      have hb : p b ∈ τ := Multiset.mem_of_le hle (by simp)
      have hab : p a ≠ p b := by
        intro h
        have := hL.nodup τ hτ
        rw [h] at hle
        have h2 := Multiset.le_iff_count.mp hle (p b)
        rw [Multiset.count_eq_one_of_mem this hb] at h2
        simp at h2
      have ha' := (mem_ord_iff hL O hτ).mp ha
      have hb' := (mem_ord_iff hL O hτ).mp hb
      by_cases h1 : p b = cycNext (O.ord τ) (p a)
      · exact ⟨⟨(a, b, ⟨τ, hτ⟩), he, ha, h1⟩, rfl⟩
      · have h2 : p a = cycNext (O.ord τ) (p b) := by
          rcases cycNext_cases hd ha' with ⟨ea, na⟩ | ⟨ea, na⟩ | ⟨ea, na⟩ <;>
            rcases (mem_three_iff hd).mp hb' with eb | eb | eb <;>
            simp_all [cycNext, hd.1, hd.2.1, hd.2.2, Ne.symm hd.1, Ne.symm hd.2.1, Ne.symm hd.2.2]
        exact ⟨⟨(b, a, ⟨τ, hτ⟩), by rw [Sym2.eq_swap]; exact he, hb, h2⟩, Sym2.eq_swap⟩

end Trails

end PartitionedTriangleAbsorption.BlowupB
