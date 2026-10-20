/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.Template

/-!
# Exact decompositions of the template and of the template plus the piece

Transformer data for `T_P` and `T_Q`, the edge classes separating the eight blocks, and
the two exact triangle decompositions:

* `A = (P₁ ∪ P₂) ∪ (T_P ∪ J) ∪ (T_Q ∪ Q₂) ∪ (Q₁ ∪ Q)`;
* `A ∪ P = (P ∪ P₁) ∪ (P₂ ∪ T_P) ∪ (J ∪ T_Q) ∪ (Q₂ ∪ Q₁) ∪ Q`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

variable {Rt : Type*} [DecidableEq Rt] {m : ℕ}

/-! ### Membership in the subdivided trails and in `J` -/

theorem mem_srcEdges_pathV {base : Fin m → TV Rt m} {t1 t2 t3 : Tag}
    {σ : Equiv.Perm (Fin m)} {e : Sym2 (TV Rt m)} :
    e ∈ srcEdges (blowPerm σ) (pathV base t1 t2 t3) ↔
      ∃ j, e = s(base j, aux j t1) ∨ e = s(aux j t1, aux j t2) ∨ e = s(aux j t2, aux j t3) ∨
        e = s(aux j t3, base (σ j)) := by
  rw [srcEdges, mem_posEdges]
  constructor
  · rintro ⟨⟨j, k⟩, rfl⟩
    fin_cases k <;> refine ⟨j, ?_⟩ <;> simp [pathV]
  · rintro ⟨j, h | h | h | h⟩
    · exact ⟨(j, 0), by simp [pathV, h]⟩
    · exact ⟨(j, 1), by simp [pathV, h]⟩
    · exact ⟨(j, 2), by simp [pathV, h]⟩
    · exact ⟨(j, 3), by simp [pathV, h]⟩

theorem mem_srcEdges_petalV {σ : Equiv.Perm (Fin m)} {e : Sym2 (TV Rt m)} :
    e ∈ srcEdges (blowPerm σ) petalV ↔
      ∃ j : Fin m, e = s(centre j.pos, aux j .j1) ∨ e = s(aux j .j1, aux j .j2) ∨
        e = s(aux j .j2, aux j .j3) ∨ e = s(aux j .j3, centre j.pos) := by
  rw [srcEdges, mem_posEdges]
  constructor
  · rintro ⟨⟨j, k⟩, rfl⟩
    fin_cases k <;> refine ⟨j, ?_⟩ <;> simp [petalV]
  · rintro ⟨j, h | h | h | h⟩
    · exact ⟨(j, 0), by simp [petalV, h]⟩
    · exact ⟨(j, 1), by simp [petalV, h]⟩
    · exact ⟨(j, 2), by simp [petalV, h]⟩
    · exact ⟨(j, 3), by simp [petalV, h]⟩

/-- `J` does not depend on the trail system used to present it. -/
theorem srcEdges_petalV_eq (σ σ' : Equiv.Perm (Fin m)) :
    srcEdges (blowPerm σ) (petalV : _ → TV Rt m) = srcEdges (blowPerm σ') petalV := by
  ext e; rw [mem_srcEdges_petalV, mem_srcEdges_petalV]

/-! ### Transformer data -/

variable (σt : Equiv.Perm (Fin m)) (xr : Fin m → Rt) (h3 : 3 ∣ m)

omit [DecidableEq Rt] in
theorem transformerData_P : TransformerData (blowPerm σt) (xP xr) petalV auxP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, k⟩; fin_cases k <;> simp [xP, pathV]
  · rintro ⟨j, k⟩; fin_cases k <;> simp [petalV]
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [xP, pathV] at h ⊢ <;> simp_all
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [petalV] at h ⊢ <;> simp_all
  · rintro ⟨⟨j, k⟩, c⟩ ⟨⟨j', k'⟩, c'⟩ h
    simp [auxP] at h ⊢; tauto
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxP, xP, pathV]
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxP, petalV]
  · rintro ⟨j, k⟩ ⟨j', k'⟩; fin_cases k <;> fin_cases k' <;> simp [xP, pathV, petalV]

omit [DecidableEq Rt] in
theorem transformerData_Q :
    TransformerData (blowPerm (triPerm h3)) (xQ : _ → TV Rt m) petalV auxQ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, k⟩; fin_cases k <;> simp [xQ, pathV]
  · rintro ⟨j, k⟩; fin_cases k <;> simp [petalV]
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [xQ, pathV] at h ⊢ <;> simp_all
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    fin_cases k <;> fin_cases k' <;> simp [petalV] at h ⊢ <;> simp_all
  · rintro ⟨⟨j, k⟩, c⟩ ⟨⟨j', k'⟩, c'⟩ h
    simp [auxQ] at h ⊢; tauto
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxQ, xQ, pathV]
  · rintro ⟨⟨j, k⟩, c⟩ ⟨j', k'⟩; fin_cases k' <;> simp [auxQ, petalV]
  · rintro ⟨j, k⟩ ⟨j', k'⟩; fin_cases k <;> fin_cases k' <;> simp [xQ, pathV, petalV]


/-! ### Edge classes separating the blocks -/

/-- Class of a tag. -/
def tagCls : Tag → ℕ
  | .q => 1
  | .j1 => 2
  | .j2 => 2
  | .j3 => 2
  | .p1 => 3
  | .p2a => 4
  | .p2b => 4
  | .q1 => 5
  | .q2a => 6
  | .q2b => 6
  | .tp _ _ => 7
  | .tq _ _ => 8

/-- Class of a template vertex: roots `0`, centre `2`. -/
def cls : TV Rt m → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inr _) => 2
  | Sum.inr (Sum.inl (_, t)) => tagCls t

/-- The (unordered) pair of classes of the endpoints of an edge. -/
def kappa (e : Sym2 (TV Rt m)) : ℕ × ℕ :=
  Sym2.lift ⟨fun u w => (min (cls u) (cls w), max (cls u) (cls w)), fun u w => by
    simp [min_comm, max_comm]⟩ e

omit [DecidableEq Rt] in
theorem disjoint_of_kappa {X Y : Finset (Sym2 (TV Rt m))} {p q : ℕ × ℕ → Prop}
    (hX : ∀ e ∈ X, p (kappa e)) (hY : ∀ e ∈ Y, q (kappa e)) (h : ∀ z, p z → q z → False) :
    Disjoint X Y :=
  Finset.disjoint_left.mpr fun e he he' => h _ (hX e he) (hY e he')

set_option hygiene false in
/-- Close a class computation. -/
local macro "kcls" : tactic =>
  `(tactic| simp [kappa, cls, tagCls, xP, xQ, pathV, petalV, auxP, auxQ])

theorem kappa_P : ∀ e ∈ edgesP σt xr, kappa e = (0, 0) := by
  intro e he
  obtain ⟨j, rfl⟩ := mem_posEdges.mp he
  kcls

theorem kappa_P1 : ∀ e ∈ edgesP1 σt xr, kappa e = (0, 3) := by
  intro e he
  rcases mem_union.mp he with he | he <;> obtain ⟨j, rfl⟩ := mem_posEdges.mp he <;> kcls

theorem kappa_P2 : ∀ e ∈ edgesP2 σt xr, kappa e = (0, 4) ∨ kappa e = (3, 4) := by
  intro e he
  rw [edgesP2, xP, mem_srcEdges_pathV] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> kcls

theorem kappa_J : ∀ e ∈ edgesJ σt (Rt := Rt), kappa e = (2, 2) := by
  intro e he
  rw [edgesJ, mem_srcEdges_petalV] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> kcls

theorem kappa_TP : ∀ e ∈ edgesTP σt xr, (kappa e).2 = 7 := by
  intro e he
  simp only [edgesTP, transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨⟨j, k⟩, he⟩ := he
  simp only [transAt, mem_insert, mem_singleton] at he
  fin_cases k <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kcls

theorem kappa_TQ : ∀ e ∈ edgesTQ h3 (Rt := Rt), (kappa e).2 = 8 := by
  intro e he
  simp only [edgesTQ, transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨⟨j, k⟩, he⟩ := he
  simp only [transAt, mem_insert, mem_singleton] at he
  fin_cases k <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kcls

theorem kappa_TQ_fst : ∀ e ∈ edgesTQ h3 (Rt := Rt), (kappa e).1 ≠ 0 := by
  intro e he
  simp only [edgesTQ, transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨⟨j, k⟩, he⟩ := he
  simp only [transAt, mem_insert, mem_singleton] at he
  fin_cases k <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kcls

omit [DecidableEq Rt] in
theorem kappa_fst_of_root (r : Rt) {e : Sym2 (TV Rt m)} (h : Sum.inl r ∈ e) :
    (kappa e).1 = 0 := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp h
  simp [kappa, cls]

theorem kappa_Q2 : ∀ e ∈ edgesQ2 h3 (Rt := Rt), kappa e = (1, 6) ∨ kappa e = (5, 6) := by
  intro e he
  rw [edgesQ2, xQ, mem_srcEdges_pathV] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> kcls

theorem kappa_Q1 : ∀ e ∈ edgesQ1 h3 (Rt := Rt), kappa e = (1, 5) := by
  intro e he
  rcases mem_union.mp he with he | he <;> obtain ⟨j, rfl⟩ := mem_posEdges.mp he <;> kcls

theorem kappa_Q : ∀ e ∈ edgesQ h3 (Rt := Rt), kappa e = (1, 1) := by
  intro e he
  obtain ⟨j, rfl⟩ := mem_posEdges.mp he
  kcls


/-! ### Subdivision blocks -/

omit [DecidableEq Rt] in
theorem hasDecomp_single [DecidableEq Rt] (base : Fin m → TV Rt m) (σ : Equiv.Perm (Fin m))
    (tm : Tag) (hinj : Function.Injective fun j => s(base j, base (σ j)))
    (hne : ∀ j, base j ≠ base (σ j)) (hbm : ∀ j j', base j ≠ aux j' tm) :
    HasDecomp part1 triFam (posEdges base (fun j => base (σ j)) ∪
      (posEdges base (fun j => aux j tm) ∪ posEdges (fun j => aux j tm) fun j => base (σ j))) :=
  hasDecomp_subdivision base (fun j => base (σ j)) (fun j => aux j tm) hne hinj
    (fun j j' h => by simpa using h) (fun i j h => hbm j i h.symm)
    (fun i j h => hbm (σ j) i h.symm)

theorem hasDecomp_double (base : Fin m → TV Rt m) (σ : Equiv.Perm (Fin m))
    (tm t1 t3 : Tag) (h1m : t1 ≠ tm) (h3m : t3 ≠ tm) (h13 : t1 ≠ t3)
    (hbm : ∀ j j', base j ≠ aux j' tm) (hb1 : ∀ j j', base j ≠ aux j' t1)
    (hb3 : ∀ j j', base j ≠ aux j' t3) (hne : ∀ j, base j ≠ base (σ j)) :
    HasDecomp part1 triFam
      ((posEdges base (fun j => aux j tm) ∪ posEdges (fun j => aux j tm) fun j => base (σ j)) ∪
        srcEdges (blowPerm σ) (pathV base t1 tm t3)) := by
  let a : Fin m × Fin 2 → TV Rt m := fun p => ![base p.1, aux p.1 tm] p.2
  let b : Fin m × Fin 2 → TV Rt m := fun p => ![aux p.1 tm, base (σ p.1)] p.2
  let c : Fin m × Fin 2 → TV Rt m := fun p => ![aux p.1 t1, aux p.1 t3] p.2
  have hbm' : ∀ j j', aux j' tm ≠ base j := fun j j' h => hbm j j' h.symm
  have hb1' : ∀ j j', aux j' t1 ≠ base j := fun j j' h => hb1 j j' h.symm
  have hb3' : ∀ j j', aux j' t3 ≠ base j := fun j j' h => hb3 j j' h.symm
  have h := hasDecomp_subdivision a b c
    (by rintro ⟨j, k⟩; fin_cases k <;> simp [a, b, hbm, hbm'])
    (by
      rintro ⟨j, k⟩ ⟨j', k'⟩ h
      fin_cases k <;> fin_cases k' <;>
        simp only [a, b, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Sym2.eq_iff, hbm, hbm', and_false,
          false_or, or_false, aux, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
          and_true, Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_ne_one,
          one_ne_zero] at h ⊢ <;>
        solve
        | exact h
        | exact h.2
        | exact h.1
        | exact absurd h.2 (hne j)
        | (obtain ⟨rfl, h⟩ := h; exact absurd h.symm (hne _))
        | (obtain ⟨h, rfl⟩ := h; exact absurd h (hne _)))
    (by
      rintro ⟨j, k⟩ ⟨j', k'⟩ h
      fin_cases k <;> fin_cases k' <;> simp_all [c])
    (by rintro ⟨j, k⟩ ⟨j', k'⟩; fin_cases k <;> fin_cases k' <;> simp [a, c, hb1', hb3', h1m, h3m])
    (by rintro ⟨j, k⟩ ⟨j', k'⟩; fin_cases k <;> fin_cases k' <;> simp [b, c, hb1', hb3', h1m, h3m])
  convert h using 1
  have e1 : posEdges a b =
      posEdges base (fun j => aux j tm) ∪ posEdges (fun j => aux j tm) fun j => base (σ j) := by
    ext e
    simp only [mem_union, mem_posEdges, Prod.exists, Fin.exists_fin_two, a, b]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨j, h | h⟩
      exacts [Or.inl ⟨j, h⟩, Or.inr ⟨j, h⟩]
    · rintro (⟨j, h⟩ | ⟨j, h⟩)
      exacts [⟨j, Or.inl h⟩, ⟨j, Or.inr h⟩]
  have e2 : posEdges a c ∪ posEdges c b = srcEdges (blowPerm σ) (pathV base t1 tm t3) := by
    ext e
    rw [mem_srcEdges_pathV]
    simp only [mem_union, mem_posEdges, Prod.exists, Fin.exists_fin_two, a, b, c]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor
    · rintro (⟨j, h | h⟩ | ⟨j, h | h⟩)
      · exact ⟨j, Or.inl h⟩
      · exact ⟨j, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨j, Or.inr (Or.inl h)⟩
      · exact ⟨j, Or.inr (Or.inr (Or.inr h))⟩
    · rintro ⟨j, h | h | h | h⟩
      · exact Or.inl ⟨j, Or.inl h⟩
      · exact Or.inr ⟨j, Or.inl h⟩
      · exact Or.inl ⟨j, Or.inr h⟩
      · exact Or.inr ⟨j, Or.inr h⟩
  rw [e1, e2]


/-! ### The triangle rotation -/

theorem triPerm_ne (j : Fin m) : triPerm h3 j ≠ j := by
  intro h
  have := congrArg Fin.val h
  rw [triPerm_val] at this
  split_ifs at this <;> omega

theorem triPerm_ne2 (j : Fin m) : triPerm h3 (triPerm h3 j) ≠ j := by
  intro h
  have := congrArg Fin.val h
  rw [triPerm_val, triPerm_val] at this
  split_ifs at this <;> omega

theorem triPerm_three (j : Fin m) : triPerm h3 (triPerm h3 (triPerm h3 j)) = j := by
  apply Fin.ext
  rw [triPerm_val, triPerm_val, triPerm_val]
  split_ifs <;> omega

theorem triPerm_div (j : Fin m) : (triPerm h3 j).val / 3 = j.val / 3 := by
  rw [triPerm_val]; split_ifs <;> omega

omit [DecidableEq Rt] in
theorem qEdge_injective :
    Function.Injective fun j : Fin m => s((qv j : TV Rt m), qv (triPerm h3 j)) := by
  intro j j' h
  simp only [Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] at h
  rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  · subst h1
    exact absurd h2 (triPerm_ne2 h3 j')

/-- The triangles of `Q` give an exact decomposition of `Q`. -/
theorem hasDecomp_Q : HasDecomp part1 triFam (edgesQ h3 (Rt := Rt)) := by
  let L := {j : Fin m // j.val % 3 = 0}
  let ta : L → TV Rt m := fun l => qv l.1
  let tb : L → TV Rt m := fun l => qv (triPerm h3 l.1)
  let tc : L → TV Rt m := fun l => qv (triPerm h3 (triPerm h3 l.1))
  have key : ∀ (l : L) e, e ∈ tri3 (ta l) (tb l) (tc l) → ∀ v ∈ e,
      ∃ a : Fin m, v = qv a ∧ a.val / 3 = l.1.val / 3 := by
    intro l e he v hv
    rw [mem_tri3] at he
    rcases he with rfl | rfl | rfl <;> rcases Sym2.mem_iff.mp hv with rfl | rfl <;>
      first
      | exact ⟨_, rfl, rfl⟩
      | exact ⟨_, rfl, triPerm_div h3 _⟩
      | exact ⟨_, rfl, (triPerm_div h3 _).trans (triPerm_div h3 _)⟩
  have hg : GoodLabels ta tb tc := by
    refine ⟨fun l h => ?_, fun l h => ?_, fun l h => ?_, ?_⟩
    · simp only [ta, tb, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] at h
      exact triPerm_ne h3 _ h.symm
    · simp only [ta, tc, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] at h
      exact triPerm_ne2 h3 _ h.symm
    · simp only [tb, tc, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] at h
      exact triPerm_ne h3 _ ((triPerm h3).injective h).symm
    · intro l l' e he he'
      induction e using Sym2.ind with
      | _ x y =>
      obtain ⟨a, rfl, ha⟩ := key l _ he x (Sym2.mem_mk_left x y)
      obtain ⟨a', ha', ha''⟩ := key l' _ he' (qv a) (Sym2.mem_mk_left _ y)
      simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] at ha'
      subst ha'
      have h1 := l.2
      have h2 := l'.2
      exact Subtype.ext (Fin.ext (by omega))
  have heq : labelEdges ta tb tc = edgesQ h3 := by
    ext e
    rw [mem_labelEdges, edgesQ, mem_posEdges]
    constructor
    · rintro ⟨l, he⟩
      rw [mem_tri3] at he
      rcases he with rfl | rfl | rfl
      · exact ⟨l.1, rfl⟩
      · refine ⟨triPerm h3 (triPerm h3 l.1), ?_⟩
        simp only [ta, tc, triPerm_three]
        exact Sym2.eq_swap
      · exact ⟨triPerm h3 l.1, rfl⟩
    · rintro ⟨i, rfl⟩
      have hl : (i.val - i.val % 3) % 3 = 0 := by omega
      let l : L := ⟨⟨i.val - i.val % 3, by omega⟩, hl⟩
      have h1 : (triPerm h3 l.1).val = l.1.val + 1 := by
        rw [triPerm_val]; simp only [l]; split_ifs <;> omega
      have h2 : (triPerm h3 (triPerm h3 l.1)).val = l.1.val + 2 := by
        rw [triPerm_val, h1]; simp only [l]; split_ifs <;> omega
      refine ⟨l, ?_⟩
      rw [mem_tri3]
      have hi : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hi with hi | hi | hi
      · have e0 : i = l.1 := Fin.ext (by simp only [l]; omega)
        left; rw [e0]
      · have e1 : i = triPerm h3 l.1 := Fin.ext (by rw [h1]; simp only [l]; omega)
        right; right; rw [e1]
      · have e2 : i = triPerm h3 (triPerm h3 l.1) := Fin.ext (by rw [h2]; simp only [l]; omega)
        right; left; rw [e2, triPerm_three]; exact Sym2.eq_swap
  rw [← heq]
  exact hg.hasDecomp


/-! ### Piece identifiers -/

/-- The block (piece) an edge class belongs to: `P = 0, P₁ = 1, P₂ = 2, T_P = 3, J = 4,
T_Q = 5, Q₂ = 6, Q₁ = 7, Q = 8`. -/
def pieceId (z : ℕ × ℕ) : ℕ :=
  if z.2 = 7 then 3 else if z.2 = 8 then 5 else
  if z = (0, 0) then 0 else if z = (0, 3) then 1 else if z = (0, 4) ∨ z = (3, 4) then 2 else
  if z = (2, 2) then 4 else if z = (1, 6) ∨ z = (5, 6) then 6 else if z = (1, 5) then 7 else
  if z = (1, 1) then 8 else 9

/-- Edges whose piece identifier lies in `S`. -/
def PieceIn (X : Finset (Sym2 (TV Rt m))) (S : Finset ℕ) : Prop :=
  ∀ e ∈ X, pieceId (kappa e) ∈ S

theorem PieceIn.union {X Y : Finset (Sym2 (TV Rt m))} {S T : Finset ℕ} (hX : PieceIn X S)
    (hY : PieceIn Y T) : PieceIn (X ∪ Y) (S ∪ T) := by
  intro e he
  rcases mem_union.mp he with he | he
  exacts [mem_union_left _ (hX e he), mem_union_right _ (hY e he)]

omit [DecidableEq Rt] in
theorem PieceIn.disjoint {X Y : Finset (Sym2 (TV Rt m))} {S T : Finset ℕ} (hX : PieceIn X S)
    (hY : PieceIn Y T) (h : Disjoint S T) : Disjoint X Y :=
  disjoint_of_kappa (p := fun z => pieceId z ∈ S) (q := fun z => pieceId z ∈ T) hX hY
    fun _ h1 h2 => Finset.disjoint_left.mp h h1 h2

theorem pieceIn_P : PieceIn (edgesP σt xr) {0} := fun e he => by
  simp [kappa_P σt xr e he, pieceId]

theorem pieceIn_P1 : PieceIn (edgesP1 σt xr) {1} := fun e he => by
  simp [kappa_P1 σt xr e he, pieceId]

theorem pieceIn_P2 : PieceIn (edgesP2 σt xr) {2} := fun e he => by
  rcases kappa_P2 σt xr e he with h | h <;> simp [h, pieceId]

theorem pieceIn_TP : PieceIn (edgesTP σt xr) {3} := fun e he => by
  simp [kappa_TP σt xr e he, pieceId]

theorem pieceIn_J : PieceIn (edgesJ σt (Rt := Rt)) {4} := fun e he => by
  simp [kappa_J σt e he, pieceId]

theorem pieceIn_TQ : PieceIn (edgesTQ h3 (Rt := Rt)) {5} := fun e he => by
  simp [kappa_TQ h3 e he, pieceId]

theorem pieceIn_Q2 : PieceIn (edgesQ2 h3 (Rt := Rt)) {6} := fun e he => by
  rcases kappa_Q2 h3 e he with h | h <;> simp [h, pieceId]

theorem pieceIn_Q1 : PieceIn (edgesQ1 h3 (Rt := Rt)) {7} := fun e he => by
  simp [kappa_Q1 h3 e he, pieceId]

theorem pieceIn_Q : PieceIn (edgesQ h3 (Rt := Rt)) {8} := fun e he => by
  simp [kappa_Q h3 e he, pieceId]

theorem pieceIn_template : PieceIn (template σt xr h3) {1, 2, 3, 4, 5, 6, 7, 8} := by
  have h := ((((((pieceIn_P1 σt xr).union (pieceIn_P2 σt xr)).union (pieceIn_TP σt xr)).union
    (pieceIn_J σt)).union (pieceIn_TQ h3)).union (pieceIn_Q2 h3)).union (pieceIn_Q1 h3)
    |>.union (pieceIn_Q h3)
  intro e he
  have := h e he
  simp only [mem_union, mem_singleton] at this
  simp only [mem_insert, mem_singleton]
  omega

/-- **No template edge joins two roots.** In particular `A` is disjoint from the piece. -/
theorem template_no_root_edge (r r' : Rt) :
    s((Sum.inl r : TV Rt m), Sum.inl r') ∉ template σt xr h3 := by
  intro h
  have := pieceIn_template σt xr h3 _ h
  simp [kappa, cls, pieceId] at this

theorem disjoint_template_P : Disjoint (template σt xr h3) (edgesP σt xr) :=
  (pieceIn_template σt xr h3).disjoint (pieceIn_P σt xr) (by decide)

/-! ### The two exact decompositions -/

variable {σt xr}

/-- **Exact decomposition of the template `A`.** -/
theorem hasDecomp_template (hne : ∀ j, xr j ≠ xr (σt j)) :
    HasDecomp part1 triFam (template σt xr h3) := by
  have hB1 : HasDecomp part1 triFam (edgesP1 σt xr ∪ edgesP2 σt xr) :=
    hasDecomp_double (fun j => Sum.inl (xr j)) σt .p1 .p2a .p2b (by decide) (by decide)
      (by decide) (by simp) (by simp) (by simp) (fun j => by simpa using hne j)
  have hB2 : HasDecomp part1 triFam (edgesTP σt xr ∪ edgesJ σt) :=
    (transformerData_P σt xr).hasDecomp_target
  have hB3 : HasDecomp part1 triFam (edgesTQ h3 ∪ edgesQ2 h3 (Rt := Rt)) :=
    (transformerData_Q h3).hasDecomp_source
  have hB4 : HasDecomp part1 triFam (edgesQ1 h3 ∪ edgesQ h3 (Rt := Rt)) := by
    have := hasDecomp_single (fun j => (qv j : TV Rt m)) (triPerm h3) .q1 (qEdge_injective h3)
      (fun j => by simpa using (triPerm_ne h3 j).symm) (by simp)
    rw [union_comm]; exact this
  have i1 := (pieceIn_P1 σt xr).union (pieceIn_P2 σt xr)
  have i2 := (pieceIn_TP σt xr).union (pieceIn_J σt)
  have i3 := (pieceIn_TQ h3).union (pieceIn_Q2 h3 (Rt := Rt))
  have i4 := (pieceIn_Q1 h3).union (pieceIn_Q h3 (Rt := Rt))
  have h12 := hB1.union hB2 (i1.disjoint i2 (by decide))
  have h123 := h12.union hB3 ((i1.union i2).disjoint i3 (by decide))
  have h1234 := h123.union hB4 (((i1.union i2).union i3).disjoint i4 (by decide))
  convert h1234 using 1
  simp only [template, union_assoc]

/-- **Exact decomposition of the template together with the piece, `A ∪ P`.** -/
theorem hasDecomp_template_union (hne : ∀ j, xr j ≠ xr (σt j))
    (hinj : Function.Injective fun j => s(xr j, xr (σt j))) :
    HasDecomp part1 triFam (template σt xr h3 ∪ edgesP σt xr) := by
  have hC1 : HasDecomp part1 triFam (edgesP σt xr ∪ edgesP1 σt xr) :=
    hasDecomp_single (fun j => Sum.inl (xr j)) σt .p1
      (by
        intro j j' h
        apply hinj
        simpa [Sym2.eq_iff] using h)
      (fun j => by simpa using hne j) (by simp)
  have hC2 : HasDecomp part1 triFam (edgesP2 σt xr ∪ edgesTP σt xr) := by
    rw [union_comm]; exact (transformerData_P σt xr).hasDecomp_source
  have hC3 : HasDecomp part1 triFam (edgesJ σt ∪ edgesTQ h3 (Rt := Rt)) := by
    rw [union_comm, edgesJ, srcEdges_petalV_eq σt (triPerm h3)]
    exact (transformerData_Q h3).hasDecomp_target
  have hC4 : HasDecomp part1 triFam (edgesQ2 h3 ∪ edgesQ1 h3 (Rt := Rt)) := by
    rw [union_comm]
    exact hasDecomp_double (fun j => (qv j : TV Rt m)) (triPerm h3) .q1 .q2a .q2b (by decide)
      (by decide) (by decide) (by simp) (by simp) (by simp)
      (fun j => by simpa using (triPerm_ne h3 j).symm)
  have hC5 := hasDecomp_Q h3 (Rt := Rt)
  have i1 := (pieceIn_P σt xr).union (pieceIn_P1 σt xr)
  have i2 := (pieceIn_P2 σt xr).union (pieceIn_TP σt xr)
  have i3 := (pieceIn_J σt).union (pieceIn_TQ h3 (Rt := Rt))
  have i4 := (pieceIn_Q2 h3).union (pieceIn_Q1 h3 (Rt := Rt))
  have i5 := pieceIn_Q h3 (Rt := Rt)
  have h12 := hC1.union hC2 (i1.disjoint i2 (by decide))
  have h123 := h12.union hC3 ((i1.union i2).disjoint i3 (by decide))
  have h1234 := h123.union hC4 (((i1.union i2).union i3).disjoint i4 (by decide))
  have h12345 := h1234.union hC5 ((((i1.union i2).union i3).union i4).disjoint i5 (by decide))
  convert h12345 using 1
  simp only [template]
  ac_rfl

end PartitionedTriangleAbsorption.PrivateTemplate
