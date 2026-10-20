/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-! # Finite integer chains for physical F0 certificates

Occurrences are retained as list positions.  In particular, equal physical
triangles are never silently identified, and the cost counts every signed
occurrence.  This elementary algebra is independent of host geometry.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset

/-- A finite, occurrence-indexed integer combination of objects. -/
abbrev IntegralChain (A : Type*) := List (ℤ × A)

namespace IntegralChain

variable {A B C : Type*}

def eval (L : IntegralChain A) (f : A → ℤ) : ℤ :=
  (L.map fun z => z.1 * f z.2).sum

def cost (L : IntegralChain A) : ℤ := (L.map fun z => |z.1|).sum

def Valid (P : A → Prop) (L : IntegralChain A) : Prop := ∀ z ∈ L, P z.2

/-- A zero coefficient contributes no occurrence, so validity is only needed for
objects with a nonzero coefficient. -/
def term (c : ℤ) (a : A) : IntegralChain A := if c = 0 then [] else [(c,a)]

def scale (c : ℤ) (L : IntegralChain A) : IntegralChain A :=
  L.map fun z => (c * z.1, z.2)

def reindex (f : A → B) (L : IntegralChain A) : IntegralChain B :=
  L.map fun z => (z.1, f z.2)

def substitute (f : A → IntegralChain B) (L : IntegralChain A) : IntegralChain B :=
  L.flatMap fun z => scale z.1 (f z.2)

noncomputable def sum [Fintype A] (f : A → IntegralChain B) : IntegralChain B :=
  (Finset.univ.toList).flatMap f

@[simp] theorem eval_nil (f : A → ℤ) : eval [] f = 0 := by simp [eval]

@[simp] theorem cost_nil : cost ([] : IntegralChain A) = 0 := by simp [cost]

@[simp] theorem eval_cons (z : ℤ × A) (L : IntegralChain A) (f : A → ℤ) :
    eval (z :: L) f = z.1 * f z.2 + eval L f := by simp [eval]

@[simp] theorem cost_cons (z : ℤ × A) (L : IntegralChain A) :
    cost (z :: L) = |z.1| + cost L := by simp [cost]

@[simp] theorem eval_append (L K : IntegralChain A) (f : A → ℤ) :
    eval (L ++ K) f = eval L f + eval K f := by simp [eval]

@[simp] theorem cost_append (L K : IntegralChain A) :
    cost (L ++ K) = cost L + cost K := by simp [cost]

@[simp] theorem eval_term (c : ℤ) (a : A) (f : A → ℤ) :
    eval (term c a) f = c * f a := by
  by_cases h : c = 0 <;> simp [term, h]

@[simp] theorem cost_term (c : ℤ) (a : A) : cost (term c a) = |c| := by
  by_cases h : c = 0 <;> simp [term, h]

theorem valid_term {P : A → Prop} {c : ℤ} {a : A}
    (h : c ≠ 0 → P a) : Valid P (term c a) := by
  by_cases hc : c = 0
  · simp [term, hc, Valid]
  · intro z hz
    simp only [term, if_neg hc, List.mem_singleton] at hz
    subst z
    exact h hc

theorem cost_nonneg (L : IntegralChain A) : 0 ≤ cost L := by
  induction L with
  | nil => simp
  | cons z L ih => simpa only [cost_cons] using add_nonneg (abs_nonneg z.1) ih

@[simp] theorem eval_scale (c : ℤ) (L : IntegralChain A) (f : A → ℤ) :
    eval (scale c L) f = c * eval L f := by
  induction L with
  | nil => simp [scale]
  | cons z L ih =>
    simp only [scale, List.map_cons, eval_cons] at *
    rw [ih]
    ring

@[simp] theorem cost_scale (c : ℤ) (L : IntegralChain A) :
    cost (scale c L) = |c| * cost L := by
  induction L with
  | nil => simp [scale]
  | cons z L ih =>
    simp only [scale, List.map_cons, cost_cons] at *
    rw [ih, abs_mul]
    ring

@[simp] theorem eval_reindex (g : A → B) (L : IntegralChain A) (f : B → ℤ) :
    eval (reindex g L) f = eval L (fun a => f (g a)) := by
  simp [reindex, eval, List.map_map, Function.comp_def]

@[simp] theorem cost_reindex (g : A → B) (L : IntegralChain A) :
    cost (reindex g L) = cost L := by simp [reindex, cost, List.map_map, Function.comp_def]

theorem eval_congr (L : IntegralChain A) {f g : A → ℤ}
    (h : ∀ z ∈ L, f z.2 = g z.2) : eval L f = eval L g := by
  apply congrArg List.sum
  exact List.map_congr_left fun z hz => by rw [h z hz]

@[simp] theorem eval_add (L : IntegralChain A) (f g : A → ℤ) :
    eval L (fun a => f a + g a) = eval L f + eval L g := by
  induction L with
  | nil => simp
  | cons z L ih => simp only [eval_cons, ih]; ring

@[simp] theorem eval_sub (L : IntegralChain A) (f g : A → ℤ) :
    eval L (fun a => f a - g a) = eval L f - eval L g := by
  induction L with
  | nil => simp
  | cons z L ih => simp only [eval_cons, ih]; ring

@[simp] theorem eval_mul (L : IntegralChain A) (f : A → ℤ) (c : ℤ) :
    eval L (fun a => f a * c) = eval L f * c := by
  induction L with
  | nil => simp
  | cons z L ih => simp only [eval_cons, ih]; ring

theorem eval_finite_sum [Fintype B] (L : IntegralChain A) (f : A → B → ℤ) :
    eval L (fun a => ∑ b, f a b) = ∑ b, eval L (fun a => f a b) := by
  classical
  induction L with
  | nil => simp
  | cons z L ih => simp only [eval_cons, ih, Finset.mul_sum, Finset.sum_add_distrib]

theorem valid_nil (P : A → Prop) : Valid P [] := by simp [Valid]

theorem valid_append {P : A → Prop} {L K : IntegralChain A}
    (hL : Valid P L) (hK : Valid P K) : Valid P (L ++ K) := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hL z hz
  · exact hK z hz

theorem valid_scale {P : A → Prop} (c : ℤ) {L : IntegralChain A}
    (hL : Valid P L) : Valid P (scale c L) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  exact hL y hy

theorem valid_reindex {P : A → Prop} {Q : B → Prop} {g : A → B}
    {L : IntegralChain A} (hL : Valid P L) (hg : ∀ a, P a → Q (g a)) :
    Valid Q (reindex g L) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  exact hg y.2 (hL y hy)

@[simp] theorem eval_substitute (g : A → IntegralChain B) (L : IntegralChain A)
    (f : B → ℤ) :
    eval (substitute g L) f = eval L (fun a => eval (g a) f) := by
  induction L with
  | nil => simp [substitute]
  | cons z L ih =>
    simp only [substitute, List.flatMap_cons, eval_append, eval_scale] at *
    rw [ih]
    rfl

theorem cost_substitute_le {g : A → IntegralChain B} {L : IntegralChain A} {K : ℤ}
    (hK : ∀ z ∈ L, cost (g z.2) ≤ K) : cost (substitute g L) ≤ K * cost L := by
  induction L with
  | nil => simp [substitute]
  | cons z L ih =>
    have hz := hK z (by simp)
    have ht : ∀ y ∈ L, cost (g y.2) ≤ K := fun y hy => hK y (by simp [hy])
    simp only [substitute, List.flatMap_cons, cost_append, cost_scale, cost_cons]
    change |z.1| * cost (g z.2) + cost (substitute g L) ≤ K * (|z.1| + cost L)
    have h := add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg z.1)) (ih ht)
    nlinarith

theorem valid_substitute {P : A → Prop} {Q : B → Prop}
    {g : A → IntegralChain B} {L : IntegralChain A} (hL : Valid P L)
    (hg : ∀ a, P a → Valid Q (g a)) : Valid Q (substitute g L) := by
  intro z hz
  obtain ⟨y, hy, hz⟩ := List.mem_flatMap.mp hz
  exact valid_scale y.1 (hg y.2 (hL y hy)) z hz

private theorem eval_flatMap (L : List A) (g : A → IntegralChain B) (f : B → ℤ) :
    eval (L.flatMap g) f = (L.map fun a => eval (g a) f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

private theorem cost_flatMap (L : List A) (g : A → IntegralChain B) :
    cost (L.flatMap g) = (L.map fun a => cost (g a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

@[simp] theorem eval_sum [Fintype A] (g : A → IntegralChain B) (f : B → ℤ) :
    eval (sum g) f = ∑ a, eval (g a) f := by
  classical
  rw [sum, eval_flatMap, Finset.sum_map_toList]

@[simp] theorem cost_sum [Fintype A] (g : A → IntegralChain B) :
    cost (sum g) = ∑ a, cost (g a) := by
  classical
  rw [sum, cost_flatMap, Finset.sum_map_toList]

theorem valid_sum [Fintype A] {P : B → Prop} {g : A → IntegralChain B}
    (h : ∀ a, Valid P (g a)) : Valid P (sum g) := by
  intro z hz
  obtain ⟨a, _, hz⟩ := List.mem_flatMap.mp hz
  exact h a z hz

theorem eval_eq_sum_get (L : IntegralChain A) (f : A → ℤ) :
    eval L f = ∑ i : Fin L.length, (L.get i).1 * f (L.get i).2 := by
  simpa [eval] using (Fin.sum_univ_fun_getElem L (fun z => z.1 * f z.2)).symm

theorem cost_eq_sum_get (L : IntegralChain A) :
    cost L = ∑ i : Fin L.length, |(L.get i).1| := by
  simpa [cost] using (Fin.sum_univ_fun_getElem L (fun z => |z.1|)).symm

end IntegralChain

end PartitionedTriangleAbsorption.BlowupB.F0Direct
