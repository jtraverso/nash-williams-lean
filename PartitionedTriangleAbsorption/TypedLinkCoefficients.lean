/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLinkArithmetic
public import PartitionedTriangleAbsorption.ReturnedBasic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Natural link coefficients in the actual typed divisibility interface

Unlike integral or fractional divisibility, these coefficients are natural
numbers. The constructors below use only permitted triangle types. They do
not assert that all vertex certificates can already be embedded together.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLinkCoefficients

open Finset TypedLinkArithmetic

variable {t : ℕ}

def Realizable (F : Finset (Multiset (Fin t))) (r : Fin t) (d : Fin t → ℤ) : Prop :=
  ∃ c : Multiset (Fin t) → ℕ,
    d = ∑ τ ∈ F with r ∈ τ, (c τ : ℤ) • typeDegVec τ r

def basis (a : Fin t) : Fin t → ℤ := fun j => if a = j then 1 else 0

def demand2 (a b : Fin t) (x y : ℕ) : Fin t → ℤ :=
  fun j => (x : ℤ) * basis a j + (y : ℤ) * basis b j

def demand3 (a b c : Fin t) (x y z : ℕ) : Fin t → ℤ :=
  fun j => (x : ℤ) * basis a j + (y : ℤ) * basis b j + (z : ℤ) * basis c j

theorem triple_link (r a b : Fin t) :
    typeDegVec ({r, a, b} : Multiset (Fin t)) r = basis a + basis b := by
  funext j
  by_cases hr : r = j <;> by_cases ha : a = j <;> by_cases hb : b = j <;>
    simp [typeDegVec, basis, hr, ha, hb, eq_comm]

theorem generator (F : Finset (Multiset (Fin t))) (r : Fin t)
    (τ : Multiset (Fin t)) (hF : τ ∈ F) (hr : r ∈ τ) :
    Realizable F r (typeDegVec τ r) := by
  refine ⟨fun σ => if σ = τ then 1 else 0, ?_⟩
  simp [hF, hr]

theorem Realizable.add {F : Finset (Multiset (Fin t))} {r : Fin t}
    {d e : Fin t → ℤ} (hd : Realizable F r d) (he : Realizable F r e) :
    Realizable F r (d + e) := by
  obtain ⟨a, rfl⟩ := hd
  obtain ⟨b, rfl⟩ := he
  refine ⟨fun τ => a τ + b τ, ?_⟩
  funext j
  simp only [sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_add, add_mul, sum_add_distrib]

theorem Realizable.mul {F : Finset (Multiset (Fin t))} {r : Fin t}
    {d : Fin t → ℤ} (hd : Realizable F r d) (k : ℕ) : Realizable F r ((k : ℤ) • d) := by
  obtain ⟨a, rfl⟩ := hd
  refine ⟨fun τ => k * a τ, ?_⟩
  funext j
  simp only [sum_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, mul_sum, mul_assoc]

theorem wedge (F : Finset (Multiset (Fin t))) (r b : Fin t) (x y : ℕ)
    (h1 : ({r, r, b} : Multiset (Fin t)) ∈ F)
    (h2 : ({r, b, b} : Multiset (Fin t)) ∈ F) (hxy : Wedge x y) :
    Realizable F r (demand2 r b x y) := by
  obtain ⟨a, c, hx, hy⟩ := hxy
  rw [hx, hy]
  have h := ((generator F r _ h1 (by simp)).mul a).add
    ((generator F r _ h2 (by simp)).mul c)
  convert h using 1
  funext j
  simp only [triple_link, Pi.add_apply, Pi.smul_apply, smul_eq_mul, demand2]
  push_cast
  ring

theorem triangle (F : Finset (Multiset (Fin t))) (r u v w : Fin t) (x y z : ℕ)
    (h1 : ({r, u, v} : Multiset (Fin t)) ∈ F)
    (h2 : ({r, u, w} : Multiset (Fin t)) ∈ F)
    (h3 : ({r, v, w} : Multiset (Fin t)) ∈ F) (hxyz : Triangle x y z) :
    Realizable F r (demand3 u v w x y z) := by
  obtain ⟨a, b, c, rfl, rfl, rfl⟩ := hxyz
  have h := (((generator F r _ h1 (by simp)).mul a).add
    ((generator F r _ h2 (by simp)).mul b)).add
    ((generator F r _ h3 (by simp)).mul c)
  convert h using 1
  funext j
  simp only [triple_link, Pi.add_apply, Pi.smul_apply, smul_eq_mul, demand3]
  push_cast
  ring

theorem fork (F : Finset (Multiset (Fin t))) (r u v w : Fin t) (x y z : ℕ)
    (h1 : ({r, u, v} : Multiset (Fin t)) ∈ F)
    (h2 : ({r, u, w} : Multiset (Fin t)) ∈ F)
    (h3 : ({r, v, v} : Multiset (Fin t)) ∈ F)
    (h4 : ({r, w, w} : Multiset (Fin t)) ∈ F) (hxyz : Fork x y z) :
    Realizable F r (demand3 u v w x y z) := by
  obtain ⟨a, b, c, d, rfl, rfl, rfl⟩ := hxyz
  have h := ((((generator F r _ h1 (by simp)).mul a).add
    ((generator F r _ h2 (by simp)).mul b)).add
    ((generator F r _ h3 (by simp)).mul c)).add
    ((generator F r _ h4 (by simp)).mul d)
  convert h using 1
  funext j
  simp only [triple_link, Pi.add_apply, Pi.smul_apply, smul_eq_mul, demand3]
  push_cast
  ring

end PartitionedTriangleAbsorption.TypedLinkCoefficients
