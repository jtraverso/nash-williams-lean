/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.IntVec
public import PartitionedTriangleAbsorption.ReturnedBridge

/-! # BlowupB.CompleteBlowup — complete blowups of a family, representatives, edge indicators

* `ind1 e` — integer indicator of a single edge; `indZ (triEdges {a,b,c})` as a sum of three;
* `AllowedPair F i j` — some type of `F` contains the pair `{i, j}`; `exists_third`;
* `IsCompleteBlowup p F G` — `G.Adj u v ↔ u ≠ v ∧ AllowedPair F (p u) (p v)`; every transversal
  triple of a type of `F` is a copy (`isCopy_of_complete`);
* `Reps p q` — `q` representatives in every class, with avoidance (`exists_avoid`) and a canonical
  representative `canon` of every class different from a given vertex;
* `MeetsReps`, `OnReps` — support predicates for integer edge functions, closed under the lattice
  operations.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### Single-edge indicators -/

/-- The integer indicator of a single edge. -/
def ind1 (e : Sym2 V) : Sym2 V → ℤ := indZ {e}

omit [Fintype V] in
theorem ind1_apply (e f : Sym2 V) : ind1 e f = if f = e then 1 else 0 := by
  simp [ind1, indZ]

omit [Fintype V] in
theorem ind1_self (e : Sym2 V) : ind1 e e = 1 := by simp [ind1_apply]

omit [Fintype V] in
theorem ind1_of_ne {e f : Sym2 V} (h : f ≠ e) : ind1 e f = 0 := by simp [ind1_apply, h]

omit [Fintype V] in
theorem ind1_swap (u v : V) : ind1 s(u, v) = ind1 s(v, u) := by
  rw [Sym2.eq_swap]

omit [Fintype V] in
theorem indZ_insert_of_notMem {e : Sym2 V} {E : Finset (Sym2 V)} (h : e ∉ E) :
    indZ (insert e E) = ind1 e + indZ E := by
  funext f
  simp only [indZ, ind1, Pi.add_apply, mem_insert, mem_singleton]
  by_cases hf : f = e
  · subst hf; simp [h]
  · simp [hf]

omit [Fintype V] in
theorem indZ_eq_sum_ind1 (E : Finset (Sym2 V)) : indZ E = ∑ e ∈ E, ind1 e := by
  classical
  induction E using Finset.induction_on with
  | empty => funext f; simp [indZ]
  | insert a s ha ih => rw [indZ_insert_of_notMem ha, sum_insert ha, ih]

omit [Fintype V] in
theorem indZ_triEdges_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    indZ (triEdges ({a, b, c} : Finset V)) = ind1 s(a, b) + ind1 s(a, c) + ind1 s(b, c) := by
  rw [triEdges_three hab hac hbc]
  have h1 : s(a, b) ∉ ({s(a, c), s(b, c)} : Finset (Sym2 V)) := by simp [hab, hac, hbc]
  have h2 : s(a, c) ∉ ({s(b, c)} : Finset (Sym2 V)) := by simp [hab, hac]
  rw [indZ_insert_of_notMem h1, indZ_insert_of_notMem h2, add_assoc]
  rfl

omit [Fintype V] in
theorem ind1_nonzero_iff {e f : Sym2 V} : ind1 e f ≠ 0 ↔ f = e := by
  rw [ind1_apply]; split_ifs with h <;> simp [h]

/-! ### Allowed pairs and complete blowups -/

/-- The pair of classes `{i, j}` is contained in some (3-element) type of `F`. -/
def AllowedPair (F : Finset (Multiset (Fin t))) (i j : Fin t) : Prop :=
  ∃ τ ∈ F, Multiset.card τ = 3 ∧ ({i, j} : Multiset (Fin t)) ≤ τ

theorem AllowedPair.symm {F : Finset (Multiset (Fin t))} {i j : Fin t}
    (h : AllowedPair F i j) : AllowedPair F j i := by
  obtain ⟨τ, hτ, hc, hle⟩ := h
  exact ⟨τ, hτ, hc, by rwa [Multiset.pair_comm]⟩

theorem three_swap23 {α : Type*} (x y z : α) : ({x, y, z} : Multiset α) = {x, z, y} := by
  show x ::ₘ y ::ₘ z ::ₘ 0 = x ::ₘ z ::ₘ y ::ₘ 0
  rw [Multiset.cons_swap y z]

theorem three_swap12 {α : Type*} (x y z : α) : ({x, y, z} : Multiset α) = {y, x, z} := by
  show x ::ₘ y ::ₘ z ::ₘ 0 = y ::ₘ x ::ₘ z ::ₘ 0
  rw [Multiset.cons_swap x y]

theorem pair_le_three_12 {α : Type*} (x y z : α) :
    ({x, y} : Multiset α) ≤ {x, y, z} := by
  show x ::ₘ y ::ₘ 0 ≤ x ::ₘ y ::ₘ z ::ₘ 0
  exact Multiset.cons_le_cons _ (Multiset.cons_le_cons _ (Multiset.zero_le _))

theorem pair_le_three_13 {α : Type*} (x y z : α) :
    ({x, z} : Multiset α) ≤ {x, y, z} := by
  rw [three_swap23]; exact pair_le_three_12 x z y

theorem pair_le_three_23 {α : Type*} (x y z : α) :
    ({y, z} : Multiset α) ≤ {x, y, z} := by
  show y ::ₘ z ::ₘ 0 ≤ x ::ₘ y ::ₘ z ::ₘ 0
  exact Multiset.le_cons_self _ _

theorem card_three {α : Type*} (x y z : α) : Multiset.card ({x, y, z} : Multiset α) = 3 := by
  simp

theorem allowedPair_of_three {F : Finset (Multiset (Fin t))} {i j k : Fin t}
    (h : ({i, j, k} : Multiset (Fin t)) ∈ F) :
    AllowedPair F i j ∧ AllowedPair F i k ∧ AllowedPair F j k :=
  ⟨⟨_, h, card_three i j k, pair_le_three_12 i j k⟩,
    ⟨_, h, card_three i j k, pair_le_three_13 i j k⟩,
    ⟨_, h, card_three i j k, pair_le_three_23 i j k⟩⟩

/-- An allowed pair extends to a type of `F`. -/
theorem exists_third {F : Finset (Multiset (Fin t))} {i j : Fin t} (h : AllowedPair F i j) :
    ∃ k, ({i, j, k} : Multiset (Fin t)) ∈ F := by
  obtain ⟨τ, hτ, hc, hle⟩ := h
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp hle
  have hu : Multiset.card u = 1 := by
    rw [Multiset.card_add] at hc; simp at hc; omega
  obtain ⟨k, rfl⟩ := Multiset.card_eq_one.mp hu
  exact ⟨k, hτ⟩

/-- A chosen third class completing an allowed pair. -/
noncomputable def third (F : Finset (Multiset (Fin t))) (i j : Fin t) (h : AllowedPair F i j) :
    Fin t :=
  Classical.choose (exists_third h)

theorem third_spec (F : Finset (Multiset (Fin t))) (i j : Fin t) (h : AllowedPair F i j) :
    ({i, j, third F i j h} : Multiset (Fin t)) ∈ F :=
  Classical.choose_spec (exists_third h)

/-- `G` is the **complete `F`-blowup** of the partition `p`: two distinct vertices are adjacent
iff their pair of classes is contained in a type of `F`. -/
def IsCompleteBlowup (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) :
    Prop :=
  ∀ u v, G.Adj u v ↔ u ≠ v ∧ AllowedPair F (p u) (p v)

omit [Fintype V] in
/-- Every transversal triple of a type of `F` is a copy in the complete blowup. -/
theorem isCopy_of_complete {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hτ : ({p a, p b, p c} : Multiset (Fin t)) ∈ F) : IsCopy p F G {a, b, c} := by
  obtain ⟨h12, h13, h23⟩ := allowedPair_of_three hτ
  refine ⟨?_, by rw [map_three p hab hac hbc]; exact hτ⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩⟩
  intro x hx y hy hxy
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rw [hG]
  refine ⟨hxy, ?_⟩
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact h12
  · exact h13
  · exact h12.symm
  · exact absurd rfl hxy
  · exact h23
  · exact h13.symm
  · exact h23.symm
  · exact absurd rfl hxy

omit [Fintype V] [DecidableEq V] in
/-- Edges of a complete blowup are allowed pairs. -/
theorem allowedPair_of_adj {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    (hG : IsCompleteBlowup p F G) {u v : V} (h : G.Adj u v) : AllowedPair F (p u) (p v) :=
  ((hG u v).mp h).2

/-! ### Representatives -/

/-- `q` representatives in every class of `p`, pairwise distinct. -/
structure Reps (p : V → Fin t) (q : ℕ) where
  rep : Fin t → Fin q → V
  inj : ∀ i a i' a', rep i a = rep i' a' → i = i' ∧ a = a'
  cls : ∀ i a, p (rep i a) = i

namespace Reps

variable {p : V → Fin t} {q : ℕ} (R : Reps p q)

/-- The set of all representatives. -/
def set : Finset V := univ.image (fun x : Fin t × Fin q => R.rep x.1 x.2)

omit [Fintype V] in
theorem rep_mem (i : Fin t) (a : Fin q) : R.rep i a ∈ R.set :=
  mem_image.mpr ⟨(i, a), mem_univ _, rfl⟩

omit [Fintype V] in
theorem mem_set_iff {v : V} : v ∈ R.set ↔ ∃ i a, R.rep i a = v := by
  simp [Reps.set]

omit [Fintype V] [DecidableEq V] in
theorem rep_ne_of_cls_ne {i : Fin t} {a : Fin q} {v : V} (h : p v ≠ i) : R.rep i a ≠ v := by
  intro hv; apply h; rw [← hv, R.cls]

omit [Fintype V] [DecidableEq V] in
theorem rep_inj_right {i : Fin t} {a a' : Fin q} (h : R.rep i a = R.rep i a') : a = a' :=
  (R.inj i a i a' h).2

omit [Fintype V] in
/-- Pigeonhole: a representative of class `i` avoiding any set of fewer than `q` vertices. -/
theorem exists_avoid (i : Fin t) (S : Finset V) (hS : S.card < q) : ∃ a, R.rep i a ∉ S := by
  by_contra h
  push_neg at h
  have hsub : univ.image (R.rep i) ⊆ S := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hv
    exact h a
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fun a a' h => R.rep_inj_right h), card_univ,
    Fintype.card_fin] at hcard
  omega

/-- The canonical representative of class `i` different from `v` (needs `2 ≤ q`). -/
noncomputable def canon (hq : 2 ≤ q) (i : Fin t) (v : V) : V :=
  if R.rep i ⟨0, by omega⟩ = v then R.rep i ⟨1, by omega⟩ else R.rep i ⟨0, by omega⟩

omit [Fintype V] in
theorem canon_mem (hq : 2 ≤ q) (i : Fin t) (v : V) : R.canon hq i v ∈ R.set := by
  unfold canon; split_ifs <;> exact R.rep_mem _ _

omit [Fintype V] in
theorem canon_cls (hq : 2 ≤ q) (i : Fin t) (v : V) : p (R.canon hq i v) = i := by
  unfold canon; split_ifs <;> exact R.cls _ _

omit [Fintype V] in
theorem canon_ne (hq : 2 ≤ q) (i : Fin t) (v : V) : R.canon hq i v ≠ v := by
  unfold canon
  split_ifs with h
  · intro h'
    have := R.rep_inj_right (h.trans h'.symm)
    simp at this
  · exact h

omit [Fintype V] in
/-- A non-representative sees the representative of index `0` as its canonical one. -/
theorem canon_of_notMem (hq : 2 ≤ q) (i : Fin t) {v : V} (hv : v ∉ R.set) :
    R.canon hq i v = R.rep i ⟨0, by omega⟩ := by
  unfold canon
  rw [if_neg]
  intro h; exact hv (h ▸ R.rep_mem _ _)

end Reps

/-! ### Support predicates -/

/-- Every edge in the support of `w` contains a representative. -/
def MeetsReps {p : V → Fin t} {q : ℕ} (R : Reps p q) (w : Sym2 V → ℤ) : Prop :=
  ∀ e, w e ≠ 0 → ∃ r ∈ R.set, r ∈ e

/-- Every edge in the support of `w` has both endpoints among the representatives. -/
def OnReps {p : V → Fin t} {q : ℕ} (R : Reps p q) (w : Sym2 V → ℤ) : Prop :=
  ∀ e, w e ≠ 0 → ∀ x ∈ e, x ∈ R.set

section Support

variable {p : V → Fin t} {q : ℕ} {R : Reps p q}

omit [Fintype V] in
theorem MeetsReps.zero : MeetsReps R (0 : Sym2 V → ℤ) := fun _ h => absurd rfl h

omit [Fintype V] in
theorem MeetsReps.add {w₁ w₂ : Sym2 V → ℤ} (h₁ : MeetsReps R w₁) (h₂ : MeetsReps R w₂) :
    MeetsReps R (w₁ + w₂) := by
  intro e he
  by_cases h : w₁ e = 0
  · exact h₂ e (by simpa [h] using he)
  · exact h₁ e h

omit [Fintype V] in
theorem MeetsReps.neg {w : Sym2 V → ℤ} (h : MeetsReps R w) : MeetsReps R (-w) :=
  fun e he => h e (by simpa using he)

omit [Fintype V] in
theorem MeetsReps.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : MeetsReps R w₁) (h₂ : MeetsReps R w₂) :
    MeetsReps R (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem MeetsReps.smul {w : Sym2 V → ℤ} (h : MeetsReps R w) (a : ℤ) : MeetsReps R (a • w) :=
  fun e he => h e (by intro h0; apply he; simp [h0])

omit [Fintype V] in
theorem MeetsReps.sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, MeetsReps R (f i)) : MeetsReps R (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact MeetsReps.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

omit [Fintype V] in
theorem MeetsReps.ind1 {e : Sym2 V} (h : ∃ r ∈ R.set, r ∈ e) : MeetsReps R (ind1 e) := by
  intro f hf
  rw [ind1_nonzero_iff] at hf
  subst hf; exact h

omit [Fintype V] in
theorem OnReps.zero : OnReps R (0 : Sym2 V → ℤ) := fun _ h => absurd rfl h

omit [Fintype V] in
theorem OnReps.add {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnReps R w₁) (h₂ : OnReps R w₂) :
    OnReps R (w₁ + w₂) := by
  intro e he
  by_cases h : w₁ e = 0
  · exact h₂ e (by simpa [h] using he)
  · exact h₁ e h

omit [Fintype V] in
theorem OnReps.neg {w : Sym2 V → ℤ} (h : OnReps R w) : OnReps R (-w) :=
  fun e he => h e (by simpa using he)

omit [Fintype V] in
theorem OnReps.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnReps R w₁) (h₂ : OnReps R w₂) :
    OnReps R (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem OnReps.smul {w : Sym2 V → ℤ} (h : OnReps R w) (a : ℤ) : OnReps R (a • w) :=
  fun e he => h e (by intro h0; apply he; simp [h0])

omit [Fintype V] in
theorem OnReps.sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, OnReps R (f i)) : OnReps R (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact OnReps.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

omit [Fintype V] in
theorem OnReps.ind1 {u v : V} (hu : u ∈ R.set) (hv : v ∈ R.set) : OnReps R (ind1 s(u, v)) := by
  intro f hf
  rw [ind1_nonzero_iff] at hf
  subst hf
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact hu
  · exact hv

omit [Fintype V] in
theorem OnReps.meetsReps {w : Sym2 V → ℤ} (h : OnReps R w) : MeetsReps R w := by
  intro e he
  induction e using Sym2.ind with
  | _ x y => exact ⟨x, h _ he x (Sym2.mem_mk_left x y), Sym2.mem_mk_left x y⟩

end Support

end PartitionedTriangleAbsorption.BlowupB
