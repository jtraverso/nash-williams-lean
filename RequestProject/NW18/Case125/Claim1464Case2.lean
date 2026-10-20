/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Claim1464Cases

/-!
# Claim 14.6.4, case 2: `u₁, u₂` in different parts

There are `Ω(n²)` admissible pairs `(x, y)` for the six-vertex hinge `mH6`: with
`a = P(u₁) ≠ b = P(u₂)`, choose `x, y` in the parts

* `b, b` if `v₁, v₂ ∈ V_a` (choosing `y` first),
* `a, a` if `v₁, v₂ ∈ V_b`,
* `b, a` if `v₁, v₂` lie in different parts,

so that each choice is constrained by at most one internal neighbourhood (of size `≈ n/4`) and
otherwise by cross neighbourhoods (which miss only `O(ε₀ n)` vertices of a part).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma filter_forall_insert (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (j : Fin 2)
    (a : V) (s : Finset V) [DecidableEq V] :
    (partClass p j).filter (fun x => ∀ z ∈ insert a s, G.Adj z x) =
      ((partClass p j).filter (fun x => ∀ z ∈ s, G.Adj z x)).filter (G.Adj a) := by
  ext x
  simp only [mem_filter, forall_mem_insert]
  tauto

/-- A common neighbourhood inside a part misses at most the sum of the individual misses. -/
lemma card_commonNb_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (j : Fin 2)
    (Z : Finset V) :
    ((partClass p j).card : ℝ) - ∑ z ∈ Z, missIn G p z j ≤
      ((partClass p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)).card := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [filter_forall_insert, sum_insert has]
    have := card_filter_adj_ge G p (j := j)
      (S := (partClass p j).filter (fun x => ∀ z ∈ s, G.Adj z x)) (filter_subset _ _) a
    linarith

/-- The candidate set: vertices of `V_j` adjacent to `w` (a vertex of `V_j`) and to the vertices
of `Z` (outside `V_j`), avoiding `Bd`. -/
def goodSet (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (j : Fin 2) (w : V)
    (Z Bd : Finset V) : Finset V :=
  ((partClass p j).filter (fun x => ∀ z ∈ insert w Z, G.Adj z x)) \ Bd

lemma mem_goodSet {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 2} {j : Fin 2} {w : V}
    {Z Bd : Finset V} {x : V} :
    x ∈ goodSet G p j w Z Bd ↔ (p x = j ∧ G.Adj w x ∧ ∀ z ∈ Z, G.Adj z x) ∧ x ∉ Bd := by
  simp [goodSet, partClass]

lemma card_goodSet_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {e0 : ℝ}
    (hf : IdFacts e0 G p) {j : Fin 2} {w : V} (hw : p w = j) (Z Bd : Finset V)
    (hZ : ∀ z ∈ Z, p z ≠ j) (hZc : Z.card ≤ 3) (hBd : Bd.card ≤ 4) (he0 : 0 ≤ e0) :
    (1 / 4 - 6 * e0) * Fintype.card V - 4 ≤ (goodSet G p j w Z Bd).card := by
  have hwZ : w ∉ Z := fun h => hZ w h hw
  have h1 := card_commonNb_ge G p j (insert w Z)
  rw [sum_insert hwZ] at h1
  have h2 := hf.int w
  rw [hw] at h2
  have h3 : ∑ z ∈ Z, missIn G p z j ≤ Z.card • (3 / 2 * e0 * Fintype.card V) :=
    sum_le_card_nsmul _ _ _ fun z hz => hf.cross z j (hZ z hz)
  rw [nsmul_eq_mul] at h3
  have hZc' : (Z.card : ℝ) ≤ 3 := by exact_mod_cast hZc
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have h4 : (Z.card : ℝ) * (3 / 2 * e0 * Fintype.card V) ≤ 3 * (3 / 2 * e0 * Fintype.card V) :=
    mul_le_mul_of_nonneg_right hZc' (by positivity)
  have h6 : ((partClass p j).filter (fun x => ∀ z ∈ insert w Z, G.Adj z x)).card ≤
      (((partClass p j).filter (fun x => ∀ z ∈ insert w Z, G.Adj z x)) \ Bd).card + Bd.card :=
    card_le_card_sdiff_add_card
  have h6' : (((partClass p j).filter (fun x => ∀ z ∈ insert w Z, G.Adj z x)).card : ℝ) ≤
      ((((partClass p j).filter (fun x => ∀ z ∈ insert w Z, G.Adj z x)) \ Bd).card : ℝ) +
        Bd.card := by exact_mod_cast h6
  unfold goodSet
  have hBd' : (Bd.card : ℝ) ≤ 4 := by exact_mod_cast hBd
  have hen : 0 ≤ e0 * Fintype.card V := mul_nonneg he0 hn
  nlinarith

omit [Fintype V] in
lemma vec6_injective_of {u₁ u₂ v₁ v₂ x y : V} (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ v₁) (h14 : u₁ ≠ v₂)
    (h23 : u₂ ≠ v₁) (h24 : u₂ ≠ v₂) (h34 : v₁ ≠ v₂)
    (hx : x ∉ ({u₁, u₂, v₁, v₂} : Finset V)) (hy : y ∉ ({u₁, u₂, v₁, v₂} : Finset V))
    (hxy : x ≠ y) : Function.Injective (vec6 u₁ u₂ v₁ v₂ x y) := by
  simp only [mem_insert, mem_singleton, not_or] at hx hy
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [vec6] at h ⊢ <;> simp_all [eq_comm]

open Classical in
/-- Pairs from a nested choice give six-vertex hinges. -/
lemma hinge6_count_of_nested (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (u₁ u₂ v₁ v₂ : V) (A : Finset V) (B : V → Finset V) (f : V × V → V × V)
    (hf : Function.Injective f) {r : ℝ} (hr : 0 ≤ r) (hA : r ≤ A.card)
    (hB : ∀ x ∈ A, r ≤ (B x).card)
    (hP : ∀ x ∈ A, ∀ y ∈ B x, Function.Injective (vec6 u₁ u₂ v₁ v₂ (f (x, y)).1 (f (x, y)).2) ∧
      G.Adj u₁ (f (x, y)).1 ∧ G.Adj u₂ (f (x, y)).2 ∧ G.Adj v₁ (f (x, y)).1 ∧
      G.Adj v₁ (f (x, y)).2 ∧ G.Adj v₂ (f (x, y)).1 ∧ G.Adj v₂ (f (x, y)).2 ∧
      G.Adj (f (x, y)).1 (f (x, y)).2 ∧
      ¬ (p v₁ = p u₁ ∧ p u₁ = p (f (x, y)).1) ∧ ¬ (p v₁ = p u₂ ∧ p u₂ = p (f (x, y)).2) ∧
      ¬ (p v₂ = p (f (x, y)).1 ∧ p (f (x, y)).1 = p (f (x, y)).2) ∧
      ¬ (p v₂ = p u₁ ∧ p u₁ = p (f (x, y)).1) ∧
      ¬ (p v₂ = p u₂ ∧ p u₂ = p (f (x, y)).2) ∧
      ¬ (p v₁ = p (f (x, y)).1 ∧ p (f (x, y)).1 = p (f (x, y)).2)) :
    r * r ≤ ((G.edgeFinset.powerset.filter (fun H => IsHinge p F0 {u₁, u₂, v₁} {u₁, u₂, v₂} H ∧
        (vertSet H).card = 6)).card : ℝ) := by
  set P := (A.sigma B).image (fun z => f (z.1, z.2)) with hPdef
  have hPc : (P.card : ℝ) = ∑ x ∈ A, ((B x).card : ℝ) := by
    rw [hPdef, card_image_of_injective]
    · rw [card_sigma]; push_cast; rfl
    · rintro ⟨x, y⟩ ⟨x', y'⟩ h
      have := hf h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl
  have hsum : r * r ≤ ∑ x ∈ A, ((B x).card : ℝ) := by
    calc r * r ≤ A.card * r := mul_le_mul_of_nonneg_right hA hr
      _ = ∑ x ∈ A, r := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hB
  refine le_trans (hsum.trans hPc.symm.le) (pairs_le_hingeCount6 G p u₁ u₂ v₁ v₂ P ?_)
  intro z hz
  rw [hPdef, mem_image] at hz
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hz
  rw [mem_sigma] at hxy
  exact hP x hxy.1 y hxy.2

lemma fin2_eq_of_ne {a b c : Fin 2} (hab : a ≠ b) : c = a ∨ c = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

open Classical in
/-- **Case 2 of Claim 14.6.4.** -/
theorem case2_pairs (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {e0 : ℝ}
    (hf : IdFacts e0 G p) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1 / 1000)
    (hn : 100 ≤ (Fintype.card V : ℝ)) {u₁ u₂ v₁ v₂ : V} (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ v₁)
    (h14 : u₁ ≠ v₂) (h23 : u₂ ≠ v₁) (h24 : u₂ ≠ v₂) (h34 : v₁ ≠ v₂) (hp : p u₁ ≠ p u₂) :
    (Fintype.card V : ℝ) ^ 2 / 25 ≤
      ((G.edgeFinset.powerset.filter (fun H => IsHinge p F0 {u₁, u₂, v₁} {u₁, u₂, v₂} H ∧
        (vertSet H).card = 6)).card : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set Bd : Finset V := {u₁, u₂, v₁, v₂} with hBddef
  have hBd : Bd.card ≤ 4 := card_le_four
  have hr : (0 : ℝ) ≤ n / 5 := by positivity
  have hsz : ∀ {j w} (Z : Finset V), p w = j → (∀ z ∈ Z, p z ≠ j) → Z.card ≤ 3 →
      n / 5 ≤ (goodSet G p j w Z Bd).card := by
    intro j w Z hw hZ hZc
    have := card_goodSet_ge G p hf hw Z Bd hZ hZc hBd he0
    nlinarith
  have hsq : n ^ 2 / 25 = n / 5 * (n / 5) := by ring
  rw [hsq]
  have inj := fun {x y : V} (hx : x ∉ Bd) (hy : y ∉ Bd) (hxy : x ≠ y) =>
    vec6_injective_of h12 h13 h14 h23 h24 h34 hx hy hxy
  rcases fin2_eq_of_ne hp (c := p v₁) with hv₁ | hv₁ <;>
    rcases fin2_eq_of_ne hp (c := p v₂) with hv₂ | hv₂
  · -- `v₁, v₂ ∈ V_a`: `x, y ∈ V_b`, `y` first
    refine hinge6_count_of_nested G p u₁ u₂ v₁ v₂ (goodSet G p (p u₂) u₂ {v₁, v₂} Bd)
      (fun y => goodSet G p (p u₂) y {u₁, v₁, v₂} Bd) Prod.swap Prod.swap_injective hr
      (hsz _ rfl ?_ ((card_le_two.trans (by norm_num)))) (fun y hy => hsz _ ((mem_goodSet.mp hy).1.1) ?_ card_le_three)
      ?_
    · simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hv₁]; exact hp, by rw [hv₂]; exact hp⟩
    · simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨hp, by rw [hv₁]; exact hp, by rw [hv₂]; exact hp⟩
    · intro y hy x hx
      simp only [Prod.swap_prod_mk]
      obtain ⟨⟨py, ay, hyZ⟩, hyB⟩ := mem_goodSet.mp hy
      obtain ⟨⟨px, ax, hxZ⟩, hxB⟩ := mem_goodSet.mp hx
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hyZ hxZ
      refine ⟨inj hxB hyB (G.ne_of_adj ax).symm, hxZ.1, ay, hxZ.2.1, hyZ.1, hxZ.2.2, hyZ.2,
        SimpleGraph.Adj.symm ax, ?_⟩
      simp only [px, py, hv₁, hv₂]
      simp [hp]
  · -- `v₁ ∈ V_a`, `v₂ ∈ V_b`: `x ∈ V_b`, `y ∈ V_a`
    refine hinge6_count_of_nested G p u₁ u₂ v₁ v₂ (goodSet G p (p u₂) v₂ {u₁, v₁} Bd)
      (fun x => goodSet G p (p u₁) v₁ {x, u₂, v₂} Bd) id Function.injective_id hr
      (hsz _ hv₂ ?_ (card_le_two.trans (by norm_num))) (fun x hx => hsz _ hv₁ ?_ card_le_three) ?_
    · simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨hp, by rw [hv₁]; exact hp⟩
    · have px := (mem_goodSet.mp hx).1.1
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [px]; exact Ne.symm hp, Ne.symm hp, by rw [hv₂]; exact Ne.symm hp⟩
    · intro x hx y hy
      simp only [id]
      obtain ⟨⟨px, ax, hxZ⟩, hxB⟩ := mem_goodSet.mp hx
      obtain ⟨⟨py, ay, hyZ⟩, hyB⟩ := mem_goodSet.mp hy
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hyZ hxZ
      refine ⟨inj hxB hyB (G.ne_of_adj hyZ.1), hxZ.1, hyZ.2.1, hxZ.2, ay, ax, hyZ.2.2,
        hyZ.1, ?_⟩
      simp only [px, py, hv₁, hv₂]
      simp [hp, Ne.symm hp]
  · -- `v₁ ∈ V_b`, `v₂ ∈ V_a`: `x ∈ V_b`, `y ∈ V_a`
    refine hinge6_count_of_nested G p u₁ u₂ v₁ v₂ (goodSet G p (p u₂) v₁ {u₁, v₂} Bd)
      (fun x => goodSet G p (p u₁) v₂ {x, u₂, v₁} Bd) id Function.injective_id hr
      (hsz _ hv₁ ?_ (card_le_two.trans (by norm_num))) (fun x hx => hsz _ hv₂ ?_ card_le_three) ?_
    · simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨hp, by rw [hv₂]; exact hp⟩
    · have px := (mem_goodSet.mp hx).1.1
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [px]; exact Ne.symm hp, Ne.symm hp, by rw [hv₁]; exact Ne.symm hp⟩
    · intro x hx y hy
      simp only [id]
      obtain ⟨⟨px, ax, hxZ⟩, hxB⟩ := mem_goodSet.mp hx
      obtain ⟨⟨py, ay, hyZ⟩, hyB⟩ := mem_goodSet.mp hy
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hyZ hxZ
      refine ⟨inj hxB hyB (G.ne_of_adj hyZ.1), hxZ.1, hyZ.2.1, ax, hyZ.2.2, hxZ.2, ay,
        hyZ.1, ?_⟩
      simp only [px, py, hv₁, hv₂]
      simp [hp, Ne.symm hp]
  · -- `v₁, v₂ ∈ V_b`: `x, y ∈ V_a`, `x` first
    refine hinge6_count_of_nested G p u₁ u₂ v₁ v₂ (goodSet G p (p u₁) u₁ {v₁, v₂} Bd)
      (fun x => goodSet G p (p u₁) x {u₂, v₁, v₂} Bd) id Function.injective_id hr
      (hsz _ rfl ?_ (card_le_two.trans (by norm_num))) (fun x hx => hsz _ ((mem_goodSet.mp hx).1.1) ?_ card_le_three)
      ?_
    · simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hv₁]; exact Ne.symm hp, by rw [hv₂]; exact Ne.symm hp⟩
    · simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨Ne.symm hp, by rw [hv₁]; exact Ne.symm hp, by rw [hv₂]; exact Ne.symm hp⟩
    · intro x hx y hy
      simp only [id]
      obtain ⟨⟨px, ax, hxZ⟩, hxB⟩ := mem_goodSet.mp hx
      obtain ⟨⟨py, ay, hyZ⟩, hyB⟩ := mem_goodSet.mp hy
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hyZ hxZ
      refine ⟨inj hxB hyB (G.ne_of_adj ay), ax, hyZ.1, hxZ.1, hyZ.2.1, hxZ.2, hyZ.2.2,
        ay, ?_⟩
      simp only [px, py, hv₁, hv₂]
      simp [Ne.symm hp]

end NashWilliams18
