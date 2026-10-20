/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.OddAbsorber

/-! # BlowupB.RainbowTrails — admissible trails for the rainbow type `{0, 1, 2}`

For the single rainbow type `R3 = {{0,1,2}}` every edge joins two different classes, and can be
oriented cyclically, from class `c` to class `c + 1` (`Arc`). Integral divisibility says that
at every vertex the two other classes receive the same degree (`degVec_R3_eq`), so in-degree
equals out-degree. A fibrewise bijection gives a permutation `σ` of the arcs with
`tail (σ i) = head i` (`trailPerm`): closed trails along which the class increases by one at
each step — the non-reversing transitions — and whose trail edges are exactly `P`
(`srcE_trailPerm`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

/-- The single rainbow type. -/
def R3 : Finset (Multiset (Fin 3)) := {{0, 1, 2}}

theorem card_R3 : ∀ τ ∈ R3, Multiset.card τ = 3 := by decide

theorem allowedPair_R3_iff : ∀ i j : Fin 3, AllowedPair R3 i j ↔ i ≠ j := by
  unfold AllowedPair R3; decide

theorem three_cycle_mem_R3 (c : Fin 3) : ({c, c + 1, c + 2} : Multiset (Fin 3)) ∈ R3 := by
  revert c; unfold R3; decide

/-! ### Degree vectors as counts -/

section Count

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem sum_ite_sym2_eq (p : V → Fin t) (v : V) {j : Fin t} (hj : j ≠ p v) (e : Sym2 V) :
    ∑ u, (if e = s(v, u) ∧ p u = j then (1 : ℤ) else 0) = degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk]
    by_cases ha : a = v <;> by_cases hb : b = v
    · subst ha; subst hb
      rw [Finset.sum_eq_zero]
      · simp [Ne.symm hj]
      · intro u _
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rcases Sym2.eq_iff.mp h1 with ⟨_, h3⟩ | ⟨h3, _⟩
        · exact hj (h3 ▸ h2).symm
        · exact hj (h3 ▸ h2).symm
    · subst ha
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro u _ hu
        rw [if_neg]
        rintro ⟨h1, _⟩
        rcases Sym2.eq_iff.mp h1 with ⟨_, h3⟩ | ⟨_, h3⟩
        · exact hu h3.symm
        · exact hb h3
      · intro h; exact absurd (mem_univ _) h
    · subst hb
      rw [Finset.sum_eq_single a]
      · simp [ha, Sym2.eq_swap]
      · intro u _ hu
        rw [if_neg]
        rintro ⟨h1, _⟩
        rcases Sym2.eq_iff.mp h1 with ⟨h3, _⟩ | ⟨h3, _⟩
        · exact ha h3
        · exact hu h3.symm
      · intro h; exact absurd (mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · simp [Ne.symm ha, Ne.symm hb, ha, hb]
      · intro u _
        rw [if_neg]
        rintro ⟨h1, _⟩
        rcases Sym2.eq_iff.mp h1 with ⟨h3, _⟩ | ⟨_, h3⟩
        · exact ha h3
        · exact hb h3

/-- Degree vectors count neighbours in the other classes. -/
theorem degVec_eq_card (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) {j : Fin t}
    (hj : j ≠ p v) :
    degVec p E v j = ((univ.filter fun u => s(v, u) ∈ E ∧ p u = j).card : ℤ) := by
  rw [degVec, Finset.sum_apply, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  have h : ∀ u, (if s(v, u) ∈ E ∧ p u = j then ((1 : ℕ) : ℤ) else 0) =
      ∑ e ∈ E, (if e = s(v, u) ∧ p u = j then (1 : ℤ) else 0) := by
    intro u
    simp only [ite_and, Finset.sum_ite_eq', Nat.cast_one]
  rw [sum_congr rfl fun u _ => h u, sum_comm]
  exact sum_congr rfl fun e _ => (sum_ite_sym2_eq p v hj e).symm

end Count

/-! ### Arcs and trails -/

section Trails

variable {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 3) (P : Finset (Sym2 V))

/-- Arcs of `P`, oriented from class `c` to class `c + 1`. -/
abbrev Arc : Type _ := {uw : V × V // s(uw.1, uw.2) ∈ P ∧ p uw.2 = p uw.1 + 1}

variable {p P}

/-- Tail and head of an arc. -/
def Arc.tail (i : Arc p P) : V := i.1.1
def Arc.head (i : Arc p P) : V := i.1.2

theorem Arc.cls (i : Arc p P) : p i.head = p i.tail + 1 := i.2.2

theorem fin3_succ_ne (c : Fin 3) : c + 1 ≠ c := by revert c; decide
theorem fin3_succ_succ_ne (c : Fin 3) : c + 2 ≠ c := by revert c; decide
theorem fin3_eq_add_two_iff (a b : Fin 3) : b = a + 1 ↔ a = b + 2 := by revert a b; decide

theorem card_head (v : V) :
    Fintype.card {i : Arc p P // i.head = v} =
      (univ.filter fun u => s(v, u) ∈ P ∧ p u = p v + 2).card := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun i => ⟨i.1.1.1, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩⟩
      invFun := fun u => ⟨⟨(u.1, v), ?_, ?_⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := i.1.2.1
    have h2 : i.1.1.2 = v := i.2
    rw [h2, Sym2.eq_swap] at h1; exact h1
  · have h3 := i.1.2.2
    have h2 : i.1.1.2 = v := i.2
    rw [h2] at h3; exact (fin3_eq_add_two_iff _ _).mp h3
  · rw [Sym2.eq_swap]; exact (mem_filter.mp u.2).2.1
  · exact (fin3_eq_add_two_iff _ _).mpr (mem_filter.mp u.2).2.2
  · rintro ⟨⟨⟨a, b⟩, h1⟩, h2⟩
    simp only [Arc.head] at h2
    subst h2
    rfl
  · rintro ⟨u, hu⟩; rfl

theorem card_tail (v : V) :
    Fintype.card {i : Arc p P // i.tail = v} =
      (univ.filter fun u => s(v, u) ∈ P ∧ p u = p v + 1).card := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun i => ⟨i.1.1.2, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩⟩
      invFun := fun u => ⟨⟨(v, u.1), (mem_filter.mp u.2).2.1, (mem_filter.mp u.2).2.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := i.1.2.1
    have h2 : i.1.1.1 = v := i.2
    rw [h2] at h1; exact h1
  · have h3 := i.1.2.2
    have h2 : i.1.1.1 = v := i.2
    rw [h2] at h3; exact h3
  · rintro ⟨⟨⟨a, b⟩, h1⟩, h2⟩
    simp only [Arc.tail] at h2
    subst h2
    rfl
  · rintro ⟨u, hu⟩; rfl

/-- For the rainbow type, the degrees into the two other classes agree. -/
theorem degVec_R3_eq (hdiv : IsIntDiv p R3 P) (v : V) :
    degVec p P v (p v + 1) = degVec p P v (p v + 2) := by
  obtain ⟨c, hc⟩ := hdiv.2 v
  have hmem0 : ∀ a : Fin 3, a ∈ ({0, 1, 2} : Multiset (Fin 3)) := by decide
  have hmem := hmem0 (p v)
  have hf : (R3.filter fun τ => p v ∈ τ) = {{0, 1, 2}} := by
    unfold R3; rw [Finset.filter_singleton, if_pos hmem]
  have hT0 : ∀ a j : Fin 3, typeDegVec ({0, 1, 2} : Multiset (Fin 3)) a j = if j = a then 0 else 1 := by
    unfold typeDegVec; decide
  have hT : ∀ j, typeDegVec ({0, 1, 2} : Multiset (Fin 3)) (p v) j = if j = p v then 0 else 1 :=
    fun j => hT0 (p v) j
  rw [hc, hf, sum_singleton]
  simp only [Pi.smul_apply, smul_eq_mul, hT, if_neg (fin3_succ_ne (p v)),
    if_neg (fin3_succ_succ_ne (p v))]

/-- In-degree equals out-degree. -/
theorem card_head_eq_card_tail (hdiv : IsIntDiv p R3 P) (v : V) :
    Fintype.card {i : Arc p P // i.head = v} = Fintype.card {i : Arc p P // i.tail = v} := by
  rw [card_head, card_tail]
  have h1 := degVec_eq_card p P v (fin3_succ_ne (p v))
  have h2 := degVec_eq_card p P v (fin3_succ_succ_ne (p v))
  have := degVec_R3_eq hdiv v
  rw [h1, h2] at this
  exact_mod_cast this.symm

/-- **The trail permutation**: `tail (σ i) = head i`. -/
noncomputable def trailPerm (hdiv : IsIntDiv p R3 P) : Equiv.Perm (Arc p P) :=
  Equiv.ofFiberEquiv (f := Arc.head) (g := Arc.tail)
    fun v => Fintype.equivOfCardEq (card_head_eq_card_tail hdiv v)

theorem tail_trailPerm (hdiv : IsIntDiv p R3 P) (i : Arc p P) :
    (trailPerm hdiv i).tail = i.head :=
  Equiv.ofFiberEquiv_map _ i

/-- Along a trail the class increases by one. -/
theorem cls_trailPerm (hdiv : IsIntDiv p R3 P) (i : Arc p P) :
    p (trailPerm hdiv i).tail = p i.tail + 1 := by
  rw [tail_trailPerm]; exact i.cls

theorem tail_ne_tail_trailPerm (hdiv : IsIntDiv p R3 P) (i : Arc p P) :
    i.tail ≠ (trailPerm hdiv i).tail := by
  intro h
  have := cls_trailPerm hdiv i
  rw [← h] at this
  exact fin3_succ_ne _ this.symm

theorem trailPerm_edge (hdiv : IsIntDiv p R3 P) (i : Arc p P) :
    s(i.tail, (trailPerm hdiv i).tail) = s(i.1.1, i.1.2) := by
  rw [tail_trailPerm]; rfl

theorem fin3_no_two_cycle : ∀ x y : Fin 3, x = y + 1 → y = x + 1 → False := by decide

theorem fin3_ne_cases : ∀ x y : Fin 3, x ≠ y → ¬ y = x + 1 → x = y + 1 := by decide

theorem trail_edge_injective (hdiv : IsIntDiv p R3 P) :
    Function.Injective fun i : Arc p P => s(i.tail, (trailPerm hdiv i).tail) := by
  intro i j hij
  simp only [trailPerm_edge] at hij
  rcases Sym2.eq_iff.mp hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · exfalso
    have ci : p i.1.2 = p i.1.1 + 1 := i.2.2
    have cj : p j.1.2 = p j.1.1 + 1 := j.2.2
    rw [h1, h2] at ci
    exact fin3_no_two_cycle _ _ ci cj

/-- The trail edges are exactly `P` (for `P` inside a rainbow blowup). -/
theorem srcE_trailPerm (hdiv : IsIntDiv p R3 P)
    (hP : ∀ a b, s(a, b) ∈ P → p a ≠ p b) :
    srcE (trailPerm hdiv) Arc.tail = P := by
  ext e
  simp only [srcE, mem_image, mem_univ, true_and, trailPerm_edge]
  constructor
  · rintro ⟨i, rfl⟩; exact i.2.1
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      have hab := hP a b he
      by_cases h1 : p b = p a + 1
      · exact ⟨⟨(a, b), he, h1⟩, rfl⟩
      · have h2 : p a = p b + 1 := fin3_ne_cases _ _ hab h1
        exact ⟨⟨(b, a), by rw [Sym2.eq_swap]; exact he, h2⟩, Sym2.eq_swap⟩

end Trails

end PartitionedTriangleAbsorption.BlowupB
