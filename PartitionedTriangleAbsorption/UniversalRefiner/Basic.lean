/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ModThreeLayer
public import PartitionedTriangleAbsorption.ParityChain
public import Mathlib.Tactic

/-!
# Universal ordinary refiner: request, atom and library indices; chain receipts

The bounded universal refiner is assembled from *atoms*: every physical edge set used by the
construction is either a single reserve edge (`Sum.inr e`) or the physical two-edge path
realising one *request* (`Sum.inl r`).  All the combinatorics (parity transport, telescoping
across levels, multiplicities) is carried out on finite sets of atoms; the physical graph is
only used at the end, through a pairwise edge-disjoint realisation of the atoms.

This file fixes the index types and proves the bookkeeping of one parity chain on index sets:
which wire paths a position receives (`recvLoc`), that distinct positions receive disjoint wire
paths, that every wire path is received, and the parity of the number of received paths.
The carry is `ParityChain.carry`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset

/-- Path requests of the construction.
* `ep l u j b`: level `l`, endpoint chain of `u`, wire `j`, path `A`/`B` (`b = false/true`);
* `pr l σ j b`: level `l`, chain of the hub pair `σ`, wire `j`, path `b`;
* `tm l σ b`: level `l`, terminal paths `f_σ` (`false`) and `f'_σ` (`true`);
* `md k c b`: mod-three wire `k`, cycle `c`, path `b`;
* `adj k b`: adjustment cycle `k`, path `b`. -/
inductive Req (V : Type*) where
  | ep (l : ℕ) (u : V) (j : ℕ) (b : Bool)
  | pr (l : ℕ) (σ : Sym2 V) (j : ℕ) (b : Bool)
  | tm (l : ℕ) (σ : Sym2 V) (b : Bool)
  | md (k : ℕ) (c : Fin 3) (b : Bool)
  | adj (k : ℕ) (b : Bool)
  deriving DecidableEq

/-- Atoms: realised requests and single reserve edges. -/
abbrev Atom (V : Type*) := Req V ⊕ Sym2 V

/-- Indices of the parity library.
* `alt l π x ca cb cs`: alternative of link `π` at level `l`, with selection bit `x` and the
  incoming carries of the two endpoint chains and of the pair chain;
* `cyc l σ`: the cycle piece `f_σ ∪ f'_σ`;
* `adj k`: the always-active adjustment cycle `k`. -/
inductive LibIdx (V : Type*) where
  | alt (l : ℕ) (π : Sym2 V) (x ca cb cs : Bool)
  | cyc (l : ℕ) (σ : Sym2 V)
  | adj (k : ℕ)
  deriving DecidableEq

variable {V : Type*} [DecidableEq V]

/-- Indicator of a vertex, over `ZMod 2`. -/
def ind (u : V) : V → ZMod 2 := fun w => if w = u then 1 else 0

/-- Indicator of the vertices of an unordered pair, over `ZMod 2`. -/
def symInd (e : Sym2 V) : V → ZMod 2 := fun w => if w ∈ e then 1 else 0

theorem symInd_mk {a b : V} (hab : a ≠ b) : symInd s(a, b) = ind a + ind b := by
  funext w
  by_cases ha : w = a <;> by_cases hb : w = b <;> simp_all [symInd, ind]

/-- The two chosen endpoints of an unordered pair. -/
noncomputable def endA (π : Sym2 V) : V := (Quot.out π).1
noncomputable def endB (π : Sym2 V) : V := (Quot.out π).2

omit [DecidableEq V] in
theorem mk_endA_endB (π : Sym2 V) : s(endA π, endB π) = π := Quot.out_eq π

omit [DecidableEq V] in
theorem mem_iff_endA_endB {π : Sym2 V} {u : V} : u ∈ π ↔ u = endA π ∨ u = endB π := by
  conv_lhs => rw [← mk_endA_endB π]
  exact Sym2.mem_iff

omit [DecidableEq V] in
theorem endA_ne_endB {π : Sym2 V} (hπ : ¬ π.IsDiag) : endA π ≠ endB π := by
  intro h
  apply hπ
  rw [← mk_endA_endB π, h]
  exact Sym2.mk_isDiag_iff.mpr rfl

theorem symInd_eq_ends {π : Sym2 V} (hπ : ¬ π.IsDiag) :
    symInd π = ind (endA π) + ind (endB π) := by
  conv_lhs => rw [← mk_endA_endB π]
  exact symInd_mk (endA_ne_endB hπ)

/-! ### Positions in a finite set -/

/-- The position of `a` in the finite set `C` (an arbitrary fixed enumeration). -/
noncomputable def pos {α : Type*} [DecidableEq α] (C : Finset α) (a : α) : ℕ :=
  if h : a ∈ C then (C.equivFin ⟨a, h⟩ : ℕ) else 0

theorem pos_lt {α : Type*} [DecidableEq α] {C : Finset α} {a : α} (ha : a ∈ C) :
    pos C a < C.card := by
  unfold pos; rw [dite_eq_left ha]; exact (C.equivFin ⟨a, ha⟩).isLt

theorem pos_inj {α : Type*} [DecidableEq α] {C : Finset α} {a b : α} (ha : a ∈ C) (hb : b ∈ C)
    (h : pos C a = pos C b) : a = b := by
  unfold pos at h; rw [dite_eq_left ha, dite_eq_left hb] at h
  have := C.equivFin.injective (Fin.ext h)
  simpa using this

theorem exists_pos_eq {α : Type*} [DecidableEq α] {C : Finset α} {j : ℕ} (hj : j < C.card) :
    ∃ a ∈ C, pos C a = j := by
  obtain ⟨⟨a, ha⟩, h⟩ := C.equivFin.surjective ⟨j, hj⟩
  refine ⟨a, ha, ?_⟩
  unfold pos; rw [dite_eq_left ha, h]

/-- The selection bits along the enumeration of `C`. -/
noncomputable def selBits {α : Type*} [DecidableEq α] (C S : Finset α) (j : ℕ) : Bool :=
  decide (∃ a ∈ C, a ∈ S ∧ pos C a = j)

theorem selBits_pos {α : Type*} [DecidableEq α] {C S : Finset α} {a : α} (ha : a ∈ C) :
    selBits C S (pos C a) = decide (a ∈ S) := by
  unfold selBits
  congr 1
  apply propext
  constructor
  · rintro ⟨b, hb, hbS, hab⟩
    rwa [pos_inj ha hb hab.symm]
  · intro haS; exact ⟨a, ha, haS, rfl⟩

/-- The number of selected positions is the number of selected elements. -/
theorem card_selBits {α : Type*} [DecidableEq α] (C S : Finset α) :
    ((range C.card).filter fun j => selBits C S j = true).card = (C ∩ S).card := by
  symm
  apply card_nbij (pos C)
  · intro a ha
    have ha' := mem_inter.mp ha
    rw [mem_coe, mem_filter, mem_range]
    exact ⟨pos_lt ha'.1, by rw [selBits_pos ha'.1]; simpa using ha'.2⟩
  · intro a ha b hb h
    exact pos_inj (mem_inter.mp (mem_coe.mp ha)).1 (mem_inter.mp (mem_coe.mp hb)).1 h
  · intro j hj
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj
    obtain ⟨a, ha, haS, rfl⟩ := of_decide_eq_true hj.2
    exact ⟨a, mem_coe.mpr (mem_inter.mpr ⟨ha, haS⟩), rfl⟩

/-! ### Carries -/

open ParityChain

/-- Incoming carry of position `j`. -/
def prevBit (x : ℕ → Bool) (j : ℕ) : Bool := decide (j ≠ 0 ∧ carry x (j - 1) = 1)

/-- Outgoing carry of position `j`. -/
def curBit (x : ℕ → Bool) (j : ℕ) : Bool := decide (carry x j = 1)

theorem curBit_eq (x : ℕ → Bool) (j : ℕ) : curBit x j = xor (prevBit x j) (x j) := by
  unfold curBit prevBit
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [carry_zero]; cases x 0 <;> simp
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [carry_succ]
    have hk := carry_lt x k
    simp only [Nat.add_sub_cancel]
    cases hx : x (k + 1) <;> rcases (by omega : carry x k = 0 ∨ carry x k = 1) with h | h <;>
      simp [h]

theorem prevBit_succ (x : ℕ → Bool) (j : ℕ) : prevBit x (j + 1) = curBit x j := by
  simp [prevBit, curBit]

theorem prevBit_zero (x : ℕ → Bool) : prevBit x 0 = false := by simp [prevBit]

/-- Final carry: parity of the number of selected positions. -/
theorem curBit_last (x : ℕ → Bool) (N : ℕ) (hN : 0 < N) :
    curBit x (N - 1) = decide (((range N).filter fun j => x j = true).card % 2 = 1) := by
  unfold curBit carry
  rw [Nat.sub_add_cancel hN]

/-! ### Received wire paths of one position -/

/-- Wire paths `(wire, path)` received by position `j` of a chain with `N` positions, given its
incoming carry `cp` and outgoing carry `cur`. -/
def recvLoc (N j : ℕ) (cp cur : Bool) : Finset (ℕ × Bool) :=
  (if j ≠ 0 ∧ cp = true then {(j - 1, true)} else ∅) ∪
    (if j + 1 < N then (if cur = true then {(j, false)} else {(j, false), (j, true)}) else ∅)

theorem mem_recvLoc {N j : ℕ} {cp cur : Bool} {q : ℕ × Bool} :
    q ∈ recvLoc N j cp cur ↔ (j ≠ 0 ∧ cp = true ∧ q = (j - 1, true)) ∨
      (j + 1 < N ∧ (q = (j, false) ∨ (cur = false ∧ q = (j, true)))) := by
  unfold recvLoc
  rw [mem_union]
  have e1 : (q ∈ if j ≠ 0 ∧ cp = true then ({(j - 1, true)} : Finset (ℕ × Bool)) else ∅) ↔
      (j ≠ 0 ∧ cp = true ∧ q = (j - 1, true)) := by
    split_ifs with h <;> simp <;> tauto
  have e2 : (q ∈ if j + 1 < N then (if cur = true then ({(j, false)} : Finset (ℕ × Bool))
      else {(j, false), (j, true)}) else ∅) ↔
      (j + 1 < N ∧ (q = (j, false) ∨ (cur = false ∧ q = (j, true)))) := by
    by_cases h : j + 1 < N <;> cases cur <;> simp [h]
  rw [e1, e2]

theorem recvLoc_wire_lt {N j : ℕ} {cp cur : Bool} {q : ℕ × Bool} (hj : j < N)
    (hq : q ∈ recvLoc N j cp cur) : q.1 + 1 < N := by
  rcases mem_recvLoc.mp hq with ⟨h0, -, rfl⟩ | ⟨hN, rfl | ⟨-, rfl⟩⟩ <;> simp <;> omega

theorem recvLoc_card_le (N j : ℕ) (cp cur : Bool) : (recvLoc N j cp cur).card ≤ 3 := by
  unfold recvLoc
  refine (card_union_le _ _).trans ?_
  have h1 : (if j ≠ 0 ∧ cp = true then ({(j - 1, true)} : Finset (ℕ × Bool)) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have h2 : (if j + 1 < N then (if cur = true then ({(j, false)} : Finset (ℕ × Bool))
      else {(j, false), (j, true)}) else ∅).card ≤ 2 := by
    split_ifs
    · simp
    · exact card_le_two
    · simp
  omega

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

theorem two_zmod2 : (2 : ZMod 2) = 0 := by decide

/-- Parity of the number of received wire paths. -/
theorem recvLoc_card_cast (N j : ℕ) (cp cur : Bool) :
    ((recvLoc N j cp cur).card : ZMod 2) =
      (if j ≠ 0 ∧ cp = true then 1 else 0) + (if j + 1 < N ∧ cur = true then 1 else 0) := by
  unfold recvLoc
  rw [card_union_of_disjoint]
  · push_cast
    congr 1
    · split_ifs <;> simp
    · by_cases h2 : j + 1 < N <;> cases cur <;> simp [h2, two_zmod2]
  · rw [disjoint_left]
    intro q hq hq'
    obtain ⟨hj, rfl⟩ : j ≠ 0 ∧ q = (j - 1, true) := by
      split_ifs at hq with h
      · exact ⟨h.1, mem_singleton.mp hq⟩
      · exact absurd hq (notMem_empty _)
    split_ifs at hq' with h2 h3 <;>
      simp only [mem_singleton, mem_insert, Prod.mk.injEq, notMem_empty] at hq' <;> omega

theorem prevBit_of_ne_zero (x : ℕ → Bool) {j : ℕ} (hj : j ≠ 0) :
    prevBit x j = curBit x (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simpa using prevBit_succ x k

/-- Distinct positions of one chain receive disjoint wire paths. -/
theorem recvLoc_disjoint (N : ℕ) (x : ℕ → Bool) {j j' : ℕ} (hne : j ≠ j') :
    Disjoint (recvLoc N j (prevBit x j) (curBit x j))
      (recvLoc N j' (prevBit x j') (curBit x j')) := by
  rw [disjoint_left]
  rintro ⟨i, b⟩ hq hq'
  rw [mem_recvLoc] at hq hq'
  simp only [Prod.mk.injEq] at hq hq'
  rcases hq with ⟨h0, hc, hi, hb⟩ | ⟨hN, ⟨hi, hb⟩ | ⟨hc, hi, hb⟩⟩ <;>
  rcases hq' with ⟨h0', hc', hi', hb'⟩ | ⟨hN', ⟨hi', hb'⟩ | ⟨hc', hi', hb'⟩⟩ <;>
    subst hb <;> simp at hb' <;> (try omega)
  · have hj' : j' = j - 1 := by omega
    rw [hj', ← prevBit_of_ne_zero x h0, hc] at hc'
    exact Bool.noConfusion hc'
  · have hj : j = j' - 1 := by omega
    rw [hj, ← prevBit_of_ne_zero x h0', hc'] at hc
    exact Bool.noConfusion hc

/-- Every wire path of the chain is received by some position. -/
theorem exists_recvLoc (N : ℕ) (x : ℕ → Bool) {q : ℕ × Bool} (hq : q.1 + 1 < N) :
    ∃ j < N, q ∈ recvLoc N j (prevBit x j) (curBit x j) := by
  obtain ⟨i, b⟩ := q
  cases b
  · exact ⟨i, by simp at hq; omega, mem_recvLoc.mpr (Or.inr ⟨hq, Or.inl rfl⟩)⟩
  · by_cases hc : curBit x i = true
    · refine ⟨i + 1, hq, mem_recvLoc.mpr (Or.inl ⟨by omega, ?_, by simp⟩)⟩
      rw [prevBit_succ]; exact hc
    · exact ⟨i, by simp at hq; omega,
        mem_recvLoc.mpr (Or.inr ⟨hq, Or.inr ⟨by simpa using hc, rfl⟩⟩)⟩

/-- In an endpoint chain whose final carry vanishes, a position receives an odd number of wire
paths exactly when it is selected. -/
theorem recvLoc_card_sel (x : ℕ → Bool) {N j : ℕ} (hj : j < N)
    (hlast : j + 1 = N → curBit x j = false) :
    ((recvLoc N j (prevBit x j) (curBit x j)).card : ZMod 2) = if x j = true then 1 else 0 := by
  rw [recvLoc_card_cast]
  have hp0 : j = 0 → prevBit x j = false := by rintro rfl; exact prevBit_zero x
  rw [curBit_eq] at hlast ⊢
  generalize prevBit x j = p at hp0 hlast ⊢
  generalize x j = s at hlast ⊢
  rcases eq_or_ne j 0 with rfl | h0
  · have hp := hp0 rfl
    subst hp
    by_cases hN : 1 < N
    · cases s <;> simp [hN]
    · have hN1 : N = 1 := by omega
      subst hN1
      cases s <;> simp_all
  · by_cases hN : j + 1 < N
    · cases p <;> cases s <;> simp [h0, hN, one_add_one_zmod2]
    · have hl := hlast (by omega)
      cases p <;> cases s <;> simp_all

/-- In a pair chain, the received wire paths together with the terminal `f_σ` (given at the last
position when the final carry is one) are odd exactly at selected positions. -/
theorem recvLoc_card_pair (x : ℕ → Bool) {N j : ℕ} (hj : j < N) :
    ((recvLoc N j (prevBit x j) (curBit x j)).card : ZMod 2) +
        (if j + 1 = N ∧ curBit x j = true then 1 else 0) = if x j = true then 1 else 0 := by
  rw [recvLoc_card_cast]
  have hp0 : j = 0 → prevBit x j = false := by rintro rfl; exact prevBit_zero x
  rw [curBit_eq]
  generalize prevBit x j = p at hp0 ⊢
  generalize x j = s
  rcases eq_or_ne j 0 with rfl | h0
  · have hp := hp0 rfl
    subst hp
    by_cases hN : 1 < N
    · have : ¬ (1 = N) := by omega
      cases s <;> simp [hN, this]
    · have hN1 : N = 1 := by omega
      subst hN1
      cases s <;> simp
  · by_cases hN : j + 1 < N
    · have : ¬ (j + 1 = N) := by omega
      cases p <;> cases s <;> simp [h0, hN, this, one_add_one_zmod2]
    · have : j + 1 = N := by omega
      cases p <;> cases s <;> simp [h0, this, one_add_one_zmod2]

end PartitionedTriangleAbsorption.UniversalRefiner
