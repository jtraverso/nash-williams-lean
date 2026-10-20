/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.OnePartDivisibility

/-!
# The parity chain (building block of the hub-hierarchy parity refiner)

Positions `0, …, N-1` carry bits `x j`. Between positions `j` and `j+1` there is a wire made of
two edge sets `A j`, `Bw j`, each odd exactly at the two roots `a`, `b`.
The carry is `c j = (x 0 + … + x j) mod 2`.

Position `j` receives:
* `Bw (j-1)` when `c (j-1) = 1`;
* from wire `j`, `A j` when `c j = 1`, and `A j ∪ Bw j` when `c j = 0`.

This file proves the chain mechanism of `REFINER_STATUS.md` §3.1:
* the received sets are pairwise disjoint (`recv_disjoint`);
* together they use every wire exactly once (`recv_union`);
* the received set at `j` is odd exactly at `a, b`, and only when `x j = 1`, except at the
  last position, where the final carry is added (`recv_parity`).

This is only the chain mechanism. The hub-level assembly (Lemma H) and the hierarchy
(Theorem P) are not formalised.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ParityChain

open Finset AntiEdgeSelection OnePart

variable {V : Type*} [DecidableEq V]

/-- Carry: parity of the number of set bits among positions `0..j`. -/
def carry (x : ℕ → Bool) (j : ℕ) : ℕ := ((range (j + 1)).filter fun i => x i = true).card % 2

/-- The edges received by position `j`. -/
def recv (N : ℕ) (x : ℕ → Bool) (A Bw : ℕ → Finset (Sym2 V)) (j : ℕ) : Finset (Sym2 V) :=
  (if j ≠ 0 ∧ carry x (j - 1) = 1 then Bw (j - 1) else ∅) ∪
    (if j + 1 < N then (if carry x j = 1 then A j else A j ∪ Bw j) else ∅)

/-- Indicator of the two roots. -/
def rootInd (a b w : V) : ℕ := if w = a ∨ w = b then 1 else 0

/-- Hypotheses on the wires. -/
structure ChainData (N : ℕ) (A Bw : ℕ → Finset (Sym2 V)) (a b : V) : Prop where
  disj_AB : ∀ i < N - 1, ∀ i' < N - 1, Disjoint (A i) (Bw i')
  disj_AA : ∀ i < N - 1, ∀ i' < N - 1, i ≠ i' → Disjoint (A i) (A i')
  disj_BB : ∀ i < N - 1, ∀ i' < N - 1, i ≠ i' → Disjoint (Bw i) (Bw i')
  par_A : ∀ i < N - 1, ∀ w, incidentLoad (A i) w % 2 = rootInd a b w
  par_B : ∀ i < N - 1, ∀ w, incidentLoad (Bw i) w % 2 = rootInd a b w

variable {N : ℕ} {x : ℕ → Bool} {A Bw : ℕ → Finset (Sym2 V)} {a b : V}

theorem carry_lt (x : ℕ → Bool) (j : ℕ) : carry x j < 2 := Nat.mod_lt _ (by norm_num)

theorem carry_zero (x : ℕ → Bool) : carry x 0 = if x 0 then 1 else 0 := by
  cases h : x 0 <;> simp [carry, range_one, filter_singleton, h]

theorem carry_succ (x : ℕ → Bool) (j : ℕ) :
    carry x (j + 1) = (carry x j + if x (j + 1) then 1 else 0) % 2 := by
  unfold carry
  rw [range_add_one (n := j + 1), filter_insert]
  cases h : x (j + 1)
  · simp
  · simp only [ite_true]
    rw [card_insert_of_notMem (by simp)]
    omega

theorem mem_recv {j : ℕ} {e : Sym2 V} :
    e ∈ recv N x A Bw j ↔ (j ≠ 0 ∧ carry x (j - 1) = 1 ∧ e ∈ Bw (j - 1)) ∨
      (j + 1 < N ∧ (e ∈ A j ∨ (carry x j ≠ 1 ∧ e ∈ Bw j))) := by
  unfold recv
  rw [mem_union]
  constructor
  · rintro (h1 | h1)
    · split_ifs at h1 with hc
      · exact Or.inl ⟨hc.1, hc.2, h1⟩
      · simp at h1
    · split_ifs at h1 with hN hc
      · exact Or.inr ⟨hN, Or.inl h1⟩
      · rcases mem_union.mp h1 with h2 | h2
        · exact Or.inr ⟨hN, Or.inl h2⟩
        · exact Or.inr ⟨hN, Or.inr ⟨hc, h2⟩⟩
      · simp at h1
  · rintro (⟨h0, hc, hb⟩ | ⟨hN, ha | ⟨hc, hb⟩⟩)
    · left; rw [ite_eq_left ⟨h0, hc⟩]; exact hb
    · right; rw [ite_eq_left hN]; split_ifs <;> simp [ha]
    · right; rw [ite_eq_left hN, ite_eq_right hc]; exact mem_union_right _ hb

theorem recv_disjoint (h : ChainData N A Bw a b) {j j' : ℕ} (hj : j < N) (hj' : j' < N)
    (hne : j ≠ j') : Disjoint (recv N x A Bw j) (recv N x A Bw j') := by
  rw [disjoint_left]
  intro e he he'
  rcases mem_recv.mp he with ⟨h0, hc, hb⟩ | ⟨hN, ha | ⟨hc, hb⟩⟩ <;>
  rcases mem_recv.mp he' with ⟨h0', hc', hb'⟩ | ⟨hN', ha' | ⟨hc', hb'⟩⟩
  · exact disjoint_left.mp (h.disj_BB _ (by omega) _ (by omega) (by omega)) hb hb'
  · exact disjoint_left.mp (h.disj_AB _ (by omega) _ (by omega)) ha' hb
  · by_cases hjj : j - 1 = j'
    · rw [hjj] at hc; exact hc' hc
    · exact disjoint_left.mp (h.disj_BB _ (by omega) _ (by omega) hjj) hb hb'
  · exact disjoint_left.mp (h.disj_AB _ (by omega) _ (by omega)) ha hb'
  · exact disjoint_left.mp (h.disj_AA _ (by omega) _ (by omega) hne) ha ha'
  · exact disjoint_left.mp (h.disj_AB _ (by omega) _ (by omega)) ha hb'
  · by_cases hjj : j = j' - 1
    · rw [hjj] at hc; exact hc hc'
    · exact disjoint_left.mp (h.disj_BB _ (by omega) _ (by omega) hjj) hb hb'
  · exact disjoint_left.mp (h.disj_AB _ (by omega) _ (by omega)) ha' hb
  · exact disjoint_left.mp (h.disj_BB _ (by omega) _ (by omega) hne) hb hb'

/-- The received sets use every wire edge exactly once (with `recv_disjoint`). -/
theorem recv_union :
    (range N).biUnion (recv N x A Bw) = (range (N - 1)).biUnion fun j => A j ∪ Bw j := by
  ext e
  simp only [mem_biUnion, mem_range, mem_union]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases mem_recv.mp he with ⟨h0, -, hb⟩ | ⟨hN, ha | ⟨-, hb⟩⟩
    · exact ⟨j - 1, by omega, Or.inr hb⟩
    · exact ⟨j, by omega, Or.inl ha⟩
    · exact ⟨j, by omega, Or.inr hb⟩
  · rintro ⟨j, hj, ha | hb⟩
    · exact ⟨j, by omega, mem_recv.mpr (Or.inr ⟨by omega, Or.inl ha⟩)⟩
    · by_cases hc : carry x j = 1
      · exact ⟨j + 1, by omega, mem_recv.mpr (Or.inl ⟨by omega, by simpa using hc,
          by simpa using hb⟩)⟩
      · exact ⟨j, by omega, mem_recv.mpr (Or.inr ⟨by omega, Or.inr ⟨hc, hb⟩⟩)⟩

theorem load_union_mod {E E' : Finset (Sym2 V)} (hd : Disjoint E E') (w : V) :
    incidentLoad (E ∪ E') w % 2 = (incidentLoad E w % 2 + incidentLoad E' w % 2) % 2 := by
  rw [incidentLoad_union hd]; omega

theorem rootInd_lt (w : V) : rootInd a b w < 2 := by
  unfold rootInd; split_ifs <;> norm_num

/-- **Parity of a received set.** At a position `j < N`, the received set is odd exactly at
the roots, and only when `x j = 1`. At the last position the final carry is added. -/
theorem recv_parity (h : ChainData N A Bw a b) {j : ℕ} (hj : j < N) (w : V) :
    incidentLoad (recv N x A Bw j) w % 2 =
      (rootInd a b w * ((if x j then 1 else 0) + (if j + 1 = N then carry x j else 0))) % 2 := by
  have hri := rootInd_lt (a := a) (b := b) w
  have hdisj : Disjoint (if j ≠ 0 ∧ carry x (j - 1) = 1 then Bw (j - 1) else ∅)
      (if j + 1 < N then (if carry x j = 1 then A j else A j ∪ Bw j) else ∅) := by
    rw [disjoint_left]
    intro e he he'
    by_cases h1 : j ≠ 0 ∧ carry x (j - 1) = 1
    · rw [ite_eq_left h1] at he
      by_cases hN : j + 1 < N
      · rw [ite_eq_left hN] at he'
        have hA : e ∉ A j := fun h4 =>
          disjoint_left.mp (h.disj_AB j (by omega) (j - 1) (by omega)) h4 he
        have hB : e ∉ Bw j := fun h4 =>
          disjoint_left.mp (h.disj_BB (j - 1) (by omega) j (by omega) (by omega)) he h4
        split_ifs at he' with hc
        · exact hA he'
        · rcases mem_union.mp he' with h4 | h4
          · exact hA h4
          · exact hB h4
      · rw [ite_eq_right hN] at he'; simp at he'
    · rw [ite_eq_right h1] at he; simp at he
  have hP1 : incidentLoad (if j ≠ 0 ∧ carry x (j - 1) = 1 then Bw (j - 1) else ∅) w % 2 =
      (if j ≠ 0 then rootInd a b w * carry x (j - 1) else 0) % 2 := by
    have hcl := carry_lt x (j - 1)
    by_cases h1 : j ≠ 0 ∧ carry x (j - 1) = 1
    · rw [ite_eq_left h1, h.par_B (j - 1) (by omega), ite_eq_left h1.1, h1.2, mul_one,
        Nat.mod_eq_of_lt hri]
    · rw [ite_eq_right h1]
      have : incidentLoad (∅ : Finset (Sym2 V)) w = 0 := by simp [incidentLoad]
      rw [this]
      by_cases h0 : j ≠ 0
      · have : carry x (j - 1) = 0 := by omega
        rw [ite_eq_left h0, this, mul_zero]
      · rw [ite_eq_right h0]
  have hP2 : incidentLoad (if j + 1 < N then (if carry x j = 1 then A j else A j ∪ Bw j)
      else ∅) w % 2 = (if j + 1 < N then rootInd a b w * carry x j else 0) % 2 := by
    have hcl := carry_lt x j
    by_cases hN : j + 1 < N
    · rw [ite_eq_left hN, ite_eq_left hN]
      by_cases hc : carry x j = 1
      · rw [ite_eq_left hc, h.par_A j (by omega), hc, mul_one, Nat.mod_eq_of_lt hri]
      · rw [ite_eq_right hc, load_union_mod (h.disj_AB j (by omega) j (by omega)),
          h.par_A j (by omega), h.par_B j (by omega)]
        have : carry x j = 0 := by omega
        rw [this]; omega
    · rw [ite_eq_right hN, ite_eq_right hN]; simp [incidentLoad]
  unfold recv
  rw [load_union_mod hdisj, hP1, hP2]
  generalize rootInd a b w = r at hri ⊢
  have hr01 : r = 0 ∨ r = 1 := by omega
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    have hc0 := carry_zero x
    by_cases hN : 0 + 1 < N
    · have : ¬ (0 + 1 = N) := by omega
      rw [ite_eq_right (by simp), ite_eq_left hN, ite_eq_right this]
      cases hx : x 0 <;> rcases hr01 with h' | h' <;> simp [hx, h', hc0]
    · have : 0 + 1 = N := by omega
      rw [ite_eq_right (by simp), ite_eq_right hN, ite_eq_left this]
      cases hx : x 0 <;> rcases hr01 with h' | h' <;> simp [hx, h', hc0]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hcs := carry_succ x k
    have hck := carry_lt x k
    have hck1 := carry_lt x (k + 1)
    rw [ite_eq_left (by omega), Nat.add_sub_cancel]
    by_cases hN : k + 1 + 1 < N
    · have : ¬ (k + 1 + 1 = N) := by omega
      rw [ite_eq_left hN, ite_eq_right this]
      cases hx : x (k + 1) <;> rcases hr01 with h' | h' <;> simp only [hx, h'] at hcs ⊢ <;>
        omega
    · have : k + 1 + 1 = N := by omega
      rw [ite_eq_right hN, ite_eq_left this]
      cases hx : x (k + 1) <;> rcases hr01 with h' | h' <;> simp only [hx, h'] at hcs ⊢ <;>
        omega

end PartitionedTriangleAbsorption.ParityChain

