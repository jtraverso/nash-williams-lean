/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking

/-! # Physical common-neighbour and degree tails for the reserve -/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking

open Finset Nibble ReserveTests TypedNibble BernoulliExposure BernoulliConcentration

variable {V : Type*} [Fintype V] [DecidableEq V] {m t : ℕ}

abbrev Witness (S : TriSystem V m) (p : V → Fin t) (u v : V) (k : Fin t) :=
  {w : V // w ∈ coveredWitnesses S p u v k}

noncomputable def leftBlock (S : TriSystem V m) (p : V → Fin t) (u v : V) (k : Fin t)
    (w : Witness S p u v k) : Fin m :=
  blockOf S s(u, w.val) (mem_filter.mp w.property).2.1

noncomputable def rightBlock (S : TriSystem V m) (p : V → Fin t) (u v : V) (k : Fin t)
    (w : Witness S p u v k) : Fin m :=
  blockOf S s(v, w.val) (mem_filter.mp w.property).2.2.1

theorem leftBlock_edge (S : TriSystem V m) (p : V → Fin t) (u v : V) (k : Fin t)
    (w : Witness S p u v k) :
    s(u, w.val) ∈ Nibble.triEdges (S.tri (leftBlock S p u v k w)) :=
  blockOf_mem S _ _

theorem rightBlock_edge (S : TriSystem V m) (p : V → Fin t) (u v : V) (k : Fin t)
    (w : Witness S p u v k) :
    s(v, w.val) ∈ Nibble.triEdges (S.tri (rightBlock S p u v k w)) :=
  blockOf_mem S _ _

def reserveNeighbours (S : TriSystem V m) (p : V → Fin t) (x : Fin m → Bool)
    (u v : V) (k : Fin t) : Finset V :=
  univ.filter fun w => (ReserveCoverDown.reserveGraph (S.touched x)).Adj u w ∧
    (ReserveCoverDown.reserveGraph (S.touched x)).Adj w v ∧ p w = k

theorem pairCount_le_reserveNeighbours (S : TriSystem V m) (p : V → Fin t)
    (u v : V) (k : Fin t) (x : Fin m → Bool) :
    pairCount (univ : Finset (Witness S p u v k))
      (leftBlock S p u v k) (rightBlock S p u v k) x ≤
        (reserveNeighbours S p x u v k).card := by
  classical
  let Z := (univ : Finset (Witness S p u v k)).filter fun w =>
    x (leftBlock S p u v k w) = true ∧ x (rightBlock S p u v k w) = true
  have hcount : pairCount (univ : Finset (Witness S p u v k))
      (leftBlock S p u v k) (rightBlock S p u v k) x = (Z.card : ℝ) := by
    simp only [pairCount, pairIndicator, Z, card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcount]
  have hc : Z.card ≤ (reserveNeighbours S p x u v k).card := by
    apply card_le_card_of_injOn (fun w : Witness S p u v k => w.val)
    · intro w hw
      obtain ⟨_, hL, hR⟩ := mem_filter.mp hw
      have heL : s(u, w.val) ∈ S.touched x :=
        mem_biUnion.mpr ⟨leftBlock S p u v k w,
          mem_filter.mpr ⟨mem_univ _, hL⟩, leftBlock_edge S p u v k w⟩
      have heR : s(v, w.val) ∈ S.touched x :=
        mem_biUnion.mpr ⟨rightBlock S p u v k w,
          mem_filter.mpr ⟨mem_univ _, hR⟩, rightBlock_edge S p u v k w⟩
      have hneL := (Nibble.mem_triEdges.mp (leftBlock_edge S p u v k w)).2.2
      have hneR := (Nibble.mem_triEdges.mp (rightBlock_edge S p u v k w)).2.2
      refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, (mem_filter.mp w.property).2.2.2⟩
      · exact ⟨heL, hneL⟩
      · refine ⟨?_, hneR.symm⟩
        change s(w.val, v) ∈ S.touched x
        rwa [Sym2.eq_swap]
    · exact fun _ _ _ _ h => Subtype.ext h
  exact_mod_cast hc

/-- Physical lower tail, uniformly for every admissible pair and completion
class. The random variable is the actual reserve common neighbourhood. -/
theorem reserveNeighbours_lower_tail (S : TriSystem V m) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : SimpleGraph V) [DecidableRel J.Adj]
    (ρ ω : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 0 < Fintype.card V) (hanti : AntiEdgeful p F J ω)
    (hleft : DegBounded (J.edgeFinset \ edgesOf S univ) (ω * Fintype.card V / 8))
    {u v : V} (huv : u ≠ v) {k : Fin t}
    (ht : ({p u, p v, k} : Multiset (Fin t)) ∈ F) :
    cubeProb (fun _ : Fin m => ρ)
      (fun x => ((reserveNeighbours S p x u v k).card : ℝ) <
        ρ ^ 2 * ω * Fintype.card V / 4) ≤
      Real.exp (-(ρ ^ 3 * ω ^ 2 * Fintype.card V / 48)) := by
  classical
  have hq : ∀ _i : Fin m, 0 ≤ ρ ∧ ρ ≤ 1 := fun _ => ⟨hρ.le, hρ1⟩
  have hW : (univ : Finset (Witness S p u v k)).card =
      (coveredWitnesses S p u v k).card := by simp [Witness]
  have hsize : ((univ : Finset (Witness S p u v k)).card : ℝ) ≤ Fintype.card V := by
    rw [hW]
    exact_mod_cast card_le_univ (coveredWitnesses S p u v k)
  have hwitness : 3 * ω * Fintype.card V / 4 ≤
      ((univ : Finset (Witness S p u v k)).card : ℝ) := by
    rw [hW]
    exact coveredWitnesses_card S p F J ω hanti hleft huv ht
  have hc : ∀ i, ((univ : Finset (Witness S p u v k)).filter fun w =>
      leftBlock S p u v k w = i ∨ rightBlock S p u v k w = i).card ≤ 2 :=
    block_influence_le_two S univ Subtype.val Subtype.val_injective u v
      (leftBlock S p u v k) (rightBlock S p u v k)
      (fun w _ => leftBlock_edge S p u v k w)
      (fun w _ => rightBlock_edge S p u v k w)
  calc
    _ ≤ cubeProb (fun _ : Fin m => ρ) (fun x =>
        pairCount (univ : Finset (Witness S p u v k))
          (leftBlock S p u v k) (rightBlock S p u v k) x <
            ρ ^ 2 * ω * Fintype.card V / 4) :=
      cubeProb_mono _ hq (fun x hx => (pairCount_le_reserveNeighbours S p u v k x).trans_lt hx)
    _ ≤ _ := pairCount_lower_tail univ (leftBlock S p u v k) (rightBlock S p u v k)
      ρ ω (Fintype.card V) hρ hρ1 hω hω1 (by exact_mod_cast hn) hsize hwitness hc

/-- Physical degree upper tail for a selected triangle packing. -/
theorem reserveDegree_upper_tail (S : TriSystem V m) (hpack : IsPacking S univ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 0 < Fintype.card V) (v : V) :
    cubeProb (fun _ : Fin m => ρ)
      (fun x => 2 * ρ * Fintype.card V < ((star (S.touched x) v).card : ℝ)) ≤
        Real.exp (-(ρ * Fintype.card V / 8)) := by
  have hq : ∀ _i : Fin m, 0 ≤ ρ ∧ ρ ≤ 1 := fun _ => ⟨hρ.le, hρ1⟩
  have hs : 2 * ((S.through v).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast through_card_le S hpack v
  calc
    _ ≤ cubeProb (fun _ : Fin m => ρ)
        (fun x => ρ * Fintype.card V < blockCount (S.through v) x) := by
      apply cubeProb_mono _ hq
      intro x hx
      rw [degree_touched S hpack x v] at hx
      linarith only [hx]
    _ ≤ _ := blockCount_upper_tail (S.through v) ρ (Fintype.card V)
      hρ hρ1 (by exact_mod_cast hn) hs

#print axioms pairCount_le_reserveNeighbours
#print axioms reserveNeighbours_lower_tail
#print axioms reserveDegree_upper_tail

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReservePacking
