/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPhysicalCorrection

/-! # F1 and F2: from link coordinates to a sparse physical correction

The coordinate hypotheses are explicit. The output is a typed packing in the
host complement of the supplied input, not just an arithmetic correction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedApplicationCorrection

open Finset TypedLinkCoefficients TypedApplicationLinks TypedPhysicalCorrection

variable {V : Type*} [Fintype V] [DecidableEq V]

def F1Coordinates (p : V → Fin 4) (P : Finset (Sym2 V)) : Prop :=
  ∀ u, ∃ x y z : ℕ,
    degVec p P u = demand3 (p u) (first1 (p u)) (second1 (p u)) x y z ∧
    x ≤ y + z ∧ (x + y + z) % 2 = 0

def F2Coordinates (p : V → Fin 4) (P : Finset (Sym2 V)) : Prop :=
  (∀ u r, p u = lower2 r → ∃ x y z : ℕ,
    degVec p P u = demand3 (lower2 r) 2 3 x y z ∧
    x ≤ y + z ∧ y ≤ x + z ∧ z ≤ x + y ∧ (x + y + z) % 2 = 0) ∧
  (∀ u r, p u = upper2 r → ∃ x y z : ℕ,
    degVec p P u = demand3 (central2 r) 0 1 x y z ∧
    x ≤ y + z ∧ (x + y + z) % 2 = 0)

theorem positive_link_anchor {t : ℕ} (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset) (u : V) (i : Fin t)
    (hpos : 0 < degVec p P u i) : ∃ v, u ≠ v ∧ p v = i := by
  by_contra! h
  have hz : degVec p P u i = 0 := by
    simp only [degVec, sum_apply]
    apply sum_eq_zero
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := G.mem_edgeFinset.mp (hPG he)
      have h₁ : ¬ (a = u ∧ p b = i) := by
        rintro ⟨rfl, hi⟩
        exact h b hab.ne hi
      have h₂ : ¬ (b = u ∧ p a = i) := by
        rintro ⟨rfl, hi⟩
        exact h a hab.ne.symm hi
      simp [degContrib, h₁, h₂]
  omega

theorem demand3_repair (r a b : Fin 4) (x y z : ℕ) :
    demand3 r a b x y z + (basis r + basis a) =
      demand3 r a b (x + 1) (y + 1) z := by
  funext j
  simp only [demand3, Pi.add_apply, Nat.cast_add, Nat.cast_one]
  ring

theorem F1_repair_data (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset) (hc : F1Coordinates p P)
    (u : V) (hbad : ¬ Realizable F1 (p u) (degVec p P u)) :
    (∃ v, u ≠ v ∧ p v = first1 (p u)) ∧
      Realizable F1 (p u) (degVec p P u + (basis (p u) + basis (first1 (p u)))) := by
  obtain ⟨x, y, z, hd, hcone, hparity⟩ := hc u
  have hh : x = 0 ∧ y % 2 = 1 ∧ z % 2 = 1 :=
    (F1_hole_iff (p u) x y z hcone hparity).mp (hd ▸ hbad)
  constructor
  · apply positive_link_anchor p G P hPG u (first1 (p u))
    rw [hd]
    have hy : 0 < y := by omega
    have he : demand3 (p u) (first1 (p u)) (second1 (p u)) x y z (first1 (p u)) =
        (y : ℤ) := by
      generalize p u = r
      fin_cases r <;> simp [first1, second1, demand3, basis]
    rw [he]
    exact_mod_cast hy
  · rw [hd, demand3_repair]
    exact F1_corrected_coefficients (p u) x y z hcone hparity

/-- F1 physical link completion under the explicit coordinate conditions. -/
theorem F1_physical_correction (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset)
    (α : ℝ) (hanti : AntiEdgeful p F1 G α)
    (hP : DegBounded P (α * Fintype.card V / 8)) (hc : F1Coordinates p P)
    (q : ℕ) (hq : 0 < q) (hscale : 8 ≤ α * q)
    (hsize : 16 * ((q : ℝ) + 1) ≤ α * Fintype.card V) :
    ∃ R ⊆ G.edgeFinset, Disjoint P R ∧ DegBounded R (2 * (q + 1)) ∧
      HasDecomp p F1 R ∧ ∀ u, Realizable F1 (p u) (degVec p (P ∪ R) u) := by
  classical
  let s := univ.filter (fun u => ¬ Realizable F1 (p u) (degVec p P u))
  have hdata : ∀ u ∈ s, ∃ v, u ≠ v ∧ p v = first1 (p u) := by
    intro u hu
    exact (F1_repair_data p G P hPG hc u (mem_filter.mp hu).2).1
  let anchor : V → V := fun u => if hu : u ∈ s then (hdata u hu).choose else u
  apply exists_correction p F1 G α (α * Fintype.card V / 8) hanti P hP
    anchor p (fun u => first1 (p u)) s
  · intro u hu
    simpa only [anchor, dite_eq_left hu] using (hdata u hu).choose_spec
  · intro u _
    generalize p u = r
    fin_cases r <;> decide
  · intro u hu
    simpa [s] using hu
  · intro u hu
    exact (F1_repair_data p G P hPG hc u (mem_filter.mp hu).2).2
  · exact hq
  · exact correction_budget α (Fintype.card V) q s.card (by positivity)
      (by exact_mod_cast card_le_univ s) hq hscale hsize

def centralF2 : Fin 4 → Fin 4 := ![0, 0, 3, 2]

theorem F2_repair_data (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset) (hc : F2Coordinates p P)
    (u : V) (hbad : ¬ Realizable F2 (p u) (degVec p P u)) :
    (∃ v, u ≠ v ∧ p v = 0) ∧
      ({p u, centralF2 (p u), 0} : Multiset (Fin 4)) ∈ F2 ∧
      Realizable F2 (p u) (degVec p P u + (basis (centralF2 (p u)) + basis 0)) := by
  have hlower : ∀ r, p u ≠ lower2 r := by
    intro r hr
    obtain ⟨x, y, z, hd, hx, hy, hz, hp⟩ := hc.1 u r hr
    apply hbad
    rw [hr, hd]
    exact F2_lower_coefficients r x y z hx hy hz hp
  have hu : ∃ r, p u = upper2 r := by
    have h0 := hlower 0
    have h1 := hlower 1
    generalize p u = k at *
    fin_cases k
    · exact False.elim (h0 rfl)
    · exact False.elim (h1 rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  obtain ⟨r, hr⟩ := hu
  obtain ⟨x, y, z, hd, hcone, hparity⟩ := hc.2 u r hr
  have hh : x = 0 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
    apply (F2_upper_hole_iff r x y z hcone hparity).mp
    simpa only [hr, hd] using hbad
  have hcF : centralF2 (upper2 r) = central2 r := by fin_cases r <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · apply positive_link_anchor p G P hPG u 0
    rw [hd]
    have hy : 0 < y := by omega
    have he : demand3 (central2 r) 0 1 x y z 0 = (y : ℤ) := by
      fin_cases r <;> simp [central2, demand3, basis]
    rw [he]
    exact_mod_cast hy
  · rw [hr, hcF]
    fin_cases r <;> decide
  · rw [hr, hcF, hd, demand3_repair]
    exact F2_upper_corrected_coefficients r x y z hcone hparity

/-- F2 physical completion; lower roots already satisfy the triangle semigroup. -/
theorem F2_physical_correction (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset)
    (α : ℝ) (hanti : AntiEdgeful p F2 G α)
    (hP : DegBounded P (α * Fintype.card V / 8)) (hc : F2Coordinates p P)
    (q : ℕ) (hq : 0 < q) (hscale : 8 ≤ α * q)
    (hsize : 16 * ((q : ℝ) + 1) ≤ α * Fintype.card V) :
    ∃ R ⊆ G.edgeFinset, Disjoint P R ∧ DegBounded R (2 * (q + 1)) ∧
      HasDecomp p F2 R ∧ ∀ u, Realizable F2 (p u) (degVec p (P ∪ R) u) := by
  classical
  let s := univ.filter (fun u => ¬ Realizable F2 (p u) (degVec p P u))
  have hdata : ∀ u ∈ s, ∃ v, u ≠ v ∧ p v = 0 := by
    intro u hu
    exact (F2_repair_data p G P hPG hc u (mem_filter.mp hu).2).1
  let anchor : V → V := fun u => if hu : u ∈ s then (hdata u hu).choose else u
  apply exists_correction p F2 G α (α * Fintype.card V / 8) hanti P hP
    anchor (fun u => centralF2 (p u)) (fun _ => 0) s
  · intro u hu
    simpa only [anchor, dite_eq_left hu] using (hdata u hu).choose_spec
  · intro u hu
    exact (F2_repair_data p G P hPG hc u (mem_filter.mp hu).2).2.1
  · intro u hu
    simpa [s] using hu
  · intro u hu
    exact (F2_repair_data p G P hPG hc u (mem_filter.mp hu).2).2.2
  · exact hq
  · exact correction_budget α (Fintype.card V) q s.card (by positivity)
      (by exact_mod_cast card_le_univ s) hq hscale hsize

end PartitionedTriangleAbsorption.TypedApplicationCorrection
