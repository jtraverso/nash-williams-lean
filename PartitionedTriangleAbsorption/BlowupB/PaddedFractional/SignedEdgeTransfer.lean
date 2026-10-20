/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PrismKernel
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.MassCoupling

/-!
# Coupled repair of all signed occurrences over one physical edge

Positive and negative masses are matched before the local prism placements.
The unmatched mass is exactly the absolute boundary imbalance. In
particular, no unmatched face remains over a non-host edge with zero load.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer StructuralF3General

namespace SignedEdgeTransfer

def positivePart (x : ℝ) : ℝ := max x 0
def negativePart (x : ℝ) : ℝ := max (-x) 0

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := le_max_right _ _
theorem negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := le_max_right _ _

theorem parts_sub (x : ℝ) : positivePart x - negativePart x = x := by
  unfold positivePart negativePart
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith)]
    ring

theorem parts_add (x : ℝ) : positivePart x + negativePart x = |x| := by
  unfold positivePart negativePart
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith), abs_of_nonneg hx, add_zero]
  · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith),
      abs_of_nonpos (le_of_not_ge hx), zero_add]

theorem abs_sum_mul_bound {I : Type*} (A : Finset I) (c f B : I → ℝ)
    (hB : ∀ i ∈ A, |f i| ≤ B i) :
    |∑ i ∈ A, c i * f i| ≤ ∑ i ∈ A, |c i| * B i := by
  calc
    _ ≤ ∑ i ∈ A, |c i * f i| := abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ A, |c i| * |f i| := by simp only [abs_mul]
    _ ≤ _ := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (abs_nonneg _)

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    [DecidableRel G.Adj] {a b : V} {s : ℝ}

noncomputable def positiveRemainder (u : I → ℝ) (i : I) : ℝ :=
  positivePart (u i) - ∑ j, coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j

noncomputable def negativeRemainder (u : I → ℝ) (j : I) : ℝ :=
  negativePart (u j) - ∑ i, coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j

theorem remainders_nonneg (u : I → ℝ) :
    (∀ i, 0 ≤ positiveRemainder u i) ∧ (∀ i, 0 ≤ negativeRemainder u i) := by
  have hh := coupling_remainders (fun i => positivePart (u i)) (fun i => negativePart (u i))
    (fun i => positivePart_nonneg (u i)) (fun i => negativePart_nonneg (u i))
  exact ⟨hh.1, hh.2.1⟩

theorem parts_sum_sub (u : I → ℝ) :
    (∑ i, positivePart (u i)) - (∑ i, negativePart (u i)) = ∑ i, u i := by
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun i _ => parts_sub (u i)

theorem parts_sum_add (u : I → ℝ) :
    (∑ i, positivePart (u i)) + (∑ i, negativePart (u i)) = ∑ i, |u i| := by
  rw [← sum_add_distrib]
  exact sum_congr rfl fun i _ => parts_add (u i)

theorem remainders_total (u : I → ℝ) :
    (∑ i, positiveRemainder u i) + (∑ i, negativeRemainder u i) = |∑ i, u i| := by
  have hh := (coupling_remainders (fun i => positivePart (u i)) (fun i => negativePart (u i))
    (fun i => positivePart_nonneg (u i)) (fun i => negativePart_nonneg (u i))).2.2
  simpa only [positiveRemainder, negativeRemainder, parts_sum_sub] using hh

theorem remainders_zero (u : I → ℝ) (hu : (∑ i, u i) = 0) :
    (∀ i, positiveRemainder u i = 0) ∧ (∀ i, negativeRemainder u i = 0) := by
  apply coupling_remainders_zero (fun i => positivePart (u i)) (fun i => negativePart (u i))
    (fun i => positivePart_nonneg (u i)) (fun i => negativePart_nonneg (u i))
  have hh := parts_sum_sub u
  rw [hu] at hh
  exact sub_eq_zero.mp hh

theorem twice_coupling_le_mass (u : I → ℝ) :
    2 * (∑ i, ∑ j,
      coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j) ≤
        ∑ i, |u i| := by
  rw [coupling_total _ _ (fun i => positivePart_nonneg (u i))
    (fun i => negativePart_nonneg (u i)), ← parts_sum_add]
  have h1 := min_le_left (∑ i, positivePart (u i)) (∑ i, negativePart (u i))
  have h2 := min_le_right (∑ i, positivePart (u i)) (∑ i, negativePart (u i))
  linarith only [h1, h2]

noncomputable def repairedFamily (u : I → ℝ) (μ : I → ThirdDistribution p F G a b s) :
    TriangleChain V := fun Q =>
  (∑ i, positiveRemainder u i * (μ i).chain Q) -
  (∑ i, negativeRemainder u i * (μ i).chain Q) +
  ∑ i, ∑ j, coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j *
    prismKernel (μ i) (μ j) Q

theorem repairedFamily_supported (u : I → ℝ) (μ : I → ThirdDistribution p F G a b s)
    (hzero : ¬ G.Adj a b → (∑ i, u i) = 0) :
    CopySupported p F G (repairedFamily u μ) := by
  have hpos : CopySupported p F G (fun Q => ∑ i, positiveRemainder u i * (μ i).chain Q) := by
    apply CopySupported.sum univ
    intro i _
    by_cases hab : G.Adj a b
    · exact ((μ i).chain_supported hab).smul _
    · intro Q hQ
      dsimp only
      rw [(remainders_zero u (hzero hab)).1 i, zero_mul]
  have hneg : CopySupported p F G (fun Q => ∑ i, negativeRemainder u i * (μ i).chain Q) := by
    apply CopySupported.sum univ
    intro i _
    by_cases hab : G.Adj a b
    · exact ((μ i).chain_supported hab).smul _
    · intro Q hQ
      dsimp only
      rw [(remainders_zero u (hzero hab)).2 i, zero_mul]
  have hpair : CopySupported p F G (fun Q => ∑ i, ∑ j,
      coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j *
        prismKernel (μ i) (μ j) Q) := by
    apply CopySupported.sum univ
    intro i _
    apply CopySupported.sum univ
    intro j _
    exact (prismKernel_supported (μ i) (μ j)).smul _
  exact (hpos.sub hneg).add hpair

theorem repairedFamily_boundary (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (u : I → ℝ) (μ : I → ThirdDistribution p F G a b s) (hdist : ∀ _i : I, a ≠ b)
    (e : Sym2 V) :
    boundary (repairedFamily u μ) e = ∑ i, u i * boundary (μ i).chain e := by
  have hprism (i j : I) : boundary (prismKernel (μ i) (μ j)) e =
      boundary (μ i).chain e - boundary (μ j).chain e :=
    prismKernel_boundary hs0 hs (hdist i) (μ i) (μ j) e
  unfold repairedFamily
  simp only [boundary_add, boundary_sub, boundary_sum, boundary_smul, hprism]
  unfold positiveRemainder negativeRemainder
  rw [← coupling_evaluation]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sub_mul, parts_sub]

omit [DecidableRel G.Adj] in
theorem third_chain_bound (hs0 : 0 < s) (μ : ThirdDistribution p F G a b s)
    (hab : a ≠ b) (Q : Finset V) (hQ : Q.card = 3) :
    |μ.chain Q| ≤ (if s(a, b) ∈ triEdges Q then (1 : ℝ) else 0) * (3 / s) := by
  classical
  by_cases he : s(a, b) ∈ triEdges Q
  · rw [ite_eq_left he, one_mul, abs_of_nonneg (μ.chain_nonneg Q)]
    simpa only [hQ, Nat.cast_ofNat] using μ.chain_le_window hs0 Q
  · rw [ite_eq_right he, zero_mul, μ.chain_zero_of_edge_missing hab Q he, abs_zero]

theorem repairedFamily_bound (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (u : I → ℝ) (μ : I → ThirdDistribution p F G a b s) (hdist : ∀ _i : I, a ≠ b)
    (Q : Finset V) (hQ : Q.card = 3) :
    |repairedFamily u μ Q| ≤
      |∑ i, u i| * (if s(a, b) ∈ triEdges Q then (1 : ℝ) else 0) * (3 / s) +
      (∑ i, |u i|) *
        (((if a ∈ Q then (1 : ℝ) else 0) + (if b ∈ Q then (1 : ℝ) else 0)) *
          (3 / s) ^ 2 + (3 / s) ^ 3) := by
  classical
  let R : ℝ := (if s(a, b) ∈ triEdges Q then 1 else 0) * (3 / s)
  let B : ℝ := ((if a ∈ Q then 1 else 0) + (if b ∈ Q then 1 else 0)) *
    (3 / s) ^ 2 + (3 / s) ^ 3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr := remainders_nonneg u
  have hpos : |∑ i, positiveRemainder u i * (μ i).chain Q| ≤
      (∑ i, positiveRemainder u i) * R := by
    calc
      _ ≤ ∑ i, |positiveRemainder u i| * R :=
        abs_sum_mul_bound univ _ _ _ (fun i _ => third_chain_bound hs0 (μ i) (hdist i) Q hQ)
      _ = _ := by simp only [abs_of_nonneg (hr.1 _), sum_mul]
  have hneg : |∑ i, negativeRemainder u i * (μ i).chain Q| ≤
      (∑ i, negativeRemainder u i) * R := by
    calc
      _ ≤ ∑ i, |negativeRemainder u i| * R :=
        abs_sum_mul_bound univ _ _ _ (fun i _ => third_chain_bound hs0 (μ i) (hdist i) Q hQ)
      _ = _ := by simp only [abs_of_nonneg (hr.2 _), sum_mul]
  have hpair : |∑ i, ∑ j,
      coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j *
        prismKernel (μ i) (μ j) Q| ≤ (∑ i, |u i|) * B := by
    have hc (i j : I) : 0 ≤
        coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j :=
      coupling_nonneg _ _ (fun i => positivePart_nonneg (u i))
        (fun j => negativePart_nonneg (u j)) i j
    have hk (i j : I) : |prismKernel (μ i) (μ j) Q| ≤ 2 * B := by
      have hh := prismKernel_bound hs0 hs (μ i) (μ j) Q hQ
      dsimp [B]
      nlinarith only [hh]
    calc
      _ ≤ ∑ i, |∑ j,
          coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j *
            prismKernel (μ i) (μ j) Q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j,
          coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j * (2 * B) := by
        apply sum_le_sum
        intro i _
        have hh := abs_sum_mul_bound univ
          (fun j => coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j)
          (fun j => prismKernel (μ i) (μ j) Q) (fun _ => 2 * B) (fun j _ => hk i j)
        simpa only [abs_of_nonneg (hc i _)] using hh
      _ = (2 * (∑ i, ∑ j,
          coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j)) * B := by
        simp only [← sum_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (twice_coupling_le_mass u) hB
  have hres : |(∑ i, positiveRemainder u i * (μ i).chain Q) -
      (∑ i, negativeRemainder u i * (μ i).chain Q)| ≤ |∑ i, u i| * R := by
    have hh := abs_sub (∑ i, positiveRemainder u i * (μ i).chain Q)
      (∑ i, negativeRemainder u i * (μ i).chain Q)
    have hmass := congrArg (fun x : ℝ => x * R) (remainders_total u)
    nlinarith only [hh, hpos, hneg, hmass]
  have hh := abs_add_le
    ((∑ i, positiveRemainder u i * (μ i).chain Q) -
      (∑ i, negativeRemainder u i * (μ i).chain Q))
    (∑ i, ∑ j,
      coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j *
        prismKernel (μ i) (μ j) Q)
  change |(∑ i, positiveRemainder u i * (μ i).chain Q) -
      (∑ i, negativeRemainder u i * (μ i).chain Q) +
      (∑ i, ∑ j, coupling (fun i => positivePart (u i)) (fun j => negativePart (u j)) i j *
        prismKernel (μ i) (μ j) Q)| ≤ _
  have hfinal := hh.trans (add_le_add hres hpair)
  simpa only [R, B, mul_assoc] using hfinal

#print axioms repairedFamily_supported
#print axioms repairedFamily_boundary
#print axioms repairedFamily_bound

end SignedEdgeTransfer

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
